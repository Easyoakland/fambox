use crate::{FamBox, FamBoxOwned, FamHeader};
use core::{
    marker::PhantomData,
    mem::{align_of, size_of, ManuallyDrop},
    ops::ControlFlow,
    ptr::{self, NonNull},
};

/// Incremental builder for [`FamBoxOwned`] to create a [`FamBoxOwned`] one element at a time.
/** ```rust
# use core::ops::ControlFlow;
use fambox::FamBoxBuilder;
struct H(u8, [u16; 0]);
unsafe impl fambox::FamHeader for H {
    type Element = u16;

    fn fam_len(&self) -> usize {
        self.0.into()
    }
}

let ControlFlow::Continue(builder) = FamBoxBuilder::new(H(2, [])) else { unreachable!() };
let ControlFlow::Continue(builder) = builder.add_element(1) else { unreachable!() };
let ControlFlow::Break(fambox) = builder.add_element(2) else { unreachable!() };
assert_eq!(fambox.header().0, 2);
assert_eq!(fambox.fam(), [1, 2]);
```
*/
pub struct FamBoxBuilder<H: FamHeader> {
    // Pointer to start of backing buffer including fam.
    // If `None` haven't allocated yet.
    ptr: NonNull<u8>,
    // Pointer to the next location to write `H::Element`.
    next_write: NonNull<H::Element>,
    // Type markers
    ty: PhantomData<H>,
}
impl<H: FamHeader> FamBoxBuilder<H> {
    /// Create a new [`FamBoxBuilder`]. If `header.fam_len()==0` then done building and return `Break(FamBoxOwned<H>)` otherwise return `Continue(FamBoxBuilder<H>)`.
    pub fn new(header: H) -> ControlFlow<FamBoxOwned<H>, FamBoxBuilder<H>> {
        let size = header.total_size();
        let fam_len = header.fam_len();
        debug_assert!(
            size_of::<H>() <= size,
            "invalid impl: size_of::<H>() > total size"
        );
        if size == 0 {
            // Safety: Since both `H` and `H::Element` are ZST, a dangling pointer is valid for the length of `H` followed by as many `H::Element` as fit in a slice.
            return if fam_len == 0 {
                // Safety: Since both `H` and `H::Element` are ZST the buffer is full with nothing written.
                ControlFlow::Break(unsafe {
                    FamBoxBuilder::<H> {
                        ptr: NonNull::dangling(),
                        next_write: NonNull::dangling(),
                        ty: PhantomData,
                    }
                    .build()
                })
            } else {
                ControlFlow::Continue(FamBoxBuilder::<H> {
                    ptr: NonNull::dangling(),
                    next_write: NonNull::dangling(),
                    ty: PhantomData,
                })
            };
        }

        let layout =
            alloc::alloc::Layout::from_size_align(size, align_of::<H>()).expect("invalid layout");
        // Safety: `layout` is non-zero in size. Alignment of `H` matches the allocation,
        // and the following [`H::Element`] is seperated from `H` by the necessary padding as required in the `FamHeader` trait.
        let Some(ptr) = NonNull::new(unsafe { alloc::alloc::alloc(layout) }.cast::<H>()) else {
            alloc::alloc::handle_alloc_error(layout);
        };

        // Write header
        // Safety: Allocation was created so that an `H` is valid at the start of the buffer.
        unsafe { ptr.as_ptr().write(header) };
        // Already wrote header so skip the header.
        // By the `FamHeader` trait contract ptr+1 is valid for writes of `H::Element`.
        let next_write = unsafe { NonNull::new_unchecked(ptr.as_ptr().add(1)).cast() };

        // Construct `Self` so the buffer is cleaned up on panic.
        if fam_len == 0 {
            // If no elements then done
            // Safety: The buffer is full since no elements to fill and header already written.
            ControlFlow::Break(unsafe {
                FamBoxBuilder {
                    ptr: ptr.cast(),
                    next_write,
                    ty: PhantomData,
                }
                .build()
            })
        } else {
            // Otherwise still need more elements.
            ControlFlow::Continue(FamBoxBuilder {
                ptr: ptr.cast(),
                // Already wrote header so skip the header.
                // By the `FamHeader` trait contract ptr+1 is valid for `H::Element`.
                next_write,
                ty: PhantomData,
            })
        }
    }
    /// Add an element to this [`FamBoxBuilder`]. If more elements are needed return `Continue(FamBoxBuilder<H>)`, otherwise,
    /// if done building return `Break(FamBoxOwned<H>)`.
    pub fn add_element(mut self, val: H::Element) -> ControlFlow<FamBoxOwned<H>, FamBoxBuilder<H>> {
        // Safety: `next_write` is valid to write an `H::Element` otherwise [`Self`] should have
        // called `self.build()` in a previous call to [`Self::add_element()`].
        unsafe { self.next_write.as_ptr().write(val) };

        // Set next position to write.
        // Safety: Either about to be done writing and pointer will point at 1 byte past the allocation,
        // or the next position is also valid by `FamHeader` trait contract and length of the allocation.
        self.next_write = unsafe { NonNull::new_unchecked(self.next_write.as_ptr().add(1)) };

        // Safety: Beginning is valid for dereference of `H` because `H` is ZST or buffer was allocated and start intialized with `H`.
        let total_size = unsafe { self.ptr.cast::<H>().as_ref() }.total_size();
        // Both pointers have provenance over the same allocation so `as usize` for both make sense.
        if self.next_write.as_ptr() as usize - self.ptr.as_ptr() as usize == total_size {
            // Safety: The elements have been finished writing
            ControlFlow::Break(unsafe { self.build() })
        } else {
            // If more elements need writing.
            ControlFlow::Continue(self)
        }
    }
}

impl<H: FamHeader> FamBoxBuilder<H> {
    /// Create a new `FamBoxBuilder<H>`
    // Used in the crate primarily for the purpose of re-using the builder's [`Drop`] impl.
    /// # Safety
    /// - `ptr` must be a pointer to a valid `FamBoxOwned`'s buffer.
    /// - [`Self::add_element`] must not be called if constructed with this method.
    /// Like from `FamBoxOwned::leak()`.
    pub(crate) unsafe fn from_built(ptr: NonNull<H>) -> Self {
        Self {
            ptr: ptr.cast(),
            // Safety: Since the [`FamBoxOwned`] has already been built the `next_write` pointer should point to 1 byte after the end.
            // Safety: Because the ptr is to a valid FamBoxOwned the pointer points to a valid `H`.
            next_write: unsafe {
                NonNull::new_unchecked(ptr.as_ptr().byte_add(ptr.as_ref().total_size()).cast())
            },
            ty: PhantomData,
        }
    }
    /// Consume the builder and construct a new [`FamBoxOwned<H>`]
    /// # Safety
    /// - The allocated buffer must be full with the layout of one `H` followed by `[H::Element]` of length `H::fam_len()`.
    unsafe fn build(self) -> FamBoxOwned<H> {
        // Safety: Because Self::Done is true the buffer is fully initialized.
        unsafe { FamBox::from_raw(ManuallyDrop::new(self).ptr.cast()) }
    }
}
impl<H: FamHeader> Drop for FamBoxBuilder<H> {
    fn drop(&mut self) {
        // Safety: Either ptr points to a ZST and the address doesn't matter or the header was already written to `ptr` in [`Self::new()`].
        let size = unsafe { self.ptr.cast::<H>().as_ref().total_size() };
        debug_assert!(
            size_of::<H>() <= size,
            "invalid impl: size_of::<H>() > total size"
        );
        // Drop the header.
        // Safety: Either ptr points to a ZST and the address doesn't matter or the header was already written to `ptr` in [`Self::new()`].
        unsafe { ptr::drop_in_place(self.ptr.cast::<H>().as_ptr()) };
        // Safety: A pointer to the end of the header is either pointing to 1 byte past the end of the allocation or the next `H::Element`.
        let mut next_to_drop = unsafe { self.ptr.cast::<H>().as_ptr().add(1).cast::<H::Element>() };

        // Drop the fam elements
        // `next_write` points at the end of the last written element (where the next element would have gone).
        // If `H::Element` is len 0 or `H::Element` is ZST this loop won't run at all.
        while next_to_drop != self.next_write.as_ptr() {
            // Safety: All positions before `self.next_write` have already been written to as valid `H::Element`.
            unsafe { ptr::drop_in_place(next_to_drop) };
            // Safety: The next element will either be after the previous or `next_to_drop` now points to 1 byte past the allocation which matches `self.next_write`.
            next_to_drop = unsafe { next_to_drop.add(1) };
        }
        if size == 0 {
            // If nothing allocated nothing to deallocate.
            return;
        }
        // Now that the entire buffer's elements have been dropped safe to drop the buffer itself without a leak.
        let layout =
            alloc::alloc::Layout::from_size_align(size, align_of::<H>()).expect("invalid layout");
        // Safety: [`Self`] can only be created by the same underlying allocator and layout.
        // `layout` is nonzero because `size` is nonzero.
        unsafe { alloc::alloc::dealloc(self.ptr.as_ptr(), layout) };
    }
}
