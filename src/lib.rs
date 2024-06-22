/*! [`FamBox`] datastructure to enable ergonomic and safe usage of c structs with a [flexible array member](https://en.wikipedia.org/wiki/Flexible_array_member).

[`FamBox`] comes in several flavors:
- [`FamBoxOwned`] for owned data.
- [`FamBoxMut`] for exclusively referenced data.
- [`FamBoxShared`] for aliased data.

Say you have this c struct:
```c
struct protocol_msg {
    uint8_t version;     /* Protocol version */
    uint8_t ty;          /* Protocol message type */
    uint16_t length;     /* Length in bytes including the flexible array member. */
    uint8_t elements[0]; /* msg data */
};
```
which [bindgen](https://crates.io/crates/bindgen) will translate to
```rust
# struct __IncompleteArrayField<T>([T;0]);
#[repr(C)]
pub struct protocol_msg {
    #[doc = " Protocol version"]
    version: u8,
    #[doc = " Protocol message type"]
    ty: u8,
    #[doc = " Length in bytes including the flexible array member."]
    length: u16,
    #[doc = " msg data"]
    elements: __IncompleteArrayField<u8>,
}
```
A [`FamBoxOwned`] can be used to safely construct a new instance of this type.
```rust
# #![allow(non_camel_case_types)]
use core::mem::size_of;
use fambox::FamBoxOwned;
#
// To be used safely, [`protocol_msg`] can't provide any safe mutable access to `length`.
pub use encapsulated_struct::protocol_msg;
mod encapsulated_struct {
    # use hidden::*;
    # pub mod hidden {
    #   #[derive(Debug)]
    #     pub struct Error;
    #     #[derive(Debug, PartialEq)]
    #     pub struct __IncompleteArrayField<T>([T;0]);
    #     impl<T> __IncompleteArrayField<T> {
    #         pub fn new() -> Self {
    #             Self([])
    #         }
    #     }
    # }
    use core::mem::size_of;
    use fambox::FamHeader;

    # #[repr(C)]
    # #[derive(Debug, PartialEq)]
    # pub struct protocol_msg {
    #     #[doc = " Protocol version"]
    #     pub version: u8,
    #     #[doc = " Protocol message type"]
    #     pub ty: u8,
    #     #[doc = " Length in bytes including the flexible array member."]
    #     length: u16,
    #     #[doc = " msg data"]
    #     elements: __IncompleteArrayField<u8>,
    # }
    #
    pub struct InvalidLength;

    # impl From<InvalidLength> for Error {
    #     fn from(_: InvalidLength) -> Self {
    #         Error
    #     }
    # }
    #
    impl protocol_msg {
        pub fn new(version: u8, ty: u8, buffer_len: usize) -> Result<Self, InvalidLength> {
            Ok(Self {
                version,
                ty,
                length: (size_of::<Self>()
                    + buffer_len * size_of::<<Self as FamHeader>::Element>())
                .try_into()
                .or(Err(InvalidLength))?,
                elements: __IncompleteArrayField::new(),
            })
        }
        pub fn length(&self) -> u16 {
            self.length
        }
    }

    // Safety:
    // `protocol_msg` doesn't expose a mutable setter which would make the length inconsistent.
    unsafe impl FamHeader for protocol_msg {
        type Element = u8;

        fn fam_len(&self) -> usize {
            let bytes_in_fam = usize::from(self.length) - size_of::<Self>();
            bytes_in_fam / size_of::<Self::Element>()
        }
    }
}
# fn test() -> Result<(), encapsulated_struct::hidden::Error> {
let data_buffer = [0, 1, 2, 3, 4, 5];
let header = encapsulated_struct::protocol_msg::new(1, 2, data_buffer.len())?;
let header_and_fam = FamBoxOwned::from_fn(header, |i| data_buffer[i]);
let header = encapsulated_struct::protocol_msg::new(1, 2, data_buffer.len())?;
assert_eq!(header_and_fam.header(), &header);
assert_eq!(header_and_fam.fam(), data_buffer);
assert_eq!(
    usize::from(header_and_fam.header().length()),
    size_of::<protocol_msg>() + core::mem::size_of_val(&data_buffer)
);
# Ok(())
# }
# test().unwrap()
```

or a [`FamBoxShared`]/[`FamBoxMut`] can be used to easily access and manipulate a fam containing struct from c
```rust,no_run
# use core::ptr::NonNull;
# use fambox::{FamBoxShared, FamBoxMut, FamHeader};
#
# #[repr(C)]
# #[derive(Debug, PartialEq)]
# struct __IncompleteArrayField<T>([T; 0]);
# #[repr(C)]
# #[derive(Debug, PartialEq)]
# pub struct protocol_msg {
#     #[doc = " Protocol version"]
#     version: u8,
#     #[doc = " Protocol message type"]
#     ty: u8,
#     #[doc = " Length in bytes including the flexible array member."]
#     length: u16,
#     #[doc = " msg data"]
#     elements: __IncompleteArrayField<u8>,
# }
# unsafe impl FamHeader for protocol_msg {
#     type Element = u8;
#
#     fn fam_len(&self) -> usize {
#         let bytes_in_fam = usize::from(self.length) - core::mem::size_of::<Self>();
#         bytes_in_fam / core::mem::size_of::<Self::Element>()
#     }
# }
extern "C" {
    fn original_header() -> protocol_msg;
    fn original_data() -> NonNull<u8>;
    fn original_data_len() -> usize;
    fn aliased_ptr_from_c() -> NonNull<protocol_msg>;
    fn alloc_in_c() -> NonNull<protocol_msg>;
    fn free_in_c(ptr: NonNull<protocol_msg>);
}

let header_and_fam = unsafe { FamBoxShared::from_raw(aliased_ptr_from_c()) };
assert_eq!(header_and_fam.as_parts(), unsafe {
    (&original_header(), unsafe { core::slice::from_raw_parts(original_data().as_ptr(), original_data_len()) })
});

let ptr = unsafe { alloc_in_c() };
let mut header_and_fam = unsafe { FamBoxMut::from_raw(ptr) };
assert_eq!(header_and_fam.as_parts(), unsafe {
    (&original_header(), unsafe { core::slice::from_raw_parts(original_data().as_ptr(), original_data_len()) })
});
header_and_fam.fam_mut()[2] = 10;
drop(header_and_fam);
unsafe { free_in_c(ptr) }
```

# Feature Flags
- `serde`: provide `Serialize` and `Deserialize` implementations for `FamBoxOwned`
*/

// Enable `cargo +nightly doc --all-features` to show all items and their feature requirements.
// `doccfg` is set by the `build.rs` when supported (nightly)
#![cfg_attr(doccfg, feature(doc_auto_cfg))]
#![cfg_attr(doccfg, feature(doc_cfg))]
#![no_std]

#[cfg(feature = "serde")]
mod serde;

/// Builder to create a new `FamBoxOwned` 1 element at a time.
// Also repurposed for its destructor
mod builder;
pub use builder::FamBoxBuilder;

extern crate alloc;
use core::{
    any,
    marker::PhantomData,
    mem::{self, align_of, align_of_val, size_of, size_of_val, ManuallyDrop},
    ops::ControlFlow,
    ptr::NonNull,
};

#[repr(C)]
#[derive(Debug)]
struct __IncompleteArrayField<T>([T; 0]);
impl<T> __IncompleteArrayField<T> {
    #[allow(dead_code)]
    const fn new() -> Self {
        Self([])
    }
}

/// A trait to enable usage of a struct which contains a [flexible array member](https://en.wikipedia.org/wiki/Flexible_array_member) in a [`FamBox`].
/// The struct will have some metadata which enables knowing how large the flexible array member is.
/// # Safety:
/// 1. The implementation for `fam_len` and `total_size` must be
/// - consistent with each other
/// - consistent across calls
///
/// or else undefined behavior may occur.
///
/// 2. Additionally, if `p` is a valid pointer to `H` then `p + size_of::<H>()` must match alignment requirements of `H::Element`.
/// This can be handled by placing a bindgen generated `__IncompleteArrayField<H::Element>` or `[H::Element; 0]` as the last field of the `repr(C)` `H`.
pub unsafe trait FamHeader {
    /// The element type of the flexible array member.
    type Element;
    /// The length, in `size_of::<H::Element>()` increments, of the flexible array member.
    fn fam_len(&self) -> usize;
    /// The total size of this struct, in bytes, including the header and the flexible array member.
    #[inline]
    fn total_size(&self) -> usize {
        debug_assert_eq!(
            (align_of_val(&self) + size_of_val(&self)) % align_of::<Self::Element>(),
            0,
            "FamHeader implemented for {} but its align + size doesn't match trait requirement 2",
            any::type_name_of_val(&self)
        );
        self.fam_len() * mem::size_of::<Self::Element>() + mem::size_of_val(self)
    }
}

/// The [`FamBox`] owns its buffer and will deallocate it when dropped.
#[derive(Debug, Default, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Owned;

/// The [`FamBox`] has an exclusive reference to its buffer.
#[derive(Default, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct BorrowedMut<'a>(core::marker::PhantomData<&'a ()>);
// Don't write Phantom.
impl<'a> core::fmt::Debug for BorrowedMut<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("BorrowedMut").finish()
    }
}

/// The [`FamBox`] has a shared reference to its buffer.
#[derive(Default, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct BorrowedShared<'a>(core::marker::PhantomData<&'a ()>);
// Don't write Phantom.
impl<'a> core::fmt::Debug for BorrowedShared<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("BorrowedShared").finish()
    }
}

mod sealed {
    pub trait Sealed {}
    impl Sealed for super::Owned {}
    impl<'a> Sealed for super::BorrowedMut<'a> {}
    impl<'a> Sealed for super::BorrowedShared<'a> {}
}

/// Sealed Marker trait representing if a buffer is [`Owned`] or [`BorrowedMut`] or [`BorrowedShared`].
pub trait Owner: sealed::Sealed {
    const OWNED: bool;
}
impl Owner for Owned {
    const OWNED: bool = true;
}
impl<'a> Owner for BorrowedMut<'a> {
    const OWNED: bool = false;
}
impl<'a> Owner for BorrowedShared<'a> {
    const OWNED: bool = false;
}

/// Sealed Marker trait representing that the buffer is exclusive.
pub trait Exclusive: Owner {}
impl Exclusive for Owned {}
impl<'a> Exclusive for BorrowedMut<'a> {}

/// Sealed Marker trait representing that the buffer is borrowed from somewhere else.
pub trait Borrowed: Owner {}
impl<'a> Borrowed for BorrowedMut<'a> {}
impl<'a> Borrowed for BorrowedShared<'a> {}

/// A smartpointer to a buffer which contains a [`FamHeader`] followed by a flexible array member in a continuous allocation.
pub struct FamBox<H: FamHeader, O: Owner> {
    // Pointer to backing buffer including fam.
    ptr: NonNull<u8>,
    // Type markers
    ty: PhantomData<(H, O)>,
}

/** [`Owned`] impls */
impl<H: FamHeader + Clone> Clone for FamBox<H, Owned>
where
    H::Element: Clone,
{
    /// The buffer, including the header and fam, is copied into a new allocation.
    #[inline]
    fn clone(&self) -> Self {
        self.into_owned()
    }
}
/** [`Owned`] impls */
impl<H: FamHeader + Default> Default for FamBox<H, Owned>
where
    H::Element: Default,
{
    #[inline]
    fn default() -> Self {
        Self::from_fn(H::default(), |_| H::Element::default())
    }
}
/** [`Owned`] impls */
impl<H: FamHeader> FamBox<H, Owned> {
    /// Allocate a new [`Owned`] buffer and create [`Self`] from a valid header and a callback for initializing the flexible array member.
    ///
    /// `cb` is passed the index being initialized.
    pub fn from_fn<F>(header: H, mut cb: F) -> Self
    where
        F: FnMut(usize) -> H::Element,
    {
        // By using the builder the memory will be correctly freed in the case of a `cb` panic.
        let mut builder = match FamBoxBuilder::new(header) {
            ControlFlow::Continue(builder) => builder,
            ControlFlow::Break(finished) => return finished,
        };
        let mut i = 0;
        loop {
            builder = match builder.add_element(cb(i)) {
                ControlFlow::Continue(unfinished) => unfinished,
                ControlFlow::Break(finished) => return finished,
            };
            i += 1;
        }
    }

    /// Leak [`Self`].
    pub fn leak(self) -> NonNull<H> {
        ManuallyDrop::new(self).ptr.cast()
    }
}

/** [`BorrowedMut`] impls */
impl<'a, H: FamHeader> FamBox<H, BorrowedMut<'a>> {
    /// Create a [`FamBoxMut<H>`] from a reference to a buffer containing `H` followed by `H::Element` of `H::fam_len()` length.
    /// # Safety
    /// - `slice` must match the above description (i.e. aligned to `H`, containing `H` followed by `H::fam_len()` `H::Element`s).
    #[inline]
    pub unsafe fn from_slice_mut(slice: &'a mut [u8]) -> Self {
        // Check that either the alignment is correct or `align_offset()` gave up.
        debug_assert!(
            matches!(slice.as_ptr().align_offset(align_of::<H>()), 0 | usize::MAX),
            "alignment doesn't match H"
        );
        Self {
            ty: PhantomData,
            ptr: NonNull::from(slice).cast(),
        }
    }
}

/** [`BorrowedShared`] impls */
impl<'a, H: FamHeader> Clone for FamBox<H, BorrowedShared<'a>> {
    /// Since the buffer is shared, clones the pointer but not the underlying buffer.
    #[inline]
    fn clone(&self) -> Self {
        Self {
            ptr: self.ptr,
            ty: self.ty,
        }
    }
}
/** [`BorrowedShared`] impls */
impl<'a, H: FamHeader> FamBox<H, BorrowedShared<'a>> {
    /// Create a [`FamBoxShared<H>`] from a reference to a buffer containing `H` followed by `H::Element` of `H::fam_len()` length.
    /// # Safety
    /// - `slice` must match the above description (i.e. aligned to `H`, containing `H` followed by `H::fam_len()` `H::Element`s).
    #[inline]
    pub unsafe fn from_slice(slice: &'a [u8]) -> Self {
        // Check that either the alignment is correct or `align_offset()` gave up.
        debug_assert!(
            matches!(slice.as_ptr().align_offset(align_of::<H>()), 0 | usize::MAX),
            "alignment doesn't match H"
        );
        Self {
            ty: PhantomData,
            ptr: NonNull::from(slice).cast(),
        }
    }
}
/** [`BorrowedShared`] impls */
impl<'a, H: FamHeader + PartialEq> PartialEq for FamBox<H, BorrowedShared<'a>>
where
    H::Element: PartialEq,
{
    /// Compares pointer addresses and if not equal compares parts.
    // Comparing pointers is a fast-path check since the pointed to buffer might be the same between `self` and `other`
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr || self.as_parts() == other.as_parts()
    }
}

/** [`Exclusive`] impls */
impl<H: FamHeader + PartialEq, O: Exclusive> PartialEq for FamBox<H, O>
where
    H::Element: PartialEq,
{
    /// Compares parts.
    // ptr can't be the same so it's not worth checking as a fast path.
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_parts() == other.as_parts()
    }
}
/** [`Exclusive`] impls */
impl<H: FamHeader, O: Exclusive> AsMut<H> for FamBox<H, O> {
    #[inline]
    fn as_mut(&mut self) -> &mut H {
        self.header_mut()
    }
}
/** [`Exclusive`] impls */
impl<H: FamHeader, O: Exclusive> AsMut<[H::Element]> for FamBox<H, O> {
    #[inline]
    fn as_mut(&mut self) -> &mut [H::Element] {
        self.fam_mut()
    }
}
/** [`Exclusive`] impls */
impl<H: FamHeader, O: Exclusive> FamBox<H, O> {
    #[inline]
    pub fn header_mut(&mut self) -> &mut H {
        // Safety: The head of the buffer contains a valid `H` and buffer is [`Exclusive`].
        unsafe { self.ptr.cast().as_mut() }
    }

    #[inline]
    pub fn fam_mut(&mut self) -> &mut [H::Element] {
        let fam_len = self.header().fam_len();
        // Safety: By construction `self.ptr` has provenance over the entire buffer and `self.ptr+size_of::<H>()` is the start of the fam.
        // Taking by `&mut self` on [`Exclusive`] buffer guarantees required exclusivity.
        unsafe {
            let fam = self.ptr.as_ptr().add(size_of::<H>()).cast();
            core::slice::from_raw_parts_mut(fam, fam_len)
        }
    }

    #[inline]
    pub fn as_parts_mut(&mut self) -> (&mut H, &mut [H::Element]) {
        // Safety: Inlined [`self.header_mut()`] to satisfy borrow checker.
        // Have to get header pointer before `fam` because `fam` takes by `&mut self`.
        // Have to get fam before `header.as_mut()` because `self.fam_mut()` reads header transiently.
        let mut header = self.ptr.cast();
        let fam = self.fam_mut();
        (unsafe { header.as_mut() }, fam)
    }
}

/** General impls for [`Owned`], [`BorrowedMut`], [`BorrowedShared`] */
impl<H: FamHeader + core::fmt::Debug, O: Owner + core::fmt::Debug + Default> core::fmt::Debug
    for FamBox<H, O>
where
    H::Element: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("FamBox")
            .field("ty", &O::default())
            .field("header", self.header())
            .field("fam", &self.fam())
            .finish()
    }
}
/** General impls for [`Owned`], [`BorrowedMut`], [`BorrowedShared`] */
impl<H: FamHeader + Eq, O: Owner> Eq for FamBox<H, O>
where
    H::Element: Eq,
    Self: PartialEq,
{
}
/** General impls for [`Owned`], [`BorrowedMut`], [`BorrowedShared`] */
impl<Header: FamHeader + core::hash::Hash, O: Owner> core::hash::Hash for FamBox<Header, O>
where
    Header::Element: core::hash::Hash,
{
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.as_parts().hash(state);
    }
}
/** General impls for [`Owned`], [`BorrowedMut`], [`BorrowedShared`] */
impl<H: FamHeader + PartialOrd, O: Owner> PartialOrd for FamBox<H, O>
where
    H::Element: PartialOrd,
    Self: PartialEq,
{
    /// Partial ordering is implemented with [lexicographic](https://en.wikipedia.org/wiki/Lexicographic_order) ordering,
    /// like the [`PartialOrd`] [derive macro](https://doc.rust-lang.org/std/cmp/trait.Ord.html#derivable),
    /// equivalent to a tuple of `(header, fam)`
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.as_parts().partial_cmp(&other.as_parts())
    }
}
/** General impls for [`Owned`], [`BorrowedMut`], [`BorrowedShared`] */
impl<H: FamHeader + Ord, O: Owner> Ord for FamBox<H, O>
where
    H::Element: Ord,
    Self: PartialEq,
{
    /// Partial ordering is implemented with [lexicographic](https://en.wikipedia.org/wiki/Lexicographic_order) ordering,
    /// like the [`PartialOrd`] [derive macro](https://doc.rust-lang.org/std/cmp/trait.Ord.html#derivable),
    /// equivalent to a tuple of `(header, fam)`
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_parts().cmp(&other.as_parts())
    }
}
/** General impls for [`Owned`], [`BorrowedMut`], [`BorrowedShared`] */
impl<H: FamHeader, O: Owner> AsRef<H> for FamBox<H, O> {
    #[inline]
    fn as_ref(&self) -> &H {
        self.header()
    }
}
/** General impls for [`Owned`], [`BorrowedMut`], [`BorrowedShared`] */
impl<H: FamHeader, O: Owner> AsRef<[H::Element]> for FamBox<H, O> {
    #[inline]
    fn as_ref(&self) -> &[H::Element] {
        self.fam()
    }
}
/** General impls for [`Owned`], [`BorrowedMut`], [`BorrowedShared`] */
impl<H: FamHeader, O: Owner> FamBox<H, O> {
    /// Create [`Self`] from a pointer to a buffer containing `H` followed by `[H::Element]` of `H::fam_len()` length.
    /// # Safety
    /// - `ptr` must match the above description.
    /// - the buffer must be valid for the lifetime of `Self`.
    /// - `ptr` must be exclusive if `O: Exclusive`.
    /// - `ptr` must have been allocated with [`alloc::alloc::GlobalAlloc`] if `O` = [`Owned`].
    ///
    /// The pointer from [`Self::leak()`] satisfies all of these.
    pub unsafe fn from_raw(ptr: NonNull<H>) -> Self {
        Self {
            ty: PhantomData,
            ptr: ptr.cast(),
        }
    }

    /// Copy to a [`FamBoxOwned<H>`] by copying the buffer into a newly allocated buffer.
    // Can't implement `ToOwned` because of conflict with blanket `impl<T: Clone> ToOwned for T {}`
    pub fn into_owned(&self) -> FamBox<H, Owned>
    where
        H: Clone,
        H::Element: Clone,
    {
        let (header, fam) = self.as_parts();
        FamBox::from_fn(header.clone(), |i| fam[i].clone())
    }

    /// Get a reference to the underlying buffer.
    /// # Safety
    /// - Only safe if `H` and `H::Element` don't have uninit bytes (e.g. padding).
    #[inline]
    pub unsafe fn buffer(&self) -> &[u8] {
        // Safety: Valid len by contract of [`FamHeader`] trait.
        unsafe { core::slice::from_raw_parts(self.ptr.as_ptr(), self.header().total_size()) }
    }
    #[inline]
    pub fn header(&self) -> &H {
        // Safety: The head of the buffer contains a valid `H`.
        unsafe { self.ptr.cast().as_ref() }
    }
    #[inline]
    pub fn fam(&self) -> &[H::Element] {
        let fam_len = self.header().fam_len();
        // Safety: By construction `self.ptr` has provenance over the entire buffer and `self.ptr+size_of::<H>()` is the start of the fam.
        unsafe {
            let fam = self.ptr.as_ptr().add(size_of::<H>()).cast();
            core::slice::from_raw_parts(fam, fam_len)
        }
    }
    #[inline]
    pub fn as_parts(&self) -> (&H, &[H::Element]) {
        // Safety: Inlined [`self.header()`] to satisfy borrow checker.
        (unsafe { self.ptr.cast().as_ref() }, self.fam())
    }
}
/** General impls for [`Owned`], [`BorrowedMut`], [`BorrowedShared`] */
impl<H: FamHeader, O: Owner> Drop for FamBox<H, O> {
    #[inline]
    fn drop(&mut self) {
        // Only deallocate if the buffer is owned (created with the same underlying allocator).
        // Would like to specialize the drop implementation, but that isn't currently possible in Rust.
        // See <https://github.com/rust-lang/rust/issues/8142>
        // and <https://internals.rust-lang.org/t/can-we-fix-drop-to-allow-specialization/12873/5>
        // So instead do this and expect that `#[inline]` means the impl is optimized out.
        if !O::OWNED {
            return;
        }

        // Safety: self is valid and so self.ptr is a valid pointer to the buffer.
        drop(unsafe { FamBoxBuilder::from_built(self.ptr.cast::<H>()) });
    }
}
/* Send/Sync impls */
// Exclusive [`FamBox`] can be used to get `&H`/`&mut H`/`&H::Element`/`&mut H::Element`.
unsafe impl<H: FamHeader + Send> Send for FamBox<H, Owned> where H::Element: Send {}
unsafe impl<'a, H: FamHeader + Send> Send for FamBox<H, BorrowedMut<'a>> where H::Element: Send {}

// Exclusive [`&FamBox`] can be used to get `&H`/`&H::Element`.
unsafe impl<H: FamHeader + Sync> Sync for FamBox<H, Owned> where H::Element: Sync {}
unsafe impl<'a, H: FamHeader + Sync> Sync for FamBox<H, BorrowedMut<'a>> where H::Element: Sync {}

// Shared [`FamBox`] can be used to get `&H`/`&H::Element`.
unsafe impl<'a, H: FamHeader + Sync> Send for FamBox<H, BorrowedShared<'a>> where H::Element: Sync {}
// Shared [`&FamBox`] can be used to get `&H`/`&H::Element`.
unsafe impl<'a, H: FamHeader + Sync> Sync for FamBox<H, BorrowedShared<'a>> where H::Element: Sync {}

/// A [`FamBox`] which owns its buffer.
pub type FamBoxOwned<H> = FamBox<H, Owned>;
/// A [`FamBox`] which has exclusive access to a buffer.
pub type FamBoxMut<'a, H> = FamBox<H, BorrowedMut<'a>>;
/// A [`FamBox`] which has shared access to a buffer.
pub type FamBoxShared<'a, H> = FamBox<H, BorrowedShared<'a>>;

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{rc::Rc, string::String};
    use core::{
        cell::Cell, fmt::Write, ops::ControlFlow, panic::AssertUnwindSafe, sync::atomic::AtomicBool,
    };

    /// Test struct.
    #[repr(C)]
    #[derive(Debug)]
    struct MsgHeader {
        this: u128,
        /// Bytes in this message.
        /// If this is changed may cause undefined behavior so it should only be accessible through a &self getter.
        len: u64,
        that: u8,
        val: __IncompleteArrayField<u16>,
    }
    /// Same as MsgHeader but no padding
    #[repr(C)]
    #[derive(Debug)]
    struct MsgNoPadding {
        this: u128,                       // 16
        len: u64,                         // 22
        that: u8,                         // 23
        padding: [u8; 7],                 // 30
        val: __IncompleteArrayField<u16>, // 32
    }
    impl Clone for MsgHeader {
        fn clone(&self) -> Self {
            Self {
                this: self.this.clone(),
                len: self.len.clone(),
                that: self.that.clone(),
                val: __IncompleteArrayField::new(),
            }
        }
    }
    impl PartialEq for MsgHeader {
        fn eq(&self, other: &Self) -> bool {
            self.this == other.this && self.len == other.len && self.that == other.that
        }
    }
    impl Eq for MsgHeader {}
    impl PartialOrd for MsgHeader {
        fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
            match self.this.partial_cmp(&other.this) {
                Some(core::cmp::Ordering::Equal) => {}
                ord => return ord,
            }
            match self.len.partial_cmp(&other.len) {
                Some(core::cmp::Ordering::Equal) => {}
                ord => return ord,
            }
            self.that.partial_cmp(&other.that)
        }
    }

    // Safety: matches trait contract
    unsafe impl FamHeader for MsgHeader {
        type Element = u16;
        #[inline]
        fn fam_len(&self) -> usize {
            let bytes_in_fam = self.len as usize - size_of::<Self>();
            bytes_in_fam / size_of::<u16>()
        }
    }
    impl Clone for MsgNoPadding {
        fn clone(&self) -> Self {
            Self {
                this: self.this.clone(),
                len: self.len.clone(),
                that: self.that.clone(),
                padding: self.padding.clone(),
                val: __IncompleteArrayField::new(),
            }
        }
    }
    impl PartialEq for MsgNoPadding {
        fn eq(&self, other: &Self) -> bool {
            self.this == other.this && self.len == other.len && self.that == other.that
        }
    }
    impl Eq for MsgNoPadding {}

    // Safety: matches trait contract
    unsafe impl FamHeader for MsgNoPadding {
        type Element = u16;
        #[inline]
        fn fam_len(&self) -> usize {
            let bytes_in_fam = self.len as usize - size_of::<Self>();
            bytes_in_fam / size_of::<u16>()
        }
    }
    const TEST_MSG: MsgHeader = MsgHeader {
        this: 42,
        len: size_of::<MsgHeader>() as u64 + 13,
        that: 55,
        val: __IncompleteArrayField::new(),
    };
    const TEST_MSG_NO_PADDING: MsgNoPadding = MsgNoPadding {
        this: 42,
        len: size_of::<MsgHeader>() as u64 + 13,
        that: 55,
        padding: [0; 7],
        val: __IncompleteArrayField::new(),
    };

    unsafe fn copy_for_test(buffer: &[u8]) -> &'static mut [u8] {
        let layout =
            alloc::alloc::Layout::from_size_align(buffer.len(), align_of::<MsgHeader>()).unwrap();
        let ptr = alloc::alloc::alloc(layout);
        core::ptr::copy(buffer.as_ptr(), ptr, buffer.len());
        core::slice::from_raw_parts_mut(ptr, buffer.len())
    }
    unsafe fn free_for_test(ptr: *mut u8, len: usize) {
        let layout = alloc::alloc::Layout::from_size_align(len, align_of::<MsgHeader>()).unwrap();
        alloc::alloc::dealloc(ptr, layout);
    }

    #[test]
    fn fambox_builder() {
        let ControlFlow::Continue(mut builder) = FamBoxBuilder::new(TEST_MSG) else {
            panic!("done early")
        };
        let mut i = 0;
        let mut next = builder.add_element(0);
        while let ControlFlow::Continue(x) = next {
            i += 1;
            builder = x;
            next = builder.add_element(i);
        }
        let ControlFlow::Break(_fambox) = next else {
            panic!("loop ended")
        };
    }
    #[test]
    fn fambox_builder_no_elements() {
        struct H(u8, [u32; 0]);
        unsafe impl FamHeader for H {
            type Element = u32;

            fn fam_len(&self) -> usize {
                self.0.into()
            }
        }
        assert!(FamBoxBuilder::new(H(0, [])).is_break())
    }
    #[test]
    fn fambox_builder_zst_header_and_some_elements() {
        struct H([u32; 0]);
        unsafe impl FamHeader for H {
            type Element = u32;

            fn fam_len(&self) -> usize {
                5
            }
        }
        assert!(FamBoxBuilder::new(H([])).is_continue())
    }
    #[test]
    fn fambox_builder_zst() {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        struct ZST;
        unsafe impl FamHeader for ZST {
            type Element = ();
            fn fam_len(&self) -> usize {
                0
            }
        }
        let ControlFlow::Break(_fambox) = FamBoxBuilder::new(ZST) else {
            panic!("done late")
        };
    }
    #[test]
    fn fambox_builder_drop() {
        let ControlFlow::Continue(builder) = FamBoxBuilder::new(TEST_MSG) else {
            panic!("done early")
        };
        let next = builder.add_element(0);
        drop(next)
    }
    #[test]
    fn parts_with_padding() {
        let own = FamBox::from_fn(TEST_MSG, |i| i as _);
        let (header, fam) = own.as_parts();
        assert_eq!(*header, TEST_MSG);
        assert_eq!(
            fam,
            core::array::from_fn::<_, 6, _>(|i| i as <MsgHeader as FamHeader>::Element)
        );
    }
    #[test]
    fn parts_eq() {
        let own = FamBox::from_fn(TEST_MSG_NO_PADDING, |i| i as _);
        let share = unsafe { FamBox::<MsgNoPadding, _>::from_slice(own.buffer()) };

        // Copy the buffer to a new buffer with a valid size/alignment to test exclusive shared.
        let buffer_mut = unsafe { copy_for_test(own.buffer()) };
        let exl = unsafe { FamBox::<MsgNoPadding, _>::from_slice_mut(buffer_mut) };

        assert_eq!(own.as_parts(), share.as_parts());
        assert_eq!(own.as_parts(), exl.as_parts());

        // Don't forget to free manually allocated memory.
        drop(exl);
        unsafe { free_for_test(buffer_mut.as_mut_ptr(), buffer_mut.len()) };
    }
    #[test]
    fn debug_impls() {
        let own = FamBox::from_fn(TEST_MSG_NO_PADDING, |i| i as _);
        let share = unsafe { FamBox::<MsgNoPadding, _>::from_slice(own.buffer()) };
        let buffer_mut = unsafe { copy_for_test(own.buffer()) };
        let exl = unsafe { FamBox::<MsgNoPadding, _>::from_slice_mut(buffer_mut) };
        let mut s = String::new();
        writeln!(s, "{own:?}").unwrap();
        writeln!(s, "{share:?}").unwrap();
        writeln!(s, "{exl:?}").unwrap();

        drop(exl);
        unsafe { free_for_test(buffer_mut.as_mut_ptr(), buffer_mut.len()) };
    }
    #[test]
    fn clone_impls() {
        let own = FamBox::from_fn(TEST_MSG_NO_PADDING, |i| i as _);
        let share = unsafe { FamBox::<MsgNoPadding, _>::from_slice(own.buffer()) };
        assert_eq!(own.clone().as_parts(), share.clone().as_parts());
        assert_eq!(unsafe { own.clone().buffer() }, unsafe {
            share.clone().buffer()
        });
        assert_eq!(own, own.clone());
        assert_eq!(share, share.clone());
    }
    #[test]
    fn zst() {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        struct ZST;
        unsafe impl FamHeader for ZST {
            type Element = ();
            fn fam_len(&self) -> usize {
                0
            }
        }
        let own = FamBox::from_fn(ZST, |_| ());
        let share = unsafe { FamBox::<ZST, _>::from_slice(own.buffer()) };
        let mut buf = unsafe { own.buffer() }.to_vec();
        let exl = unsafe { FamBox::<ZST, _>::from_slice_mut(&mut buf) };
        assert_eq!(unsafe { own.buffer() }.len(), 0);
        assert_eq!(own.as_parts(), share.as_parts());
        assert_eq!(own.as_parts(), exl.as_parts());
        let mut s = String::new();
        writeln!(s, "{own:?}").unwrap();
        writeln!(s, "{share:?}").unwrap();
        writeln!(s, "{exl:?}").unwrap();
    }
    #[test]
    fn zst_fam_element() {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        struct ZST(u8);
        unsafe impl FamHeader for ZST {
            type Element = ();
            fn fam_len(&self) -> usize {
                0
            }
        }
        let own = FamBox::from_fn(ZST(0), |_| ());
        let share = unsafe { FamBox::<ZST, _>::from_slice(own.buffer()) };
        let mut buf = unsafe { own.buffer() }.to_vec();
        let exl = unsafe { FamBox::<ZST, _>::from_slice_mut(&mut buf) };
        assert_eq!(unsafe { own.buffer() }.len(), 1);
        assert_eq!(own.as_parts(), share.as_parts());
        assert_eq!(own.as_parts(), exl.as_parts());
        let mut s = String::new();
        writeln!(s, "{own:?}").unwrap();
        writeln!(s, "{share:?}").unwrap();
        writeln!(s, "{exl:?}").unwrap();
    }
    #[test]
    fn zst_header() {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        struct ZST;
        unsafe impl FamHeader for ZST {
            type Element = u8;
            fn fam_len(&self) -> usize {
                3
            }
        }
        let own = FamBox::from_fn(ZST, |i| i as _);
        let share = unsafe { FamBox::<ZST, _>::from_slice(own.buffer()) };
        let mut buf = unsafe { own.buffer() }.to_vec();
        let exl = unsafe { FamBox::<ZST, _>::from_slice_mut(&mut buf) };
        assert_eq!(unsafe { own.buffer() }.len(), 3);
        assert_eq!(own.as_parts(), share.as_parts());
        assert_eq!(own.as_parts(), exl.as_parts());
        let mut s = String::new();
        writeln!(s, "{own:?}").unwrap();
        writeln!(s, "{share:?}").unwrap();
        writeln!(s, "{exl:?}").unwrap();
    }
    #[test]
    fn leak_from_raw() {
        let own = FamBox::from_fn(TEST_MSG, |i| i as _);
        let own_clone = own.clone();
        let from_leak = unsafe { FamBox::from_raw(own.leak()) };
        assert_eq!(own_clone, from_leak);
    }
    #[test]
    fn drop_cnt() {
        struct H(u8, [DropCnt; 0]);
        unsafe impl FamHeader for H {
            type Element = DropCnt;

            fn fam_len(&self) -> usize {
                self.0.into()
            }
        }
        static H_DROPPED: AtomicBool = AtomicBool::new(false);
        impl Drop for H {
            fn drop(&mut self) {
                H_DROPPED.store(true, core::sync::atomic::Ordering::Relaxed);
            }
        }
        #[derive(Debug, Clone)]
        struct DropCnt(Rc<Cell<u8>>);
        impl Drop for DropCnt {
            fn drop(&mut self) {
                self.0.set(self.0.get() + 1);
            }
        }
        let item = DropCnt(Rc::new(Cell::new(0)));
        let own = FamBox::from_fn(H(13, []), |_| item.clone());
        drop(own);
        assert_eq!(item.0.get(), 13);
        assert!(H_DROPPED.load(core::sync::atomic::Ordering::Relaxed));
    }
    #[test]
    fn callback_panic() {
        struct H(u8, Rc<Cell<u8>>, [DropCnt; 0]);
        unsafe impl FamHeader for H {
            type Element = DropCnt;

            fn fam_len(&self) -> usize {
                self.0.into()
            }
        }
        static H_DROPPED: AtomicBool = AtomicBool::new(false);
        impl Drop for H {
            fn drop(&mut self) {
                H_DROPPED.store(true, core::sync::atomic::Ordering::Relaxed);
                self.1.set(self.1.get() + 1);
            }
        }
        #[derive(Debug, Clone)]
        struct DropCnt(Rc<Cell<u8>>);
        impl Drop for DropCnt {
            fn drop(&mut self) {
                self.0.set(self.0.get() + 1);
            }
        }
        extern crate std;
        let item = DropCnt(Rc::new(Cell::new(0)));
        let h_drop = Rc::new(Cell::new(0));
        if !std::panic::catch_unwind(AssertUnwindSafe(|| {
            drop(FamBox::from_fn(H(4, h_drop.clone(), []), |i| {
                if i > 2 {
                    panic!("oops")
                } else {
                    item.clone()
                }
            }))
        }))
        .is_err()
        {
            panic!("didn't panic when constructing")
        }
        assert_eq!(item.0.get(), 3);
        assert!(H_DROPPED.load(core::sync::atomic::Ordering::Relaxed));
        assert_eq!(h_drop.get(), 1);
    }
    #[test]
    fn as_ref_as_mut() {
        // use core::convert::AsRef;
        let mut own = FamBox::from_fn(TEST_MSG, |i| i as _);
        let _header: &MsgHeader = own.as_ref();
        let _fam: &[<MsgHeader as FamHeader>::Element] = own.as_ref();
        let header_mut: &mut MsgHeader = own.as_mut();
        header_mut.that += 1;
        let fam_mut: &mut [<MsgHeader as FamHeader>::Element] = own.as_mut();
        fam_mut[3] = 4;
    }
    #[test]
    fn eq_test() {
        let mut own = FamBox::from_fn(TEST_MSG, |i| i as _);
        let own2 = FamBox::from_fn(TEST_MSG, |i| i as _);
        assert_eq!(own, own2);
        own.fam_mut()[3] += 1;
        assert_ne!(own, own2);
        own.fam_mut()[3] -= 1;
        assert_eq!(own, own2);
        own.header_mut().that += 1;
        assert_ne!(own, own2);
        own.header_mut().that -= 1;
        assert_eq!(own, own2);
    }
    #[test]
    fn ord_test() {
        let mut own = FamBox::from_fn(TEST_MSG, |i| i as _);
        let mut own2 = FamBox::from_fn(TEST_MSG, |i| i as _);
        assert_eq!(own, own2);
        own.fam_mut()[3] += 1;
        assert!(own > own2);
        own2.header_mut().that += 1;
        assert!(own < own2);
    }
}
