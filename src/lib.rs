//! Utilities to use a struct with a flexible array member.

// Enable `cargo +nightly doc --all-features` to show all items and their feature requirements.
// `doccfg` is set by the `build.rs` when supported (nightly)
#![cfg_attr(doccfg, feature(doc_auto_cfg))]
#![cfg_attr(doccfg, feature(doc_cfg))]
#![no_std]

#[cfg(feature = "serde")]
mod serde;

extern crate alloc;
use core::{
    any,
    marker::PhantomData,
    mem::{self, align_of, align_of_val, size_of, size_of_val},
    ptr::{self, NonNull},
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

/// Construct a slice from [`__IncompleteArrayField`] without breaking stacked borrows in miri.
/// # Safety
/// - The `orig_ptr` should have provenance over the entire returned slice.
/// - `array` should be the start of a valid slice of `T` with a `length >= len`
///
/// See <https://github.com/rust-lang/rust-bindgen/issues/1892>
#[inline]
unsafe fn slice_from_flexarray<S, T>(
    orig_ptr: *const S,
    array: &__IncompleteArrayField<T>,
    len: usize,
) -> &[T] {
    let offs = ptr::from_ref(array) as usize - orig_ptr as usize;
    let sanitized_ptr = (orig_ptr as *const u8).add(offs) as *const T;
    core::slice::from_raw_parts(sanitized_ptr, len)
}
/// Construct a mut slice from [`__IncompleteArrayField`] without breaking stacked borrows in miri.
/// # Safety
/// - The `orig_ptr` should have provenance over the entire returned slice.
/// - `array` should be the start of a valid slice of `T` with a `length >= len`
/// - No other reference exists to any element of the slice.
///
/// See <https://github.com/rust-lang/rust-bindgen/issues/1892>
#[inline]
unsafe fn slice_from_flexarray_mut<S, T>(
    orig_ptr: *mut S,
    array: &mut __IncompleteArrayField<T>,
    len: usize,
) -> &mut [T] {
    let offs = ptr::from_ref(array) as usize - orig_ptr as usize;
    let sanitized_ptr = (orig_ptr as *mut u8).add(offs) as *mut T;
    core::slice::from_raw_parts_mut(sanitized_ptr, len)
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
/// 2. Additionally, if `p` is a valid pointer to `H` then `p` + `size_of::<H>` must be a valid pointer to an `H::Element`.
/// This can be handled by placing a bindgen generated `__IncompleteArrayField<H::Element>` or `[H::Element; 0]` as the last field of the `repr(C)` `H`.
pub unsafe trait FamHeader {
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

mod sealed {
    pub trait Sealed {}
    impl Sealed for super::Owned {}
    impl<'a> Sealed for super::BorrowedMut<'a> {}
    impl<'a> Sealed for super::BorrowedShared<'a> {}
}
/// The [`FamBox`] owns its buffer and will deallocate it when dropped.
#[derive(Debug, Default, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Owned;
#[derive(Default, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
/// The [`FamBox`] has an exclusive reference to its buffer.
pub struct BorrowedMut<'a>(core::marker::PhantomData<&'a ()>);
// Don't write Phantom.
impl<'a> core::fmt::Debug for BorrowedMut<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("BorrowedMut").finish()
    }
}
#[derive(Default, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
/// The [`FamBox`] has a shared reference to its buffer.
pub struct BorrowedShared<'a>(core::marker::PhantomData<&'a ()>);
// Don't write Phantom.
impl<'a> core::fmt::Debug for BorrowedShared<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("BorrowedShared").finish()
    }
}
/// Sealed Marker trait representing if a buffer is [`Owned`] or [`BorrowedMut`] or [`BorrowedShared`].
pub trait Owner: sealed::Sealed {
    const OWNED: bool;
}
/// Sealed Marker trait representing that the buffer is exclusive.
pub trait Exclusive: Owner {}
impl Owner for Owned {
    const OWNED: bool = true;
}
impl Exclusive for Owned {}
impl<'a> Owner for BorrowedMut<'a> {
    const OWNED: bool = false;
}
impl<'a> Exclusive for BorrowedMut<'a> {}
impl<'a> Owner for BorrowedShared<'a> {
    const OWNED: bool = false;
}
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

/* Owned impls */
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
impl<H: FamHeader + Default> Default for FamBox<H, Owned>
where
    H::Element: Default,
{
    fn default() -> Self {
        Self::from_fn(H::default(), |_| H::Element::default())
    }
}
impl<H: FamHeader + PartialEq> PartialEq for FamBox<H, Owned>
where
    H::Element: PartialEq,
{
    /// Compares parts.
    fn eq(&self, other: &Self) -> bool {
        self.as_parts() == other.as_parts()
    }
}
impl<H: FamHeader> FamBox<H, Owned> {
    /// Allocate a new [`Owned`] buffer and create [`Self`] from a valid header and a callback for initializing the flexible array member.
    ///
    /// `cb` is passed the index being initialized. If `cb` panics a memory leak may occur.
    pub fn from_fn<F>(header: H, mut cb: F) -> Self
    where
        F: FnMut(usize) -> H::Element,
    {
        let size = header.total_size();
        debug_assert!(
            size_of::<H>() <= size,
            "invalid impl: size_of::<H>() > total size"
        );
        if size == 0 {
            // Safety: Since both `H` and `H::Element` are ZST, a dangling pointer is valid for the length of `H` followed by as many `H::Element` as fit in a slice.
            return unsafe { FamBox::from_raw(NonNull::dangling()) };
        }

        let layout =
            alloc::alloc::Layout::from_size_align(size, align_of::<H>()).expect("invalid layout");
        // Safety: `layout` is non-zero in size. Alignment of `H` matches the allocation,
        // and the following `[H::Element]` is seperated from `H` by the necessary padding as required in the `FamHeader` trait.
        let Some(ptr) = NonNull::new(unsafe { alloc::alloc::alloc(layout) }.cast::<H>()) else {
            alloc::alloc::handle_alloc_error(layout);
        };

        // Write header
        let fam_len = header.fam_len();
        // Safety: Allocation was created so that an `H` is valid at the start of the buffer.
        unsafe { ptr.as_ptr().write(header) };

        // Write fam
        {
            let ptr = ptr.as_ptr();
            // Already wrote header so skip the header including.
            let ptr = unsafe { ptr.add(1) };
            // Initialize the buffer
            let mut ptr = ptr.cast::<H::Element>();
            for i in 0..fam_len {
                // Safety: ptr is valid for writing `H::Element`.
                // If panic occurs here in `cb` a leak will happen, but [`Self`] hasn't been constructed, so its destructor won't run and no preparation is needed.
                unsafe { ptr.write(cb(i)) };
                // Safety: Allocation was made so that `ptr` is valid at `ptr+1`. `ptr` will be at the end of one `H::Element` and/or the start of another `H::Element`.
                unsafe { ptr = ptr.add(1) };
            }
        }

        // Safety: Finished initializing buffer and `ptr` is allocated as valid.
        // `ptr` is valid for `'static` and exclusive.
        unsafe { FamBox::from_raw(ptr) }
    }

    /// Leak [`Self`]. Like [`Self::buffer`] but always safe regardless of stored data.
    pub fn leak<'a>(self) -> NonNull<H> {
        mem::ManuallyDrop::new(self).ptr.cast()
    }
}

/* BorrowedMut impls */
impl<'a, H: FamHeader> FamBox<H, BorrowedMut<'a>> {
    /// Create a `[FamBox<H, BorrowedMut<'a>>]` from a reference to a buffer containing `H` followed by `[H::Element]` of `H::fam_len()` length.
    /// # Safety
    /// - `slice` must match the above description (i.e. aligned to `H`, containing `H` followed by `H::fam_len()` `H::Element`s).
    /// - `slice` must be valid for the lifetime of `Self`.
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

/* BorrowedShared impls */
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
impl<'a, H: FamHeader> FamBox<H, BorrowedShared<'a>> {
    /// Create a `[FamBox<H, BorrowedShared<'a>>]` from a reference to a buffer containing `H` followed by `[H::Element]` of `H::fam_len()` length.
    /// # Safety
    /// - `slice` must match the above description (i.e. aligned to `H`, containing `H` followed by `H::fam_len()` `H::Element`s).
    /// - `slice` must be valid for the lifetime of `Self`.
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

/* Borrowed impls */
impl<H: FamHeader + PartialEq, O: Borrowed> PartialEq for FamBox<H, O>
where
    H::Element: PartialEq,
{
    /// Compares pointer addresses and if not equal compares parts.
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr || self.as_parts() == other.as_parts()
    }
}

/* Exclusive impls */
impl<H: FamHeader, O: Exclusive> FamBox<H, O> {
    #[inline]
    pub fn header_mut(&mut self) -> &mut H {
        // Safety: The head of the buffer contains a valid `H` and buffer is [`Exclusive`].
        unsafe { self.ptr.cast().as_mut() }
    }

    #[inline]
    pub fn fam_mut(&mut self) -> &mut [H::Element] {
        let fam_len = self.header().fam_len();
        // Safety: By construction `self.buf` has provenance over the entire buffer and `self.buf+size_of::<H>()` is the start of the fam.
        // Taking by `&mut self` on [`Exclusive`] buffer guarantees required exclusivity.
        unsafe {
            slice_from_flexarray_mut(
                self.ptr.as_ptr(),
                self.ptr
                    .as_ptr()
                    .add(size_of::<H>())
                    .cast::<__IncompleteArrayField<_>>()
                    .as_mut()
                    .unwrap(),
                fam_len,
            )
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

/* General impls ([`Owned`] or [`BorrowedMut`] or [`BorrowedShared`]) */
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
impl<H: FamHeader, O: Owner> FamBox<H, O> {
    /// Create [`Self`] from a pointer to a buffer containing `H` followed by `[H::Element]` of `H::fam_len()` length.
    /// # Safety
    /// - `ptr` must match the above description.
    /// - buffer must be valid for the lifetime of `Self`.
    /// - `ptr` must be exclusive if `O: Exclusive`.
    /// - `ptr` must have been allocated with [`alloc::GlobalAlloc`] if `O` = [`Owned`].
    ///
    /// The pointer from [`self.leak()`] satisfies all of these.
    pub unsafe fn from_raw(ptr: NonNull<H>) -> Self {
        Self {
            ty: PhantomData,
            ptr: ptr.cast(),
        }
    }

    /// Copy to a [`FamBox<H,Owned>`] by copying the buffer into a newly allocated buffer.
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
        // Safety: By construction `self.buf` has provenance over the entire buffer and `self.buf+size_of::<H>()` is the start of the fam.
        unsafe {
            slice_from_flexarray(
                self.ptr.as_ptr(),
                self.ptr
                    .as_ptr()
                    .add(size_of::<H>())
                    .cast::<__IncompleteArrayField<_>>()
                    .as_ref()
                    .unwrap(),
                fam_len,
            )
        }
    }
    #[inline]
    pub fn as_parts(&self) -> (&H, &[H::Element]) {
        // Safety: Inlined [`self.header()`] to satisfy borrow checker.
        (unsafe { self.ptr.cast().as_ref() }, self.fam())
    }
}
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

        let size = self.header().total_size();
        if size == 0 {
            return;
        }
        let layout =
            alloc::alloc::Layout::from_size_align(size, align_of::<H>()).expect("invalid layout");
        // Safety: [`Self`] is `Owned` and therefore was created with the same underlying allocator and layout.
        unsafe { alloc::alloc::dealloc(self.ptr.as_ptr(), layout) };
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

pub type FamBoxOwned<H> = FamBox<H, Owned>;
pub type FamBoxShared<'a, H> = FamBox<H, BorrowedShared<'a>>;
pub type FamBoxMut<'a, H> = FamBox<H, BorrowedShared<'a>>;

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::String;
    use core::fmt::Write;

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
    fn parts_with_padding() {
        let own = FamBox::from_fn(TEST_MSG, |i| i as _);
        let (header, fam) = own.as_parts();
        assert_eq!(*header, TEST_MSG);
        assert_eq!(fam, core::array::from_fn::<_, 6, _>(|i| i as _));
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
}
