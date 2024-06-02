<!-- cargo-rdme start -->

 [`FamBox`] datastructure to enable ergonomic and safe usage of c structs with a [flexible array member](https://en.wikipedia.org/wiki/Flexible_array_member).

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
use core::mem::size_of;
use fambox::FamBoxOwned;
// To be used safely, [`protocol_msg`] can't provide any safe mutable access to `length`.
pub use encapsulated_struct::protocol_msg;
mod encapsulated_struct {
    use core::mem::size_of;
    use fambox::FamHeader;

    pub struct InvalidLength;

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
```

or a [`FamBoxShared`]/[`FamBoxMut`] can be used to easily access and manipulate a fam containing struct from c
```rust
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

<!-- cargo-rdme end -->

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
