use crate::{builder::FamBoxBuilder, FamBox, FamHeader, Owned, Owner};
use core::{convert::Infallible, marker::PhantomData, ops::ControlFlow};
use serde::{
    de::{self, DeserializeSeed, Visitor},
    ser::{SerializeStruct, SerializeTuple},
    Deserialize, Serialize,
};

/// Serialize slice without length.
struct SerializeSliceAsTuple<'a, T>(&'a [T]);
impl<'a, T: Serialize> Serialize for SerializeSliceAsTuple<'a, T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut serializer = serializer.serialize_tuple(self.0.len())?;
        for value in self.0 {
            serializer.serialize_element(value)?;
        }
        serializer.end()
    }
}

impl<H: FamHeader, O: Owner> Serialize for FamBox<H, O>
where
    H: Serialize,
    H::Element: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let (header, elements) = self.as_parts();
        let mut serializer = serializer.serialize_struct("FamBox", 2)?;
        serializer.serialize_field("header", header)?;
        serializer.serialize_field("fam", &SerializeSliceAsTuple(elements))?;
        serializer.end()
    }
}

/// Deserialize a slice without a stored prefix with runtime length.
struct DeserializeNoPrefixSlice<T, Output, UnfinishedState, F>
where
    F: FnMut(UnfinishedState, T) -> ControlFlow<Output, UnfinishedState>,
{
    len: usize,
    f: F,
    unfinished_state: UnfinishedState,
    ty: PhantomData<T>,
}
impl<'de, T: Deserialize<'de>, Output, State, F: FnMut(State, T) -> ControlFlow<Output, State>>
    Visitor<'de> for DeserializeNoPrefixSlice<T, Output, State, F>
{
    type Value = Output;

    fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
        formatter.write_str("a sequence of values without a length prefix")
    }
    fn visit_seq<A>(mut self, seq: A) -> Result<Self::Value, A::Error>
    where
        A: de::SeqAccess<'de>,
    {
        /// Convert seq into iterator asssuming homogeneity (1 type).
        struct HomogeneousSeq<'de, A: de::SeqAccess<'de>, T>(A, PhantomData<(&'de (), T)>);
        impl<'de, A: de::SeqAccess<'de>, T: serde::Deserialize<'de>> Iterator
            for HomogeneousSeq<'de, A, T>
        {
            type Item = Result<T, A::Error>;

            fn next(&mut self) -> Option<Self::Item> {
                self.0.next_element().transpose()
            }
            fn size_hint(&self) -> (usize, Option<usize>) {
                if let Some(x) = self.0.size_hint() {
                    (x, Some(x))
                } else {
                    (0, None)
                }
            }
        }
        /// Error message. Using a struct because Serde requires the error message to impl `Visitor`.
        struct ExpectedLen(usize);
        impl Visitor<'_> for ExpectedLen {
            type Value = Infallible;

            fn expecting(&self, formatter: &mut alloc::fmt::Formatter) -> alloc::fmt::Result {
                writeln!(formatter, "{} elements", self.0)
            }
        }

        let mut iter = HomogeneousSeq(seq, PhantomData).into_iter();
        let mut i = 0;
        // Take items until an error is received from the iterator (Error),
        // the iterator runs out prematurely (Error), or the function breaks (final output)
        loop {
            match (self.f)(
                self.unfinished_state,
                match iter.next() {
                    Some(x) => match x {
                        Ok(x) => x,
                        Err(e) => break Err(e),
                    },
                    None => break Err(de::Error::invalid_length(i, &ExpectedLen(self.len))),
                },
            ) {
                ControlFlow::Continue(unfinished) => self.unfinished_state = unfinished,
                ControlFlow::Break(finished) => break Ok(finished),
            }
            i += 1;
        }
    }
}

impl<
        'de,
        T: serde::Deserialize<'de>,
        Output,
        UnfinishedState,
        F: FnMut(UnfinishedState, T) -> ControlFlow<Output, UnfinishedState>,
    > DeserializeSeed<'de> for DeserializeNoPrefixSlice<T, Output, UnfinishedState, F>
{
    type Value = Output;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        deserializer.deserialize_tuple(self.len, self)
    }
}

/// Visitor to deserialize the `FamBox`.
/// Current implementation allocates an additional buffer if more than [`INLINE_SIZE`] elements.
#[derive(Debug)]
struct FamBoxVisitor<H, O: Owner>(PhantomData<(H, O)>);
impl<'de, H: FamHeader> Visitor<'de> for FamBoxVisitor<H, Owned>
where
    H: Deserialize<'de>,
    H::Element: Deserialize<'de>,
{
    type Value = FamBox<H, Owned>;

    fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
        formatter.write_str("sequence of elements H then [H::Element]")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'de>,
    {
        let header: H = seq
            .next_element()?
            .ok_or_else(|| de::Error::missing_field("header"))?;
        let fam_len = header.fam_len();
        let builder = match FamBoxBuilder::new(header) {
            core::ops::ControlFlow::Continue(unfinished) => unfinished,
            core::ops::ControlFlow::Break(finished) => return Ok(finished.build()),
        };
        Ok(seq
            .next_element_seed(DeserializeNoPrefixSlice {
                len: fam_len,
                unfinished_state: builder,
                f: |builder: FamBoxBuilder<H, false>, x: H::Element| match builder.add_element(x) {
                    ControlFlow::Continue(unfinished) => ControlFlow::Continue(unfinished),
                    ControlFlow::Break(finished) => ControlFlow::Break(finished.build()),
                },
                ty: PhantomData,
            })?
            .ok_or_else(|| de::Error::missing_field("fam elements"))?)
    }
}

impl<'de, H: FamHeader + 'de> Deserialize<'de> for FamBox<H, Owned>
where
    H: Deserialize<'de>,
    H::Element: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        Ok(deserializer.deserialize_struct(
            "FamBox",
            &["header", "fam"],
            FamBoxVisitor(PhantomData),
        )?)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn ser_de() {
        use crate::{FamBoxOwned, FamHeader};
        use bincode::Options;
        extern crate std;
        use std::io::Cursor;
        #[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
        struct S(u16, [u8; 0]);
        unsafe impl FamHeader for S {
            type Element = u8;

            fn fam_len(&self) -> usize {
                self.0.into()
            }
        }
        let s = S(3, []);
        let fambox = FamBoxOwned::from_fn(s, |i| i as _);
        let opt = bincode::DefaultOptions::new()
            .with_big_endian()
            .with_fixint_encoding();
        let mut buf = alloc::vec![0u8; fambox.header().total_size()];
        opt.serialize_into(buf.as_mut_slice(), &fambox).unwrap();
        let de: FamBoxOwned<S> = opt.deserialize_from(Cursor::new(buf)).unwrap();
        assert_eq!(fambox, de);
    }
}
