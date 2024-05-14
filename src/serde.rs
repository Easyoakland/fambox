use crate::{FamBox, FamHeader, Owned, Owner};
use serde::{
    de::{self, DeserializeSeed, Visitor},
    ser::{SerializeStruct, SerializeTuple},
    Deserialize, Serialize,
};
use std::marker::PhantomData;

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
struct DeserializeNoPrefixSlice<Item, Collection> {
    len: usize,
    item: PhantomData<Item>,
    out: PhantomData<Collection>,
}
impl<'de, T: Deserialize<'de>, O: FromIterator<T>> Visitor<'de> for DeserializeNoPrefixSlice<T, O> {
    type Value = O;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a sequence of values without a length prefix")
    }
    fn visit_seq<A>(self, seq: A) -> Result<Self::Value, A::Error>
    where
        A: de::SeqAccess<'de>,
    {
        /// Convert seq into iterator asssuming heterogeneity.
        struct HeterogeneousSeq<'de, A: de::SeqAccess<'de>, T>(A, PhantomData<(&'de (), T)>);
        impl<'de, A: de::SeqAccess<'de>, T: serde::Deserialize<'de>> Iterator
            for HeterogeneousSeq<'de, A, T>
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
        HeterogeneousSeq(seq, PhantomData).collect::<Result<Self::Value, A::Error>>()
    }
}

impl<'de, T: serde::Deserialize<'de>, O: std::iter::FromIterator<T>> DeserializeSeed<'de>
    for DeserializeNoPrefixSlice<T, O>
{
    type Value = O;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        deserializer.deserialize_tuple(self.len, self)
    }
}

/// Visitor to deserialize the `FamBox`.
/// Current implementation allocates a temporary vec.
#[derive(Debug)]
struct FamBoxVisitor<H, O: Owner>(PhantomData<(H, O)>);
impl<'de, H: FamHeader> Visitor<'de> for FamBoxVisitor<H, Owned>
where
    H: Deserialize<'de> + std::fmt::Debug,
    H::Element: Deserialize<'de> + std::fmt::Debug,
{
    type Value = FamBox<H, Owned>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("sequence of elements H then [H::Element]")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'de>,
    {
        let header: H = seq
            .next_element()?
            .ok_or_else(|| de::Error::missing_field("header"))?;
        let mut fam = seq
            .next_element_seed(DeserializeNoPrefixSlice {
                len: header.fam_len(),
                item: PhantomData::<H::Element>,
                out: PhantomData::<Vec<H::Element>>,
            })?
            .ok_or_else(|| de::Error::missing_field("fam elements"))?;
        let mut drain = fam.drain(..);

        Ok(Self::Value::from_fn(header, |_| drain.next().unwrap()))
    }
}

impl<'de, H: FamHeader + 'de> Deserialize<'de> for FamBox<H, Owned>
where
    H: Deserialize<'de> + Clone + std::fmt::Debug,
    H: Clone + std::fmt::Debug,
    H::Element: Deserialize<'de> + Clone + std::fmt::Debug,
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
    use crate::{FamBoxOwned, FamHeader};
    use bincode::Options;
    use std::io::Cursor;

    #[test]
    fn ser_de() {
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
        let mut buf = vec![0u8; fambox.header().total_size()];
        opt.serialize_into(buf.as_mut_slice(), &fambox).unwrap();
        let de: FamBoxOwned<S> = opt.deserialize_from(Cursor::new(buf)).unwrap();
        assert_eq!(fambox, de);
    }
}
