#![cfg_attr(docsrs, doc(cfg(feature = "rkyv")))]

use core::cmp::Ordering;

use rkyv::{
    string::{ArchivedString, StringResolver},
    Archive, Deserialize, DeserializeUnsized, Fallible, Serialize, SerializeUnsized,
};

use crate::GStr;

impl Archive for GStr {
    type Archived = ArchivedString;

    type Resolver = StringResolver;

    #[inline]
    unsafe fn resolve(&self, pos: usize, resolver: Self::Resolver, out: *mut Self::Archived) {
        // SAFETY: It's caller's responsibility to ensure the safety invariants.
        unsafe { ArchivedString::resolve_from_str(self.as_str(), pos, resolver, out) }
    }
}

impl<S: Fallible + ?Sized> Serialize<S> for GStr
where
    str: SerializeUnsized<S>,
{
    #[inline]
    fn serialize(&self, serializer: &mut S) -> Result<Self::Resolver, <S as Fallible>::Error> {
        ArchivedString::serialize_from_str(self.as_str(), serializer)
    }
}

impl<D: Fallible + ?Sized> Deserialize<GStr, D> for ArchivedString
where
    str: DeserializeUnsized<str, D>,
{
    #[inline]
    fn deserialize(&self, _deserializer: &mut D) -> Result<GStr, <D as Fallible>::Error> {
        // TODO: Avoid panic if the string's length is too large?
        Ok(GStr::new(self.as_str()))
    }
}

impl PartialEq<ArchivedString> for GStr {
    #[inline]
    fn eq(&self, other: &ArchivedString) -> bool {
        self == other.as_str()
    }
}

impl PartialEq<GStr> for ArchivedString {
    #[inline]
    fn eq(&self, other: &GStr) -> bool {
        self.as_str() == other
    }
}

impl PartialOrd<ArchivedString> for GStr {
    #[inline]
    fn partial_cmp(&self, other: &ArchivedString) -> Option<Ordering> {
        self.partial_cmp(other.as_str())
    }
}

impl PartialOrd<GStr> for ArchivedString {
    #[inline]
    fn partial_cmp(&self, other: &GStr) -> Option<Ordering> {
        self.as_str().partial_cmp(other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    extern crate alloc;
    use alloc::string::String;

    use proptest::prelude::*;

    fn test_gstr_rkyv(string: String) {
        let gstr = GStr::new(&string);

        let string_bytes = rkyv::to_bytes::<_, 32>(&string).unwrap();
        let gstr_bytes = rkyv::to_bytes::<_, 32>(&gstr).unwrap();
        assert_eq!(&*string_bytes, &*gstr_bytes);

        // SAFETY: The byte slice is serialized from `rkyv::to_bytes`.
        let archived = unsafe { rkyv::archived_root::<String>(&string_bytes) };
        let string_de: String = archived.deserialize(&mut rkyv::Infallible).unwrap();
        let gstr_de: GStr = archived.deserialize(&mut rkyv::Infallible).unwrap();
        assert_eq!(*archived, string);
        assert_eq!(string_de, string);
        assert_eq!(gstr_de, string);

        // SAFETY: The byte slice is serialized from `rkyv::to_bytes`.
        let archived = unsafe { rkyv::archived_root::<GStr>(&gstr_bytes) };
        let string_de: String = archived.deserialize(&mut rkyv::Infallible).unwrap();
        let gstr_de: GStr = archived.deserialize(&mut rkyv::Infallible).unwrap();
        assert_eq!(*archived, string);
        assert_eq!(string_de, string);
        assert_eq!(gstr_de, string);
    }

    #[cfg_attr(miri, ignore)]
    #[test]
    fn gstr_rkyv() {
        test_gstr_rkyv("".into());
        test_gstr_rkyv("foo".into());
        test_gstr_rkyv("hello, 🦀 and 🌎!".into());
    }

    proptest! {
        #[cfg_attr(miri, ignore)]
        #[test]
        fn prop_gstr_rkyv(string: String) {
            test_gstr_rkyv(string);
        }
    }
}
