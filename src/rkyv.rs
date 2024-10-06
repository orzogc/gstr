#![cfg_attr(docsrs, doc(cfg(feature = "rkyv")))]

use core::cmp::Ordering;

use rkyv::{
    rancor::{Fallible, ResultExt as _, Source},
    string::{ArchivedString, StringResolver},
    Archive, Deserialize, DeserializeUnsized, Place, Serialize, SerializeUnsized,
};

use crate::{GStr, ResultExt as _};

impl Archive for GStr {
    type Archived = ArchivedString;

    type Resolver = StringResolver;

    #[inline]
    fn resolve(&self, resolver: Self::Resolver, out: Place<Self::Archived>) {
        ArchivedString::resolve_from_str(self.as_str(), resolver, out);
    }
}

impl<S: Fallible + ?Sized> Serialize<S> for GStr
where
    S::Error: Source,
    str: SerializeUnsized<S>,
{
    #[inline]
    fn serialize(&self, serializer: &mut S) -> Result<Self::Resolver, <S as Fallible>::Error> {
        ArchivedString::serialize_from_str(self.as_str(), serializer)
    }
}

impl<D: Fallible + ?Sized> Deserialize<GStr, D> for ArchivedString
where
    D::Error: Source,
    str: DeserializeUnsized<str, D>,
{
    #[inline]
    fn deserialize(&self, _deserializer: &mut D) -> Result<GStr, <D as Fallible>::Error> {
        GStr::try_new(self.as_str())
            .map_err_source(|_| {})
            .into_error()
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
    use rkyv::rancor::Error;

    fn test_gstr_rkyv(string: String) {
        let gstr = GStr::new(&string);

        let string_bytes = rkyv::to_bytes::<Error>(&string).unwrap();
        let gstr_bytes = rkyv::to_bytes::<Error>(&gstr).unwrap();
        assert_eq!(&*string_bytes, &*gstr_bytes);

        // SAFETY: `string_bytes` is serialized from `rkyv::to_bytes`.
        unsafe {
            let string_de: String = rkyv::from_bytes_unchecked::<_, Error>(&string_bytes).unwrap();
            let gstr_de: GStr = rkyv::from_bytes_unchecked::<_, Error>(&string_bytes).unwrap();
            assert_eq!(string_de, string);
            assert_eq!(gstr_de, string);
        }

        // SAFETY: `gstr_bytes` is serialized from `rkyv::to_bytes`.
        unsafe {
            let string_de: String = rkyv::from_bytes_unchecked::<_, Error>(&gstr_bytes).unwrap();
            let gstr_de: GStr = rkyv::from_bytes_unchecked::<_, Error>(&gstr_bytes).unwrap();
            assert_eq!(string_de, string);
            assert_eq!(gstr_de, string);
        }
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
