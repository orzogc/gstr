#![cfg_attr(docsrs, doc(cfg(feature = "rkyv")))]

use core::cmp::Ordering;

use rkyv::{
    rancor::{Fallible, ResultExt as _, Source},
    string::{ArchivedString, StringResolver},
    Archive, Deserialize, DeserializeUnsized, Place, Serialize, SerializeUnsized,
};

use crate::gstr::{GStr, ResultExt as _};

impl<const SHARED: bool> Archive for GStr<SHARED> {
    type Archived = ArchivedString;

    type Resolver = StringResolver;

    #[inline]
    fn resolve(&self, resolver: Self::Resolver, out: Place<Self::Archived>) {
        ArchivedString::resolve_from_str(self.as_str(), resolver, out);
    }
}

impl<S: Fallible + ?Sized, const SHARED: bool> Serialize<S> for GStr<SHARED>
where
    S::Error: Source,
    str: SerializeUnsized<S>,
{
    #[inline]
    fn serialize(&self, serializer: &mut S) -> Result<Self::Resolver, <S as Fallible>::Error> {
        ArchivedString::serialize_from_str(self.as_str(), serializer)
    }
}

impl<D: Fallible + ?Sized, const SHARED: bool> Deserialize<GStr<SHARED>, D> for ArchivedString
where
    D::Error: Source,
    str: DeserializeUnsized<str, D>,
{
    #[inline]
    fn deserialize(&self, _deserializer: &mut D) -> Result<GStr<SHARED>, <D as Fallible>::Error> {
        GStr::try_new(self.as_str())
            .map_err_source(|_| {})
            .into_error()
    }
}

impl<const SHARED: bool> PartialEq<ArchivedString> for GStr<SHARED> {
    #[inline]
    fn eq(&self, other: &ArchivedString) -> bool {
        self == other.as_str()
    }
}

impl<const SHARED: bool> PartialEq<GStr<SHARED>> for ArchivedString {
    #[inline]
    fn eq(&self, other: &GStr<SHARED>) -> bool {
        self.as_str() == other
    }
}

impl<const SHARED: bool> PartialOrd<ArchivedString> for GStr<SHARED> {
    #[inline]
    fn partial_cmp(&self, other: &ArchivedString) -> Option<Ordering> {
        self.partial_cmp(other.as_str())
    }
}

impl<const SHARED: bool> PartialOrd<GStr<SHARED>> for ArchivedString {
    #[inline]
    fn partial_cmp(&self, other: &GStr<SHARED>) -> Option<Ordering> {
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

    fn test_gstr_rkyv<const SHARED: bool>(string: String) {
        let gstr = GStr::<SHARED>::new(&string);

        let string_bytes = rkyv::to_bytes::<Error>(&string).unwrap();
        let gstr_bytes = rkyv::to_bytes::<Error>(&gstr).unwrap();
        assert_eq!(&*string_bytes, &*gstr_bytes);

        // SAFETY: `string_bytes` is serialized from `rkyv::to_bytes`.
        unsafe {
            let string_de: String = rkyv::from_bytes_unchecked::<_, Error>(&string_bytes).unwrap();
            let gstr_de: GStr<SHARED> =
                rkyv::from_bytes_unchecked::<_, Error>(&string_bytes).unwrap();
            assert_eq!(string_de, string);
            assert_eq!(gstr_de, string);
        }

        // SAFETY: `gstr_bytes` is serialized from `rkyv::to_bytes`.
        unsafe {
            let string_de: String = rkyv::from_bytes_unchecked::<_, Error>(&gstr_bytes).unwrap();
            let gstr_de: GStr<SHARED> =
                rkyv::from_bytes_unchecked::<_, Error>(&gstr_bytes).unwrap();
            assert_eq!(string_de, string);
            assert_eq!(gstr_de, string);
        }
    }

    #[cfg_attr(miri, ignore)]
    #[test]
    fn gstr_rkyv() {
        test_gstr_rkyv::<false>("".into());
        test_gstr_rkyv::<true>("".into());
        test_gstr_rkyv::<false>("foo".into());
        test_gstr_rkyv::<true>("foo".into());
        test_gstr_rkyv::<false>("hello, 🦀 and 🌎!".into());
        test_gstr_rkyv::<true>("hello, 🦀 and 🌎!".into());
    }

    proptest! {
        #[cfg_attr(miri, ignore)]
        #[test]
        fn prop_gstr_rkyv(string: String) {
            test_gstr_rkyv::<false>(string.clone());
            test_gstr_rkyv::<true>(string);
        }
    }
}
