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
mod tests {}
