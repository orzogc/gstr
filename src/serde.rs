#![cfg_attr(docsrs, doc(cfg(feature = "serde")))]

use core::fmt;

extern crate alloc;
use alloc::{format, string::String, vec::Vec};

use serde::{
    de::{Error, Unexpected, Visitor},
    Deserialize, Deserializer, Serialize, Serializer,
};

use crate::{ErrorKind, GStr};

impl Serialize for GStr {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(self.as_str())
    }
}

impl<'de> Deserialize<'de> for GStr {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_string(GStrVisitor)
    }
}

#[derive(Clone, Copy, Debug)]
struct GStrVisitor;

impl<'de> Visitor<'de> for GStrVisitor {
    type Value = GStr;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a string")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: Error,
    {
        match GStr::try_new(v) {
            Ok(s) => Ok(s),
            Err(e) => match e.error_kind() {
                ErrorKind::LengthOverflow(len) => length_overflow(len),
                ErrorKind::AllocationFailure(layout) => crate::handle_alloc_error(layout),
                // SAFETY: `GStr::try_new` doesn't return other errors.
                _ => unsafe { core::hint::unreachable_unchecked() },
            },
        }
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: Error,
    {
        match GStr::try_from_string(v) {
            Ok(s) => Ok(s),
            Err(e) => match e.error_kind() {
                ErrorKind::LengthOverflow(len) => length_overflow(len),
                ErrorKind::AllocationFailure(layout) => crate::handle_alloc_error(layout),
                // SAFETY: `GStr::try_from_string` doesn't return other errors.
                _ => unsafe { core::hint::unreachable_unchecked() },
            },
        }
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: Error,
    {
        if v.len() > GStr::MAX_LENGTH {
            length_overflow(v.len())
        } else {
            match core::str::from_utf8(v) {
                Ok(s) => self.visit_str(s),
                Err(_) => Err(Error::invalid_value(Unexpected::Bytes(v), &self)),
            }
        }
    }

    fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
    where
        E: Error,
    {
        match GStr::from_utf8(v) {
            Ok(s) => Ok(s),
            Err(e) => match e.error_kind() {
                ErrorKind::LengthOverflow(len) => length_overflow(len),
                ErrorKind::AllocationFailure(layout) => crate::handle_alloc_error(layout),
                ErrorKind::Utf8Error(_) => {
                    Err(Error::invalid_value(Unexpected::Bytes(e.source()), &self))
                }
                // SAFETY: `GStr::from_utf8` doesn't return other errors.
                _ => unsafe { core::hint::unreachable_unchecked() },
            },
        }
    }
}

#[cold]
#[inline(never)]
fn length_overflow<E: Error>(len: usize) -> Result<GStr, E> {
    Err(E::custom(format!(
        "the length of string/bytes should be less than or equal to {}: {}",
        GStr::MAX_LENGTH,
        len
    )))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    use proptest::prelude::*;

    #[derive(Debug, Deserialize, Eq, PartialEq, Serialize)]
    struct StringStruct {
        a: String,
    }

    #[derive(Debug, Deserialize, Eq, PartialEq, Serialize)]
    struct GStrStruct {
        a: GStr,
    }

    fn test_gstr_serde(string: String) {
        let str_json = serde_json::to_string(string.as_str()).unwrap();
        let gstr: GStr = serde_json::from_str(&str_json).unwrap();
        assert_eq!(gstr, string);

        let string_struct = StringStruct { a: string };
        let gstr_struct = GStrStruct { a: gstr };

        let string_json = serde_json::to_string(&string_struct).unwrap();
        let gstr_json = serde_json::to_string(&gstr_struct).unwrap();
        assert_eq!(string_json, gstr_json);

        let string_de: StringStruct = serde_json::from_str(&string_json).unwrap();
        let gstr_de: GStrStruct = serde_json::from_str(&gstr_json).unwrap();
        assert_eq!(string_de, string_struct);
        assert_eq!(gstr_de, gstr_struct);
    }

    #[test]
    fn gstr_serde() {
        test_gstr_serde("".into());
        test_gstr_serde("foo".into());
        test_gstr_serde("hello, 🦀 and 🌎!".into());
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    proptest! {
        #[test]
        fn prop_gstr_serde(string: String) {
            test_gstr_serde(string);
        }
    }
}
