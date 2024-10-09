#![cfg_attr(docsrs, doc(cfg(feature = "std")))]

extern crate std;
use std::{
    ffi::{OsStr, OsString},
    path::{Path, PathBuf},
};

use crate::gstr::GStr;

impl<const SHARED: bool> AsRef<OsStr> for GStr<SHARED> {
    #[inline]
    fn as_ref(&self) -> &OsStr {
        self.as_str().as_ref()
    }
}

impl<const SHARED: bool> AsRef<Path> for GStr<SHARED> {
    #[inline]
    fn as_ref(&self) -> &Path {
        Path::new(self)
    }
}

impl<const SHARED: bool> From<GStr<SHARED>> for OsString {
    #[inline]
    fn from(string: GStr<SHARED>) -> Self {
        Self::from(string.gstr_into_string())
    }
}

impl<const SHARED: bool> From<GStr<SHARED>> for PathBuf {
    #[inline]
    fn from(string: GStr<SHARED>) -> Self {
        Self::from(OsString::from(string))
    }
}
