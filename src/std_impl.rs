#![cfg_attr(docsrs, doc(cfg(feature = "std")))]

extern crate std;
use std::{
    ffi::{OsStr, OsString},
    path::{Path, PathBuf},
};

use crate::GStr;

impl AsRef<OsStr> for GStr {
    #[inline]
    fn as_ref(&self) -> &OsStr {
        self.as_str().as_ref()
    }
}

impl AsRef<Path> for GStr {
    #[inline]
    fn as_ref(&self) -> &Path {
        Path::new(self)
    }
}

impl From<GStr> for OsString {
    #[inline]
    fn from(string: GStr) -> Self {
        Self::from(string.into_string())
    }
}

impl From<GStr> for PathBuf {
    #[inline]
    fn from(string: GStr) -> Self {
        Self::from(OsString::from(string))
    }
}
