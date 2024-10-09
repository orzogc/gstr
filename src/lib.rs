#![doc = include_str!("../README.md")]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(feature = "nightly_test", feature(str_from_utf16_endian))]
#![no_std]

#[cfg(target_pointer_width = "16")]
compile_error!("16-bit platforms aren't supported");

pub mod gstr;

#[cfg(feature = "serde")]
mod serde;

#[cfg(feature = "rkyv")]
mod rkyv;

#[cfg(feature = "std")]
mod std_impl;

/// An immutable string implementation optimized for small strings and comparison.
pub type GStr = gstr::GStr<false>;

/// An immutable string implementation optimized for small strings and comparison.
///
/// [`SharedGStr`] uses the atomic reference internally, so cloning a [`SharedGStr`] only takes
/// `O(1)` time.
pub type SharedGStr = gstr::GStr<true>;
