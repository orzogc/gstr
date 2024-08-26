#![cfg_attr(docsrs, feature(doc_cfg))]
#![no_std]

#[cfg(feature = "serde")]
mod serde;

#[cfg(feature = "rkyv")]
mod rkyv;

#[cfg(feature = "std")]
mod std_impl;

use core::{
    borrow::Borrow,
    cmp::Ordering,
    error::Error,
    fmt,
    hash::{Hash, Hasher},
    mem::{self, align_of, size_of, ManuallyDrop},
    num::NonZeroU32,
    ops::{Deref, Index},
    ptr::{self, NonNull},
    slice::{self, SliceIndex},
    str::{FromStr, Utf8Error},
};

extern crate alloc;
use alloc::{
    alloc::Layout,
    borrow::Cow,
    boxed::Box,
    rc::Rc,
    string::{FromUtf8Error, String},
    sync::Arc,
    vec::Vec,
};

/// Represents the different kinds of errors in [`ToGStrError`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ErrorKind {
    /// Indicates that the string's length exceeds the maximum allowed length
    /// ([`GStr::MAX_LENGTH`]).
    ///
    /// The wrapped `usize` represents the actual length of the string.
    LengthOverflow(usize),
    /// Occurs when there is a failure to allocate memory.
    AllocationFailure,
    /// Errors that occur when attempting to interpret a byte sequence as a UTF-8 string.
    ///
    /// The wrapped [`Utf8Error`] is the specific UTF-8 error encountered.
    Utf8Error(Utf8Error),
    /// Indicates that the byte sequence does not represent a valid UTF-16 string.
    InvalidUtf16,
    /// Errors indicating that the length of the [`u8`] sequence, intended to be a valid UTF-16
    /// string, is not an odd number.
    FromUtf16OddLength,
}

/// Errors which can occur when attempting to convert a string or a byte sequence to a [`GStr`].
#[derive(Clone, Eq, PartialEq)]
pub struct ToGStrError<S> {
    /// The kind of error that occurred.
    kind: ErrorKind,
    /// The source attempted to be converted to a [`GStr`].
    source: S,
}

impl<S> ToGStrError<S> {
    /// Creates a new error indicating the length of `source` overflows.
    #[inline]
    fn new_length_overflow(source: S, len: usize) -> Self {
        Self {
            kind: ErrorKind::LengthOverflow(len),
            source,
        }
    }

    /// Creates a new error indicating that the memory allocation failed.
    #[inline]
    fn new_allocation_failure(source: S) -> Self {
        Self {
            kind: ErrorKind::AllocationFailure,
            source,
        }
    }

    /// Creates a new error indicating that `source` isn't a valid UTF-16 string.
    #[inline]
    fn new_invalid_utf16(source: S) -> Self {
        Self {
            kind: ErrorKind::InvalidUtf16,
            source,
        }
    }

    /// Creates a new error indicating that the length of `source`, which is intended to be a valid
    /// UTF-16 string , is not an odd number.
    #[inline]
    fn new_from_utf16_odd_length(source: S) -> Self {
        Self {
            kind: ErrorKind::FromUtf16OddLength,
            source,
        }
    }

    /// Returns the error kind.
    #[inline]
    pub fn error_kind(&self) -> ErrorKind {
        self.kind
    }

    /// Returns the source that failed to be converted to a [`GStr`].
    #[inline]
    pub fn source(&self) -> &S {
        &self.source
    }

    /// Consumes the error and returns the source that failed to be converted to a [`GStr`].
    #[inline]
    pub fn into_source(self) -> S {
        self.source
    }

    /// Converts the source into a new source.
    #[inline]
    fn map_source<T, F: FnOnce(S) -> T>(self, f: F) -> ToGStrError<T> {
        ToGStrError {
            kind: self.kind,
            source: f(self.source),
        }
    }
}

impl<S: AsRef<str>> ToGStrError<S> {
    #[inline]
    pub fn as_str(&self) -> &str {
        self.source.as_ref()
    }
}

impl<S: AsRef<str>> AsRef<str> for ToGStrError<S> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<S: AsRef<[u8]>> AsRef<[u8]> for ToGStrError<S> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.source.as_ref()
    }
}

impl<S> fmt::Debug for ToGStrError<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Error")
            .field("kind", &self.kind)
            .finish_non_exhaustive()
    }
}

impl<S> fmt::Display for ToGStrError<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            ErrorKind::LengthOverflow(len) => write!(
                f,
                "the source's length {} shouldn't be greater than `GStr`'s max length {}",
                GStr::MAX_LENGTH,
                len
            ),
            ErrorKind::AllocationFailure => write!(f, "failed to allocate memory"),
            ErrorKind::Utf8Error(e) => write!(f, "{e}"),
            ErrorKind::InvalidUtf16 => write!(f, "invalid UTF-16: lone surrogate found"),
            ErrorKind::FromUtf16OddLength => {
                write!(f, "invalid UTF-16: odd length of the byte sequence")
            }
        }
    }
}

impl<S> Error for ToGStrError<S> {
    #[inline]
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.kind {
            ErrorKind::LengthOverflow(_)
            | ErrorKind::AllocationFailure
            | ErrorKind::InvalidUtf16
            | ErrorKind::FromUtf16OddLength => None,
            ErrorKind::Utf8Error(e) => Some(e),
        }
    }
}

impl From<FromUtf8Error> for ToGStrError<Vec<u8>> {
    #[inline]
    fn from(error: FromUtf8Error) -> Self {
        Self {
            kind: ErrorKind::Utf8Error(error.utf8_error()),
            source: error.into_bytes(),
        }
    }
}

/// A trait extending [`Result`].
trait ResultExt<S, NS> {
    /// The result type.
    type Result<T>;

    /// Transforms the source within the error to a new source.
    fn map_err_source<F: FnOnce(S) -> NS>(self, f: F) -> Self::Result<NS>;
}

impl<T, S, NS> ResultExt<S, NS> for Result<T, ToGStrError<S>> {
    type Result<U> = Result<T, ToGStrError<U>>;

    #[inline]
    fn map_err_source<F: FnOnce(S) -> NS>(self, f: F) -> Self::Result<NS> {
        self.map_err(|e| e.map_source(f))
    }
}

/// The raw buffer of [`GStr`].
#[derive(Debug, Eq, Hash, PartialEq)]
pub enum RawBuffer {
    /// A inline buffer.
    Inline([u8; Self::INLINE_LENGTH]),
    /// A pointer points to a static [`str`].
    Static(NonNull<u8>),
    /// A pointer points to a heap allocated [`String`].
    Heap(NonNull<u8>),
}

impl RawBuffer {
    /// The length of the inline buffer.
    pub const INLINE_LENGTH: usize = GStr::MAX_INLINE_LENGTH;

    /// Returns the raw pointer of this raw buffer.
    ///
    /// The returned pointer will be pointing to the first byte of the string slice if it isn't
    /// empty.
    ///
    /// The caller must ensure that the returned pointer is never written to.
    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        match self {
            Self::Inline(buf) => buf.as_ptr(),
            Self::Static(ptr) | Self::Heap(ptr) => ptr.as_ptr(),
        }
    }
}

/// The length of [`GStr`].
///
/// If the most significant bit is 1, then the string is static.
///
/// The actual length is the `bitwise not` value of the wrapped [`NonZeroU32`] ignoring the static
/// flag.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Length(NonZeroU32);

impl Length {
    /// The number of bits used to represent the length (`31`).
    const LENGTH_BITS: u8 = (size_of::<Self>() * 8 - 1) as _;

    /// A mask where all bits are 1 (`0xFFFF_FFFF`).
    const MASK: u32 = u32::MAX;

    /// A mask that isolates the length part of the value (`0x7FFF_FFFF`).
    const LENGTH_MASK: u32 = (1 << Self::LENGTH_BITS) - 1;

    /// A mask intended to set the static flag (`0x8000_0000`).
    const STATIC_MASK: u32 = !Self::LENGTH_MASK;

    /// The maximum length (`0x7FFF_FFFE`).
    const MAX_LENGTH: usize = (Self::LENGTH_MASK - 1) as _;

    /// Creates a new [`Length`] for non-static strings.
    ///
    /// # Safety
    ///
    /// - `len` must not be greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - The returned [`Length`] is for non-static strings.
    #[inline]
    const unsafe fn new_unchecked(len: usize) -> Self {
        debug_assert!(len <= Self::MAX_LENGTH);

        // Because `len` does not exceed `MAX_LENGTH`, `len as u32 ^ Self::LENGTH_MASK` keeps the
        // static flag to be 0.
        // SAFETY: `len` does not exceed `MAX_LENGTH` so `len as u32 ^ Self::LENGTH_MASK` is
        //         non-zero.
        unsafe { Self(NonZeroU32::new_unchecked(len as u32 ^ Self::LENGTH_MASK)) }
    }

    /// Creates a new [`Length`] for static strings.
    ///
    /// # Safety
    ///
    /// - `len` must be greater than [`MAX_INLINE_LENGTH`](GStr::MAX_INLINE_LENGTH) and not exceed
    ///   [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - The returned [`Length`] is for static strings.
    #[inline]
    const unsafe fn new_static_unchecked(len: usize) -> Self {
        debug_assert!(len > GStr::MAX_INLINE_LENGTH && len <= Self::MAX_LENGTH);

        // `len` is not greater than `Self::MAX_LENGTH` so `len as u32 ^ Self::MASK` sets the static
        // flag to be 1.
        // SAFETY: `len` does not exceed `MAX_LENGTH` so `len as u32 ^ Self::MASK` is non-zero.
        unsafe { Self(NonZeroU32::new_unchecked(len as u32 ^ Self::MASK)) }
    }

    /// Returns the actual length.
    #[inline]
    const fn as_len(self) -> usize {
        ((self.0.get() ^ Self::MASK) & Self::LENGTH_MASK) as _
    }

    /// Indicates whether the string is a inline string.
    #[inline]
    const fn is_inline(self) -> bool {
        (self.0.get() | Self::STATIC_MASK) >= (u32::MAX - GStr::MAX_INLINE_LENGTH as u32)
    }

    /// Indicates whether the string is a static string.
    #[inline]
    const fn is_static(self) -> bool {
        self.0.get() >= Self::STATIC_MASK
    }

    /// Indicates whether the string is a heap allocated string.
    #[inline]
    const fn is_heap(self) -> bool {
        self.0.get() < (Self::LENGTH_MASK - GStr::MAX_INLINE_LENGTH as u32)
    }
}

#[repr(C)]
pub struct GStr {
    len: Length,
    prefix: [u8; Self::PREFIX_LENGTH],
    ptr: *const u8,
}

impl GStr {
    const PREFIX_LENGTH: usize = 4;

    pub const MAX_INLINE_LENGTH: usize = size_of::<Self>() - size_of::<Length>();

    pub const MAX_LENGTH: usize = Length::MAX_LENGTH;

    pub const EMPTY: Self = Self::const_new("");

    const UTF8_REPLACEMENT: &'static str = "\u{FFFD}";

    /// Creates [`GStr`] from a string.
    ///
    /// This clones the string.
    pub fn try_new<S: AsRef<str>>(string: S) -> Result<Self, ToGStrError<S>> {
        let s = string.as_ref();
        let len = s.len();

        if len <= Self::MAX_INLINE_LENGTH {
            unsafe { Ok(InlineBuffer::new(s).into_gstr()) }
        } else if len <= Self::MAX_LENGTH {
            let ptr = unsafe { alloc::alloc::alloc(Layout::array::<u8>(len).unwrap_unchecked()) };

            if ptr.is_null() {
                Err(ToGStrError::new_allocation_failure(string))
            } else {
                unsafe {
                    ptr::copy_nonoverlapping::<u8>(s.as_ptr(), ptr, len);
                }

                Ok(GStr {
                    len: unsafe { Length::new_unchecked(len) },
                    prefix: unsafe { copy_prefix(s) },
                    ptr,
                })
            }
        } else {
            length_overflow(string, len)
        }
    }

    /// Creates [`GStr`] from a string.
    ///
    /// This clones the string.
    ///
    /// # Panics
    ///
    /// - Panics if the length of `string` is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to allocate heap memory.
    pub fn new<S: AsRef<str>>(string: S) -> Self {
        match Self::try_new(string) {
            Ok(s) => s,
            Err(e) => match e.kind {
                ErrorKind::LengthOverflow(_) => panic!("{}", e),
                ErrorKind::AllocationFailure => handle_alloc_error(e.as_str()),
                _ => unsafe { core::hint::unreachable_unchecked() },
            },
        }
    }

    /// # Panics
    ///
    /// Panics if the length of `s` is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    #[inline]
    pub const fn const_new(string: &'static str) -> Self {
        if string.len() <= Self::MAX_INLINE_LENGTH {
            InlineBuffer::const_new(string).into_gstr()
        } else if string.len() <= Self::MAX_LENGTH {
            Self {
                len: unsafe { Length::new_static_unchecked(string.len()) },
                prefix: const_copy_prefix(string.as_bytes()),
                ptr: string.as_ptr(),
            }
        } else {
            panic!("the string's length should not be greater than `GStr`'s max length")
        }
    }

    /// Creates [`GStr`] from [`String`].
    ///
    /// This doesn't clone the string but shrinks it if the string's length isn't greater than
    /// [`MAX_INLINE_LENGTH`](Self::MAX_INLINE_LENGTH).
    #[inline]
    pub fn try_from_string(string: String) -> Result<Self, ToGStrError<String>> {
        let len = string.len();

        if len <= Self::MAX_INLINE_LENGTH {
            unsafe { Ok(InlineBuffer::new(&string).into_gstr()) }
        } else if len <= Self::MAX_LENGTH {
            match unsafe { shrink_and_leak_string(string) } {
                Ok(s) => {
                    debug_assert_eq!(s.len(), len);

                    Ok(Self {
                        len: unsafe { Length::new_unchecked(len) },
                        prefix: unsafe { copy_prefix(s) },
                        ptr: s.as_mut_ptr(),
                    })
                }
                Err(s) => Err(ToGStrError::new_allocation_failure(s)),
            }
        } else {
            length_overflow(string, len)
        }
    }

    /// Creates [`GStr`] from [`String`].
    ///
    /// This doesn't clone the string but shrinks it if the string's length isn't greater than
    /// [`MAX_INLINE_LENGTH`](Self::MAX_INLINE_LENGTH).
    ///
    /// # Panics
    ///
    /// - Panics if the length of `string` is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to shrink `string`'s capacity.
    #[inline]
    pub fn from_string(string: String) -> Self {
        match Self::try_from_string(string) {
            Ok(s) => s,
            Err(e) => match e.kind {
                ErrorKind::LengthOverflow(_) => panic!("{}", e),
                ErrorKind::AllocationFailure => handle_alloc_error(e),
                _ => unsafe { core::hint::unreachable_unchecked() },
            },
        }
    }

    #[inline]
    pub const unsafe fn from_raw_parts(buf: RawBuffer, len: usize) -> Self {
        debug_assert!(len <= Self::MAX_LENGTH);

        match buf {
            RawBuffer::Inline(buf) => {
                debug_assert!(len <= Self::MAX_INLINE_LENGTH);

                let buf = InlineBuffer {
                    len: unsafe { Length::new_unchecked(len) },
                    buf,
                };

                buf.into_gstr()
            }
            RawBuffer::Static(ptr) => {
                debug_assert!(len > Self::MAX_INLINE_LENGTH);

                let prefix = unsafe { slice::from_raw_parts(ptr.as_ptr(), Self::PREFIX_LENGTH) };

                Self {
                    len: unsafe { Length::new_static_unchecked(len) },
                    prefix: const_copy_prefix(prefix),
                    ptr: ptr.as_ptr(),
                }
            }
            RawBuffer::Heap(ptr) => {
                debug_assert!(len > Self::MAX_INLINE_LENGTH);

                let prefix = unsafe { slice::from_raw_parts(ptr.as_ptr(), Self::PREFIX_LENGTH) };

                Self {
                    len: unsafe { Length::new_unchecked(len) },
                    prefix: const_copy_prefix(prefix),
                    ptr: ptr.as_ptr(),
                }
            }
        }
    }

    #[inline]
    pub fn from_utf8(bytes: Vec<u8>) -> Result<Self, ToGStrError<Vec<u8>>> {
        let len = bytes.len();

        if len > Self::MAX_LENGTH {
            length_overflow(bytes, len)
        } else {
            let s = String::from_utf8(bytes)?;

            Self::try_from_string(s).map_err_source(String::into_bytes)
        }
    }

    /// # Safety
    ///
    /// `bytes` must be a valid sequence.
    ///
    /// # Panics
    ///
    /// - Panics if the length of `bytes` is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to shrink `bytes`' capacity.
    #[inline]
    pub unsafe fn from_utf8_unchecked(bytes: Vec<u8>) -> Self {
        unsafe { Self::from_string(String::from_utf8_unchecked(bytes)) }
    }

    /// # Panics
    ///
    /// - Panics if the length in bytes of the UTF-8 sequence converted is greater than
    ///   [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to allocate memory.
    #[must_use]
    pub fn from_utf8_lossy(bytes: Vec<u8>) -> Self {
        let mut iter = bytes.utf8_chunks();

        let first_valid = if let Some(chunk) = iter.next() {
            let valid = chunk.valid();

            if chunk.invalid().is_empty() {
                debug_assert_eq!(valid.len(), bytes.len());

                return unsafe { Self::from_utf8_unchecked(bytes) };
            }

            valid
        } else {
            return Self::EMPTY;
        };

        let mut res = String::with_capacity(bytes.len());
        res.push_str(first_valid);
        res.push_str(Self::UTF8_REPLACEMENT);

        for chunk in iter {
            res.push_str(chunk.valid());
            if !chunk.invalid().is_empty() {
                res.push_str(Self::UTF8_REPLACEMENT);
            }
        }

        Self::from_string(res)
    }

    /// # Panics
    ///
    /// Panics if fails to allocate memory.
    pub fn from_utf16<B: AsRef<[u16]>>(bytes: B) -> Result<Self, ToGStrError<B>> {
        let b = bytes.as_ref();

        match String::from_utf16(b) {
            Ok(s) => GStr::try_from_string(s).map_err_source(|_| bytes),
            Err(_) => Err(ToGStrError::new_invalid_utf16(bytes)),
        }
    }

    /// # Panics
    ///
    /// - Panics if the length in bytes of the UTF-8 sequence converted from the UTF-16 sequence
    ///   is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to allocate memory.
    pub fn from_utf16_lossy<B: AsRef<[u16]>>(bytes: B) -> Self {
        Self::from_string(String::from_utf16_lossy(bytes.as_ref()))
    }

    /// # Panics
    ///
    /// Panics if fails to allocate memory.
    pub fn from_utf16le<B: AsRef<[u8]>>(bytes: B) -> Result<Self, ToGStrError<B>> {
        let b = bytes.as_ref();

        if b.len() % 2 != 0 {
            return Err(ToGStrError::new_from_utf16_odd_length(bytes));
        }

        match (cfg!(target_endian = "little"), unsafe {
            b.align_to::<u16>()
        }) {
            (true, ([], v, [])) => match Self::from_utf16(v) {
                Ok(s) => Ok(s),
                Err(e) => Err(ToGStrError {
                    kind: e.kind,
                    source: bytes,
                }),
            },
            _ => {
                let iter = b.chunks_exact(2).map(|s| unsafe {
                    u16::from_le_bytes(<[u8; 2]>::try_from(s).unwrap_unchecked())
                });

                char::decode_utf16(iter)
                    .collect::<Result<_, _>>()
                    .map_err(|_| ToGStrError::new_invalid_utf16(bytes))
            }
        }
    }

    /// # Panics
    ///
    /// - Panics if the length in bytes of the UTF-8 sequence converted from the UTF-16 sequence
    ///   is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to allocate memory.
    pub fn from_utf16le_lossy<B: AsRef<[u8]>>(bytes: B) -> Self {
        let b = bytes.as_ref();

        match (cfg!(target_endian = "little"), unsafe {
            b.align_to::<u16>()
        }) {
            (true, ([], v, [])) => Self::from_utf16_lossy(v),
            (true, ([], v, [_])) => {
                Self::from_string(String::from_utf16_lossy(v) + Self::UTF8_REPLACEMENT)
            }
            _ => {
                let mut iter = b.chunks_exact(2);
                let u16_iter = iter.by_ref().map(|s| unsafe {
                    u16::from_le_bytes(<[u8; 2]>::try_from(s).unwrap_unchecked())
                });
                let string = char::decode_utf16(u16_iter)
                    .map(|r| r.unwrap_or(char::REPLACEMENT_CHARACTER))
                    .collect::<String>();

                if iter.remainder().is_empty() {
                    Self::from_string(string)
                } else {
                    Self::from_string(string + Self::UTF8_REPLACEMENT)
                }
            }
        }
    }

    /// # Panics
    ///
    /// Panics if fails to allocate memory.
    pub fn from_utf16be<B: AsRef<[u8]>>(bytes: B) -> Result<Self, ToGStrError<B>> {
        let b = bytes.as_ref();

        if b.len() % 2 != 0 {
            return Err(ToGStrError::new_from_utf16_odd_length(bytes));
        }

        match (cfg!(target_endian = "big"), unsafe { b.align_to::<u16>() }) {
            (true, ([], v, [])) => match Self::from_utf16(v) {
                Ok(s) => Ok(s),
                Err(e) => Err(ToGStrError {
                    kind: e.kind,
                    source: bytes,
                }),
            },
            _ => {
                let iter = b.chunks_exact(2).map(|s| unsafe {
                    u16::from_be_bytes(<[u8; 2]>::try_from(s).unwrap_unchecked())
                });

                char::decode_utf16(iter)
                    .collect::<Result<_, _>>()
                    .map_err(|_| ToGStrError::new_invalid_utf16(bytes))
            }
        }
    }

    /// # Panics
    ///
    /// - Panics if the length in bytes of the UTF-8 sequence converted from the UTF-16 sequence
    ///   is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to allocate memory.
    pub fn from_utf16be_lossy<B: AsRef<[u8]>>(bytes: B) -> Self {
        let b = bytes.as_ref();

        match (cfg!(target_endian = "big"), unsafe { b.align_to::<u16>() }) {
            (true, ([], v, [])) => Self::from_utf16_lossy(v),
            (true, ([], v, [_])) => {
                Self::from_string(String::from_utf16_lossy(v) + Self::UTF8_REPLACEMENT)
            }
            _ => {
                let mut iter = b.chunks_exact(2);
                let u16_iter = iter.by_ref().map(|s| unsafe {
                    u16::from_be_bytes(<[u8; 2]>::try_from(s).unwrap_unchecked())
                });
                let string = char::decode_utf16(u16_iter)
                    .map(|r| r.unwrap_or(char::REPLACEMENT_CHARACTER))
                    .collect::<String>();

                if iter.remainder().is_empty() {
                    Self::from_string(string)
                } else {
                    Self::from_string(string + Self::UTF8_REPLACEMENT)
                }
            }
        }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.len.as_len()
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub const fn is_inline(&self) -> bool {
        self.len.is_inline()
    }

    #[inline]
    pub const fn is_static(&self) -> bool {
        self.len.is_static()
    }

    #[inline]
    pub const fn is_heap(&self) -> bool {
        self.len.is_heap()
    }

    #[inline]
    const fn as_len_prefix_u64(&self) -> u64 {
        #[cfg(target_pointer_width = "64")]
        // SAFETY:
        // - `GStr` is valid for reading its first 8 bytes as `u64`.
        // - `GStr` is properly initialized.
        // - `GStr`'s alignment is the same as `u64`.
        unsafe {
            ptr::read(ptr::from_ref(self).cast::<u64>())
        }

        #[cfg(target_pointer_width = "32")]
        // SAFETY:
        // - `GStr` is valid for reading its first 8 bytes as `u64`.
        // - `GStr` is properly initialized.
        // - `GStr`'s alignment is 4 and `u64`'s alignment is 8, so `ptr::read_unaligned` is used.
        unsafe {
            ptr::read_unaligned(ptr::from_ref(self).cast::<u64>())
        }
    }

    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        if self.is_inline() {
            let buf = unsafe { InlineBuffer::from_gstr(self) };

            buf.buf.as_ptr()
        } else {
            self.ptr
        }
    }

    #[inline]
    pub const fn as_bytes(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    #[inline]
    #[must_use]
    pub const fn as_str(&self) -> &str {
        unsafe { core::str::from_utf8_unchecked(self.as_bytes()) }
    }

    #[inline]
    pub const fn as_inline_buffer(&self) -> Option<&[u8; Self::MAX_INLINE_LENGTH]> {
        if self.is_inline() {
            unsafe { Some(&InlineBuffer::from_gstr(self).buf) }
        } else {
            None
        }
    }

    #[inline]
    pub const fn as_static_str(&self) -> Option<&'static str> {
        if self.is_static() {
            unsafe {
                Some(core::str::from_utf8_unchecked(slice::from_raw_parts(
                    self.ptr,
                    self.len(),
                )))
            }
        } else {
            None
        }
    }

    #[inline]
    pub fn try_into_string(self) -> Result<String, Self> {
        let string = ManuallyDrop::new(self);

        if string.is_heap() {
            let len = string.len();

            unsafe { Ok(String::from_raw_parts(string.ptr.cast_mut(), len, len)) }
        } else {
            let s = string.as_str();
            let len = s.len();
            let ptr = unsafe { alloc::alloc::alloc(Layout::array::<u8>(len).unwrap_unchecked()) };

            if ptr.is_null() {
                Err(ManuallyDrop::into_inner(string))
            } else {
                unsafe {
                    ptr::copy_nonoverlapping::<u8>(s.as_ptr(), ptr, len);
                }

                unsafe { Ok(String::from_raw_parts(ptr, len, len)) }
            }
        }
    }

    /// # Panics
    ///
    /// Panics if fails to allocate memory.
    #[inline]
    pub fn into_string(self) -> String {
        match self.try_into_string() {
            Ok(s) => s,
            Err(s) => handle_alloc_error(s),
        }
    }

    /// # Panics
    ///
    /// Panics if fails to allocate memory.
    #[inline]
    pub fn into_boxed_str(self) -> Box<str> {
        self.into_string().into_boxed_str()
    }

    /// # Panics
    ///
    /// Panics if fails to allocate memory.
    #[inline]
    pub fn into_bytes(self) -> Vec<u8> {
        self.into_string().into_bytes()
    }

    #[inline]
    pub const fn into_raw_parts(self) -> (RawBuffer, usize) {
        let len = self.len();
        let buf = if self.is_inline() {
            let buf = unsafe { InlineBuffer::from_gstr(&self) };

            RawBuffer::Inline(buf.buf)
        } else if self.is_static() {
            unsafe { RawBuffer::Static(NonNull::new_unchecked(self.ptr.cast_mut())) }
        } else {
            debug_assert!(self.is_heap());

            unsafe { RawBuffer::Heap(NonNull::new_unchecked(self.ptr.cast_mut())) }
        };
        mem::forget(self);

        (buf, len)
    }

    /// # Panics
    ///
    /// Panics if fails to allocate memory.
    #[inline]
    pub fn leak<'a>(self) -> &'a str {
        let string = ManuallyDrop::new(self);
        let len = string.len();

        if string.is_inline() {
            let buf = unsafe { InlineBuffer::from_gstr(&string) };
            let s = unsafe {
                core::str::from_utf8_unchecked(slice::from_raw_parts(buf.buf.as_ptr(), len))
            };

            String::from(s).leak()
        } else {
            unsafe { core::str::from_utf8_unchecked(slice::from_raw_parts(string.ptr, len)) }
        }
    }

    /// # Panics
    ///
    /// - Panics if the total length of `self` and `string` is greater than
    ///   [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to allocate memory.
    pub fn concat<S: AsRef<str>>(&self, string: S) -> Self {
        let a = self.as_str();
        let b = string.as_ref();
        let total_len = a.len() + b.len();

        if total_len <= Self::MAX_INLINE_LENGTH {
            unsafe { InlineBuffer::concat(a, b).into_gstr() }
        } else {
            let mut s = String::with_capacity(total_len);
            s.push_str(a);
            s.push_str(b);

            Self::from_string(s)
        }
    }
}

impl Drop for GStr {
    #[inline]
    fn drop(&mut self) {
        if self.is_heap() {
            debug_assert!(!self.ptr.is_null());

            unsafe {
                alloc::alloc::dealloc(
                    self.ptr.cast_mut(),
                    Layout::array::<u8>(self.len()).unwrap_unchecked(),
                );
            }
        }
    }
}

impl AsRef<str> for GStr {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl Deref for GStr {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl Borrow<str> for GStr {
    #[inline]
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl fmt::Debug for GStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("GStr")
            .field("len", &self.len())
            .field("is_static", &self.is_static())
            .field("prefix", &self.prefix)
            .field("str", &self.as_str())
            .finish()
    }
}

impl fmt::Display for GStr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl Clone for GStr {
    #[inline]
    fn clone(&self) -> Self {
        if self.is_heap() {
            Self::new(self)
        } else {
            Self {
                len: self.len,
                prefix: self.prefix,
                ptr: self.ptr,
            }
        }
    }
}

impl Default for GStr {
    #[inline]
    fn default() -> Self {
        Self::EMPTY
    }
}

impl PartialEq for GStr {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // TODO: benchmark this
        if gstr_len_prefix_eq(self, other) {
            let len = self.len();

            if len <= Self::MAX_INLINE_LENGTH {
                ptr::addr_eq(self.ptr, other.ptr)
            } else {
                let a = unsafe { slice::from_raw_parts(self.ptr, len) };
                let b = unsafe { slice::from_raw_parts(other.ptr, len) };

                a == b
            }
        } else {
            false
        }
    }
}

impl Eq for GStr {}

impl PartialOrd for GStr {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for GStr {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match self.prefix.cmp(&other.prefix) {
            Ordering::Equal => self.as_bytes().cmp(other.as_bytes()),
            not_eq => not_eq,
        }
    }
}

impl Hash for GStr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl FromStr for GStr {
    type Err = ToGStrError<()>;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_new(s).map_err_source(|_| {})
    }
}

impl<I: SliceIndex<str>> Index<I> for GStr {
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        self.as_str().index(index)
    }
}

unsafe impl Send for GStr {}

unsafe impl Sync for GStr {}

impl AsRef<[u8]> for GStr {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<T: ?Sized> PartialEq<&'_ T> for GStr
where
    Self: PartialEq<T>,
{
    #[inline]
    fn eq(&self, other: &&'_ T) -> bool {
        PartialEq::<T>::eq(self, *other)
    }
}

impl PartialEq<str> for GStr {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        if gstr_str_len_prefix_eq(self, other) {
            debug_assert_eq!(self.len(), other.len());
            let len = other.len();

            let a = unsafe { slice::from_raw_parts(self.as_ptr(), len) };
            let b = unsafe { slice::from_raw_parts(other.as_ptr(), len) };

            a == b
        } else {
            false
        }
    }
}

impl PartialEq<GStr> for str {
    #[inline]
    fn eq(&self, other: &GStr) -> bool {
        other == self
    }
}

impl PartialEq<GStr> for &'_ str {
    #[inline]
    fn eq(&self, other: &GStr) -> bool {
        *self == other
    }
}

impl PartialEq<String> for GStr {
    #[inline]
    fn eq(&self, other: &String) -> bool {
        self == other.as_str()
    }
}

impl PartialEq<GStr> for String {
    #[inline]
    fn eq(&self, other: &GStr) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<Cow<'_, str>> for GStr {
    #[inline]
    fn eq(&self, other: &Cow<'_, str>) -> bool {
        self == other.as_ref()
    }
}

impl PartialEq<GStr> for Cow<'_, str> {
    #[inline]
    fn eq(&self, other: &GStr) -> bool {
        self.as_ref() == other
    }
}

impl<T: ?Sized> PartialOrd<&'_ T> for GStr
where
    Self: PartialOrd<T>,
{
    #[inline]
    fn partial_cmp(&self, other: &&'_ T) -> Option<Ordering> {
        PartialOrd::<T>::partial_cmp(self, *other)
    }
}

impl PartialOrd<str> for GStr {
    #[inline]
    fn partial_cmp(&self, other: &str) -> Option<Ordering> {
        match self.prefix.cmp(&str_prefix(other)) {
            Ordering::Equal => self.as_str().partial_cmp(other),
            not_eq => Some(not_eq),
        }
    }
}

impl PartialOrd<GStr> for str {
    #[inline]
    fn partial_cmp(&self, other: &GStr) -> Option<Ordering> {
        match str_prefix(self).cmp(&other.prefix) {
            Ordering::Equal => self.partial_cmp(other.as_str()),
            not_eq => Some(not_eq),
        }
    }
}

impl PartialOrd<GStr> for &'_ str {
    #[inline]
    fn partial_cmp(&self, other: &GStr) -> Option<Ordering> {
        (*self).partial_cmp(other)
    }
}

impl From<char> for GStr {
    #[inline]
    fn from(c: char) -> Self {
        InlineBuffer::from_char(c).into_gstr()
    }
}

impl From<&GStr> for GStr {
    #[inline]
    fn from(string: &GStr) -> Self {
        string.clone()
    }
}

impl<'a> TryFrom<&'a str> for GStr {
    type Error = ToGStrError<&'a str>;

    /// Converts `&str` into [`GStr`].
    ///
    /// This clones the string.
    #[inline]
    fn try_from(string: &'a str) -> Result<Self, Self::Error> {
        Self::try_new(string)
    }
}

impl<'a> TryFrom<&'a mut str> for GStr {
    type Error = ToGStrError<&'a mut str>;

    /// Converts `&mut str` into [`GStr`].
    ///
    /// This clones the string.
    #[inline]
    fn try_from(string: &'a mut str) -> Result<Self, Self::Error> {
        Self::try_new(string)
    }
}

impl TryFrom<String> for GStr {
    type Error = ToGStrError<String>;

    /// Converts [`String`] into [`GStr`].
    ///
    /// This doesn't clone the string but shrinks it if the string's length isn't greater than
    /// [`MAX_INLINE_LENGTH`](Self::MAX_INLINE_LENGTH).
    #[inline]
    fn try_from(string: String) -> Result<Self, Self::Error> {
        Self::try_from_string(string)
    }
}

impl<'a> TryFrom<&'a String> for GStr {
    type Error = ToGStrError<&'a String>;

    /// Converts `&String` into [`GStr`].
    ///
    /// This clones the string.
    #[inline]
    fn try_from(string: &'a String) -> Result<Self, Self::Error> {
        Self::try_new(string)
    }
}

impl TryFrom<Box<str>> for GStr {
    type Error = ToGStrError<Box<str>>;

    /// Converts `Box<str>` into [`GStr`].
    ///
    /// This doesn't clone the string if the string's length isn't greater than
    /// [`MAX_INLINE_LENGTH`](Self::MAX_INLINE_LENGTH).
    #[inline]
    fn try_from(string: Box<str>) -> Result<Self, Self::Error> {
        let string = string.into_string();

        Self::try_from_string(string).map_err_source(String::into_boxed_str)
    }
}

impl<'a> TryFrom<Cow<'a, str>> for GStr {
    type Error = ToGStrError<Cow<'a, str>>;

    #[inline]
    fn try_from(string: Cow<'a, str>) -> Result<Self, Self::Error> {
        match string {
            Cow::Borrowed(s) => Self::try_new(s).map_err_source(Cow::Borrowed),
            Cow::Owned(s) => Self::try_from_string(s).map_err_source(Cow::Owned),
        }
    }
}

impl<'a> From<&'a GStr> for &'a [u8] {
    #[inline]
    fn from(string: &'a GStr) -> Self {
        string.as_bytes()
    }
}

impl<'a> From<&'a GStr> for &'a str {
    #[inline]
    fn from(string: &'a GStr) -> Self {
        string.as_str()
    }
}

impl From<GStr> for String {
    #[inline]
    fn from(string: GStr) -> Self {
        string.into_string()
    }
}

impl From<GStr> for Vec<u8> {
    #[inline]
    fn from(string: GStr) -> Self {
        string.into_bytes()
    }
}

impl From<GStr> for Box<str> {
    #[inline]
    fn from(string: GStr) -> Self {
        string.into_boxed_str()
    }
}

impl<'a> From<&'a GStr> for Cow<'a, str> {
    #[inline]
    fn from(string: &'a GStr) -> Self {
        Self::Borrowed(string.as_str())
    }
}

impl From<GStr> for Rc<str> {
    #[inline]
    fn from(string: GStr) -> Self {
        Self::from(string.as_ref())
    }
}

impl From<GStr> for Arc<str> {
    #[inline]
    fn from(string: GStr) -> Self {
        Self::from(string.as_ref())
    }
}

impl From<GStr> for Box<dyn Error + Send + Sync + '_> {
    #[inline]
    fn from(string: GStr) -> Self {
        struct StringError(GStr);

        impl fmt::Debug for StringError {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Debug::fmt(&self.0, f)
            }
        }

        impl fmt::Display for StringError {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(&self.0, f)
            }
        }

        impl Error for StringError {}

        Box::new(StringError(string))
    }
}

impl From<GStr> for Box<dyn Error + '_> {
    #[inline]
    fn from(string: GStr) -> Self {
        let err1: Box<dyn Error + Send + Sync> = From::from(string);
        let err2: Box<dyn Error> = err1;

        err2
    }
}

impl<T> FromIterator<T> for GStr
where
    String: FromIterator<T>,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self::from_string(String::from_iter(iter))
    }
}

impl FromIterator<GStr> for String {
    fn from_iter<T: IntoIterator<Item = GStr>>(iter: T) -> Self {
        let mut string = String::new();
        for s in iter {
            string.push_str(s.as_str());
        }

        string
    }
}

impl FromIterator<GStr> for Box<str> {
    fn from_iter<T: IntoIterator<Item = GStr>>(iter: T) -> Self {
        String::from_iter(iter).into_boxed_str()
    }
}

impl FromIterator<GStr> for Cow<'_, str> {
    fn from_iter<T: IntoIterator<Item = GStr>>(iter: T) -> Self {
        String::from_iter(iter).into()
    }
}

#[cfg(target_pointer_width = "64")]
/// The inline buffer variant of [`GStr`]. It should have the same size and alignment as [`GStr`].
#[repr(C, align(8))]
struct InlineBuffer {
    /// The inline buffer's length.
    len: Length,
    /// The inline buffer.
    buf: [u8; Self::BUFFER_LENGTH],
}

#[cfg(target_pointer_width = "32")]
/// The inline buffer variant of [`GStr`]. It should have the same size and alignment as [`GStr`].
#[repr(C, align(4))]
struct InlineBuffer {
    len: Length,
    buf: [u8; Self::BUFFER_LENGTH],
}

impl InlineBuffer {
    /// The inline buffer's length.
    const BUFFER_LENGTH: usize = GStr::MAX_INLINE_LENGTH;

    /// Creates a [`InlineBuffer`] from `&str`.
    ///
    /// # Safety
    ///
    /// The length of `string` must not exceed [`BUFFER_LENGTH`](Self::BUFFER_LENGTH).
    #[inline]
    unsafe fn new(string: &str) -> Self {
        debug_assert!(string.len() <= Self::BUFFER_LENGTH);

        let mut buf = [0u8; Self::BUFFER_LENGTH];
        // SAFETY: The length of `string` is guaranteed not to exceed `BUFFER_LENGTH`.
        unsafe {
            ptr::copy_nonoverlapping::<u8>(string.as_ptr(), buf.as_mut_ptr(), string.len());
        }

        Self {
            // SAFETY:
            // - The length of `string` isn't greater than `BUFFER_LENGTH` so it's less than
            //   `Length::MAX_LENGTH`.
            // - The inline buffer isn't static.
            len: unsafe { Length::new_unchecked(string.len()) },
            buf,
        }
    }

    /// Creates a [`InlineBuffer`] from `&str` in const context.
    ///
    /// # Panics
    ///
    /// Panics if the length of `string` is greater than [`BUFFER_LENGTH`](Self::BUFFER_LENGTH).
    #[inline]
    const fn const_new(string: &'static str) -> Self {
        let len = string.len();
        if len > Self::BUFFER_LENGTH {
            panic!("the string's length should not be greater than the inline buffer's length");
        }

        let mut buf = [0u8; Self::BUFFER_LENGTH];
        let bytes = string.as_bytes();
        let mut i = 0;
        while i < len {
            // The bound checks are optimized away.
            buf[i] = bytes[i];
            i += 1;
        }

        Self {
            // SAFETY:
            // - The length of `string` isn't greater than `BUFFER_LENGTH` so it's less than
            //   `Length::MAX_LENGTH`.
            // - The inline buffer isn't static.
            len: unsafe { Length::new_unchecked(len) },
            buf,
        }
    }

    /// Creates a [`InlineBuffer`] from a char.
    #[inline]
    fn from_char(c: char) -> Self {
        let mut buf = [0u8; Self::BUFFER_LENGTH];
        let s = c.encode_utf8(&mut buf);

        Self {
            // SAFETY: The length of string returned from `char::encode_utf8` isn't greater than 4.
            len: unsafe { Length::new_unchecked(s.len()) },
            buf,
        }
    }

    /// Creates a [`InlineBuffer`] reference from a [`GStr`] reference.
    ///
    /// # Safety
    ///
    /// `string` must be inline.
    #[inline]
    const unsafe fn from_gstr(string: &GStr) -> &Self {
        // SAFETY: `InlineBuffer` is a variant of `GStr` and have the same layout as `GStr`.
        unsafe { mem::transmute::<&GStr, &Self>(string) }
    }

    /// Concatenates two strings to a [`InlineBuffer`].
    ///
    /// # Safety
    ///
    /// The total length of `a` and `b` must not exceed [`BUFFER_LENGTH`](Self::BUFFER_LENGTH).
    #[inline]
    unsafe fn concat(a: &str, b: &str) -> Self {
        let a_len = a.len();
        let b_len = b.len();
        debug_assert!(a_len + b_len <= Self::BUFFER_LENGTH);

        let mut buf = [0u8; Self::BUFFER_LENGTH];
        let buf_ptr = buf.as_mut_ptr();
        // SAFETY: The length of `a` and `b` isn't greater than `BUFFER_LENGTH` so it's valid for
        //         copying `a` and `b` into `buf`.
        unsafe {
            ptr::copy_nonoverlapping::<u8>(a.as_ptr(), buf_ptr, a_len);
            ptr::copy_nonoverlapping::<u8>(b.as_ptr(), buf_ptr.add(a_len), b_len);
        }

        Self {
            // SAFETY: The length of `a` and `b` isn't greater than `BUFFER_LENGTH` so it's less
            // than `Length::MAX_LENGTH`.
            len: unsafe { Length::new_unchecked(a_len + b_len) },
            buf,
        }
    }

    /// Converts this [`InlineBuffer`] to a [`GStr`].
    #[inline]
    const fn into_gstr(self) -> GStr {
        // SAFETY: `InlineBuffer` is a variant of `GStr` and have the same layout as `GStr`.
        unsafe { mem::transmute::<Self, GStr>(self) }
    }
}

/// Copies the first [`PREFIX_LENGTH`](GStr::PREFIX_LENGTH) bytes of `string` into an array.
///
/// # Safety
///
/// The length of `string` must not be less than [`PREFIX_LENGTH`](GStr::PREFIX_LENGTH).
#[inline]
unsafe fn copy_prefix(string: &str) -> [u8; GStr::PREFIX_LENGTH] {
    debug_assert!(string.len() >= GStr::PREFIX_LENGTH);

    let mut prefix = [0u8; GStr::PREFIX_LENGTH];
    // SAFETY: The length of `string` is guaranteed to be not less than `PREFIX_LENGTH`.
    unsafe {
        ptr::copy_nonoverlapping::<u8>(string.as_ptr(), prefix.as_mut_ptr(), GStr::PREFIX_LENGTH);
    }

    prefix
}

/// Copies the first [`PREFIX_LENGTH`](GStr::PREFIX_LENGTH) bytes of `bytes` into an array.
///
/// # Panics
///
/// Panics if the length of `bytes` is less than [`PREFIX_LENGTH`](GStr::PREFIX_LENGTH).
#[inline]
const fn const_copy_prefix(bytes: &[u8]) -> [u8; GStr::PREFIX_LENGTH] {
    if bytes.len() < GStr::PREFIX_LENGTH {
        panic!("the bytes' length should not be less than the prefix buffer's length");
    }

    let mut prefix = [0u8; GStr::PREFIX_LENGTH];
    let mut i = 0;
    while i < GStr::PREFIX_LENGTH {
        prefix[i] = bytes[i];
        i += 1;
    }

    prefix
}

#[cfg(target_endian = "little")]
/// A mask for [`GStr`]'s `len` and `prefix` to set the static flag 0 (`0xFFFF_FFFF_7FFF_FFFF`).
const LEN_PREFIX_MASK: u64 = !(Length::STATIC_MASK as u64);

#[cfg(target_endian = "big")]
/// A mask for [`GStr`]'s `len` and `prefix` to set the static flag 0 (`0x7FFF_FFFF_FFFF_FFFF`).
const LEN_PREFIX_MASK: u64 = !((Length::STATIC_MASK as u64) << 32);

/// Compares two [`GStr`]'s `len` and `prefix` at the same time.
#[inline]
const fn gstr_len_prefix_eq(a: &GStr, b: &GStr) -> bool {
    (a.as_len_prefix_u64() & LEN_PREFIX_MASK) == (b.as_len_prefix_u64() & LEN_PREFIX_MASK)
}

/// Gets the first [`PREFIX_LENGTH`](GStr::PREFIX_LENGTH) bytes of `string`.
#[inline]
fn str_prefix(string: &str) -> [u8; GStr::PREFIX_LENGTH] {
    let mut prefix = [0u8; 4];

    unsafe {
        ptr::copy_nonoverlapping::<u8>(
            string.as_ptr(),
            prefix.as_mut_ptr(),
            string.len().min(GStr::PREFIX_LENGTH),
        );
    }

    prefix
}

#[inline]
fn gstr_str_len_prefix_eq(a: &GStr, b: &str) -> bool {
    let a_prefix = a.as_len_prefix_u64();

    let b_prefix_array = [
        (b.len().min(u32::MAX as _) as u32) ^ Length::LENGTH_MASK,
        unsafe { mem::transmute::<[u8; GStr::PREFIX_LENGTH], u32>(str_prefix(b)) },
    ];

    // If `b.len()` is greater than `GStr::MAX_INLINE_LENGTH`, `b_prefix_array[0]` will be 0 or its
    // most significant bit will be 1, so `false` will be returned.
    (a_prefix & LEN_PREFIX_MASK) == unsafe { mem::transmute::<[u32; 2], u64>(b_prefix_array) }
}

/// Shrinks `string`'s capacity to match its length and leaks it as a static mutable [`str`].
///
/// If shrinking `string`'s capacity fails, returns the original `string`.
///
/// # Safety
///
/// The length of `string` must be greater than 0.
#[inline]
unsafe fn shrink_and_leak_string(string: String) -> Result<&'static mut str, String> {
    debug_assert!(string.len() > GStr::MAX_INLINE_LENGTH && string.len() <= GStr::MAX_LENGTH);

    if string.len() == string.capacity() {
        Ok(string.leak())
    } else {
        debug_assert!(string.capacity() > string.len());

        /// Shrinks `string`'s capacity to match its length and leaks it as a static mutable
        /// [`str`].
        ///
        /// If shrinking `string`'s capacity fails, returns the original `string`.
        ///
        /// # Safety
        ///
        /// The length of `string` must be greater than 0.
        #[cold]
        #[inline(never)]
        unsafe fn realloc_string(string: String) -> Result<&'static mut str, String> {
            let mut s = ManuallyDrop::new(string);
            let len = s.len();
            let capacity = s.capacity();
            // Not using `s.as_mut_ptr()` to get the raw pointer because it only covers `len` bytes
            // under the Stacked Borrows rules. Reallocating the memory requires the raw pointer
            // covers `capacity` bytes.
            // SAFETY: We just get the raw pointer from `string`'s inner buffer, not mutating its
            //         content.
            let ptr = unsafe { s.as_mut_vec().as_mut_ptr() };
            // SAFETY: The layout of string's inner buffer is valid.
            let layout = unsafe { Layout::array::<u8>(capacity).unwrap_unchecked() };

            // SAFETY:
            // - `ptr` is the pointer of `string`'s inner buffer, so it was allocated by the global
            //   allocator.
            // - `layout` is the layout of `string`'s inner buffer.
            // - The length of `string` is guaranteed to be greater than 0.
            // - `len` doesn't overflows `isize`.
            let new_ptr = unsafe { alloc::alloc::realloc(ptr, layout, len) };

            if new_ptr.is_null() {
                Err(ManuallyDrop::into_inner(s))
            } else {
                // SAFETY:
                // - `new_ptr` points to a valid UTF-8 string buffer whose length is `len`.
                // - `string` is consumed and won't be dropped.
                unsafe {
                    Ok(core::str::from_utf8_unchecked_mut(
                        slice::from_raw_parts_mut(new_ptr, len),
                    ))
                }
            }
        }

        // SAFETY: The length of `string` is guaranteed to be greater than 0.
        unsafe { realloc_string(string) }
    }
}

/// Returns a length overflow error.
#[cold]
#[inline(never)]
fn length_overflow<S>(string: S, len: usize) -> Result<GStr, ToGStrError<S>> {
    Err(ToGStrError::new_length_overflow(string, len))
}

/// Handle the memory allocation error.
///
/// For more details, see [`handle_alloc_error`](alloc::alloc::handle_alloc_error).
#[cold]
#[inline(never)]
pub(crate) fn handle_alloc_error<B: AsRef<[u8]>>(buf: B) -> ! {
    // SAFETY: The layout of the buffer is valid.
    unsafe {
        alloc::alloc::handle_alloc_error(Layout::array::<u8>(buf.as_ref().len()).unwrap_unchecked())
    }
}

const _: () = {
    assert!(size_of::<Length>() == size_of::<u32>());
    assert!(size_of::<Option<Length>>() == size_of::<u32>());

    #[cfg(target_pointer_width = "64")]
    {
        assert!(size_of::<GStr>() == 4 * size_of::<u32>());
        assert!(size_of::<Option<GStr>>() == 4 * size_of::<u32>());
    }

    #[cfg(target_pointer_width = "32")]
    {
        assert!(size_of::<GStr>() == 3 * size_of::<u32>());
        assert!(size_of::<Option<GStr>>() == 3 * size_of::<u32>());
    }

    assert!(align_of::<GStr>() == align_of::<usize>());

    assert!(size_of::<InlineBuffer>() == size_of::<GStr>());
    assert!(size_of::<Option<InlineBuffer>>() == size_of::<Option<GStr>>());
    assert!(align_of::<InlineBuffer>() == align_of::<GStr>());

    assert!(RawBuffer::INLINE_LENGTH == GStr::MAX_INLINE_LENGTH);

    assert!(Length::LENGTH_BITS == 31);
    assert!(Length::MASK == 0xFFFF_FFFF);
    assert!(Length::LENGTH_MASK == 0x7FFF_FFFF);
    assert!(Length::STATIC_MASK == 0x8000_0000);
    assert!(Length::MAX_LENGTH == 0x7FFF_FFFE);

    assert!(GStr::PREFIX_LENGTH == 4);
    #[cfg(target_pointer_width = "64")]
    assert!(GStr::MAX_INLINE_LENGTH == 12);
    #[cfg(target_pointer_width = "32")]
    assert!(GStr::MAX_INLINE_LENGTH == 8);
    assert!(GStr::MAX_LENGTH == Length::MAX_LENGTH);
    assert!(GStr::MAX_LENGTH <= isize::MAX as _);

    assert!(InlineBuffer::BUFFER_LENGTH == GStr::MAX_INLINE_LENGTH);

    #[cfg(target_endian = "little")]
    assert!(LEN_PREFIX_MASK == 0xFFFF_FFFF_7FFF_FFFF);
    #[cfg(target_endian = "big")]
    assert!(LEN_PREFIX_MASK == 0x7FFF_FFFF_FFFF_FFFF);
};

#[cfg(target_pointer_width = "16")]
compile_error!("16-bit platforms aren't supported");

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    use proptest::prelude::*;

    //extern crate std;

    fn test_literal_strings<F: Fn(&'static str)>(f: F) {
        f("");
        f("a");
        f("ab");
        f("abc");
        f("abcd");
        f("abcde");
        f("abcdefghijkl");
        f("hello, 🌎!");
        f("abcdefghijklm");
        f("hello, 🦀 and 🌎!");
    }

    #[allow(clippy::eq_op)]
    fn test_gstr_is_eq(a: GStr, b: &str) {
        assert_eq!(a.len(), b.len());
        assert_eq!(a, a);
        assert_eq!(a, b);
        assert_eq!(b, a);
        assert_eq!(a.cmp(&a), Ordering::Equal);
        assert_eq!(a.partial_cmp(&a), Some(Ordering::Equal));
        assert_eq!(a.partial_cmp(b), Some(Ordering::Equal));
        assert_eq!(b.partial_cmp(&a), Some(Ordering::Equal));

        let c = GStr::new(b);
        assert_eq!(a, c);
        assert_eq!(c, a);
        assert_eq!(a.cmp(&c), Ordering::Equal);
        assert_eq!(c.cmp(&a), Ordering::Equal);
        assert_eq!(a.partial_cmp(&c), Some(Ordering::Equal));
        assert_eq!(c.partial_cmp(&a), Some(Ordering::Equal));

        let bytes = b.as_bytes();
        #[allow(clippy::needless_range_loop)]
        for i in 0..(bytes.len().min(GStr::PREFIX_LENGTH)) {
            assert_eq!(a.prefix[i], bytes[i]);
        }
        for i in bytes.len()..GStr::PREFIX_LENGTH {
            assert_eq!(a.prefix[i], 0);
        }
    }

    fn test_gstr_new(string: &str) {
        let gstr = GStr::new(string);

        assert!(!gstr.is_static());
        if string.len() <= GStr::MAX_INLINE_LENGTH {
            assert!(gstr.is_inline());
        } else {
            assert!(gstr.is_heap());
        }

        test_gstr_is_eq(gstr, string);
    }

    fn test_gstr_const_new(string: &'static str) {
        let gstr = GStr::const_new(string);

        assert!(!gstr.is_heap());
        if string.len() <= GStr::MAX_INLINE_LENGTH {
            assert!(gstr.is_inline());
        } else {
            assert!(gstr.is_static());
        }

        test_gstr_is_eq(gstr, string);
    }

    fn test_gstr_from_string(string: &str) {
        let gstr = GStr::from_string(String::from(string));

        assert!(!gstr.is_static());
        if string.len() <= GStr::MAX_INLINE_LENGTH {
            assert!(gstr.is_inline());
        } else {
            assert!(gstr.is_heap());
        }

        test_gstr_is_eq(gstr, string);

        let mut s = String::from(string);
        s.reserve(16);
        let gstr = GStr::from_string(s);

        assert!(!gstr.is_static());
        if string.len() <= GStr::MAX_INLINE_LENGTH {
            assert!(gstr.is_inline());
        } else {
            assert!(gstr.is_heap());
        }

        test_gstr_is_eq(gstr, string);
    }

    fn test_gstr_eq_cmp(a: &str, b: &str) {
        let gstr_a = GStr::new(a);
        let gstr_b = GStr::new(b);

        assert_eq!(gstr_a > gstr_b, a > b);
        assert_eq!(gstr_a < gstr_b, a < b);
        assert_eq!(gstr_a == gstr_b, a == b);
        assert_eq!(gstr_a >= gstr_b, a >= b);
        assert_eq!(gstr_a <= gstr_b, a <= b);
        assert_eq!(gstr_a.cmp(&gstr_b), a.cmp(b));
        assert_eq!(gstr_a.partial_cmp(&gstr_b), a.partial_cmp(b));

        assert_eq!(gstr_b > gstr_a, b > a);
        assert_eq!(gstr_b < gstr_a, b < a);
        assert_eq!(gstr_b == gstr_a, b == a);
        assert_eq!(gstr_b >= gstr_a, b >= a);
        assert_eq!(gstr_b <= gstr_a, b <= a);
        assert_eq!(gstr_b.cmp(&gstr_a), b.cmp(a));
        assert_eq!(gstr_b.partial_cmp(&gstr_a), b.partial_cmp(a));

        assert_eq!(gstr_a > b, a > gstr_b);
        assert_eq!(gstr_a < b, a < gstr_b);
        assert_eq!(gstr_a == b, a == gstr_b);
        assert_eq!(gstr_a >= b, a >= gstr_b);
        assert_eq!(gstr_a <= b, a <= gstr_b);
        assert_eq!(gstr_a.partial_cmp(b), a.partial_cmp(&gstr_b));

        assert_eq!(gstr_b > a, b > gstr_a);
        assert_eq!(gstr_b < a, b < gstr_a);
        assert_eq!(gstr_b == a, b == gstr_a);
        assert_eq!(gstr_b >= a, b >= gstr_a);
        assert_eq!(gstr_b <= a, b <= gstr_a);
        assert_eq!(gstr_b.partial_cmp(a), b.partial_cmp(&gstr_a));
    }

    #[test]
    fn gstr_new() {
        test_literal_strings(test_gstr_new);
    }

    #[test]
    fn gstr_const_new() {
        test_literal_strings(test_gstr_const_new);
    }

    #[test]
    fn gstr_from_string() {
        test_literal_strings(test_gstr_from_string);
    }

    #[test]
    fn gstr_eq_cmp() {
        test_gstr_eq_cmp("", "");
        test_gstr_eq_cmp("", "a");
        test_gstr_eq_cmp("", "abcdefghijklm");
        test_gstr_eq_cmp("ab", "ab");
        test_gstr_eq_cmp("ab", "ac");
        test_gstr_eq_cmp("ab", "bd");
        test_gstr_eq_cmp("ab", "abc");
        test_gstr_eq_cmp("ab", "abcdefghijklm");
        test_gstr_eq_cmp("ab", "hello, 🦀 and 🌎!");
        test_gstr_eq_cmp("abcdefghijklm", "abcdefghijklm");
        test_gstr_eq_cmp("abcdefghijklm", "abcdefghijkln");
        test_gstr_eq_cmp("abcdefghijklm", "nopqrstuvwxyz");
        test_gstr_eq_cmp("abcdefghijklm", "abcdefghijklmn");
        test_gstr_eq_cmp("abcdefghijklm", "hello, 🦀 and 🌎!");
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    proptest! {
        #[test]
        fn prop_gstr_new(string: String) {
            test_gstr_new(&string);
        }
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    proptest! {
        #[test]
        fn prop_gstr_const_new(string: String) {
            let len = string.len();
            let capacity = string.capacity();
            let string = string.leak();
            let ptr = string.as_mut_ptr();

            test_gstr_const_new(string);

            // To avoid memory leaks.
            // SAFETY: `GStr` doesn't drop its inner string buffer if it's created by `const_new`.
            unsafe {
                drop(String::from_raw_parts(ptr, len, capacity));
            }
        }
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    proptest! {
        #[test]
        fn prop_gstr_from_string(string: String) {
            test_gstr_from_string(&string);
        }
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    proptest! {
        #[test]
        fn prop_gstr_eq_cmp(a: String, b: String) {
            test_gstr_eq_cmp(&a, &b);
        }
    }
}
