use core::{
    borrow::Borrow,
    cmp::Ordering,
    error::Error,
    fmt,
    hash::{Hash, Hasher},
    mem::{self, align_of, size_of, ManuallyDrop},
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
    #[must_use]
    pub fn error_kind(&self) -> ErrorKind {
        self.kind
    }

    /// Returns the source that failed to be converted to a [`GStr`].
    #[inline]
    #[must_use]
    pub fn source(&self) -> &S {
        &self.source
    }

    /// Consumes the error and returns the source that failed to be converted to a [`GStr`].
    #[inline]
    #[must_use]
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
    /// Returns the source's string slice.
    #[inline]
    #[must_use]
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
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RawBuffer {
    /// A pointer points to a static string buffer.
    Static(NonNull<u8>),
    /// A pointer points to a heap allocated string buffer which isn't empty.
    Heap(NonNull<u8>),
}

impl RawBuffer {
    /// Returns the raw pointer of this raw buffer.
    ///
    /// The returned pointer will be pointing to the first byte of the string buffer if it isn't
    /// empty.
    ///
    /// The caller must ensure that the returned pointer is never written to.
    #[inline]
    #[must_use]
    pub const fn as_ptr(&self) -> *const u8 {
        match self {
            Self::Static(ptr) | Self::Heap(ptr) => ptr.as_ptr(),
        }
    }
}

#[cfg(target_pointer_width = "64")]
/// The prefix buffer and length of a [`GStr`].
///
/// The most significant 32 bits are used to store the prefix buffer. On little endian platforms,
/// the prefix buffer's order is reversed for comparison optimization.
///
/// The least significant 31 bits are used to store the length of the string buffer.
///
/// The remained one bit is the static flag. If the static flag is 1, then the string buffer is
/// static.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct PrefixAndLength(u64);

#[cfg(target_pointer_width = "64")]
impl PrefixAndLength {
    /// The length of the prefix buffer (`4`).
    const PREFIX_LENGTH: usize = size_of::<u32>();

    /// The half length of [`PrefixAndLength`] in bits (`32`).
    const HALF_BITS: u8 = u32::BITS as _;

    /// A mask that isolates the prefix part of the value (`0xFFFF_FFFF_0000_0000`).
    const PREFIX_MASK: u64 = (u32::MAX as u64) << Self::HALF_BITS;

    /// The number of bits used to represent the length (`31`).
    const LENGTH_BITS: u8 = Self::HALF_BITS - 1;

    /// A mask intended to set the static flag (`0x8000_0000`).
    const STATIC_MASK: u64 = 1 << Self::LENGTH_BITS;

    /// A mask that isolates the length part of the value (`0x7FFF_FFFF`).
    const LENGTH_MASK: u64 = Self::STATIC_MASK - 1;

    /// The maximum length (`0x7FFF_FFFF`).
    const MAX_LENGTH: usize = Self::LENGTH_MASK as _;

    /// A mask for [`PrefixAndLength`] to set the static flag as 0 (`0xFFFF_FFFF_7FFF_FFFF`).
    const LEN_PREFIX_MASK: u64 = !Self::STATIC_MASK;

    /// Creates a new [`PrefixAndLength`] for non-static strings.
    ///
    /// # Safety
    ///
    /// - `len` must not be greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - The returned [`PrefixAndLength`] is for non-static strings.
    #[inline]
    const unsafe fn new_unchecked(prefix: [u8; Self::PREFIX_LENGTH], len: usize) -> Self {
        debug_assert!(len <= Self::MAX_LENGTH);

        // Reversed the order of the prefix buffer on little endian platforms to optimize
        // comparison.
        #[cfg(target_endian = "little")]
        let array = [len as u32, u32::from_be_bytes(prefix)];

        #[cfg(target_endian = "big")]
        let array = [u32::from_be_bytes(prefix), len as u32];

        // SAFETY: `[u32; 2]` is safe to be represented as `u64`.
        unsafe { Self(mem::transmute::<[u32; 2], u64>(array)) }
    }

    /// Creates a new [`Length`] for static strings.
    ///
    /// # Safety
    ///
    /// - `len` must not be greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - The returned [`Length`] is for static strings.
    #[inline]
    const unsafe fn new_static_unchecked(prefix: [u8; Self::PREFIX_LENGTH], len: usize) -> Self {
        // SAFETY: `len` is guaranteed to not be greate than `MAX_LENGTH`.
        let prefix_and_len = unsafe { Self::new_unchecked(prefix, len) };

        Self(prefix_and_len.0 | Self::STATIC_MASK)
    }

    /// Returns the prefix buffer.
    #[inline]
    const fn as_prefix(self) -> [u8; Self::PREFIX_LENGTH] {
        ((self.0 >> Self::HALF_BITS) as u32).to_be_bytes()
    }

    /// Returns the actual length.
    #[inline]
    const fn as_len(self) -> usize {
        (self.0 & Self::LENGTH_MASK) as _
    }

    /// Returns the prefix buffer (its order is reversed on little endian platforms) and the actual
    /// length as a [`u64`].
    #[inline]
    const fn as_prefix_len_u64(self) -> u64 {
        self.0 & Self::LEN_PREFIX_MASK
    }

    /// Indicates whether the string buffer is static.
    #[inline]
    const fn is_static(self) -> bool {
        !self.is_heap()
    }

    /// Indicates whether the string buffer is heap allocated.
    #[inline]
    const fn is_heap(self) -> bool {
        (self.0 as u32) <= Self::LENGTH_MASK as u32
    }

    /// Compares the prefix buffers of two [`PrefixAndLength`]s.
    #[inline]
    fn prefix_cmp(self, other: Self) -> Ordering {
        (self.0 & Self::PREFIX_MASK).cmp(&(other.0 & Self::PREFIX_MASK))
    }

    /// Returns whether the prefix buffers and the lengths of two [`PrefixAndLength`]s are equal.
    #[inline]
    const fn prefix_len_eq(self, other: Self) -> bool {
        self.as_prefix_len_u64() == other.as_prefix_len_u64()
    }
}

#[cfg(target_pointer_width = "32")]
/// The prefix buffer and length of a [`GStr`].
///
/// On little endian platforms, the prefix buffer's order is reversed for comparison optimization.
///
/// The most significant bit in `len` is the static flag. If the static flag is 1, then the string
/// buffer is static.
#[derive(Clone, Copy, Debug)]
struct PrefixAndLength {
    /// The length of the string buffer.
    len: u32,
    /// The prefix buffer represented as an [`u32`].
    prefix: u32,
}

#[cfg(target_pointer_width = "32")]
impl PrefixAndLength {
    /// The length of the prefix buffer (`4`).
    const PREFIX_LENGTH: usize = size_of::<u32>();

    /// The number of bits used to represent the length (`31`).
    const LENGTH_BITS: u8 = u32::BITS as u8 - 1;

    /// A mask intended to set the static flag (`0x8000_0000`).
    const STATIC_MASK: u32 = 1 << Self::LENGTH_BITS;

    /// A mask that isolates the length part of the value (`0x7FFF_FFFF`).
    const LENGTH_MASK: u32 = Self::STATIC_MASK - 1;

    /// The maximum length (`0x7FFF_FFFF`).
    const MAX_LENGTH: usize = Self::LENGTH_MASK as _;

    /// Creates a new [`PrefixAndLength`] for non-static strings.
    ///
    /// # Safety
    ///
    /// - `len` must not be greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - The returned [`PrefixAndLength`] is for non-static strings.
    #[inline]
    const unsafe fn new_unchecked(prefix: [u8; Self::PREFIX_LENGTH], len: usize) -> Self {
        debug_assert!(len <= Self::MAX_LENGTH);

        Self {
            len: len as _,
            prefix: u32::from_be_bytes(prefix),
        }
    }

    /// Creates a new [`Length`] for static strings.
    ///
    /// # Safety
    ///
    /// - `len` must not be greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - The returned [`Length`] is for static strings.
    #[inline]
    const unsafe fn new_static_unchecked(prefix: [u8; Self::PREFIX_LENGTH], len: usize) -> Self {
        debug_assert!(len <= Self::MAX_LENGTH);

        Self {
            len: len as u32 | Self::STATIC_MASK,
            prefix: u32::from_be_bytes(prefix),
        }
    }

    /// Returns the prefix buffer.
    #[inline]
    const fn as_prefix(self) -> [u8; Self::PREFIX_LENGTH] {
        self.prefix.to_be_bytes()
    }

    /// Returns the actual length.
    #[inline]
    const fn as_len(self) -> usize {
        (self.len & Self::LENGTH_MASK) as _
    }

    /// Indicates whether the string buffer is static.
    #[inline]
    const fn is_static(self) -> bool {
        !self.is_heap()
    }

    /// Indicates whether the string buffer is heap allocated.
    #[inline]
    const fn is_heap(self) -> bool {
        self.len <= Self::LENGTH_MASK
    }

    /// Returns whether the prefix buffers of two [`PrefixAndLength`]s is equal.
    #[inline]
    const fn prefix_eq(self, other: Self) -> bool {
        self.prefix == other.prefix
    }

    /// Compares the prefix buffers of two [`PrefixAndLength`]s.
    #[inline]
    fn prefix_cmp(self, other: Self) -> Ordering {
        self.prefix.cmp(&other.prefix)
    }

    /// Returns whether the prefix buffers and the lengths of two [`PrefixAndLength`]s are equal.
    #[inline]
    const fn prefix_len_eq(self, other: Self) -> bool {
        self.as_len() == other.as_len() && self.prefix_eq(other)
    }
}

/// An immutable string implementation optimized for small strings and comparison.
// NOTE: If the string buffer is heap allocated, it can't be empty.
pub struct GStr {
    /// The pointer which points to the string buffer.
    ptr: NonNull<u8>,
    /// The prefix buffer and the length of the string buffer.
    prefix_and_len: PrefixAndLength,
}

impl GStr {
    /// The maximum length of [`GStr`].
    pub const MAX_LENGTH: usize = PrefixAndLength::MAX_LENGTH;

    /// The empty string of [`GStr`].
    pub const EMPTY: Self = Self::from_static("");

    /// The UTF-8 character used to replace invalid UTF-8 sequences.
    const UTF8_REPLACEMENT: &'static str = "\u{FFFD}";

    /// Creates a [`GStr`] from a string.
    ///
    /// The string is cloned if it isn't empty, otherwise [`GStr::EMPTY`] is returned.
    ///
    /// # Errors
    ///
    /// Returns an [`Err`] if the string's length is greater than [`MAX_LENGTH`](Self::MAX_LENGTH)
    /// or allocation failure occurs.
    ///
    /// # Example
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string = GStr::try_new("Hello, World!").unwrap();
    /// assert_eq!(string, "Hello, World!");
    /// ```
    pub fn try_new<S: AsRef<str>>(string: S) -> Result<Self, ToGStrError<S>> {
        let s = string.as_ref();
        let len = s.len();

        if len == 0 {
            Ok(empty_gstr())
        } else if len <= Self::MAX_LENGTH {
            // SAFETY:
            // - The layout of `s` is valid.
            // - `len` is greater than 0, so the layout's size isn't 0.
            let ptr = unsafe { alloc::alloc::alloc(Layout::array::<u8>(len).unwrap_unchecked()) };

            if ptr.is_null() {
                allocation_failure(string)
            } else {
                // SAFETY: `s.as_ptr()` is valid for reads of `len` bytes and `ptr` is valid for
                //         writes of `len` bytes`.
                unsafe {
                    ptr::copy_nonoverlapping::<u8>(s.as_ptr(), ptr, len);
                }

                Ok(Self {
                    // SAFETY: `ptr` isn't null.
                    ptr: unsafe { NonNull::new_unchecked(ptr) },
                    // SAFETY: `len` isn't greater than `Length::MAX_LENGTH`.
                    prefix_and_len: unsafe {
                        PrefixAndLength::new_unchecked(copy_prefix(s.as_bytes()), len)
                    },
                })
            }
        } else {
            length_overflow(string, len)
        }
    }

    /// Creates a [`GStr`] from a string.
    ///
    /// The string is cloned if it isn't empty, otherwise [`GStr::EMPTY`] is returned.
    ///
    /// # Panics
    ///
    /// - Panics if the length of `string` is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to allocate heap memory.
    ///
    /// # Example
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string = GStr::new("Hello, World!");
    /// assert_eq!(string, "Hello, World!");
    /// ```
    #[must_use]
    pub fn new<S: AsRef<str>>(string: S) -> Self {
        match Self::try_new(string) {
            Ok(s) => s,
            Err(e) => match e.kind {
                ErrorKind::LengthOverflow(_) => panic!("{}", e),
                ErrorKind::AllocationFailure => handle_alloc_error(e.as_str()),
                // SAFETY: `GStr::try_new` doesn't return other errors.
                _ => unsafe { core::hint::unreachable_unchecked() },
            },
        }
    }

    /// Creates a [`GStr`] from a static string. It can be used in const context.
    ///
    /// If the string buffer is allocated from the heap memory, when the returned [`GStr`] is
    /// dropped, the string buffer's memory will be leaked.
    ///
    /// # Panics
    ///
    /// Panics if the length of `s` is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    ///
    /// # Example
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string = const { GStr::from_static("Hello, World!")};
    /// assert_eq!(string, "Hello, World!");
    /// ```
    #[inline]
    #[must_use]
    pub const fn from_static(string: &'static str) -> Self {
        if string.len() <= Self::MAX_LENGTH {
            Self {
                // SAFETY: The pointer which points to `string`'s buffer is non-null.
                ptr: unsafe { NonNull::new_unchecked(string.as_ptr().cast_mut()) },
                // SAFETY: `string.len()` isn't greater than `Length::MAX_LENGTH`.
                prefix_and_len: unsafe {
                    PrefixAndLength::new_static_unchecked(
                        copy_prefix(string.as_bytes()),
                        string.len(),
                    )
                },
            }
        } else {
            panic!("the string's length should not be greater than `GStr`'s max length")
        }
    }

    /// Creates a [`GStr`] from a [`String`].
    ///
    /// This doesn't clone the string but shrinks it's capacity to match its length. If the string's
    /// capacity is equal to its length, no reallocation occurs.
    ///
    /// If the string is empty, [`GStr::EMPTY`] is returned.
    ///
    /// # Errors
    ///
    /// Returns an [`Err`] if the string's length is greater than [`MAX_LENGTH`](Self::MAX_LENGTH)
    /// or shrinking the string's capacity fails.
    ///
    /// # Example
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string = String::from("Hello, World!");
    /// let string_ptr = string.as_ptr();
    /// let gstr = GStr::try_from_string(string).unwrap();
    /// assert_eq!(gstr, "Hello, World!");
    /// assert_eq!(string_ptr, gstr.as_ptr());
    /// ```
    #[inline]
    pub fn try_from_string(string: String) -> Result<Self, ToGStrError<String>> {
        let len = string.len();

        if len == 0 {
            Ok(empty_gstr())
        } else if len <= Self::MAX_LENGTH {
            // SAFETY: `string` isn't empty.
            match unsafe { shrink_and_leak_string(string) } {
                Ok(s) => {
                    // SAFETY: The length of `s` returned from `shrink_and_leak_string` is equal to
                    //         the length of `string`. This assertion is used to avoid some extra
                    //         branches.
                    unsafe {
                        core::hint::assert_unchecked(s.len() == len);
                    }

                    Ok(Self {
                        // SAFETY: The pointer which points to the string buffer is non-null.
                        ptr: unsafe { NonNull::new_unchecked(s.as_mut_ptr()) },
                        // SAFETY: `len` isn't greater than `Length::MAX_LENGTH`.
                        prefix_and_len: unsafe {
                            PrefixAndLength::new_unchecked(copy_prefix(s.as_bytes()), len)
                        },
                    })
                }
                Err(s) => allocation_failure(s),
            }
        } else {
            length_overflow(string, len)
        }
    }

    /// Creates a [`GStr`] from a [`String`].
    ///
    /// This doesn't clone the string but shrinks it's capacity to match its length. If the string's
    /// capacity is equal to its length, no reallocation occurs.
    ///
    /// If the string is empty, [`GStr::EMPTY`] is returned.
    ///
    /// # Panics
    ///
    /// - Panics if the length of `string` is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to shrink `string`'s capacity.
    ///
    /// # Example
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string = String::from("Hello, World!");
    /// let string_ptr = string.as_ptr();
    /// let gstr = GStr::from_string(string);
    /// assert_eq!(gstr, "Hello, World!");
    /// assert_eq!(string_ptr, gstr.as_ptr());
    /// ```
    #[inline]
    #[must_use]
    pub fn from_string(string: String) -> Self {
        match Self::try_from_string(string) {
            Ok(s) => s,
            Err(e) => match e.kind {
                ErrorKind::LengthOverflow(_) => panic!("{}", e),
                ErrorKind::AllocationFailure => handle_alloc_error(e),
                // SAFETY: `GStr::try_from_string` doesn't return other errors.
                _ => unsafe { core::hint::unreachable_unchecked() },
            },
        }
    }

    /// Creates a [`GStr`] from a raw buffer and its length.
    ///
    /// If the raw buffer is static, when the returned [`GStr`] is dropped, the buffer's memory
    /// won't be deallocated.
    ///
    /// # Safety
    ///
    /// - If the raw buffer is heap allocated, its memory needs to have been previously allocated
    ///   by the global allocator, with a non-zero size of exactly `len` and an alignment of exactly
    ///   one.
    /// - If the raw buffer is static, its first `len` bytes must be valid.
    /// - `len` must be less than or equal to [`MAX_LENGTH`](Self::MAX_LENGTH). If the raw buffer
    ///   is heap allocated, `len` must be greater than zero.
    /// - The first `len` bytes at `buf` must be valid UTF-8.
    /// - The ownership of `buf` is effectively transferred to the return [`GStr`]. Ensure that
    ///   nothing else uses the buffer pointer after calling this function.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string = GStr::new("Hello, World!");
    /// let (buf, len) = string.into_raw_parts();
    /// let string = unsafe { GStr::from_raw_parts(buf, len) };
    /// assert_eq!(string, "Hello, World!");
    ///
    /// let string = GStr::from_static("Hello, Rust!");
    /// let (buf, len) = string.into_raw_parts();
    /// let string = unsafe { GStr::from_raw_parts(buf, len) };
    /// assert_eq!(string, "Hello, Rust!");
    /// ```
    #[inline]
    #[must_use]
    pub const unsafe fn from_raw_parts(buf: RawBuffer, len: usize) -> Self {
        debug_assert!(len <= Self::MAX_LENGTH);

        // SAFETY:
        // - `buf.as_ptr()` is valid for reads for `len` bytes and it's properly aligned for `u8`.
        // - `buf.as_ptr()` points to a valid UTF-8 string whose length in bytes is `len`.
        let bytes = unsafe { slice::from_raw_parts(buf.as_ptr(), len) };

        match buf {
            RawBuffer::Static(ptr) => Self {
                ptr,
                // SAFETY: `len` isn't greater than `Length::MAX_LENGTH`.
                prefix_and_len: unsafe {
                    PrefixAndLength::new_static_unchecked(copy_prefix(bytes), len)
                },
            },
            RawBuffer::Heap(ptr) => {
                // SAFETY: The raw buffer is heap allocated, so `len` is greater than 0. This
                //         assertion can remove a branch in `copy_prefix`.
                unsafe {
                    core::hint::assert_unchecked(len > 0);
                }

                Self {
                    ptr,
                    // SAFETY: `len` isn't greater than `Length::MAX_LENGTH`.
                    prefix_and_len: unsafe {
                        PrefixAndLength::new_unchecked(copy_prefix(bytes), len)
                    },
                }
            }
        }
    }

    /// Converts a vector of bytes to a [`GStr`].
    ///
    /// # Errors
    ///
    /// - Returns an [`Err`] if the slice is not a valid UTF-8 sequence.
    /// - Returns an [`Err`] if the slice's length is greater than [`MAX_LENGTH`](Self::MAX_LENGTH)
    ///   or shrinking the vector's capacity fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let sparkle_heart = vec![240, 159, 146, 150];
    /// let string = GStr::from_utf8(sparkle_heart).unwrap();
    /// assert_eq!(string, "💖");
    ///
    /// let invalid = vec![0, 159, 146, 150];
    /// assert!(GStr::from_utf8(invalid).is_err());
    /// ```
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

    /// Converts a vector of bytes to a [`GStr`] without checking that the slice is a valid UTF-8
    /// sequence.
    ///
    /// # Safety
    ///
    /// `bytes` must be a valid UTF-8 sequence.
    ///
    /// # Panics
    ///
    /// - Panics if the length of `bytes` is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to shrink the capacity of `bytes`.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let sparkle_heart = vec![240, 159, 146, 150];
    /// let string = unsafe { GStr::from_utf8_unchecked(sparkle_heart) };
    /// assert_eq!(string, "💖");
    /// ```
    #[inline]
    #[must_use]
    pub unsafe fn from_utf8_unchecked(bytes: Vec<u8>) -> Self {
        // SAFETY: `bytes` is guranteed to be a valid UTF-8 sequence.
        unsafe { Self::from_string(String::from_utf8_unchecked(bytes)) }
    }

    /// Converts a slice of bytes to a [`GStr`], including invalid characters.
    ///
    /// This function will replace any invalid UTF-8 sequences with
    /// [`U+FFFD REPLACEMENT CHARACTER`](core::char::REPLACEMENT_CHARACTER) , which looks like �.
    ///
    /// # Panics
    ///
    /// - Panics if the length in bytes of the UTF-8 sequence converted is greater than
    ///   [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to allocate memory or shrink the capacity of `bytes`.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let sparkle_heart = vec![240, 159, 146, 150];
    /// let string = GStr::from_utf8_lossy(sparkle_heart);
    /// assert_eq!(string, "💖");
    ///
    /// let input = Vec::from(b"Hello \xF0\x90\x80World");
    /// let output = GStr::from_utf8_lossy(input);
    /// assert_eq!(output, "Hello �World");
    /// ```
    #[must_use]
    pub fn from_utf8_lossy(bytes: Vec<u8>) -> Self {
        let mut iter = bytes.utf8_chunks();

        let first_valid = if let Some(chunk) = iter.next() {
            let valid = chunk.valid();

            if chunk.invalid().is_empty() {
                debug_assert_eq!(valid.len(), bytes.len());

                // SAFETY: The invalid UTF-8 sequence is empty, so `bytes` is a valid UTF-8
                //         sequence.
                return unsafe { Self::from_utf8_unchecked(bytes) };
            }

            valid
        } else {
            return empty_gstr();
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

    /// Decode a UTF-16–encoded slice into a [`GStr`].
    ///
    /// # Errors
    ///
    /// - Returns an [`Err`] if the slice contains any invalid UTF-16 sequences.
    /// - Returns an [`Err`] if length in bytes of the UTF-8 sequence converted is greater than
    ///   [`MAX_LENGTH`](Self::MAX_LENGTH) or shrinking the intermediate string's capacity fails.
    ///
    /// # Panics
    ///
    /// Panics if fails to allocate memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075, 0x0073, 0x0069, 0x0063];
    /// assert_eq!(GStr::from_utf16(v).unwrap(), "𝄞music");
    ///
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,0xD800, 0x0069, 0x0063];
    /// assert!(GStr::from_utf16(v).is_err())
    /// ```
    pub fn from_utf16<B: AsRef<[u16]>>(bytes: B) -> Result<Self, ToGStrError<B>> {
        let b = bytes.as_ref();

        match String::from_utf16(b) {
            Ok(s) => GStr::try_from_string(s).map_err_source(|_| bytes),
            Err(_) => Err(ToGStrError::new_invalid_utf16(bytes)),
        }
    }

    /// Decode a UTF-16–encoded slice into a [`GStr`], replacing invalid data with
    /// [`U+FFFD REPLACEMENT CHARACTER`](core::char::REPLACEMENT_CHARACTER) , which looks like �.
    ///
    /// # Panics
    ///
    /// - Panics if the length in bytes of the UTF-8 sequence converted from the UTF-16 sequence
    ///   is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to allocate memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075, 0x0073, 0x0069, 0x0063];
    /// assert_eq!(GStr::from_utf16_lossy(v), "𝄞music");
    ///
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075, 0x0073, 0xDD1E, 0x0069, 0x0063, 0xD834];
    /// assert_eq!(GStr::from_utf16_lossy(v), "𝄞mus\u{FFFD}ic\u{FFFD}")
    /// ```
    #[must_use]
    pub fn from_utf16_lossy<B: AsRef<[u16]>>(bytes: B) -> Self {
        Self::from_string(String::from_utf16_lossy(bytes.as_ref()))
    }

    /// Decode a UTF-16-little-endian–encoded slice into a [`GStr`]
    ///
    /// # Errors
    ///
    /// Returns an [`Err`] if the slice contains any invalid data or the length of the slice is odd.
    ///
    /// # Panics
    ///
    /// - Panics if the length in bytes of the UTF-8 sequence converted from the UTF-16 sequence
    ///   is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to allocate memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let v = &[0x34, 0xD8, 0x1E, 0xDD, 0x6d, 0x00, 0x75, 0x00,
    ///           0x73, 0x00, 0x69, 0x00, 0x63, 0x00];
    /// assert_eq!(GStr::from_utf16le(v).unwrap(), "𝄞music");
    ///
    /// let v = &[0x34, 0xD8, 0x1E, 0xDD, 0x6d, 0x00, 0x75, 0x00,
    ///           0x00, 0xD8, 0x69, 0x00, 0x63, 0x00];
    /// assert!(GStr::from_utf16le(v).is_err())
    /// ```
    pub fn from_utf16le<B: AsRef<[u8]>>(bytes: B) -> Result<Self, ToGStrError<B>> {
        let b = bytes.as_ref();

        if b.len() % 2 != 0 {
            return Err(ToGStrError::new_from_utf16_odd_length(bytes));
        }

        // SAFETY: Two `u8`s can be transmuted to a `u16`.
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
                // SAFETY: a byte slice whose length is 2 can be converted to a `[u8; 2]`;
                let iter = b.chunks_exact(2).map(|s| unsafe {
                    u16::from_le_bytes(<[u8; 2]>::try_from(s).unwrap_unchecked())
                });

                char::decode_utf16(iter)
                    .collect::<Result<_, _>>()
                    .map_err(|_| ToGStrError::new_invalid_utf16(bytes))
            }
        }
    }

    /// Decode a UTF-16-little-endian–encoded slice into a [`GStr`], replacing invalid data with
    /// [`U+FFFD REPLACEMENT CHARACTER`](core::char::REPLACEMENT_CHARACTER) , which looks like �.
    ///
    /// # Panics
    ///
    /// - Panics if the length in bytes of the UTF-8 sequence converted from the UTF-16 sequence
    ///   is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to allocate memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let v = &[0x34, 0xD8, 0x1E, 0xDD, 0x6d, 0x00, 0x75, 0x00,
    ///           0x73, 0x00, 0x69, 0x00, 0x63, 0x00];
    /// assert_eq!(GStr::from_utf16le_lossy(v), "𝄞music");
    ///
    /// let v = &[0x34, 0xD8, 0x1E, 0xDD, 0x6d, 0x00, 0x75, 0x00,
    ///           0x73, 0x00, 0x1E, 0xDD, 0x69, 0x00, 0x63, 0x00,
    ///           0x34, 0xD8];
    /// assert_eq!(GStr::from_utf16le_lossy(v), "𝄞mus\u{FFFD}ic\u{FFFD}")
    /// ```
    #[must_use]
    pub fn from_utf16le_lossy<B: AsRef<[u8]>>(bytes: B) -> Self {
        let b = bytes.as_ref();

        // SAFETY: Two `u8`s can be transmuted to a `u16`.
        match (cfg!(target_endian = "little"), unsafe {
            b.align_to::<u16>()
        }) {
            (true, ([], v, [])) => Self::from_utf16_lossy(v),
            (true, ([], v, [_])) => {
                Self::from_string(String::from_utf16_lossy(v) + Self::UTF8_REPLACEMENT)
            }
            _ => {
                let mut iter = b.chunks_exact(2);
                // SAFETY: a byte slice whose length is 2 can be converted to a `[u8; 2]`;
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

    /// Decode a UTF-16-big-endian–encoded slice into a [`GStr`]
    ///
    /// # Errors
    ///
    /// Returns an [`Err`] if the slice contains any invalid data or the length of the slice is odd.
    ///
    /// # Panics
    ///
    /// - Panics if the length in bytes of the UTF-8 sequence converted from the UTF-16 sequence
    ///   is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to allocate memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let v = &[0xD8, 0x34, 0xDD, 0x1E, 0x00, 0x6d, 0x00, 0x75,
    ///           0x00, 0x73, 0x00, 0x69, 0x00, 0x63];
    /// assert_eq!(GStr::from_utf16be(v).unwrap(), "𝄞music");
    ///
    /// let v = &[0xD8, 0x34, 0xDD, 0x1E, 0x00, 0x6d, 0x00, 0x75,
    ///           0xD8, 0x00, 0x00, 0x69, 0x00, 0x63];
    /// assert!(GStr::from_utf16be(v).is_err())
    /// ```
    pub fn from_utf16be<B: AsRef<[u8]>>(bytes: B) -> Result<Self, ToGStrError<B>> {
        let b = bytes.as_ref();

        if b.len() % 2 != 0 {
            return Err(ToGStrError::new_from_utf16_odd_length(bytes));
        }

        // SAFETY: Two `u8`s can be transmuted to a `u16`.
        match (cfg!(target_endian = "big"), unsafe { b.align_to::<u16>() }) {
            (true, ([], v, [])) => match Self::from_utf16(v) {
                Ok(s) => Ok(s),
                Err(e) => Err(ToGStrError {
                    kind: e.kind,
                    source: bytes,
                }),
            },
            _ => {
                // SAFETY: a byte slice whose length is 2 can be converted to a `[u8; 2]`;
                let iter = b.chunks_exact(2).map(|s| unsafe {
                    u16::from_be_bytes(<[u8; 2]>::try_from(s).unwrap_unchecked())
                });

                char::decode_utf16(iter)
                    .collect::<Result<_, _>>()
                    .map_err(|_| ToGStrError::new_invalid_utf16(bytes))
            }
        }
    }

    /// Decode a UTF-16-little-endian–encoded slice into a [`GStr`], replacing invalid data with
    /// [`U+FFFD REPLACEMENT CHARACTER`](core::char::REPLACEMENT_CHARACTER) , which looks like �.
    ///
    /// # Panics
    ///
    /// - Panics if the length in bytes of the UTF-8 sequence converted from the UTF-16 sequence
    ///   is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to allocate memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let v = &[0xD8, 0x34, 0xDD, 0x1E, 0x00, 0x6d, 0x00, 0x75,
    ///           0x00, 0x73, 0x00, 0x69, 0x00, 0x63];
    /// assert_eq!(GStr::from_utf16be_lossy(v), "𝄞music");
    ///
    /// let v = &[0xD8, 0x34, 0xDD, 0x1E, 0x00, 0x6d, 0x00, 0x75,
    ///           0x00, 0x73, 0xDD, 0x1E, 0x00, 0x69, 0x00, 0x63,
    ///           0xD8, 0x34];
    /// assert_eq!(GStr::from_utf16be_lossy(v), "𝄞mus\u{FFFD}ic\u{FFFD}")
    /// ```
    #[must_use]
    pub fn from_utf16be_lossy<B: AsRef<[u8]>>(bytes: B) -> Self {
        let b = bytes.as_ref();

        // SAFETY: Two `u8`s can be transmuted to a `u16`.
        match (cfg!(target_endian = "big"), unsafe { b.align_to::<u16>() }) {
            (true, ([], v, [])) => Self::from_utf16_lossy(v),
            (true, ([], v, [_])) => {
                Self::from_string(String::from_utf16_lossy(v) + Self::UTF8_REPLACEMENT)
            }
            _ => {
                let mut iter = b.chunks_exact(2);
                // SAFETY: a byte slice whose length is 2 can be converted to a `[u8; 2]`;
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

    /// Returns the prefix buffer of this [`GStr`].
    #[inline]
    const fn prefix(&self) -> [u8; PrefixAndLength::PREFIX_LENGTH] {
        self.prefix_and_len.as_prefix()
    }

    /// Returns the length of this [`GStr`], in bytes, not chars or graphemes.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string = GStr::new("foo");
    /// assert_eq!(string.len(), 3);
    ///
    /// let fancy_f = GStr::new("ƒoo");
    /// assert_eq!(fancy_f.len(), 4);
    /// assert_eq!(fancy_f.chars().count(), 3);
    /// ```
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.prefix_and_len.as_len()
    }

    /// Returns `true` if this string's length is zero, and `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// assert!(GStr::new("").is_empty());
    /// assert!(!GStr::new("foo").is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns whether the string buffer of this [`GStr`] is static.
    ///
    /// If a [`GStr`] is empty, it's string buffer must be static.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// assert!(GStr::from_static("Hello, World!").is_static());
    /// assert!(GStr::new("").is_static());
    /// assert!(GStr::from_string(String::new()).is_static());
    /// assert!(!GStr::new("Hello, World!").is_static());
    /// assert!(!GStr::from_string(String::from("Hello, World!")).is_static());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_static(&self) -> bool {
        self.prefix_and_len.is_static()
    }

    /// Returns whether the string buffer of this [`GStr`] is heap-allocated.
    ///
    /// If a [`GStr`] is empty, it's string buffer can't be heap-allocated.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// assert!(GStr::new("Hello, World!").is_heap());
    /// assert!(GStr::from_string(String::from("Hello, World!")).is_heap());
    /// assert!(!GStr::new("").is_heap());
    /// assert!(!GStr::from_string(String::new()).is_heap());
    /// assert!(!GStr::from_static("Hello, World!").is_heap());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_heap(&self) -> bool {
        self.prefix_and_len.is_heap()
    }

    /// Returns a raw pointer of the string buffer. If the string buffer isn't empty, the raw
    /// pointer points to the first byte of the string buffer.
    ///
    /// The returned raw pointer is never null.
    ///
    /// The caller must ensure that the returned pointer is never written to.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string = GStr::new("Hello, World!");
    /// assert!(!string.as_ptr().is_null());
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_ptr(&self) -> *const u8 {
        self.ptr.as_ptr()
    }

    /// Return a mutable raw pointer of the string buffer.
    #[inline]
    fn as_mut_ptr(&mut self) -> *mut u8 {
        self.ptr.as_ptr()
    }

    /// Returns a byte slice of this [`GStr`]'s contents.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string = GStr::new("hello");
    /// assert_eq!(string.as_bytes(), &[104, 101, 108, 108, 111]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8] {
        // SAFETY:
        // - `self.as_ptr()` is valid for reads of `self.len()` bytes and is properly aligned as
        //   `u8`.
        // - The first `self.len()` bytes of the slice are all properly initialized.
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    /// Returns a string slice of this [`GStr`].
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string = GStr::new("Hello, World!");
    /// assert_eq!(string.as_str(), "Hello, World!");
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_str(&self) -> &str {
        // SAFETY: The byte slice of a `GStr` is always a valid UTF-8 sequence.
        unsafe { core::str::from_utf8_unchecked(self.as_bytes()) }
    }

    /// Returns a static string slice of this [`GStr`], if it is static.
    ///
    /// Returns `None` if the string buffer is heap-allocated.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string = GStr::from_static("Hello, World!");
    /// assert_eq!(string.as_static_str(), Some("Hello, World!"));
    ///
    /// let string = GStr::new("Hello, World!");
    /// assert_eq!(string.as_static_str(), None);
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_static_str(&self) -> Option<&'static str> {
        if self.is_static() {
            // SAFETY: The byte slice of a `GStr` is always a valid UTF-8 sequence.
            unsafe {
                Some(core::str::from_utf8_unchecked(slice::from_raw_parts(
                    self.as_ptr(),
                    self.len(),
                )))
            }
        } else {
            None
        }
    }

    /// Converts this [`GStr`] into a [`String`].
    ///
    /// If the string buffer is heap-allocated, no allocation is performed. Otherwise the string
    /// buffer is cloned into a new [`String`].
    ///
    /// # Errors
    ///
    /// Returns an [`Err`] containing this [`GStr`] if fails to allocate memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string = String::from("Hello, World!");
    /// let string_ptr = string.as_ptr();
    /// let gstr = GStr::from_string(string);
    /// let string = gstr.try_into_string().unwrap();
    /// assert_eq!(string, "Hello, World!");
    /// assert_eq!(string_ptr, string.as_ptr());
    ///
    /// let string = GStr::from_static("Hello, Rust!").try_into_string().unwrap();
    /// assert_eq!(string, "Hello, Rust!");
    ///
    /// let empty_string = GStr::EMPTY.try_into_string().unwrap();
    /// assert_eq!(empty_string, "");
    /// ```
    #[inline]
    pub fn try_into_string(self) -> Result<String, Self> {
        let mut string = ManuallyDrop::new(self);
        let len = string.len();

        if string.is_heap() {
            debug_assert!(len > 0);

            // SAFETY:
            // - The memory pointed by `string.as_mut_ptr()` was allocated by the global allocator
            //   with a alignment of `u8`. And the size of this memory is `len`.
            // - The whole memory is a valid UTF-8 sequence.
            // - The ownership of the memory is transferred to the returned `String`.
            unsafe { Ok(String::from_raw_parts(string.as_mut_ptr(), len, len)) }
        } else if len == 0 {
            /// Returns the empty string.
            #[cold]
            fn return_empty_string() -> Result<String, GStr> {
                Ok(String::new())
            }

            return_empty_string()
        } else {
            // SAFETY: The layout of the string buffer is valid and its size is greater than 0.
            let ptr = unsafe { alloc::alloc::alloc(Layout::array::<u8>(len).unwrap_unchecked()) };

            if ptr.is_null() {
                /// Returns the original [`GStr`].
                #[cold]
                fn return_gstr(string: ManuallyDrop<GStr>) -> Result<String, GStr> {
                    Err(ManuallyDrop::into_inner(string))
                }

                return_gstr(string)
            } else {
                // SAFETY: It's valid to copy `len` bytes from `string.as_ptr()` to `ptr`.
                unsafe {
                    ptr::copy_nonoverlapping::<u8>(string.as_ptr(), ptr, len);
                }

                // SAFETY:
                // - `ptr` points to a memory which is allocated by the global allocator. And the
                //   size of this memory is `len`.
                // - The whole memory is a valid UTF-8 sequence.
                // - The ownership of the memory is transferred to the returned `String`.
                unsafe { Ok(String::from_raw_parts(ptr, len, len)) }
            }
        }
    }

    /// Converts this [`GStr`] into a [`String`].
    ///
    /// If the string buffer is heap-allocated, no allocation is performed. Otherwise the string
    /// buffer is cloned into a new [`String`].
    ///
    /// # Panics
    ///
    /// Panics if fails to allocate memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string = String::from("Hello, World!");
    /// let string_ptr = string.as_ptr();
    /// let gstr = GStr::from_string(string);
    /// let string = gstr.into_string();
    /// assert_eq!(string, "Hello, World!");
    /// assert_eq!(string_ptr, string.as_ptr());
    ///
    /// let string = GStr::from_static("Hello, Rust!").into_string();
    /// assert_eq!(string, "Hello, Rust!");
    /// ```
    #[inline]
    #[must_use]
    pub fn into_string(self) -> String {
        match self.try_into_string() {
            Ok(s) => s,
            Err(s) => handle_alloc_error(s),
        }
    }

    /// Converts this [`GStr`] into a <code>[Box]<[str]></code>.
    ///
    /// If the string buffer is heap-allocated, no allocation is performed. Otherwise the string
    /// buffer is cloned into a new <code>[Box]<[str]></code>.
    ///
    /// # Panics
    ///
    /// Panics if fails to allocate memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string = String::from("Hello, World!");
    /// let string_ptr = string.as_ptr();
    /// let gstr = GStr::from_string(string);
    /// let boxed_str = gstr.into_boxed_str();
    /// assert_eq!(boxed_str.as_ref(), "Hello, World!");
    /// assert_eq!(string_ptr, boxed_str.as_ptr());
    ///
    /// let boxed_str = GStr::from_static("Hello, Rust!").into_boxed_str();
    /// assert_eq!(boxed_str.as_ref(), "Hello, Rust!");
    /// ```
    #[inline]
    #[must_use]
    pub fn into_boxed_str(self) -> Box<str> {
        self.into_string().into_boxed_str()
    }

    /// Converts this [`GStr`] into a byte vector.
    ///
    /// If the string buffer is heap-allocated, no allocation is performed. Otherwise the string
    /// buffer is cloned into a new byte vector.
    ///
    /// # Panics
    ///
    /// Panics if fails to allocate memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string = String::from("Hello, World!");
    /// let string_ptr = string.as_ptr();
    /// let gstr = GStr::from_string(string);
    /// let bytes = gstr.into_bytes();
    /// assert_eq!(bytes, b"Hello, World!");
    /// assert_eq!(string_ptr, bytes.as_ptr());
    ///
    /// let bytes = GStr::from_static("Hello, Rust!").into_bytes();
    /// assert_eq!(bytes, b"Hello, Rust!");
    /// ```
    #[inline]
    #[must_use]
    pub fn into_bytes(self) -> Vec<u8> {
        self.into_string().into_bytes()
    }

    /// Decomposes the [`GStr`] into its raw buffer and length.
    ///
    /// After calling this function, the caller is responsible for the memory previously managed
    /// by the [`GStr`]. The only way to do this is to convert the raw buffer and the length back
    /// into a [`GStr`] with the [`from_raw_parts`](GStr::from_raw_parts) function, allowing the
    /// destructor to perform the cleanup.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string = GStr::new("Hello, World!");
    /// let (buf, len) = string.into_raw_parts();
    /// let string = unsafe { GStr::from_raw_parts(buf, len) };
    /// assert_eq!(string, "Hello, World!");
    ///
    /// let string = GStr::from_static("Hello, Rust!");
    /// let (buf, len) = string.into_raw_parts();
    /// let string = unsafe { GStr::from_raw_parts(buf, len) };
    /// assert_eq!(string, "Hello, Rust!");
    /// ```
    #[inline]
    #[must_use]
    pub const fn into_raw_parts(self) -> (RawBuffer, usize) {
        let len = self.len();

        let buf = if self.is_static() {
            RawBuffer::Static(self.ptr)
        } else {
            debug_assert!(self.is_heap() && !self.is_empty());

            RawBuffer::Heap(self.ptr)
        };
        mem::forget(self);

        (buf, len)
    }

    /// Compares the prefix buffers.
    #[inline]
    fn prefix_cmp(&self, other: &Self) -> Ordering {
        self.prefix_and_len.prefix_cmp(other.prefix_and_len)
    }

    /// Returns whether the prefix buffers and the lengths of two [`GStr`]s are equal.
    #[inline]
    const fn prefix_len_eq(&self, other: &GStr) -> bool {
        self.prefix_and_len.prefix_len_eq(other.prefix_and_len)
    }

    /// Concatenates two strings to a new [`GStr`].
    ///
    /// # Panics
    ///
    /// - Panics if the total length in bytes of `self` and `string` is greater than
    ///   [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Panics if fails to allocate memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string1 = GStr::new("Hello ");
    /// let string2 = string1.concat("World!");
    /// assert_eq!(string2, "Hello World!");
    /// ```
    #[must_use]
    pub fn concat<S: AsRef<str>>(&self, string: S) -> Self {
        let a = self.as_str();
        let b = string.as_ref();
        let total_len = a.len() + b.len();

        if total_len <= Self::MAX_LENGTH {
            let mut s = String::with_capacity(total_len);
            s.push_str(a);
            s.push_str(b);

            match Self::try_from_string(s) {
                Ok(s) => s,
                Err(e) => match e.kind {
                    ErrorKind::AllocationFailure => handle_alloc_error(e),
                    // SAFETY:
                    // - `total_len` isn't greater than `GStr::MAX_LENGTH`.
                    // - `GStr::try_from_string` doesn't return other errors.
                    _ => unsafe { core::hint::unreachable_unchecked() },
                },
            }
        } else {
            panic!(
                "The total length in bytes of two strings shouldn't be greater than `GStr`'s max length {}",
                GStr::MAX_LENGTH
            );
        }
    }
}

impl Drop for GStr {
    #[inline]
    fn drop(&mut self) {
        if self.is_heap() {
            debug_assert!(!self.is_empty());

            // SAFETY:
            // - The layout of the string buffer is valid.
            // - `self.as_mut_ptr()` points to a memory allocated by the global allocator with the
            //   string buffer's layout.
            unsafe {
                alloc::alloc::dealloc(
                    self.as_mut_ptr(),
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
            .field("is_static", &self.is_static())
            .field("len", &self.len())
            .field("prefix", &self.prefix())
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
            // SAFETY: The string isn't empty if it's heap allocated. This assertion can remove some
            //         branches.
            unsafe {
                core::hint::assert_unchecked(!self.is_empty());
            }

            match Self::try_new(self) {
                Ok(s) => s,
                Err(e) => match e.kind {
                    ErrorKind::AllocationFailure => handle_alloc_error(e),
                    // SAFETY:
                    // - A `GStr`'s length isn't greater than `GStr::MAX_LENGTH`.
                    // - `GStr::try_new` doesn't return other errors.
                    _ => unsafe { core::hint::unreachable_unchecked() },
                },
            }
        } else {
            Self {
                ptr: self.ptr,
                prefix_and_len: self.prefix_and_len,
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
        // Test if this two strings's lengths and prefix buffers are equal.
        if self.prefix_len_eq(other) {
            debug_assert_eq!(self.len(), other.len());
            debug_assert_eq!(self.prefix(), other.prefix());

            let len = self.len();
            // SAFETY: The length of `self`'s string buffer is `len`.
            let a = unsafe { slice::from_raw_parts(self.as_ptr(), len) };
            // SAFETY: The length of `other`'s string buffer is `len`.
            let b = unsafe { slice::from_raw_parts(other.as_ptr(), len) };

            a == b
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
        match self.prefix_cmp(other) {
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

// SAFETY: A [`GStr`] can be transferred across different threads.
unsafe impl Send for GStr {}

// SAFETY: A [`GStr`] is immutable, so it's safe to share references between threads.
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
        self.as_str() == other
    }
}

impl PartialEq<GStr> for str {
    #[inline]
    fn eq(&self, other: &GStr) -> bool {
        self == other.as_str()
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

impl PartialEq<GStr> for &'_ String {
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
        self.as_str().partial_cmp(other)
    }
}

impl PartialOrd<GStr> for str {
    #[inline]
    fn partial_cmp(&self, other: &GStr) -> Option<Ordering> {
        self.partial_cmp(other.as_str())
    }
}

impl PartialOrd<GStr> for &'_ str {
    #[inline]
    fn partial_cmp(&self, other: &GStr) -> Option<Ordering> {
        (*self).partial_cmp(other)
    }
}

impl PartialOrd<String> for GStr {
    #[inline]
    fn partial_cmp(&self, other: &String) -> Option<Ordering> {
        self.partial_cmp(other.as_str())
    }
}

impl PartialOrd<GStr> for String {
    #[inline]
    fn partial_cmp(&self, other: &GStr) -> Option<Ordering> {
        self.as_str().partial_cmp(other)
    }
}

impl PartialOrd<GStr> for &'_ String {
    #[inline]
    fn partial_cmp(&self, other: &GStr) -> Option<Ordering> {
        self.as_str().partial_cmp(other)
    }
}

impl From<char> for GStr {
    /// Converts a [`char`] into a [`GStr`].
    ///
    /// # Examples
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// assert_eq!(GStr::from('a'), "a");
    /// ```
    #[inline]
    fn from(c: char) -> Self {
        let mut buf = [0u8; 4];
        let s = c.encode_utf8(&mut buf);

        match Self::try_new(s) {
            Ok(s) => s,
            Err(e) => match e.kind {
                ErrorKind::AllocationFailure => handle_alloc_error(e),
                // SAFETY:
                // - The max length in bytes of a single UTF-8 character is 4.
                // - `GStr::try_new` doesn't return other errors.
                _ => unsafe { core::hint::unreachable_unchecked() },
            },
        }
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

    /// Converts a `&str` into a [`GStr`].
    ///
    /// This clones the string.
    #[inline]
    fn try_from(string: &'a str) -> Result<Self, Self::Error> {
        Self::try_new(string)
    }
}

impl<'a> TryFrom<&'a mut str> for GStr {
    type Error = ToGStrError<&'a mut str>;

    /// Converts a `&mut str` into a [`GStr`].
    ///
    /// This clones the string.
    #[inline]
    fn try_from(string: &'a mut str) -> Result<Self, Self::Error> {
        Self::try_new(string)
    }
}

impl TryFrom<String> for GStr {
    type Error = ToGStrError<String>;

    /// Converts a [`String`] into a [`GStr`].
    ///
    /// This doesn't clone the string but shrinks it's capacity to match its length.
    #[inline]
    fn try_from(string: String) -> Result<Self, Self::Error> {
        Self::try_from_string(string)
    }
}

impl<'a> TryFrom<&'a String> for GStr {
    type Error = ToGStrError<&'a String>;

    /// Converts a `&String` into a [`GStr`].
    ///
    /// This clones the string.
    #[inline]
    fn try_from(string: &'a String) -> Result<Self, Self::Error> {
        Self::try_new(string)
    }
}

impl TryFrom<Box<str>> for GStr {
    type Error = ToGStrError<Box<str>>;

    /// Converts a `Box<str>` into a [`GStr`].
    ///
    /// This doesn't clone the string.
    #[inline]
    fn try_from(string: Box<str>) -> Result<Self, Self::Error> {
        let string = string.into_string();

        Self::try_from_string(string).map_err_source(String::into_boxed_str)
    }
}

impl<'a> TryFrom<Cow<'a, str>> for GStr {
    type Error = ToGStrError<Cow<'a, str>>;

    /// Converts a `Cow<str>` into a [`GStr`].
    ///
    /// If the string is owned, this doesn't clone the string but shrinks it's capacity to match its
    /// length. Otherwise it clones the string.
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

impl From<GStr> for Cow<'_, str> {
    #[inline]
    fn from(string: GStr) -> Self {
        Self::Owned(string.into_string())
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

/// Copies the first [`PREFIX_LENGTH`](GStr::PREFIX_LENGTH) bytes of `bytes` into an array in const
/// context.
///
/// If the length of `bytes` is less than [`PREFIX_LENGTH`](GStr::PREFIX_LENGTH), the remaining
/// bytes are filled with 0.
// NOTE: If the compiler can't confirm that `bytes` isn't empty, this function will have an extra
//       branch.
#[inline]
const fn copy_prefix(bytes: &[u8]) -> [u8; PrefixAndLength::PREFIX_LENGTH] {
    let mut prefix = [0u8; PrefixAndLength::PREFIX_LENGTH];
    let mut i = 0;
    let len = if bytes.len() < PrefixAndLength::PREFIX_LENGTH {
        bytes.len()
    } else {
        PrefixAndLength::PREFIX_LENGTH
    };

    while i < len {
        // No bound checks here.
        prefix[i] = bytes[i];
        i += 1;
    }

    prefix
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
    debug_assert!(!string.is_empty() && string.len() <= GStr::MAX_LENGTH);

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
        /// Both the length and capacity of `string` must be greater than 0.
        #[cold]
        #[inline(never)]
        unsafe fn realloc_string(string: String) -> Result<&'static mut str, String> {
            let mut string = ManuallyDrop::new(string);
            let len = string.len();
            let capacity = string.capacity();
            // Not using `string.as_mut_ptr()` to get the raw pointer because it only covers `len`
            // bytes under the Stacked Borrows rules. Reallocating the memory requires the raw
            // pointer covers `capacity` bytes.
            // SAFETY: We just get the raw pointer from `string`'s inner buffer, not mutating its
            //         content.
            let ptr = unsafe { string.as_mut_vec().as_mut_ptr() };
            // SAFETY: The layout of string's inner buffer is valid.
            let layout = unsafe { Layout::array::<u8>(capacity).unwrap_unchecked() };

            // SAFETY:
            // - `ptr` is the pointer of `string`'s inner buffer, so it was allocated by the global
            //   allocator.
            // - `layout` is the layout of `string`'s inner buffer and its size is greater than 0.
            // - The length of `string` is guaranteed to be greater than 0.
            // - `len` doesn't overflows `isize`.
            let new_ptr = unsafe { alloc::alloc::realloc(ptr, layout, len) };

            if new_ptr.is_null() {
                Err(ManuallyDrop::into_inner(string))
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

        // SAFETY:
        // - The length of `string` is guaranteed to be greater than 0.
        // - The capacity of `string` is greater than its length, so the capacity is greater than 0.
        unsafe { realloc_string(string) }
    }
}

/// Returns an empty [`GStr`].
#[cold]
const fn empty_gstr() -> GStr {
    GStr::EMPTY
}

/// Returns an allocation failure error.
#[cold]
#[inline(never)]
fn allocation_failure<S>(string: S) -> Result<GStr, ToGStrError<S>> {
    Err(ToGStrError::new_allocation_failure(string))
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
    assert!(size_of::<PrefixAndLength>() == size_of::<u64>());
    assert!(align_of::<PrefixAndLength>() == align_of::<usize>());

    #[cfg(target_pointer_width = "64")]
    {
        assert!(size_of::<GStr>() == 4 * size_of::<u32>());
        assert!(size_of::<Option<GStr>>() == 4 * size_of::<u32>());

        assert!(PrefixAndLength::HALF_BITS == 32);
        assert!(PrefixAndLength::PREFIX_MASK == 0xFFFF_FFFF_0000_0000);
        assert!(PrefixAndLength::LEN_PREFIX_MASK == 0xFFFF_FFFF_7FFF_FFFF);
    }

    #[cfg(target_pointer_width = "32")]
    {
        assert!(size_of::<GStr>() == 3 * size_of::<u32>());
        assert!(size_of::<Option<GStr>>() == 3 * size_of::<u32>());
    }

    assert!(align_of::<GStr>() == align_of::<usize>());

    assert!(PrefixAndLength::PREFIX_LENGTH == 4);
    assert!(PrefixAndLength::LENGTH_BITS == 31);
    assert!(PrefixAndLength::STATIC_MASK == 0x8000_0000);
    assert!(PrefixAndLength::LENGTH_MASK == 0x7FFF_FFFF);
    assert!(PrefixAndLength::MAX_LENGTH == 0x7FFF_FFFF);

    assert!(GStr::MAX_LENGTH == PrefixAndLength::MAX_LENGTH);
    assert!(GStr::MAX_LENGTH <= isize::MAX as _);
};

#[cfg(test)]
mod tests {
    use super::*;

    use alloc::format;
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

    fn test_gstr_is_eq(a: &GStr, b: &str) {
        assert_eq!(a.len(), b.len());
        assert_eq!(a, b);
        assert_eq!(b, a);
        assert_eq!(a.cmp(a), Ordering::Equal);
        assert_eq!(a.partial_cmp(a), Some(Ordering::Equal));
        assert_eq!(a.partial_cmp(b), Some(Ordering::Equal));
        assert_eq!(b.partial_cmp(a), Some(Ordering::Equal));

        let c = GStr::new(b);
        assert_eq!(a.len(), c.len());
        assert_eq!(a, &c);
        assert_eq!(c, a);
        assert_eq!(a.cmp(&c), Ordering::Equal);
        assert_eq!(c.cmp(a), Ordering::Equal);
        assert_eq!(a.partial_cmp(&c), Some(Ordering::Equal));
        assert_eq!(c.partial_cmp(&a), Some(Ordering::Equal));
        assert!(a.prefix_len_eq(&c));
        assert!(c.prefix_len_eq(a));

        let d = a.clone();
        assert_eq!(a.len(), d.len());
        assert_eq!(a, &d);
        assert_eq!(d, a);
        assert_eq!(a.cmp(&d), Ordering::Equal);
        assert_eq!(d.cmp(a), Ordering::Equal);
        assert_eq!(a.partial_cmp(&d), Some(Ordering::Equal));
        assert_eq!(d.partial_cmp(&a), Some(Ordering::Equal));
        assert!(a.prefix_len_eq(&d));
        assert!(d.prefix_len_eq(a));

        let bytes = b.as_bytes();
        #[allow(clippy::needless_range_loop)]
        for i in 0..(bytes.len().min(PrefixAndLength::PREFIX_LENGTH)) {
            assert_eq!(a.prefix()[i], bytes[i]);
        }
        for i in bytes.len()..PrefixAndLength::PREFIX_LENGTH {
            assert_eq!(a.prefix()[i], 0);
        }
    }

    fn test_gstr_concat(gstr: &GStr, string: &str) {
        assert_eq!(gstr.concat(""), gstr);
        assert_eq!(gstr.concat("foo"), format!("{}{}", gstr, "foo"));
        assert_eq!(gstr.concat(string), format!("{}{}", gstr, string));
    }

    fn test_gstr_raw_parts(gstr: GStr, string: &str) {
        let ptr = gstr.as_ptr();
        let is_static = gstr.is_static();
        let (buf, len) = gstr.into_raw_parts();
        if is_static {
            assert!(matches!(buf, RawBuffer::Static(_)));
        } else {
            assert!(matches!(buf, RawBuffer::Heap(_)));
        }
        if string.is_empty() {
            assert!(matches!(buf, RawBuffer::Static(_)));
        }
        assert_eq!(buf.as_ptr(), ptr);
        assert_eq!(len, string.len());

        // SAFETY: `buf` and `len` are from `GStr::into_raw_parts`.
        let gstr = unsafe { GStr::from_raw_parts(buf, len) };
        assert_eq!(gstr, string);
        assert_eq!(gstr.as_ptr(), ptr);
        assert_eq!(gstr.len(), len);
        assert_eq!(gstr.is_static(), is_static);
        assert_eq!(gstr.is_heap(), !is_static);
        if string.is_empty() {
            assert!(gstr.is_static());
        }
    }

    fn test_gstr_into_string(gstr: GStr, string: &str) {
        let is_heap = gstr.is_heap();
        let gstr_clone = gstr.clone();
        let ptr = gstr_clone.as_ptr();
        let mut s = gstr_clone.into_string();
        if is_heap {
            assert_eq!(s.as_ptr(), ptr);
        }
        assert_eq!(s, string);
        assert_eq!(s.len(), string.len());
        s.push('a');

        let gstr_clone = gstr.clone();
        let ptr = gstr_clone.as_ptr();
        let boxed_str = gstr_clone.into_boxed_str();
        if is_heap {
            assert_eq!(boxed_str.as_ptr(), ptr);
        }
        assert_eq!(boxed_str.as_ref(), string);
        assert_eq!(boxed_str.len(), string.len());

        let ptr = gstr.as_ptr();
        let mut bytes = gstr.into_bytes();
        if is_heap {
            assert_eq!(bytes.as_ptr(), ptr);
        }
        assert_eq!(bytes, string.as_bytes());
        assert_eq!(bytes.len(), string.len());
        bytes.push(0);
    }

    fn test_gstr_new(string: &str) {
        let gstr = GStr::new(string);

        if gstr.is_empty() {
            assert!(gstr.is_static());
            assert!(!gstr.is_heap());
            assert_eq!(gstr.as_static_str(), Some(""));
        } else {
            assert!(gstr.is_heap());
            assert!(!gstr.is_static());
            assert_eq!(gstr.as_static_str(), None);
        }

        test_gstr_is_eq(&gstr, string);
        test_gstr_concat(&gstr, string);
        test_gstr_raw_parts(gstr.clone(), string);
        test_gstr_into_string(gstr, string);
    }

    fn test_gstr_from_static(string: &'static str) {
        let gstr = GStr::from_static(string);

        assert!(gstr.is_static());
        assert!(!gstr.is_heap());
        assert_eq!(gstr.as_static_str(), Some(string));

        test_gstr_is_eq(&gstr, string);
        test_gstr_concat(&gstr, string);
        test_gstr_raw_parts(gstr.clone(), string);
        test_gstr_into_string(gstr, string);
    }

    fn test_gstr_from_string(string: &str) {
        let gstr = GStr::from_string(String::from(string));

        if gstr.is_empty() {
            assert!(gstr.is_static());
            assert!(!gstr.is_heap());
            assert_eq!(gstr.as_static_str(), Some(""));
        } else {
            assert!(gstr.is_heap());
            assert!(!gstr.is_static());
            assert_eq!(gstr.as_static_str(), None);
        }

        test_gstr_is_eq(&gstr, string);
        test_gstr_concat(&gstr, string);
        test_gstr_raw_parts(gstr.clone(), string);
        test_gstr_into_string(gstr, string);

        let mut s = String::from(string);
        s.reserve(16);
        let gstr = GStr::from_string(s);

        if gstr.is_empty() {
            assert!(gstr.is_static());
            assert!(!gstr.is_heap());
            assert_eq!(gstr.as_static_str(), Some(""));
        } else {
            assert!(gstr.is_heap());
            assert!(!gstr.is_static());
            assert_eq!(gstr.as_static_str(), None);
        }

        test_gstr_is_eq(&gstr, string);
        test_gstr_concat(&gstr, string);
        test_gstr_raw_parts(gstr.clone(), string);
        test_gstr_into_string(gstr, string);
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

        match a.as_bytes()[..a.len().min(PrefixAndLength::PREFIX_LENGTH)]
            .cmp(&b.as_bytes()[..b.len().min(PrefixAndLength::PREFIX_LENGTH)])
        {
            Ordering::Less => {
                assert_eq!(gstr_a.prefix_cmp(&gstr_b), Ordering::Less);
                assert_eq!(gstr_b.prefix_cmp(&gstr_a), Ordering::Greater);
                assert!(!gstr_a.prefix_len_eq(&gstr_b));
            }
            Ordering::Equal => {
                assert_eq!(gstr_a.prefix_cmp(&gstr_b), Ordering::Equal);
                assert_eq!(gstr_b.prefix_cmp(&gstr_a), Ordering::Equal);
                assert_eq!(gstr_a.prefix_len_eq(&gstr_b), a.len() == b.len());
            }
            Ordering::Greater => {
                assert_eq!(gstr_a.prefix_cmp(&gstr_b), Ordering::Greater);
                assert_eq!(gstr_b.prefix_cmp(&gstr_a), Ordering::Less);
                assert!(!gstr_a.prefix_len_eq(&gstr_b));
            }
        }
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    fn test_gstr_valid_utf8(string: String) {
        let gstr = GStr::from_utf8(string.clone().into_bytes()).unwrap();
        assert_eq!(gstr, string);

        let gstr = GStr::from_utf8_lossy(string.clone().into_bytes());
        assert_eq!(gstr, string);

        // SAFETY: `string` is valid UTF-8.
        let gstr = unsafe { GStr::from_utf8_unchecked(string.clone().into_bytes()) };
        assert_eq!(gstr, string);
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    fn test_gstr_utf8_bytes(bytes: Vec<u8>) {
        let gstr = GStr::from_utf8(bytes.clone());
        let string = String::from_utf8(bytes.clone());
        if let Ok(string) = string {
            assert_eq!(string, gstr.unwrap());

            // SAFETY: `bytes` is valid UTF-8.
            let gstr = unsafe { GStr::from_utf8_unchecked(bytes.clone()) };
            assert_eq!(gstr, string);
        } else {
            let err = gstr.unwrap_err();
            assert!(matches!(err.error_kind(), ErrorKind::Utf8Error(_)));
            assert_eq!(err.into_source(), bytes);
        }

        let gstr = GStr::from_utf8_lossy(bytes.clone());
        let string = String::from_utf8_lossy(&bytes);
        assert_eq!(gstr, string);
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    fn test_gstr_valid_utf16(string: String) {
        let bytes = string.encode_utf16().collect::<Vec<_>>();
        let gstr = GStr::from_utf16(&bytes).unwrap();
        assert_eq!(gstr, string);

        let gstr = GStr::from_utf16_lossy(&bytes);
        assert_eq!(gstr, string);

        let utf16_le = bytes
            .iter()
            .flat_map(|n| n.to_le_bytes())
            .collect::<Vec<_>>();
        let gstr = GStr::from_utf16le(&utf16_le).unwrap();
        assert_eq!(gstr, string);
        let gstr = GStr::from_utf16le_lossy(&utf16_le);
        assert_eq!(gstr, string);

        let utf16_be = bytes
            .iter()
            .flat_map(|n| n.to_be_bytes())
            .collect::<Vec<_>>();
        let gstr = GStr::from_utf16be(&utf16_be).unwrap();
        assert_eq!(gstr, string);
        let gstr = GStr::from_utf16be_lossy(&utf16_be);
        assert_eq!(gstr, string);
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    fn test_gstr_utf16_u16_bytes(bytes: Vec<u16>) {
        let gstr = GStr::from_utf16(&bytes);
        let string = String::from_utf16(&bytes);
        if let Ok(string) = string {
            assert_eq!(string, gstr.unwrap());
        } else {
            let err = gstr.unwrap_err();
            assert!(matches!(err.error_kind(), ErrorKind::InvalidUtf16));
            assert_eq!(err.into_source(), &bytes);
        }

        let gstr = GStr::from_utf16_lossy(&bytes);
        let string = String::from_utf16_lossy(&bytes);
        assert_eq!(gstr, string);
    }

    #[cfg(feature = "nightly_test")]
    fn test_gstr_utf16_u8_bytes(bytes: Vec<u8>) {
        let string = String::from_utf16le(&bytes);
        let gstr = GStr::from_utf16le(&bytes);
        if let Ok(string) = string {
            assert_eq!(string, gstr.unwrap());
        } else {
            let err = gstr.unwrap_err();
            assert!(matches!(
                err.error_kind(),
                ErrorKind::InvalidUtf16 | ErrorKind::FromUtf16OddLength
            ));
            assert_eq!(err.into_source(), &bytes);
        }

        let string = String::from_utf16le_lossy(&bytes);
        let gstr = GStr::from_utf16le_lossy(&bytes);
        assert_eq!(string, gstr);

        let string = String::from_utf16be(&bytes);
        let gstr = GStr::from_utf16be(&bytes);
        if let Ok(string) = string {
            assert_eq!(string, gstr.unwrap());
        } else {
            let err = gstr.unwrap_err();
            assert!(matches!(
                err.error_kind(),
                ErrorKind::InvalidUtf16 | ErrorKind::FromUtf16OddLength
            ));
            assert_eq!(err.into_source(), &bytes);
        }

        let string = String::from_utf16be_lossy(&bytes);
        let gstr = GStr::from_utf16be_lossy(&bytes);
        assert_eq!(string, gstr);
    }

    #[test]
    fn gstr_new() {
        test_literal_strings(test_gstr_new);
    }

    #[test]
    fn gstr_from_static() {
        test_literal_strings(test_gstr_from_static);
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
    fn string_to_static<F: FnOnce(&'static str)>(string: String, f: F) {
        let len = string.len();
        let capacity = string.capacity();
        let string = string.leak();
        let ptr = string.as_mut_ptr();

        f(string);

        // To avoid memory leaks.
        // SAFETY: `ptr`, `len` and `capacity` are from the original string.
        unsafe {
            drop(String::from_raw_parts(ptr, len, capacity));
        }
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
        fn prop_gstr_from_static(string: String) {
            string_to_static(string, test_gstr_from_static);
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

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    proptest! {
        #[test]
        fn prop_gstr_valid_utf8(string: String) {
            test_gstr_valid_utf8(string);
        }
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    proptest! {
        #[test]
        fn prop_gstr_utf8_bytes(bytes: Vec<u8>) {
            test_gstr_utf8_bytes(bytes);
        }
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    proptest! {
        #[test]
        fn prop_gstr_valid_utf16(string: String) {
            test_gstr_valid_utf16(string);
        }
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    proptest! {
        #[test]
        fn prop_gstr_utf16_u16_bytes(bytes: Vec<u16>) {
            test_gstr_utf16_u16_bytes(bytes);
        }
    }

    #[cfg(feature = "nightly_test")]
    proptest! {
        #[test]
        fn prop_gstr_utf16_u8_bytes(bytes: Vec<u8>) {
            test_gstr_utf16_u8_bytes(bytes);
        }
    }
}
