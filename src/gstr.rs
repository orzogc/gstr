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
    sync::atomic::{self, AtomicUsize},
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

const ATOMIC_SIZE: usize = size_of::<AtomicUsize>();

const ATOMIC_ALIGN: usize = align_of::<AtomicUsize>();

/// Represents the different kinds of errors in [`ToGStrError`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ErrorKind {
    /// Indicates that the string's length exceeds the maximum allowed length
    /// ([`MAX_LENGTH`](GStr::MAX_LENGTH)).
    ///
    /// The wrapped [`usize`] represents the requested length of the string.
    LengthOverflow(usize),
    /// Occurs when there is a failure to allocate memory.
    ///
    /// The wrapped [`Layout`] represents the layout of the memory allocation that failed.
    AllocationFailure(Layout),
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
    /// The source attempted to be converted to a [`GStr`]. It may be a `()` if fails to get the
    /// source.
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
    fn new_allocation_failure(source: S, layout: Layout) -> Self {
        Self {
            kind: ErrorKind::AllocationFailure(layout),
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

    /// Removes the source.
    #[inline]
    pub fn remove_source(self) -> ToGStrError<()> {
        ToGStrError {
            kind: self.kind,
            source: (),
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
                "the source's length {len} shouldn't be greater than `GStr`'s maximum length",
            ),
            ErrorKind::AllocationFailure(layout) => write!(
                f,
                "failed to allocate memory, the allocated size is {}, align is {}",
                layout.size(),
                layout.align()
            ),
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
            | ErrorKind::AllocationFailure(_)
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
pub(crate) trait ResultExt<S, NS> {
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

/// An error for [`StringBuffer`].
enum StringBufferError {
    /// Indicates that the string buffer's length exceeds the maximum allowed capacity
    /// ([`MAX_CAPACITY`](StringBuffer::MAX_CAPACITY)).
    ///
    /// The wrapped [`usize`] represents the requested capacity of the string buffer.
    CapacityOverflow(usize),
    /// Occurs when there is a failure to allocate memory.
    ///
    /// The wrapped [`Layout`] represents the layout of the memory allocation that failed.
    AllocationFailure(Layout),
}

impl StringBufferError {
    /// Returns an error from a closure.
    #[cold]
    fn return_err<F: FnOnce() -> Self>(f: F) -> Result<(), Self> {
        Err(f())
    }

    /// Panics with the error.
    ///
    /// # Panics
    ///
    /// - Panics if the capacity exceed [`MAX_CAPACITY`](StringBuffer::MAX_CAPACITY).
    /// - Panics if fails to allocate memory.
    #[cold]
    fn panic(self) -> ! {
        match self {
            Self::CapacityOverflow(capacity) => {
                panic!("the string buffer's capacity {capacity} shouldn't be greater than its maximum capacity");
            }
            Self::AllocationFailure(layout) => handle_alloc_error(layout),
        }
    }

    /// Converts the error into a [`ToGStrError`].
    #[inline]
    fn into_gstr_error<S>(self, source: S) -> ToGStrError<S> {
        match self {
            Self::CapacityOverflow(capacity) => ToGStrError::new_length_overflow(source, capacity),
            Self::AllocationFailure(layout) => ToGStrError::new_allocation_failure(source, layout),
        }
    }
}

/// A string buffer.
struct StringBuffer<const SHARED: bool> {
    /// This pointer points to a valid UTF-8 string buffer.
    ///
    /// If `SHARED` is true, an [`AtomicUsize`] is stored before the string buffer.
    ptr: NonNull<u8>,
    /// The string buffer's length.
    len: usize,
    /// The string buffer's capacity.
    capacity: usize,
}

impl<const SHARED: bool> StringBuffer<SHARED> {
    /// The maximum capacity of a [`StringBuffer`].
    const MAX_CAPACITY: usize = GStr::<SHARED>::MAX_LENGTH;

    /// Returns the size of the layout for a string buffer with the given length.
    ///
    /// The returned value isn't less than `len`.
    ///
    /// If `SHARED` is true, the returned value is `ATOMIC_SIZE + len`.
    ///
    /// # Safety
    ///
    /// `len` must not be greater than [`MAX_CAPACITY`](Self::MAX_CAPACITY).
    #[inline]
    const unsafe fn layout_size(len: usize) -> usize {
        if SHARED {
            ATOMIC_SIZE + len
        } else {
            len
        }
    }

    /// Returns the alignment of the layout for a string buffer.
    ///
    /// The returned value is a power of two.
    ///
    /// If `SHARED` is true, the returned value is [`ATOMIC_ALIGN`].
    #[inline]
    const fn layout_align() -> usize {
        if SHARED {
            ATOMIC_ALIGN
        } else {
            align_of::<u8>()
        }
    }

    /// Returns the layout for a string buffer with the given length.
    ///
    /// The returned layout's size isn't less than `len`.
    ///
    /// If `SHARED` is true, the returned layout's size is `ATOMIC_SIZE + len` and its alignment
    /// is [`ATOMIC_ALIGN`].
    ///
    /// # Safety
    ///
    /// `len` must not be greater than [`MAX_CAPACITY`](Self::MAX_CAPACITY).
    #[inline]
    const unsafe fn layout(len: usize) -> Layout {
        debug_assert!(len <= Self::MAX_CAPACITY);

        // SAFETY:
        // - `len` is guaranteed that it isn't greater than `MAX_CAPACITY` which can't overflow
        //   `isize`.
        // - The alignment returned by `layout_align` is a power of two.
        unsafe { Layout::from_size_align_unchecked(Self::layout_size(len), Self::layout_align()) }
    }

    /// Creates a new empty [`StringBuffer`].
    #[inline]
    const fn new() -> Self {
        Self {
            ptr: NonNull::dangling(),
            len: 0,
            capacity: 0,
        }
    }

    /// Creates a new [`StringBuffer`] with the given capacity.
    ///
    /// # Errors
    ///
    /// Returns an [`Err`] if the string buffer's length is greater than
    /// [`MAX_CAPACITY`](Self::MAX_CAPACITY) or allocation failure occurs.
    #[inline]
    fn try_with_capacity(capacity: usize) -> Result<Self, StringBufferError> {
        let mut buffer = Self::new();
        buffer.grow_memory(capacity)?;

        Ok(buffer)
    }

    /// Creates a new [`StringBuffer`] with the given capacity.
    ///
    /// # Panics
    ///
    /// - Panics if the string buffer capacity is greater than [`MAX_CAPACITY`](Self::MAX_CAPACITY).
    /// - Calls [`handle_alloc_error`] if fails to allocate heap memory.
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
    #[inline]
    fn with_capacity(capacity: usize) -> Self {
        match Self::try_with_capacity(capacity) {
            Ok(buffer) => buffer,
            Err(err) => err.panic(),
        }
    }

    /// Returns the pointer which points to the memory buffer.
    ///
    /// # Safety
    ///
    /// The string buffer's capacity must be greater than zero.
    #[inline]
    unsafe fn memory_ptr(&mut self) -> *mut u8 {
        if SHARED {
            // SAFETY: If `SHARED` is true, there is an `AtomicUsize` stored before the string
            //         buffer. They are in the same allocated object.
            unsafe { self.ptr.sub(ATOMIC_SIZE).as_ptr() }
        } else {
            self.ptr.as_ptr()
        }
    }

    /// Grows the memory buffer for the additional capacity.
    ///
    /// # Errors
    ///
    /// Returns an [`Err`] if the string buffer's length is greater than
    /// [`MAX_CAPACITY`](Self::MAX_CAPACITY) or allocation failure occurs.
    #[inline]
    fn grow_memory(&mut self, additional: usize) -> Result<(), StringBufferError> {
        debug_assert!(self.capacity <= Self::MAX_CAPACITY);
        debug_assert!(self.len <= self.capacity);

        if self.capacity == 0 {
            if additional > 0 {
                if additional <= Self::MAX_CAPACITY {
                    // SAFETY: `additional` isn't greater than `MAX_CAPACITY`.
                    let layout = unsafe { Self::layout(additional) };
                    // SAFETY: `additional` is greater than zero, so the size of `layout` is greater
                    //         than zero.
                    let mut ptr = unsafe { alloc::alloc::alloc(layout) };

                    if ptr.is_null() {
                        return StringBufferError::return_err(|| {
                            StringBufferError::AllocationFailure(layout)
                        });
                    }

                    if SHARED {
                        // SAFETY: `SHARED` is true, the size of the memory pointed by `ptr` is
                        //         greater than the size of `AtomicUsize` and its alignment is the
                        //         same as `AtomicUsize`. So `ptr` is valid for writes of
                        //         `AtomicUsize`.
                        unsafe {
                            ptr::write(ptr.cast::<AtomicUsize>(), AtomicUsize::new(1));
                        }
                        // SAFETY: The size of the memory pointed by `ptr` is greater than
                        //         `ATOMIC_SIZE`.
                        ptr = unsafe { ptr.add(ATOMIC_SIZE) };
                    }

                    // SAFETY: `ptr` isn't null.
                    self.ptr = unsafe { NonNull::new_unchecked(ptr) };
                    self.capacity = additional;
                } else {
                    return StringBufferError::return_err(|| {
                        StringBufferError::CapacityOverflow(additional)
                    });
                }
            }
        // The string buffer's capacity isn't less than its length, so `self.capacity - self.len`
        // doesn't overflow.
        } else if self.capacity - self.len < additional {
            // The string buffer's capacity isn't greater than `MAX_CAPACITY`, so
            // `self.capacity * 2` doesn't overflow. `self.capacity - self.len < additional` means
            // that `additional` is greater than zero, so `new_capacity` is also greater than zero.
            let new_capacity = (self.capacity * 2)
                .min(Self::MAX_CAPACITY)
                .max(self.capacity.saturating_add(additional));

            if new_capacity <= Self::MAX_CAPACITY {
                // SAFETY: The string buffer's capacity isn't greater than `MAX_CAPACITY`.
                let old_layout = unsafe { Self::layout(self.capacity) };
                // SAFETY:
                // - The string buffer's capacity is greater than zero, so `self.memory_ptr()`
                //   returns the pointer which is currently allocated via the global allocator.
                // - `old_layout` is the same layout that was used to allocate that block of memory.
                // - `new_capacity` is greater than zero, so the size returned by
                //   `Self::layout_size(new_capacity)` is greater than zero and it can't overflow
                //   `isize`.
                let mut ptr = unsafe {
                    alloc::alloc::realloc(
                        self.memory_ptr(),
                        old_layout,
                        Self::layout_size(new_capacity),
                    )
                };

                if ptr.is_null() {
                    // SAFETY: `new_capacity` isn't greater than `MAX_CAPACITY`.
                    return StringBufferError::return_err(|| unsafe {
                        StringBufferError::AllocationFailure(Self::layout(new_capacity))
                    });
                }

                if SHARED {
                    // SAFETY: `SHARED` is true, so the size of the memory pointed by `ptr` is
                    //         greater than `ATOMIC_SIZE`.
                    ptr = unsafe { ptr.add(ATOMIC_SIZE) };
                }

                // SAFETY: `ptr` isn't null.
                self.ptr = unsafe { NonNull::new_unchecked(ptr) };
                self.capacity = new_capacity;
            } else {
                return StringBufferError::return_err(|| {
                    StringBufferError::CapacityOverflow(new_capacity)
                });
            }
        }

        Ok(())
    }

    /// Shrinks the string buffer's capacity to match its length.
    ///
    /// # Safety
    ///
    /// The string buffer's length must be greater than zero.
    ///
    /// # Error
    ///
    /// Returns an [`Err`] if fails to shrink the string buffer.
    #[inline]
    unsafe fn shrink(&mut self) -> Result<(), StringBufferError> {
        debug_assert!(self.len > 0);
        debug_assert!(self.capacity >= self.len);

        if self.capacity > self.len {
            // SAFETY: The string buffer's capacity isn't greater than `MAX_CAPACITY`.
            let old_layout = unsafe { Self::layout(self.capacity) };
            // SAFETY:
            // - The string buffer's capacity is greater than its length, the capacity is greater
            //   than zero, so `self.memory_ptr()` returns the pointer which is currently allocated
            //   via the global allocator.
            // - `old_layout` is the same layout that was used to allocate that block of memory.
            // - The string buffer's length is guaranteed to be in the range `1..=MAX_CAPACITY`, so
            //   the new size returned from `layout_size` is greater than zero and it can't overflow
            //   `isize`.
            let mut ptr = unsafe {
                alloc::alloc::realloc(self.memory_ptr(), old_layout, Self::layout_size(self.len))
            };

            if ptr.is_null() {
                return StringBufferError::return_err(|| {
                    // SAFETY: The string buffer's length is guaranteed that it isn't greater than
                    //         `MAX_CAPACITY`.
                    StringBufferError::AllocationFailure(unsafe { Self::layout(self.len) })
                });
            }

            if SHARED {
                // SAFETY: `SHARED` is true, so the size of the memory pointed by `ptr` is
                //         greater than `ATOMIC_SIZE`.
                ptr = unsafe { ptr.add(ATOMIC_SIZE) };
            }

            // SAFETY: `ptr` isn't null.
            self.ptr = unsafe { NonNull::new_unchecked(ptr) };
            self.capacity = self.len;
        }

        Ok(())
    }

    /// Pushes a slice of bytes to the string buffer.
    ///
    /// # Safety
    ///
    /// `slice` must be a valid UTF-8 sequence.
    ///
    /// # Errors
    ///
    /// Returns an [`Err`] if the string buffer's length is greater than
    /// [`MAX_CAPACITY`](Self::MAX_CAPACITY) or allocation failure occurs.
    #[inline]
    unsafe fn try_push_slice(&mut self, slice: &[u8]) -> Result<(), StringBufferError> {
        let slice_len = slice.len();
        self.grow_memory(slice_len)?;
        debug_assert!(self.capacity - self.len >= slice_len);

        // SAFETY:
        // - `slice.as_ptr()` is properly aligned and valid for reads of `slice_len` bytes.
        // - After calling `grow_memory`, the string buffer's capacity isn't less than its length
        //   plus `slice_len`, so `self.ptr.add(self.len).as_ptr()` is properly aligned and valid
        //   for writes of `slice_len` bytes.
        // - The slice's memory and the string buffer's memory can't overlap each other.
        unsafe {
            ptr::copy_nonoverlapping::<u8>(
                slice.as_ptr(),
                self.ptr.add(self.len).as_ptr(),
                slice_len,
            );
        }
        self.len += slice_len;

        Ok(())
    }

    /// Pushes a [`char`] to the string buffer.
    ///
    /// # Errors
    ///
    /// Returns an [`Err`] if the string buffer's length is greater than
    /// [`MAX_CAPACITY`](Self::MAX_CAPACITY) or allocation failure occurs.
    #[inline]
    fn try_push_char(&mut self, ch: char) -> Result<(), StringBufferError> {
        // SAFETY: `encode_utf8` converts `ch` to a valid UTF-8 sequence.
        unsafe { self.try_push_slice(ch.encode_utf8(&mut [0; 4]).as_bytes()) }
    }

    /// Pushes a [`char`] to the string buffer.
    ///
    /// # Panics
    ///
    /// - Panics if the string buffer capacity is greater than [`MAX_CAPACITY`](Self::MAX_CAPACITY).
    /// - Calls [`handle_alloc_error`] if fails to allocate heap memory.
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
    #[inline]
    fn push_char(&mut self, ch: char) {
        if let Err(err) = self.try_push_char(ch) {
            err.panic();
        }
    }

    /// Pushes a [`str`] to the string buffer.
    ///
    /// # Errors
    ///
    /// Returns an [`Err`] if the string buffer's length is greater than
    /// [`MAX_CAPACITY`](Self::MAX_CAPACITY) or allocation failure occurs.
    #[inline]
    fn try_push_str(&mut self, string: &str) -> Result<(), StringBufferError> {
        // SAFETY: a `str` is always a valid UTF-8 sequence.
        unsafe { self.try_push_slice(string.as_bytes()) }
    }

    /// Pushes a [`str`] to the string buffer.
    ///
    /// # Panics
    ///
    /// - Panics if the string buffer capacity is greater than [`MAX_CAPACITY`](Self::MAX_CAPACITY).
    /// - Calls [`handle_alloc_error`] if fails to allocate heap memory.
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
    #[inline]
    fn push_str(&mut self, string: &str) {
        if let Err(err) = self.try_push_str(string) {
            err.panic();
        }
    }

    /// Converts the string buffer into a [`GStr`].
    ///
    /// # Error
    ///
    /// Returns an [`Err`] if fails to shrink the string buffer.
    #[inline]
    fn try_into_gstr(mut self) -> Result<GStr<SHARED>, StringBufferError> {
        if self.len == 0 {
            Ok(empty_gstr::<SHARED>())
        } else {
            // SAFETY: The string buffer's length is greater than zero.
            unsafe {
                self.shrink()?;
            }
            debug_assert!(self.len == self.capacity);
            debug_assert!(self.len <= GStr::<SHARED>::MAX_LENGTH);

            let buffer = ManuallyDrop::new(self);

            Ok(GStr::<SHARED> {
                ptr: buffer.ptr,
                // SAFETY:
                // - The string buffer can be converted to a slice of `u8`.
                // - The string buffer's length isn't greater than `MAX_CAPACITY`, so it's also less
                //   than `PrefixAndLength::MAX_LENGTH`.
                // - The returned `GStr` is heap-allocated.
                prefix_and_len: unsafe {
                    PrefixAndLength::new_unchecked(
                        copy_prefix(slice::from_raw_parts(buffer.ptr.as_ptr(), buffer.len)),
                        buffer.len,
                    )
                },
            })
        }
    }

    /// Converts the string buffer into a [`GStr`].
    ///
    /// # Panics
    ///
    /// Calls [`handle_alloc_error`] if fails to shrink the string buffer.
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
    #[inline]
    fn into_gstr(self) -> GStr<SHARED> {
        match self.try_into_gstr() {
            Ok(gstr) => gstr,
            Err(StringBufferError::AllocationFailure(layout)) => handle_alloc_error(layout),
            // SAFETY: `try_into_gstr` doesn't return `StringBufferError::CapacityOverflow` error.
            Err(StringBufferError::CapacityOverflow(_)) => unsafe {
                core::hint::unreachable_unchecked()
            },
        }
    }
}

impl<const SHARED: bool> Drop for StringBuffer<SHARED> {
    #[inline]
    fn drop(&mut self) {
        if self.capacity > 0 {
            // SAFETY:
            // - The pointer returned from `self.memory_ptr()` points the memory which is currently
            //   allocated via the global allocator.
            // - The string buffer's capacity isn't greater than `MAX_CAPACITY`.
            // - `Self::layout(self.capacity)` returns the layout which was used to allocate the
            //   memory.
            unsafe {
                alloc::alloc::dealloc(self.memory_ptr(), Self::layout(self.capacity));
            }
        }
    }
}

impl<const SHARED: bool> FromIterator<char> for StringBuffer<SHARED> {
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (lower_bound, _) = iter.size_hint();
        let mut buffer = Self::with_capacity(lower_bound);
        for ch in iter {
            buffer.push_char(ch);
        }

        buffer
    }
}

/// An immutable string implementation optimized for small strings and comparison.
// NOTE: If the string buffer is heap allocated, it can't be empty.
pub struct GStr<const SHARED: bool> {
    /// The pointer which points to the string buffer.
    ///
    /// If `SHARED` is true and the string buffer is heap-allocated, an [`AtomicUsize`] is stored
    /// before the string buffer.
    ptr: NonNull<u8>,
    /// The prefix buffer and the length of the string buffer.
    prefix_and_len: PrefixAndLength,
}

impl<const SHARED: bool> GStr<SHARED> {
    /// The maximum length of [`GStr`] in bytes.
    pub const MAX_LENGTH: usize = if SHARED {
        GStr::<true>::_MAX_LENGTH
    } else {
        GStr::<false>::_MAX_LENGTH
    };

    /// The empty string of [`GStr`].
    pub const EMPTY: Self = Self::from_static("");

    /// The UTF-8 character used to replace invalid UTF-8 sequences.
    const UTF8_REPLACEMENT: &'static str = "\u{FFFD}";

    /// Returns the layout of a [`GStr`] with the given length.
    ///
    /// If `SHARED` is false, the returned layout's size is `len` and the alignment is 1, otherwise
    /// the returned layout's size is `ATOMIC_SIZE + len` and the alignment is `ATOMIC_ALIGN`.
    ///
    /// # Safety
    ///
    /// `len` must not be greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    #[inline]
    unsafe fn layout(len: usize) -> Layout {
        debug_assert!(len <= Self::MAX_LENGTH);

        if SHARED {
            // SAFETY:
            // - `len` is guaranteed that it isn't greater than `MAX_LENGTH`, so
            //   `ATOMIC_SIZE + len`, when rounded up to the nearest multiple of `ATOMIC_ALIGN`,
            //   can't exceed `isize::MAX`.
            // - `ATOMIC_ALIGN` is the alignment of `AtomicUsize`, so it is greater than zero and
            //   it's a power of two.
            unsafe { Layout::from_size_align_unchecked(ATOMIC_SIZE + len, ATOMIC_ALIGN) }
        } else {
            // SAFETY: `len` is guaranteed that it isn't greater than `MAX_LENGTH`.
            unsafe { Layout::array::<u8>(len).unwrap_unchecked() }
        }
    }

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
        let mut buffer = StringBuffer::<SHARED>::new();
        match buffer.try_push_str(s) {
            Ok(_) => {}
            Err(StringBufferError::CapacityOverflow(len)) => return length_overflow(string, len),
            Err(StringBufferError::AllocationFailure(_)) => return allocation_failure(string),
        }

        match buffer.try_into_gstr() {
            Ok(gstr) => Ok(gstr),
            // SAFETY: `buffer`'s capacity is equal to its length, so it can't be shrinked.
            Err(_) => unsafe { core::hint::unreachable_unchecked() },
        }
    }

    /// Creates a [`GStr`] from a string.
    ///
    /// The string is cloned if it isn't empty, otherwise [`GStr::EMPTY`] is returned.
    ///
    /// # Panics
    ///
    /// - Panics if the length of `string` is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Calls [`handle_alloc_error`] if fails to allocate heap memory.
    ///
    /// # Example
    ///
    /// ```
    /// use gstr::GStr;
    ///
    /// let string = GStr::new("Hello, World!");
    /// assert_eq!(string, "Hello, World!");
    /// ```
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
    #[must_use]
    pub fn new<S: AsRef<str>>(string: S) -> Self {
        match Self::try_new(string) {
            Ok(s) => s,
            Err(e) => match e.kind {
                ErrorKind::LengthOverflow(_) => panic!("{}", e),
                ErrorKind::AllocationFailure(layout) => handle_alloc_error(layout),
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
                // SAFETY: `string.len()` isn't greater than `PrefixAndLength::MAX_LENGTH`.
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

            Self::gstr_try_from_string(s).map_err_source(String::into_bytes)
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
    /// - Calls [`handle_alloc_error`] if fails to allocate memory.
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
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
    #[inline]
    #[must_use]
    pub unsafe fn from_utf8_unchecked(bytes: Vec<u8>) -> Self {
        // SAFETY: `bytes` is guranteed to be a valid UTF-8 sequence.
        unsafe { Self::gstr_from_string(String::from_utf8_unchecked(bytes)) }
    }

    /// Converts a slice of bytes to a [`GStr`], including invalid characters.
    ///
    /// This function will replace any invalid UTF-8 sequences with
    /// [`U+FFFD REPLACEMENT CHARACTER`](core::char::REPLACEMENT_CHARACTER) , which looks like �.
    ///
    /// # Panics
    ///
    /// - Panics if the length of the UTF-8 sequence converted in bytes is greater than
    ///   [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Calls [`handle_alloc_error`] if fails to allocate memory.
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
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
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

        let mut buffer = StringBuffer::<SHARED>::with_capacity(bytes.len());
        buffer.push_str(first_valid);
        buffer.push_str(Self::UTF8_REPLACEMENT);

        for chunk in iter {
            buffer.push_str(chunk.valid());
            if !chunk.invalid().is_empty() {
                buffer.push_str(Self::UTF8_REPLACEMENT);
            }
        }

        buffer.into_gstr()
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
    /// Calls [`handle_alloc_error`] if fails to allocate memory.
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
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
    pub fn from_utf16<B: AsRef<[u16]>>(bytes: B) -> Result<Self, ToGStrError<B>> {
        let b = bytes.as_ref();
        let mut buffer = StringBuffer::<SHARED>::with_capacity(b.len());
        for result in char::decode_utf16(b.iter().copied()) {
            if let Ok(ch) = result {
                if let Err(err) = buffer.try_push_char(ch) {
                    return Err(err.into_gstr_error(bytes));
                }
            } else {
                return Err(ToGStrError::new_invalid_utf16(bytes));
            }
        }

        buffer.try_into_gstr().map_err(|e| e.into_gstr_error(bytes))
    }

    /// Decode a UTF-16–encoded slice into a [`GStr`], replacing invalid data with
    /// [`U+FFFD REPLACEMENT CHARACTER`](core::char::REPLACEMENT_CHARACTER) , which looks like �.
    ///
    /// # Panics
    ///
    /// - Panics if the length in bytes of the UTF-8 sequence converted from the UTF-16 sequence
    ///   is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Calls [`handle_alloc_error`] if fails to allocate memory.
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
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
    #[must_use]
    pub fn from_utf16_lossy<B: AsRef<[u16]>>(bytes: B) -> Self {
        char::decode_utf16(bytes.as_ref().iter().copied())
            .map(|r| r.unwrap_or(char::REPLACEMENT_CHARACTER))
            .collect()
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
    /// - Calls [`handle_alloc_error`] if fails to allocate memory.
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
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
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
    /// - Calls [`handle_alloc_error`] if fails to allocate memory.
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
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
    #[must_use]
    pub fn from_utf16le_lossy<B: AsRef<[u8]>>(bytes: B) -> Self {
        let b = bytes.as_ref();

        // SAFETY: Two `u8`s can be transmuted to a `u16`.
        match (cfg!(target_endian = "little"), unsafe {
            b.align_to::<u16>()
        }) {
            (true, ([], v, [])) => Self::from_utf16_lossy(v),
            (true, ([], v, [_])) => {
                let mut buffer = char::decode_utf16(v.iter().copied())
                    .map(|r| r.unwrap_or(char::REPLACEMENT_CHARACTER))
                    .collect::<StringBuffer<SHARED>>();
                buffer.push_str(Self::UTF8_REPLACEMENT);

                buffer.into_gstr()
            }
            _ => {
                let mut iter = b.chunks_exact(2);
                // SAFETY: a byte slice whose length is 2 can be converted to a `[u8; 2]`;
                let u16_iter = iter.by_ref().map(|s| unsafe {
                    u16::from_le_bytes(<[u8; 2]>::try_from(s).unwrap_unchecked())
                });
                let mut buffer = char::decode_utf16(u16_iter)
                    .map(|r| r.unwrap_or(char::REPLACEMENT_CHARACTER))
                    .collect::<StringBuffer<SHARED>>();

                if iter.remainder().is_empty() {
                    buffer.into_gstr()
                } else {
                    buffer.push_str(Self::UTF8_REPLACEMENT);

                    buffer.into_gstr()
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
    /// - Calls [`handle_alloc_error`] if fails to allocate memory.
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
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
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
    /// - Calls [`handle_alloc_error`] if fails to allocate memory.
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
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
    #[must_use]
    pub fn from_utf16be_lossy<B: AsRef<[u8]>>(bytes: B) -> Self {
        let b = bytes.as_ref();

        // SAFETY: Two `u8`s can be transmuted to a `u16`.
        match (cfg!(target_endian = "big"), unsafe { b.align_to::<u16>() }) {
            (true, ([], v, [])) => Self::from_utf16_lossy(v),
            (true, ([], v, [_])) => {
                let mut buffer = char::decode_utf16(v.iter().copied())
                    .map(|r| r.unwrap_or(char::REPLACEMENT_CHARACTER))
                    .collect::<StringBuffer<SHARED>>();
                buffer.push_str(Self::UTF8_REPLACEMENT);

                buffer.into_gstr()
            }
            _ => {
                let mut iter = b.chunks_exact(2);
                // SAFETY: a byte slice whose length is 2 can be converted to a `[u8; 2]`;
                let u16_iter = iter.by_ref().map(|s| unsafe {
                    u16::from_be_bytes(<[u8; 2]>::try_from(s).unwrap_unchecked())
                });
                let mut buffer = char::decode_utf16(u16_iter)
                    .map(|r| r.unwrap_or(char::REPLACEMENT_CHARACTER))
                    .collect::<StringBuffer<SHARED>>();

                if iter.remainder().is_empty() {
                    buffer.into_gstr()
                } else {
                    buffer.push_str(Self::UTF8_REPLACEMENT);

                    buffer.into_gstr()
                }
            }
        }
    }

    /// Transmutes a [`GStr`] to a [`GStr`] specified by `S`.
    ///
    /// # Panics
    ///
    /// Panics if `S` isn't equal to `SHARED`.
    #[inline]
    fn transmute_from<const S: bool>(gstr: GStr<S>) -> Self {
        if SHARED == S {
            let gstr = ManuallyDrop::new(gstr);

            Self {
                ptr: gstr.ptr,
                prefix_and_len: gstr.prefix_and_len,
            }
        } else {
            panic!("`SHARED` must be equal to `S`")
        }
    }

    /// Creates a [`GStr`] from a [`String`].
    ///
    /// If `SHARED` is false, this doesn't clone the string but shrinks it's capacity to match its
    /// length. And if the string's capacity is equal to its length, no reallocation occurs.
    ///
    /// If the string is empty, [`GStr::EMPTY`] is returned.
    ///
    /// # Errors
    ///
    /// Returns an [`Err`] if the string's length is greater than [`MAX_LENGTH`](Self::MAX_LENGTH)
    /// or allocation failure occurs.
    #[inline]
    pub(crate) fn gstr_try_from_string(string: String) -> Result<Self, ToGStrError<String>> {
        if SHARED {
            Self::try_new(string)
        } else {
            Ok(Self::transmute_from(GStr::<false>::try_from_string(
                string,
            )?))
        }
    }

    /// Creates a [`GStr`] from a [`String`].
    ///
    /// If `SHARED` is false, this doesn't clone the string but shrinks it's capacity to match its
    /// length. And if the string's capacity is equal to its length, no reallocation occurs.
    ///
    /// If the string is empty, [`GStr::EMPTY`] is returned.
    ///
    /// # Panics
    ///
    /// - Panics if the length of `string` is greater than [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Calls [`handle_alloc_error`] if fails to allocate memory.
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
    #[inline]
    fn gstr_from_string(string: String) -> Self {
        match Self::gstr_try_from_string(string) {
            Ok(s) => s,
            Err(e) => match e.kind {
                ErrorKind::LengthOverflow(_) => panic!("{}", e),
                ErrorKind::AllocationFailure(layout) => handle_alloc_error(layout),
                // SAFETY: `GStr::gstr_try_from_string` doesn't return other errors.
                _ => unsafe { core::hint::unreachable_unchecked() },
            },
        }
    }

    /// Transmutes a [`GStr`] to a [`GStr`] specified by `S`.
    ///
    /// # Panics
    ///
    /// Panics if `S` isn't equal to `SHARED`.
    #[inline]
    fn transmute_to<const S: bool>(self) -> GStr<S> {
        if SHARED == S {
            let gstr = ManuallyDrop::new(self);

            GStr::<S> {
                ptr: gstr.ptr,
                prefix_and_len: gstr.prefix_and_len,
            }
        } else {
            panic!("`SHARED` must be equal to `S`")
        }
    }

    /// Converts this [`GStr`] into a [`String`].
    ///
    /// If `SHARED` is false and the string buffer is heap-allocated, no allocation is performed.
    /// Otherwise the string buffer is cloned into a new [`String`].
    ///
    /// # Panics
    ///
    /// Calls [`handle_alloc_error`] if fails to allocate memory.
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
    #[inline]
    pub(crate) fn gstr_into_string(self) -> String {
        if SHARED {
            String::from(self.as_str())
        } else {
            self.transmute_to::<false>().into_string()
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

    /// Return a mutable raw pointer of the allocated memory.
    ///
    /// # Safety
    ///
    /// This [`GStr`] must be heap-allocated.
    #[inline]
    unsafe fn memory_ptr(&mut self) -> *mut u8 {
        debug_assert!(self.is_heap());
        debug_assert!(!self.is_empty());

        if SHARED {
            // SAFETY: If `SHARED` is true, there is an `AtomicUsize` stored before the string
            //         buffer. They are in the same allocated object.
            unsafe { self.ptr.sub(ATOMIC_SIZE).as_ptr() }
        } else {
            self.ptr.as_ptr()
        }
    }

    /// Returns the layout of the allocated memory.
    #[inline]
    fn memory_layout(&self) -> Layout {
        // SAFETY: A `GStr`'s length isn't greater than `MAX_LENGTH`.
        unsafe { Self::layout(self.len()) }
    }

    /// Returns the reference count of this [`GStr`] if `SHARED` is true.
    ///
    /// # Panics
    ///
    /// Panics if `SHARED` is false.
    #[inline]
    fn ref_count(&self) -> &AtomicUsize {
        if SHARED {
            // SAFETY: If `SHARED` is true, there is an `AtomicUsize` placed before the string
            //         buffer. They are in the same allocated object.
            unsafe { &*self.ptr.sub(ATOMIC_SIZE).cast::<AtomicUsize>().as_ptr() }
        } else {
            unreachable!("`ref_count` is only available when `SHARED` is true")
        }
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

    /// Concatenates two strings to a new [`GStr`].
    ///
    /// # Panics
    ///
    /// - Panics if the total length in bytes of `self` and `string` is greater than
    ///   [`MAX_LENGTH`](Self::MAX_LENGTH).
    /// - Calls [`handle_alloc_error`] if fails to allocate memory.
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
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
    #[must_use]
    pub fn concat<S: AsRef<str>>(&self, string: S) -> Self {
        let a = self.as_str();
        let b = string.as_ref();
        let total_len = a.len() + b.len();

        if total_len <= Self::MAX_LENGTH {
            let mut buffer = StringBuffer::<SHARED>::with_capacity(total_len);
            // SAFETY: `buffer`'s capacity isn't less than the length of `a`. This may remove some
            //         branches in `push_str`.
            unsafe {
                core::hint::assert_unchecked(buffer.capacity >= a.len());
            }
            buffer.push_str(a);
            // SAFETY: `buffer`'s remained capacity isn't less than the length of `b`. This may
            //         remove some branches in `push_str`.
            unsafe {
                core::hint::assert_unchecked(buffer.capacity - buffer.len >= b.len());
            }
            buffer.push_str(b);

            buffer.into_gstr()
        } else {
            panic!(
                "The total length in bytes of two strings shouldn't be greater than `GStr`'s max length {}",
                Self::MAX_LENGTH
            );
        }
    }

    /// Compares the prefix buffers.
    #[inline]
    fn prefix_cmp<const S: bool>(&self, other: &GStr<S>) -> Ordering {
        self.prefix_and_len.prefix_cmp(other.prefix_and_len)
    }

    /// Returns whether the prefix buffers and the lengths of two [`GStr`]s are equal.
    #[inline]
    const fn prefix_len_eq<const S: bool>(&self, other: &GStr<S>) -> bool {
        self.prefix_and_len.prefix_len_eq(other.prefix_and_len)
    }
}

impl GStr<false> {
    /// The maximum length of [`GStr`] in bytes.
    const _MAX_LENGTH: usize = PrefixAndLength::MAX_LENGTH;

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
                    //         the length of `string`. This assertion is used to remove some extra
                    //         branches.
                    unsafe {
                        core::hint::assert_unchecked(s.len() == len);
                    }

                    Ok(Self {
                        // SAFETY: The pointer which points to the string buffer is non-null.
                        ptr: unsafe { NonNull::new_unchecked(s.as_mut_ptr()) },
                        // SAFETY: `len` isn't greater than `PrefixAndLength::MAX_LENGTH`.
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
    /// - Calls [`handle_alloc_error`] if fails to shrink `string`'s capacity.
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
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
    #[inline]
    #[must_use]
    pub fn from_string(string: String) -> Self {
        match Self::try_from_string(string) {
            Ok(s) => s,
            Err(e) => match e.kind {
                ErrorKind::LengthOverflow(_) => panic!("{}", e),
                ErrorKind::AllocationFailure(layout) => handle_alloc_error(layout),
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
                // SAFETY: `len` isn't greater than `PrefixAndLength::MAX_LENGTH`.
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
                    // SAFETY: `len` isn't greater than `PrefixAndLength::MAX_LENGTH`.
                    prefix_and_len: unsafe {
                        PrefixAndLength::new_unchecked(copy_prefix(bytes), len)
                    },
                }
            }
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
            // - `string` is heap-allocated.
            // - The memory pointed by `string.memory_ptr()` was allocated by the global allocator
            //   with a alignment of `u8`. And the size of this memory is `len`.
            // - The whole memory is a valid UTF-8 sequence.
            // - The ownership of the memory is transferred to the returned `String`.
            unsafe { Ok(String::from_raw_parts(string.memory_ptr(), len, len)) }
        } else if len == 0 {
            /// Returns the empty string.
            #[cold]
            fn return_empty_string() -> Result<String, GStr<false>> {
                Ok(String::new())
            }

            return_empty_string()
        } else {
            // SAFETY: The size of the string buffer's layout is greater than 0.
            let ptr = unsafe { alloc::alloc::alloc(string.memory_layout()) };

            if ptr.is_null() {
                /// Returns the original [`GStr`].
                #[cold]
                fn return_err(string: ManuallyDrop<GStr<false>>) -> Result<String, GStr<false>> {
                    Err(ManuallyDrop::into_inner(string))
                }

                return_err(string)
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
    /// Calls [`handle_alloc_error`] if fails to allocate memory.
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
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
    #[inline]
    #[must_use]
    pub fn into_string(self) -> String {
        match self.try_into_string() {
            Ok(s) => s,
            Err(s) => handle_alloc_error(s.memory_layout()),
        }
    }

    /// Converts this [`GStr`] into a <code>[Box]<[str]></code>.
    ///
    /// If the string buffer is heap-allocated, no allocation is performed. Otherwise the string
    /// buffer is cloned into a new <code>[Box]<[str]></code>.
    ///
    /// # Panics
    ///
    /// Calls [`handle_alloc_error`] if fails to allocate memory.
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
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
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
    /// Calls [`handle_alloc_error`] if fails to allocate memory.
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
    ///
    /// [`handle_alloc_error`]: alloc::alloc::handle_alloc_error
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
}

impl GStr<true> {
    #[cfg(target_pointer_width = "64")]
    /// The maximum length of [`GStr`] in bytes.
    const _MAX_LENGTH: usize = PrefixAndLength::MAX_LENGTH;

    #[cfg(target_pointer_width = "32")]
    /// The maximum length of [`GStr`] in bytes.
    const _MAX_LENGTH: usize = PrefixAndLength::MAX_LENGTH - (ATOMIC_ALIGN - 1) - ATOMIC_SIZE;
}

impl<const SHARED: bool> Drop for GStr<SHARED> {
    #[inline]
    fn drop(&mut self) {
        if self.is_heap() {
            debug_assert!(!self.is_empty());

            if SHARED {
                // We must make sure that nothing can access this `GStr`'s memory when dropping it,
                // so `Ordering::Release` and `Ordering::Acquire` are used here.
                if self.ref_count().fetch_sub(1, atomic::Ordering::Release) == 1 {
                    atomic::fence(atomic::Ordering::Acquire);

                    // SAFETY:
                    // - The string buffer is heap-allocated.
                    // - `self.memory_ptr()` points to a memory allocated by the global allocator
                    //   with the layout returned from `memory_layout`. The reference count is 1,
                    //   so this `GStr` owns the memory.
                    unsafe {
                        alloc::alloc::dealloc(self.memory_ptr(), self.memory_layout());
                    }
                }
            } else {
                // SAFETY:
                // - The string buffer is heap-allocated.
                // - `self.memory_ptr()` points to a memory allocated by the global allocator with
                //   the string buffer's layout.
                unsafe {
                    alloc::alloc::dealloc(self.memory_ptr(), self.memory_layout());
                }
            }
        }
    }
}

impl<const SHARED: bool> AsRef<str> for GStr<SHARED> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<const SHARED: bool> Deref for GStr<SHARED> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<const SHARED: bool> Borrow<str> for GStr<SHARED> {
    #[inline]
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl<const SHARED: bool> fmt::Debug for GStr<SHARED> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("GStr")
            .field("shared", &SHARED)
            .field("is_static", &self.is_static())
            .field("len", &self.len())
            .field("prefix", &self.prefix())
            .field("str", &self.as_str())
            .finish()
    }
}

impl<const SHARED: bool> fmt::Display for GStr<SHARED> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl<const SHARED: bool> Clone for GStr<SHARED> {
    #[inline]
    fn clone(&self) -> Self {
        if self.is_heap() {
            // SAFETY: The string isn't empty if it's heap allocated. This assertion can remove some
            //         branches.
            unsafe {
                core::hint::assert_unchecked(!self.is_empty());
            }

            if SHARED {
                // We have accessed this `GStr`, its refernece count is greater than zero, so its
                // memory can't be deallocated, using `Ordering::Relaxed` is safe here.
                if self.ref_count().fetch_add(1, atomic::Ordering::Relaxed) > isize::MAX as usize {
                    // If the reference count is greater than `isize::MAX`, aborts the program.
                    #[cfg(feature = "std")]
                    {
                        extern crate std;

                        std::process::abort();
                    }

                    #[cfg(not(feature = "std"))]
                    {
                        panic!("the reference count of `GStr` is greater than `isize::MAX`");
                    }
                }

                Self {
                    ptr: self.ptr,
                    prefix_and_len: self.prefix_and_len,
                }
            } else {
                match Self::try_new(self) {
                    Ok(s) => s,
                    Err(e) => match e.kind {
                        ErrorKind::AllocationFailure(layout) => handle_alloc_error(layout),
                        // SAFETY:
                        // - A `GStr`'s length isn't greater than `GStr::MAX_LENGTH`.
                        // - `GStr::try_new` doesn't return other errors.
                        _ => unsafe { core::hint::unreachable_unchecked() },
                    },
                }
            }
        } else {
            Self {
                ptr: self.ptr,
                prefix_and_len: self.prefix_and_len,
            }
        }
    }
}

impl<const SHARED: bool> Default for GStr<SHARED> {
    #[inline]
    fn default() -> Self {
        Self::EMPTY
    }
}

impl<const S1: bool, const S2: bool> PartialEq<GStr<S2>> for GStr<S1> {
    #[inline]
    fn eq(&self, other: &GStr<S2>) -> bool {
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

impl<const SHARED: bool> Eq for GStr<SHARED> {}

impl<const S1: bool, const S2: bool> PartialOrd<GStr<S2>> for GStr<S1> {
    #[inline]
    fn partial_cmp(&self, other: &GStr<S2>) -> Option<Ordering> {
        Some(match self.prefix_cmp(other) {
            Ordering::Equal => self.as_bytes().cmp(other.as_bytes()),
            not_eq => not_eq,
        })
    }
}

impl<const SHARED: bool> Ord for GStr<SHARED> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match self.prefix_cmp(other) {
            Ordering::Equal => self.as_bytes().cmp(other.as_bytes()),
            not_eq => not_eq,
        }
    }
}

impl<const SHARED: bool> Hash for GStr<SHARED> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl<const SHARED: bool> FromStr for GStr<SHARED> {
    type Err = ToGStrError<()>;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_new(s).map_err_source(|_| {})
    }
}

impl<I: SliceIndex<str>, const SHARED: bool> Index<I> for GStr<SHARED> {
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        self.as_str().index(index)
    }
}

// SAFETY: A `GStr` can be transferred across different threads.
unsafe impl<const SHARED: bool> Send for GStr<SHARED> {}

// SAFETY: A `GStr` is immutable, so it's safe to share references between threads.
unsafe impl<const SHARED: bool> Sync for GStr<SHARED> {}

impl<const SHARED: bool> AsRef<[u8]> for GStr<SHARED> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<T: ?Sized, const SHARED: bool> PartialEq<&'_ T> for GStr<SHARED>
where
    Self: PartialEq<T>,
{
    #[inline]
    fn eq(&self, other: &&'_ T) -> bool {
        PartialEq::<T>::eq(self, *other)
    }
}

impl<const SHARED: bool> PartialEq<str> for GStr<SHARED> {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl<const SHARED: bool> PartialEq<GStr<SHARED>> for str {
    #[inline]
    fn eq(&self, other: &GStr<SHARED>) -> bool {
        self == other.as_str()
    }
}

impl<const SHARED: bool> PartialEq<GStr<SHARED>> for &'_ str {
    #[inline]
    fn eq(&self, other: &GStr<SHARED>) -> bool {
        *self == other
    }
}

impl<const SHARED: bool> PartialEq<String> for GStr<SHARED> {
    #[inline]
    fn eq(&self, other: &String) -> bool {
        self == other.as_str()
    }
}

impl<const SHARED: bool> PartialEq<GStr<SHARED>> for String {
    #[inline]
    fn eq(&self, other: &GStr<SHARED>) -> bool {
        self.as_str() == other
    }
}

impl<const SHARED: bool> PartialEq<GStr<SHARED>> for &'_ String {
    #[inline]
    fn eq(&self, other: &GStr<SHARED>) -> bool {
        self.as_str() == other
    }
}

impl<const SHARED: bool> PartialEq<Cow<'_, str>> for GStr<SHARED> {
    #[inline]
    fn eq(&self, other: &Cow<'_, str>) -> bool {
        self == other.as_ref()
    }
}

impl<const SHARED: bool> PartialEq<GStr<SHARED>> for Cow<'_, str> {
    #[inline]
    fn eq(&self, other: &GStr<SHARED>) -> bool {
        self.as_ref() == other
    }
}

impl<T: ?Sized, const SHARED: bool> PartialOrd<&'_ T> for GStr<SHARED>
where
    Self: PartialOrd<T>,
{
    #[inline]
    fn partial_cmp(&self, other: &&'_ T) -> Option<Ordering> {
        PartialOrd::<T>::partial_cmp(self, *other)
    }
}

impl<const SHARED: bool> PartialOrd<str> for GStr<SHARED> {
    #[inline]
    fn partial_cmp(&self, other: &str) -> Option<Ordering> {
        self.as_str().partial_cmp(other)
    }
}

impl<const SHARED: bool> PartialOrd<GStr<SHARED>> for str {
    #[inline]
    fn partial_cmp(&self, other: &GStr<SHARED>) -> Option<Ordering> {
        self.partial_cmp(other.as_str())
    }
}

impl<const SHARED: bool> PartialOrd<GStr<SHARED>> for &'_ str {
    #[inline]
    fn partial_cmp(&self, other: &GStr<SHARED>) -> Option<Ordering> {
        (*self).partial_cmp(other)
    }
}

impl<const SHARED: bool> PartialOrd<String> for GStr<SHARED> {
    #[inline]
    fn partial_cmp(&self, other: &String) -> Option<Ordering> {
        self.partial_cmp(other.as_str())
    }
}

impl<const SHARED: bool> PartialOrd<GStr<SHARED>> for String {
    #[inline]
    fn partial_cmp(&self, other: &GStr<SHARED>) -> Option<Ordering> {
        self.as_str().partial_cmp(other)
    }
}

impl<const SHARED: bool> PartialOrd<GStr<SHARED>> for &'_ String {
    #[inline]
    fn partial_cmp(&self, other: &GStr<SHARED>) -> Option<Ordering> {
        self.as_str().partial_cmp(other)
    }
}

impl<const SHARED: bool> From<char> for GStr<SHARED> {
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
                ErrorKind::AllocationFailure(layout) => handle_alloc_error(layout),
                // SAFETY:
                // - The max length in bytes of a single UTF-8 character is 4.
                // - `GStr::try_new` doesn't return other errors.
                _ => unsafe { core::hint::unreachable_unchecked() },
            },
        }
    }
}

impl<const SHARED: bool> From<&GStr<SHARED>> for GStr<SHARED> {
    #[inline]
    fn from(string: &GStr<SHARED>) -> Self {
        string.clone()
    }
}

impl<'a, const SHARED: bool> TryFrom<&'a str> for GStr<SHARED> {
    type Error = ToGStrError<&'a str>;

    /// Converts a `&str` into a [`GStr`].
    ///
    /// This clones the string.
    #[inline]
    fn try_from(string: &'a str) -> Result<Self, Self::Error> {
        Self::try_new(string)
    }
}

/* impl<'a, const SHARED: bool> TryFrom<&'a mut str> for GStr<SHARED> {
    type Error = ToGStrError<&'a mut str>;

    /// Converts a `&mut str` into a [`GStr`].
    ///
    /// This clones the string.
    #[inline]
    fn try_from(string: &'a mut str) -> Result<Self, Self::Error> {
        Self::try_new(string)
    }
} */

impl<const SHARED: bool> TryFrom<String> for GStr<SHARED> {
    type Error = ToGStrError<String>;

    /// Converts a [`String`] into a [`GStr`].
    ///
    /// If `SHARED` is false, this doesn't clone the string but shrinks it's capacity to match its
    /// length.
    #[inline]
    fn try_from(string: String) -> Result<Self, Self::Error> {
        Self::gstr_try_from_string(string)
    }
}

impl<'a, const SHARED: bool> TryFrom<&'a String> for GStr<SHARED> {
    type Error = ToGStrError<&'a String>;

    /// Converts a `&String` into a [`GStr`].
    ///
    /// This clones the string.
    #[inline]
    fn try_from(string: &'a String) -> Result<Self, Self::Error> {
        Self::try_new(string)
    }
}

impl<const SHARED: bool> TryFrom<Box<str>> for GStr<SHARED> {
    type Error = ToGStrError<Box<str>>;

    /// Converts a `Box<str>` into a [`GStr`].
    ///
    /// If `SHARED` is false, this doesn't clone the string.
    #[inline]
    fn try_from(string: Box<str>) -> Result<Self, Self::Error> {
        let string = string.into_string();

        Self::gstr_try_from_string(string).map_err_source(String::into_boxed_str)
    }
}

impl<'a, const SHARED: bool> TryFrom<Cow<'a, str>> for GStr<SHARED> {
    type Error = ToGStrError<Cow<'a, str>>;

    /// Converts a `Cow<str>` into a [`GStr`].
    ///
    /// If the string is owned and `SHARED` is false, this doesn't clone the string but shrinks it's
    /// capacity to match its length. Otherwise it clones the string.
    #[inline]
    fn try_from(string: Cow<'a, str>) -> Result<Self, Self::Error> {
        match string {
            Cow::Borrowed(s) => Self::try_new(s).map_err_source(Cow::Borrowed),
            Cow::Owned(s) => Self::gstr_try_from_string(s).map_err_source(Cow::Owned),
        }
    }
}

impl<'a, const SHARED: bool> From<&'a GStr<SHARED>> for &'a [u8] {
    #[inline]
    fn from(string: &'a GStr<SHARED>) -> Self {
        string.as_bytes()
    }
}

impl<'a, const SHARED: bool> From<&'a GStr<SHARED>> for &'a str {
    #[inline]
    fn from(string: &'a GStr<SHARED>) -> Self {
        string.as_str()
    }
}

impl<const SHARED: bool> From<GStr<SHARED>> for String {
    #[inline]
    fn from(string: GStr<SHARED>) -> Self {
        string.gstr_into_string()
    }
}

impl<const SHARED: bool> From<GStr<SHARED>> for Vec<u8> {
    #[inline]
    fn from(string: GStr<SHARED>) -> Self {
        string.gstr_into_string().into_bytes()
    }
}

impl<const SHARED: bool> From<GStr<SHARED>> for Box<str> {
    #[inline]
    fn from(string: GStr<SHARED>) -> Self {
        string.gstr_into_string().into_boxed_str()
    }
}

impl<const SHARED: bool> From<GStr<SHARED>> for Cow<'_, str> {
    #[inline]
    fn from(string: GStr<SHARED>) -> Self {
        Self::Owned(string.gstr_into_string())
    }
}

impl<'a, const SHARED: bool> From<&'a GStr<SHARED>> for Cow<'a, str> {
    #[inline]
    fn from(string: &'a GStr<SHARED>) -> Self {
        Self::Borrowed(string.as_str())
    }
}

impl<const SHARED: bool> From<GStr<SHARED>> for Rc<str> {
    #[inline]
    fn from(string: GStr<SHARED>) -> Self {
        Self::from(string.as_str())
    }
}

impl<const SHARED: bool> From<GStr<SHARED>> for Arc<str> {
    #[inline]
    fn from(string: GStr<SHARED>) -> Self {
        Self::from(string.as_str())
    }
}

impl<const SHARED: bool> From<GStr<SHARED>> for Box<dyn Error + Send + Sync + '_> {
    #[inline]
    fn from(string: GStr<SHARED>) -> Self {
        struct StringError<const SHARED: bool>(GStr<SHARED>);

        impl<const SHARED: bool> fmt::Debug for StringError<SHARED> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Debug::fmt(&self.0, f)
            }
        }

        impl<const SHARED: bool> fmt::Display for StringError<SHARED> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(&self.0, f)
            }
        }

        impl<const SHARED: bool> Error for StringError<SHARED> {}

        Box::new(StringError(string))
    }
}

impl<const SHARED: bool> From<GStr<SHARED>> for Box<dyn Error + '_> {
    #[inline]
    fn from(string: GStr<SHARED>) -> Self {
        let err1: Box<dyn Error + Send + Sync> = From::from(string);
        let err2: Box<dyn Error> = err1;

        err2
    }
}

impl<const SHARED: bool> FromIterator<char> for GStr<SHARED> {
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        StringBuffer::<SHARED>::from_iter(iter).into_gstr()
    }
}

impl<'a, const SHARED: bool> FromIterator<&'a char> for GStr<SHARED> {
    fn from_iter<T: IntoIterator<Item = &'a char>>(iter: T) -> Self {
        Self::from_iter(iter.into_iter().copied())
    }
}

fn from_str_iter<I, T, const SHARED: bool>(iter: I) -> GStr<SHARED>
where
    I: IntoIterator<Item = T>,
    T: AsRef<str>,
{
    let mut buffer = StringBuffer::<SHARED>::new();
    for item in iter {
        buffer.push_str(item.as_ref());
    }

    buffer.into_gstr()
}

impl<'a, const SHARED: bool> FromIterator<&'a str> for GStr<SHARED> {
    fn from_iter<T: IntoIterator<Item = &'a str>>(iter: T) -> Self {
        from_str_iter(iter)
    }
}

impl<const SHARED: bool> FromIterator<String> for GStr<SHARED> {
    fn from_iter<T: IntoIterator<Item = String>>(iter: T) -> Self {
        from_str_iter(iter)
    }
}

impl<const SHARED: bool> FromIterator<Box<str>> for GStr<SHARED> {
    fn from_iter<T: IntoIterator<Item = Box<str>>>(iter: T) -> Self {
        from_str_iter(iter)
    }
}

impl<'a, const SHARED: bool> FromIterator<Cow<'a, str>> for GStr<SHARED> {
    fn from_iter<T: IntoIterator<Item = Cow<'a, str>>>(iter: T) -> Self {
        from_str_iter(iter)
    }
}

impl<const S1: bool, const S2: bool> FromIterator<GStr<S2>> for GStr<S1> {
    fn from_iter<T: IntoIterator<Item = GStr<S2>>>(iter: T) -> Self {
        from_str_iter(iter)
    }
}

impl<const SHARED: bool> FromIterator<GStr<SHARED>> for String {
    fn from_iter<T: IntoIterator<Item = GStr<SHARED>>>(iter: T) -> Self {
        let mut string = String::new();
        for s in iter {
            string.push_str(s.as_str());
        }

        string
    }
}

impl<const SHARED: bool> FromIterator<GStr<SHARED>> for Box<str> {
    fn from_iter<T: IntoIterator<Item = GStr<SHARED>>>(iter: T) -> Self {
        String::from_iter(iter).into_boxed_str()
    }
}

impl<const SHARED: bool> FromIterator<GStr<SHARED>> for Cow<'_, str> {
    fn from_iter<T: IntoIterator<Item = GStr<SHARED>>>(iter: T) -> Self {
        Cow::Owned(String::from_iter(iter))
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
    debug_assert!(!string.is_empty() && string.len() <= GStr::<false>::MAX_LENGTH);

    if string.len() == string.capacity() {
        Ok(string.leak())
    } else {
        debug_assert!(string.capacity() > string.len());

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
}

/// Returns an empty [`GStr`].
#[cold]
const fn empty_gstr<const SHARED: bool>() -> GStr<SHARED> {
    GStr::<SHARED>::EMPTY
}

/// Returns an allocation failure error.
#[cold]
fn allocation_failure<S: AsRef<str>, const SHARED: bool>(
    string: S,
) -> Result<GStr<SHARED>, ToGStrError<S>> {
    // SAFETY: The layout of `string` is valid.
    let layout = unsafe { Layout::array::<u8>(string.as_ref().len()).unwrap_unchecked() };

    Err(ToGStrError::new_allocation_failure(string, layout))
}

/// Returns a length overflow error.
#[cold]
fn length_overflow<S, const SHARED: bool>(
    string: S,
    len: usize,
) -> Result<GStr<SHARED>, ToGStrError<S>> {
    Err(ToGStrError::new_length_overflow(string, len))
}

/// Handles the memory allocation error.
///
/// For more details, see [`handle_alloc_error`](alloc::alloc::handle_alloc_error).
#[cold]
pub(crate) fn handle_alloc_error(layout: Layout) -> ! {
    alloc::alloc::handle_alloc_error(layout)
}

const _: () = {
    assert!(size_of::<PrefixAndLength>() == size_of::<u64>());
    assert!(align_of::<PrefixAndLength>() == align_of::<usize>());

    #[cfg(target_pointer_width = "64")]
    {
        assert!(size_of::<GStr<false>>() == 4 * size_of::<u32>());
        assert!(size_of::<GStr<true>>() == 4 * size_of::<u32>());
        assert!(size_of::<Option<GStr<false>>>() == 4 * size_of::<u32>());
        assert!(size_of::<Option<GStr<true>>>() == 4 * size_of::<u32>());

        assert!(PrefixAndLength::HALF_BITS == 32);
        assert!(PrefixAndLength::PREFIX_MASK == 0xFFFF_FFFF_0000_0000);
        assert!(PrefixAndLength::LEN_PREFIX_MASK == 0xFFFF_FFFF_7FFF_FFFF);

        assert!(GStr::<true>::_MAX_LENGTH == PrefixAndLength::MAX_LENGTH);
        assert!(
            GStr::<true>::_MAX_LENGTH + ATOMIC_SIZE <= isize::MAX as usize - (ATOMIC_ALIGN - 1)
        );
    }

    #[cfg(target_pointer_width = "32")]
    {
        assert!(size_of::<GStrr<false>>() == 3 * size_of::<u32>());
        assert!(size_of::<GStr<true>>() == 3 * size_of::<u32>());
        assert!(size_of::<Option<GStrr<false>>>() == 3 * size_of::<u32>());
        assert!(size_of::<Option<GStr<true>>>() == 3 * size_of::<u32>());

        assert!(GStr::<true>::_MAX_LENGTH == PrefixAndLength::MAX_LENGTH - 7);
        assert!(
            GStr::<true>::_MAX_LENGTH + ATOMIC_SIZE <= isize::MAX as usize - (ATOMIC_ALIGN - 1)
        );
    }

    assert!(align_of::<GStr<false>>() == align_of::<usize>());
    assert!(align_of::<GStr<true>>() == align_of::<usize>());

    assert!(PrefixAndLength::PREFIX_LENGTH == 4);
    assert!(PrefixAndLength::LENGTH_BITS == 31);
    assert!(PrefixAndLength::STATIC_MASK == 0x8000_0000);
    assert!(PrefixAndLength::LENGTH_MASK == 0x7FFF_FFFF);
    assert!(PrefixAndLength::MAX_LENGTH == 0x7FFF_FFFF);

    assert!(GStr::<false>::_MAX_LENGTH == PrefixAndLength::MAX_LENGTH);
    assert!(GStr::<false>::_MAX_LENGTH <= isize::MAX as _);

    assert!(GStr::<false>::MAX_LENGTH <= PrefixAndLength::MAX_LENGTH);
    assert!(GStr::<true>::MAX_LENGTH <= PrefixAndLength::MAX_LENGTH);
    assert!(GStr::<false>::MAX_LENGTH == GStr::<false>::_MAX_LENGTH);
    assert!(GStr::<true>::MAX_LENGTH == GStr::<true>::_MAX_LENGTH);
    assert!(GStr::<false>::MAX_LENGTH == StringBuffer::<false>::MAX_CAPACITY);
    assert!(GStr::<true>::MAX_LENGTH == StringBuffer::<true>::MAX_CAPACITY);
};

#[cfg(test)]
mod tests {
    use super::*;

    use alloc::format;
    #[cfg(any(not(miri), feature = "proptest_miri"))]
    use proptest::prelude::*;

    //extern crate std;

    /* fn transmute_gstr<const S1: bool, const S2: bool>(gstr: &GStr<S1>) -> &GStr<S2> {
        if S1 == S2 {
            &GStr::<S2> {
                ptr: gstr.ptr,
                prefix_and_len: gstr.prefix_and_len,
            }
        } else {
            panic!("")
        }
    } */

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

    fn test_gstr_is_eq<const SHARED: bool>(a: &GStr<SHARED>, b: &str) {
        assert_eq!(a.len(), b.len());
        assert_eq!(a, b);
        assert_eq!(b, a);
        assert_eq!(a.cmp(a), Ordering::Equal);
        assert_eq!(a.partial_cmp(a), Some(Ordering::Equal));
        assert_eq!(a.partial_cmp(b), Some(Ordering::Equal));
        assert_eq!(b.partial_cmp(a), Some(Ordering::Equal));

        let c = GStr::<SHARED>::new(b);
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

    fn test_gstr_concat<const SHARED: bool>(gstr: &GStr<SHARED>, string: &str) {
        assert_eq!(gstr.concat(""), gstr);
        assert_eq!(gstr.concat("foo"), format!("{}{}", gstr, "foo"));
        assert_eq!(gstr.concat(string), format!("{}{}", gstr, string));
    }

    fn test_gstr_raw_parts(gstr: GStr<false>, string: &str) {
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

    fn test_gstr_into_string(gstr: GStr<false>, string: &str) {
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

    fn test_gstr_new<const SHARED: bool>(string: &str) {
        let gstr = GStr::<SHARED>::new(string);

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
        if !SHARED {
            test_gstr_raw_parts(gstr.clone().transmute_to::<false>(), string);
            test_gstr_into_string(gstr.transmute_to::<false>(), string);
        }
    }

    fn test_gstr_from_static<const SHARED: bool>(string: &'static str) {
        let gstr = GStr::<SHARED>::from_static(string);

        assert!(gstr.is_static());
        assert!(!gstr.is_heap());
        assert_eq!(gstr.as_static_str(), Some(string));

        test_gstr_is_eq(&gstr, string);
        test_gstr_concat(&gstr, string);
        if !SHARED {
            test_gstr_raw_parts(gstr.clone().transmute_to::<false>(), string);
            test_gstr_into_string(gstr.transmute_to::<false>(), string);
        }
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

    fn test_gstr_eq_cmp<const S1: bool, const S2: bool>(a: &str, b: &str) {
        let gstr_a = GStr::<S1>::new(a);
        let gstr_b = GStr::<S2>::new(b);

        assert_eq!(gstr_a > gstr_b, a > b);
        assert_eq!(gstr_a < gstr_b, a < b);
        assert_eq!(gstr_a == gstr_b, a == b);
        assert_eq!(gstr_a >= gstr_b, a >= b);
        assert_eq!(gstr_a <= gstr_b, a <= b);
        if S1 == S2 {
            assert_eq!(gstr_a.cmp(&gstr_b.clone().transmute_to::<S1>()), a.cmp(b));
        }
        assert_eq!(gstr_a.partial_cmp(&gstr_b), a.partial_cmp(b));

        assert_eq!(gstr_b > gstr_a, b > a);
        assert_eq!(gstr_b < gstr_a, b < a);
        assert_eq!(gstr_b == gstr_a, b == a);
        assert_eq!(gstr_b >= gstr_a, b >= a);
        assert_eq!(gstr_b <= gstr_a, b <= a);
        if S1 == S2 {
            assert_eq!(gstr_b.cmp(&gstr_a.clone().transmute_to::<S2>()), b.cmp(a));
        }
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

    fn gstr_eq_cmp_all(a: &str, b: &str) {
        test_gstr_eq_cmp::<false, false>(a, b);
        test_gstr_eq_cmp::<false, true>(a, b);
        test_gstr_eq_cmp::<true, true>(a, b);
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    fn test_gstr_valid_utf8<const SHARED: bool>(string: String) {
        let gstr = GStr::<SHARED>::from_utf8(string.clone().into_bytes()).unwrap();
        assert_eq!(gstr, string);

        let gstr = GStr::<SHARED>::from_utf8_lossy(string.clone().into_bytes());
        assert_eq!(gstr, string);

        // SAFETY: `string` is valid UTF-8.
        let gstr = unsafe { GStr::<SHARED>::from_utf8_unchecked(string.clone().into_bytes()) };
        assert_eq!(gstr, string);
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    fn test_gstr_utf8_bytes<const SHARED: bool>(bytes: Vec<u8>) {
        let gstr = GStr::<SHARED>::from_utf8(bytes.clone());
        let string = String::from_utf8(bytes.clone());
        if let Ok(string) = string {
            assert_eq!(string, gstr.unwrap());

            // SAFETY: `bytes` is valid UTF-8.
            let gstr = unsafe { GStr::<SHARED>::from_utf8_unchecked(bytes.clone()) };
            assert_eq!(gstr, string);
        } else {
            let err = gstr.unwrap_err();
            assert!(matches!(err.error_kind(), ErrorKind::Utf8Error(_)));
            assert_eq!(err.into_source(), bytes);
        }

        let gstr = GStr::<SHARED>::from_utf8_lossy(bytes.clone());
        let string = String::from_utf8_lossy(&bytes);
        assert_eq!(gstr, string);
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    fn test_gstr_valid_utf16<const SHARED: bool>(string: String) {
        let bytes = string.encode_utf16().collect::<Vec<_>>();
        let gstr = GStr::<SHARED>::from_utf16(&bytes).unwrap();
        assert_eq!(gstr, string);

        let gstr = GStr::<SHARED>::from_utf16_lossy(&bytes);
        assert_eq!(gstr, string);

        let utf16_le = bytes
            .iter()
            .flat_map(|n| n.to_le_bytes())
            .collect::<Vec<_>>();
        let gstr = GStr::<SHARED>::from_utf16le(&utf16_le).unwrap();
        assert_eq!(gstr, string);
        let gstr = GStr::<SHARED>::from_utf16le_lossy(&utf16_le);
        assert_eq!(gstr, string);

        let utf16_be = bytes
            .iter()
            .flat_map(|n| n.to_be_bytes())
            .collect::<Vec<_>>();
        let gstr = GStr::<SHARED>::from_utf16be(&utf16_be).unwrap();
        assert_eq!(gstr, string);
        let gstr = GStr::<SHARED>::from_utf16be_lossy(&utf16_be);
        assert_eq!(gstr, string);
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    fn test_gstr_utf16_u16_bytes<const SHARED: bool>(bytes: Vec<u16>) {
        let gstr = GStr::<SHARED>::from_utf16(&bytes);
        let string = String::from_utf16(&bytes);
        if let Ok(string) = string {
            assert_eq!(string, gstr.unwrap());
        } else {
            let err = gstr.unwrap_err();
            assert!(matches!(err.error_kind(), ErrorKind::InvalidUtf16));
            assert_eq!(err.into_source(), &bytes);
        }

        let gstr = GStr::<SHARED>::from_utf16_lossy(&bytes);
        let string = String::from_utf16_lossy(&bytes);
        assert_eq!(gstr, string);
    }

    #[cfg(feature = "nightly_test")]
    fn test_gstr_utf16_u8_bytes<const SHARED: bool>(bytes: Vec<u8>) {
        let string = String::from_utf16le(&bytes);
        let gstr = GStr::<SHARED>::from_utf16le(&bytes);
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
        let gstr = GStr::<SHARED>::from_utf16le_lossy(&bytes);
        assert_eq!(string, gstr);

        let string = String::from_utf16be(&bytes);
        let gstr = GStr::<SHARED>::from_utf16be(&bytes);
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
        let gstr = GStr::<SHARED>::from_utf16be_lossy(&bytes);
        assert_eq!(string, gstr);
    }

    #[test]
    fn gstr_new() {
        test_literal_strings(test_gstr_new::<false>);
        test_literal_strings(test_gstr_new::<true>);
    }

    #[test]
    fn gstr_from_static() {
        test_literal_strings(test_gstr_from_static::<false>);
        test_literal_strings(test_gstr_from_static::<true>);
    }

    #[test]
    fn gstr_from_string() {
        test_literal_strings(test_gstr_from_string);
    }

    #[test]
    fn gstr_eq_cmp() {
        gstr_eq_cmp_all("", "");
        gstr_eq_cmp_all("", "a");
        gstr_eq_cmp_all("", "abcdefghijklm");
        gstr_eq_cmp_all("ab", "ab");
        gstr_eq_cmp_all("ab", "ac");
        gstr_eq_cmp_all("ab", "bd");
        gstr_eq_cmp_all("ab", "abc");
        gstr_eq_cmp_all("ab", "abcdefghijklm");
        gstr_eq_cmp_all("ab", "hello, 🦀 and 🌎!");
        gstr_eq_cmp_all("abcdefghijklm", "abcdefghijklm");
        gstr_eq_cmp_all("abcdefghijklm", "abcdefghijkln");
        gstr_eq_cmp_all("abcdefghijklm", "nopqrstuvwxyz");
        gstr_eq_cmp_all("abcdefghijklm", "abcdefghijklmn");
        gstr_eq_cmp_all("abcdefghijklm", "hello, 🦀 and 🌎!");
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
            test_gstr_new::<false>(&string);
            test_gstr_new::<true>(&string);
        }
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    proptest! {
        #[test]
        fn prop_gstr_from_static(string: String) {
            string_to_static(string.clone(), test_gstr_from_static::<false>);
            string_to_static(string, test_gstr_from_static::<true>);
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
            gstr_eq_cmp_all(&a, &b);
        }
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    proptest! {
        #[test]
        fn prop_gstr_valid_utf8(string: String) {
            test_gstr_valid_utf8::<false>(string.clone());
            test_gstr_valid_utf8::<true>(string);
        }
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    proptest! {
        #[test]
        fn prop_gstr_utf8_bytes(bytes: Vec<u8>) {
            test_gstr_utf8_bytes::<false>(bytes.clone());
            test_gstr_utf8_bytes::<true>(bytes);
        }
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    proptest! {
        #[test]
        fn prop_gstr_valid_utf16(string: String) {
            test_gstr_valid_utf16::<false>(string.clone());
            test_gstr_valid_utf16::<true>(string);
        }
    }

    #[cfg(any(not(miri), feature = "proptest_miri"))]
    proptest! {
        #[test]
        fn prop_gstr_utf16_u16_bytes(bytes: Vec<u16>) {
            test_gstr_utf16_u16_bytes::<false>(bytes.clone());
            test_gstr_utf16_u16_bytes::<true>(bytes);
        }
    }

    #[cfg(feature = "nightly_test")]
    proptest! {
        #[test]
        fn prop_gstr_utf16_u8_bytes(bytes: Vec<u8>) {
            test_gstr_utf16_u8_bytes::<false>(bytes.clone());
            test_gstr_utf16_u8_bytes::<true>(bytes);
        }
    }
}
