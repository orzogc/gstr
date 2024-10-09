# gstr

## GStr

`GStr` is an immutable string implementation optimized for small strings and comparison.

The size of `GStr` or `Option<GStr>` is guaranteed to be 16 bytes on 64-bit platforms or 12 bytes on 32-bit platforms.

The first 4 bytes of the string buffer are inlined in `GStr`, so comparing two `GStr`s is faster than comparing two [`str`](https://doc.rust-lang.org/core/primitive.str.html)s in most cases.

The maximum length of `GStr` is [`i32::MAX`](https://doc.rust-lang.org/core/primitive.i32.html#associatedconstant.MAX).

## SharedGStr

`SharedGStr` is similar to `GStr`, but using the atomic reference counting internally, so cloning a `SharedGStr` only takes `O(1)` time.

The maximum length of `SharedGStr` is [`i32::MAX`](https://doc.rust-lang.org/core/primitive.i32.html#associatedconstant.MAX) on 64-bit platforms or `i32::MAX - 7` on 32-bit platforms.

## Usage

```rust
use gstr::GStr;

// This clones the string into the heap memory.
let gstr = GStr::new("Hello, World!");
assert_eq!(gstr, "Hello, World!");

// `GStr` can be constructed from a static string in const context without allocating memory.
let gstr = const { GStr::from_static("Hello, Rust!") };
assert_eq!(gstr, "Hello, Rust!");

// `GStr` can be converted from `String` without allocating memory.
let gstr = GStr::from_string(String::from("Hello, 🦀 and 🌎!"));
assert_eq!(gstr, "Hello, 🦀 and 🌎!");
```

## Features

`gstr` supports `no_std`, but needs the [`alloc`](https://doc.rust-lang.org/alloc/index.html) crate to work.

`gstr` has the following features:

- `std`: Enable support for some types in [`std`](https://doc.rust-lang.org/std/index.html). It's enabled by default.
- `serde`: Enable serialization and deserialization support for [`serde`](https://crates.io/crates/serde).
- `rkyv`: Enable serialization and deserialization support for [`rkyv`](https://crates.io/crates/rkyv).

## Warnings

`gstr` is not tested on big-endian platforms, but it maybe works fine on them.
