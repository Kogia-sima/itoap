//! This crate provides even faster functions for printing integers with decimal format
//! than [itoa](https://crates.io/crates/itoa) crate.
//!
//! If you want to write integers in decimal format to `String`, `Vec` or any other
//! contiguous buffer, then this crate is the best choice.
//!
//! If you want to write integers to a `std::io::Write` or `std::fmt::Write`,
//! [itoa](https://github.com/dtolnay/itoa) crate and `itoap` crate shows almost same
//! performance.
//!
//! The implementation is based on the `sse2` algorithm from
//! [itoa-benchmark](https://github.com/miloyip/itoa-benchmark) repository.
//! While `itoa` crate writes integers from **last** digits, this algorithm writes
//! from **first** digits. It allows integers to be written directly to the buffer.
//! That's why `itoap` is faster than `itoa`.
//!
//! # Feature Flags
//!
//! - `alloc`: use [alloc](https://doc.rust-lang.org/alloc/) crate (enabled by default)
//! - `std`: use [std](https://doc.rust-lang.org/std/) crate (enabled by default)
//! - `simd`: use SIMD intrinsics if available
//!
//! # Examples
//!
//! ```
//! # #[cfg(feature = "std")] {
//! let value = 17u64;
//!
//! let mut buf = String::new();
//! buf.push_str("value: ");
//! itoap::write_to_string(&mut buf, value);
//!
//! assert_eq!(buf, "value: 17");
//! # }
//! ```
//!
//! ```
//! use core::mem::{MaybeUninit, transmute};
//! use itoap::Integer;
//!
//! unsafe {
//!     let mut buf = [MaybeUninit::<u8>::uninit(); i32::MAX_LEN];
//!     let len = itoap::write_to_ptr(buf.as_mut_ptr() as *mut u8, -2953);
//!     let buf: [u8; i32::MAX_LEN] = transmute(buf);
//!     let result = buf.get_unchecked(0..len);
//!     assert_eq!(result, b"-2953");
//! }
//! ```

#![allow(clippy::many_single_char_names)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "alloc")]
use alloc::string::String;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;

#[cfg(feature = "std")]
extern crate std;

mod common;
use common::*;

#[cfg(not(all(
    any(target_arch = "x86_64", target_arch = "x86"),
    target_feature = "sse2",
    feature = "simd",
    not(miri),
)))]
mod fallback;

#[cfg(not(all(
    any(target_arch = "x86_64", target_arch = "x86"),
    target_feature = "sse2",
    feature = "simd",
    not(miri),
)))]
use fallback::{write_u32, write_u64};

#[cfg(all(
    any(target_arch = "x86_64", target_arch = "x86"),
    target_feature = "sse2",
    feature = "simd",
    not(miri),
))]
mod sse2;

#[cfg(all(
    any(target_arch = "x86_64", target_arch = "x86"),
    target_feature = "sse2",
    feature = "simd",
    not(miri),
))]
use sse2::{write_u32, write_u64};

mod private {
    pub trait Sealed {}
}

/// An integer that can be written to pointer.
pub trait Integer: private::Sealed {
    /// Maximum digits of the integer
    const MAX_LEN: usize;

    #[doc(hidden)]
    unsafe fn write_to(self, buf: *mut u8) -> usize;
}

macro_rules! impl_integer {
    ($unsigned:ty, $signed:ty, $conv:ty, $func:ident, $max_len:expr) => {
        impl private::Sealed for $unsigned {}
        impl private::Sealed for $signed {}

        impl Integer for $unsigned {
            const MAX_LEN: usize = $max_len;

            #[inline]
            unsafe fn write_to(self, buf: *mut u8) -> usize {
                $func(self as $conv, buf)
            }
        }

        impl Integer for $signed {
            const MAX_LEN: usize = $max_len + 1;

            #[inline]
            unsafe fn write_to(self, mut buf: *mut u8) -> usize {
                if self >= 0 {
                    $func(self as $conv, buf)
                } else {
                    *buf = b'-';
                    buf = buf.add(1);
                    let n = (!(self as $conv)).wrapping_add(1);
                    $func(n, buf) + 1
                }
            }
        }
    };
}

impl_integer!(u8, i8, u8, write_u8, 3);
impl_integer!(u16, i16, u16, write_u16, 5);
impl_integer!(u32, i32, u32, write_u32, 10);
impl_integer!(u64, i64, u64, write_u64, 20);
impl_integer!(u128, i128, u128, write_u128, 39);

#[cfg(target_pointer_width = "16")]
impl_integer!(usize, isize, u16, write_u16, 5);

#[cfg(target_pointer_width = "32")]
impl_integer!(usize, isize, u32, write_u32, 10);

#[cfg(target_pointer_width = "64")]
impl_integer!(usize, isize, u64, write_u64, 20);

/// Write integer to the buffer pointer directly.
///
/// This is fast operation, but does not check any safety.
///
/// # Safety
///
/// Behaviour is undefined if any of the following conditions are violated:
///
/// - `buf` must point to sufficient
/// [valid](https://doc.rust-lang.org/core/ptr/index.html#safety) bytes of memory to
/// write `value`
/// - `buf` must be aligned with `core::mem::align_of::<u8>()` bytes
#[inline]
pub unsafe fn write_to_ptr<V: Integer>(buf: *mut u8, value: V) -> usize {
    value.write_to(buf)
}

/// Write integer to `Vec<u8>`.
///
/// Note that this function is safe because it checks the capacity of `Vec` and calls
/// `Vec::reserve()` if the `Vec` doesn't have enough capacity.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
#[inline]
pub fn write_to_vec<V: Integer>(buf: &mut Vec<u8>, value: V) {
    buf.reserve(V::MAX_LEN);

    unsafe {
        let l = value.write_to(buf.as_mut_ptr().add(buf.len()));
        buf.set_len(buf.len() + l);
    }
}

/// Write integer to `String`.
///
/// Note that this function is safe because it checks the capacity of `String` and calls
/// `String::reserve()` if the `String` doesn't have enough capacity.
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
#[inline]
pub fn write_to_string<V: Integer>(buf: &mut String, value: V) {
    unsafe { write_to_vec(buf.as_mut_vec(), value) };
}

/// Write integer to an `io::Write`
///
/// Note that this operation may be slow because it writes the `value` to stack memory,
/// and then copy the result into `writer`.
///
/// This function is for compatibility with [itoa](https://docs.rs/itoa) crate and you
/// should use `write_to_vec` or `write_to_string` if possible.
pub fn fmt<W: core::fmt::Write, V: Integer>(
    mut writer: W,
    value: V,
) -> core::fmt::Result {
    use core::mem::MaybeUninit;

    unsafe {
        let mut buf = [MaybeUninit::<u8>::uninit(); 40];
        let l = value.write_to(buf.as_mut_ptr() as *mut u8);
        let buf = core::mem::transmute::<_, [u8; 40]>(buf);
        let slc = core::str::from_utf8_unchecked(buf.get_unchecked(0..l));
        writer.write_str(slc)
    }
}

/// Write integer to an `io::Write`
///
/// Note that this operation may be slow because it writes the `value` to stack memory,
/// and then copy the result into `writer`.
/// You should use `write_to_vec` or `write_to_string` if possible.
///
/// This function is for compatibility with [itoa](https://docs.rs/itoa) crate and you
/// should use `write_to_vec` or `write_to_string` if possible.
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
pub fn write<W: std::io::Write, V: Integer>(
    mut writer: W,
    value: V,
) -> std::io::Result<usize> {
    use core::mem::MaybeUninit;

    unsafe {
        let mut buf = [MaybeUninit::<u8>::uninit(); 40];
        let l = value.write_to(buf.as_mut_ptr() as *mut u8);
        let buf = core::mem::transmute::<_, [u8; 40]>(buf);
        let slc = buf.get_unchecked(0..l);
        writer.write(slc)
    }
}

#[cfg(all(test, feature = "alloc"))]
mod tests {
    use alloc::format;
    use alloc::string::String;
    use alloc::vec::Vec;

    // comprehenisive test
    #[test]
    fn test_i8_all() {
        let mut buf = Vec::new();

        for n in core::i8::MIN..=core::i8::MAX {
            unsafe {
                buf.clear();
                super::write_to_vec(&mut buf, n);
                assert_eq!(core::str::from_utf8_unchecked(&*buf), format!("{}", n));
            }
        }
    }

    // random test
    #[test]
    #[cfg(not(miri))]
    fn test_u64_random() {
        use super::Integer;
        let mut buf = Vec::with_capacity(u64::MAX_LEN);

        let mut state = 88172645463325252u64;

        for _ in 0..10000 {
            // xorshift
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;

            unsafe {
                buf.clear();
                super::write_to_vec(&mut buf, state);
                assert_eq!(core::str::from_utf8_unchecked(&*buf), format!("{}", state));
            }
        }
    }

    // random test
    #[test]
    #[cfg(not(miri))]
    fn test_u128_random() {
        use super::Integer;
        let mut buf = Vec::with_capacity(u128::MAX_LEN);

        let mut state = 88172645463325252u64;

        for _ in 0..10000 {
            // xorshift
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let h = state;
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;

            let value = (h as u128) << 64 | (state as u128);

            unsafe {
                buf.clear();
                super::write_to_vec(&mut buf, value);
                assert_eq!(core::str::from_utf8_unchecked(&*buf), format!("{}", value));
            }
        }
    }

    // random digits test
    #[test]
    #[cfg(not(miri))]
    fn test_u64_random_digits() {
        use super::Integer;
        let mut buf = Vec::with_capacity(u64::MAX_LEN);

        let mut state = 2721461171958153741u64;

        for _ in 0..10000 {
            // xorshift
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;

            let value = state >> (state % 64);
            unsafe {
                buf.clear();
                super::write_to_vec(&mut buf, value);
                assert_eq!(core::str::from_utf8_unchecked(&*buf), format!("{}", value));
            }
        }
    }

    // random digits test
    #[test]
    #[cfg(not(miri))]
    fn test_u128_random_digits() {
        use super::Integer;
        let mut buf = Vec::with_capacity(u128::MAX_LEN);

        let mut state = 88172645463325252u64;

        for _ in 0..10000 {
            // xorshift
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            let h = state;
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;

            let value = ((h as u128) << 64 | (state as u128)) >> (state % 128);

            unsafe {
                buf.clear();
                super::write_to_vec(&mut buf, value);
                assert_eq!(core::str::from_utf8_unchecked(&*buf), format!("{}", value));
            }
        }
    }

    // cov:begin-ignore
    macro_rules! make_test {
        ($name:ident, $type:ident) => {
            #[test]
            fn $name() {
                use super::Integer;

                fn test_write(val: $type, buf: &mut String) {
                    buf.clear();
                    super::write_to_string(buf, val);
                    assert_eq!(buf.as_str(), format!("{}", val));
                }

                let mut buf = String::with_capacity(<$type>::MAX_LEN);

                let mut current = 1;
                while current <= core::$type::MAX / 10 {
                    test_write(current - 1, &mut buf);
                    test_write(current, &mut buf);
                    test_write(current + 1, &mut buf);

                    current *= 10;
                }

                test_write(core::$type::MIN, &mut buf);
                test_write(core::$type::MAX, &mut buf);
            }
        };
    }
    // cov:end-ignore

    // boundary tests
    make_test!(test_u8, u8);
    make_test!(test_u16, u16);
    make_test!(test_u32, u32);
    make_test!(test_u64, u64);
    make_test!(test_u128, u128);

    make_test!(test_i8, i8);
    make_test!(test_i16, i16);
    make_test!(test_i32, i32);
    make_test!(test_i64, i64);
    make_test!(test_i128, i128);
}
