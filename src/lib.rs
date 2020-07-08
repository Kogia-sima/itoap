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
//! The implementation is based on the `branchlut` algorithm from
//! [itoa-benchmark](https://github.com/miloyip/itoa-benchmark) repository.
//! While `itoa` crate writes integers from **last** digits, this algorithm writes
//! from **first** digits. It allows integers to be written directly to the buffer.
//! That's why `itoap` is faster than `itoa`.
//!
//! # Feature Flags
//!
//! - `alloc`: use [alloc](https://doc.rust-lang.org/alloc/) crate (enabled by default)
//! - `std`: use [std](https://doc.rust-lang.org/std/) crate (enabled by default)
//!
//! # Examples
//!
//! ```
//! let value = 17u64;
//!
//! let mut buf = String::new();
//! buf.push_str("value: ");
//! itoap::write_to_string(&mut buf, value);
//!
//! assert_eq!(buf, "value: 17");
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

use core::ptr;

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "alloc")]
use alloc::string::String;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;

#[cfg(feature = "std")]
extern crate std;

const DEC_DIGITS_LUT: &[u8] = b"\
      0001020304050607080910111213141516171819\
      2021222324252627282930313233343536373839\
      4041424344454647484950515253545556575859\
      6061626364656667686970717273747576777879\
      8081828384858687888990919293949596979899";

macro_rules! lookup {
    ($idx:expr) => {
        DEC_DIGITS_LUT.as_ptr().add(($idx as usize) << 1)
    };
}

/// write integer smaller than 10000
#[inline]
unsafe fn write4(n: u16, buf: *mut u8) -> usize {
    debug_assert!(n < 10000);

    if n < 100 {
        if n < 10 {
            *buf = n as u8 + 0x30;
            1
        } else {
            ptr::copy_nonoverlapping(lookup!(n), buf, 2);
            2
        }
    } else if n < 1000 {
        let d1 = (n / 100) as u8;
        let d2 = n % 100;
        *buf = d1 + 0x30;
        ptr::copy_nonoverlapping(lookup!(d2), buf.add(1), 2);
        3
    } else {
        let d1 = n / 100;
        let d2 = n % 100;
        ptr::copy_nonoverlapping(lookup!(d1), buf, 2);
        ptr::copy_nonoverlapping(lookup!(d2), buf.add(2), 2);
        4
    }
}

/// write integer smaller than 10000 with 0 padding
#[inline]
unsafe fn write4_pad(n: u16, buf: *mut u8) {
    debug_assert!(n < 10000);

    let d1 = n / 100;
    let d2 = n % 100;

    ptr::copy_nonoverlapping(lookup!(d1), buf, 2);
    ptr::copy_nonoverlapping(lookup!(d2), buf.add(2), 2);
}

#[inline]
unsafe fn write8(n: u32, buf: *mut u8) -> usize {
    debug_assert!(n < 100_000_000);

    if n < 10000 {
        write4(n as u16, buf)
    } else {
        let d1 = (n / 10000) as u16;
        let d2 = (n % 10000) as u16;
        let l = write4(d1, buf);
        write4_pad(d2, buf.add(l));
        l + 4
    }
}

#[inline]
unsafe fn write8_pad(n: u32, buf: *mut u8) {
    debug_assert!(n < 100_000_000);

    let c1 = (n / 10000) as u32;
    let c2 = (n % 10000) as u32;

    let d1 = (c1 / 100) as u16;
    let d2 = (c1 % 100) as u16;
    let d3 = (c2 / 100) as u16;
    let d4 = (c2 % 100) as u16;

    ptr::copy_nonoverlapping(lookup!(d1), buf, 2);
    ptr::copy_nonoverlapping(lookup!(d2), buf.add(2), 2);
    ptr::copy_nonoverlapping(lookup!(d3), buf.add(4), 2);
    ptr::copy_nonoverlapping(lookup!(d4), buf.add(6), 2);
}

unsafe fn write_u8(n: u8, buf: *mut u8) -> usize {
    if n < 10 {
        *buf = n + 0x30;
        1
    } else if n < 100 {
        ptr::copy_nonoverlapping(lookup!(n), buf, 2);
        2
    } else {
        let d1 = n / 100;
        let d2 = n % 100;
        *buf = d1 + 0x30;
        ptr::copy_nonoverlapping(lookup!(d2), buf.add(1), 2);
        3
    }
}

unsafe fn write_u16(n: u16, buf: *mut u8) -> usize {
    if n < 100 {
        if n < 10 {
            *buf = n as u8 + 0x30;
            1
        } else {
            ptr::copy_nonoverlapping(lookup!(n), buf, 2);
            2
        }
    } else if n < 10000 {
        if n < 1000 {
            let d1 = (n / 100) as u8;
            let d2 = n % 100;
            *buf = d1 + 0x30;
            ptr::copy_nonoverlapping(lookup!(d2), buf.add(1), 2);
            3
        } else {
            let d1 = n / 100;
            let d2 = n % 100;
            ptr::copy_nonoverlapping(lookup!(d1), buf, 2);
            ptr::copy_nonoverlapping(lookup!(d2), buf.add(2), 2);
            4
        }
    } else {
        let b = (n / 10000) as u8; // 1 to 6
        let c = n % 10000;

        *buf = b + 0x30;
        write4_pad(c, buf.add(1));
        5
    }
}

unsafe fn write_u32(mut n: u32, buf: *mut u8) -> usize {
    if n < 10000 {
        write4(n as u16, buf)
    } else if n < 100_000_000 {
        let b = n / 10000;
        let c = n % 10000;

        let l = write4(b as u16, buf);
        write4_pad(c as u16, buf.add(l));
        l + 4
    } else {
        let a = n / 100_000_000; // 1 to 42
        n %= 100_000_000;

        let l = if a >= 10 {
            ptr::copy_nonoverlapping(lookup!(a), buf, 2);
            2
        } else {
            *buf = a as u8 + 0x30;
            1
        };

        write8_pad(n, buf.add(l));
        l + 8
    }
}

unsafe fn write_u64(mut n: u64, buf: *mut u8) -> usize {
    if n < 10000 {
        write4(n as u16, buf)
    } else if n < 100_000_000 {
        let n = n as u32;
        let b = n / 10000;
        let c = n % 10000;

        let l = write4(b as u16, buf);
        write4_pad(c as u16, buf.add(l));
        l + 4
    } else if n < 10_000_000_000_000_000 {
        let v0 = n / 100_000_000;
        let v1 = (n % 100_000_000) as u32;

        let l = if v0 < 10000 {
            write4(v0 as u16, buf)
        } else {
            let b0 = v0 / 10000;
            let c0 = v0 % 10000;
            let l = write4(b0 as u16, buf);
            write4_pad(c0 as u16, buf.add(l));
            l + 4
        };

        let b1 = v1 / 10000;
        let c1 = v1 % 10000;

        write4_pad(b1 as u16, buf.add(l));
        write4_pad(c1 as u16, buf.add(l + 4));

        l + 8
    } else {
        let a = n / 10_000_000_000_000_000; // 1 to 1844
        n %= 10_000_000_000_000_000;

        let v0 = (n / 100_000_000) as u32;
        let v1 = (n % 100_000_000) as u32;

        let b0 = v0 / 10000;
        let c0 = v0 % 10000;

        let b1 = v1 / 10000;
        let c1 = v1 % 10000;

        let l = write4(a as u16, buf);
        write4_pad(b0 as u16, buf.add(l));
        write4_pad(c0 as u16, buf.add(l + 4));
        write4_pad(b1 as u16, buf.add(l + 8));
        write4_pad(c1 as u16, buf.add(l + 12));
        l + 16
    }
}

// write u128 in decimal format
//
// current implementation is based on [6502's method](https://stackoverflow.com/a/8025958),
// but may changes if faster algorithm will be found.
unsafe fn write_u128_big(n: u128, mut buf: *mut u8) -> usize {
    use core::mem::{transmute_copy, MaybeUninit};

    debug_assert!(n > core::u64::MAX as u128);

    // expand to per-32-bit elements.
    // should use `transmute_copy` because results of `to_ne_bytes` may be not aligned.
    let mut x: [u32; 4] = transmute_copy(&n.to_ne_bytes());

    // hold per-8-digits results
    // i.e. result[0] holds n % 10^8, result[1] holds (n / 10^8) % 10^8, ...
    let mut result = [MaybeUninit::<u32>::uninit(); 5];

    let rp_begin = result.as_mut_ptr() as *mut u32;
    let mut rp = rp_begin;

    // loops at most 5 times
    loop {
        #[cfg(target_endian = "little")]
        const ORDER: [usize; 4] = [3, 2, 1, 0];
        #[cfg(target_endian = "big")]
        const ORDER: [usize; 4] = [0, 1, 2, 3];

        let mut carry = 0u32;
        let mut d;

        // performs x /= 10^8 and store the remainder to carry
        // TODO: speed up using SIMD intrinsics
        {
            d = ((carry as u64) << 32) | x[ORDER[0]] as u64;
            x[ORDER[0]] = (d / 100_000_000) as u32;
            carry = (d % 100_000_000) as u32;

            d = ((carry as u64) << 32) | x[ORDER[1]] as u64;
            x[ORDER[1]] = (d / 100_000_000) as u32;
            carry = (d % 100_000_000) as u32;

            d = ((carry as u64) << 32) | x[ORDER[2]] as u64;
            x[ORDER[2]] = (d / 100_000_000) as u32;
            carry = (d % 100_000_000) as u32;

            d = ((carry as u64) << 32) | x[ORDER[3]] as u64;
            x[ORDER[3]] = (d / 100_000_000) as u32;
            carry = (d % 100_000_000) as u32;
        }

        *rp = carry;

        if x[0] == 0 && x[1] == 0 && x[2] == 0 && x[3] == 0 {
            break;
        }

        rp = rp.add(1);
    }

    let result_len = (rp as usize - rp_begin as usize) / core::mem::size_of::<u32>();
    debug_assert!(result_len < 5);

    let l = write8(*rp, buf);
    buf = buf.add(l);

    while rp > rp_begin {
        rp = rp.sub(1);
        write8_pad(*rp, buf);
        buf = buf.add(8);
    }

    l + result_len * 8
}

#[inline]
unsafe fn write_u128(n: u128, buf: *mut u8) -> usize {
    if n <= core::u64::MAX as u128 {
        write_u64(n as u64, buf)
    } else {
        write_u128_big(n, buf)
    }
}

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
    if buf.len() + V::MAX_LEN > buf.capacity() {
        buf.reserve(V::MAX_LEN);
    }

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
    if buf.len() + V::MAX_LEN > buf.capacity() {
        buf.reserve(V::MAX_LEN);
    }

    unsafe {
        let l = value.write_to(buf.as_mut_vec().as_mut_ptr().add(buf.len()));
        let new_len = buf.len() + l;
        buf.as_mut_vec().set_len(new_len);
    }
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
    use alloc::vec::Vec;

    // comprehenisive test
    #[test]
    fn test_i8_all() {
        use super::Integer;
        let mut buf = Vec::with_capacity(i8::MAX_LEN);

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

    macro_rules! make_test {
        ($name:ident, $type:ty, $($value:expr),*) => {
            #[test]
            fn $name() {
                use super::Integer;

                unsafe fn test_write(val: $type, buf: &mut Vec<u8>) {
                    buf.clear();
                    super::write_to_vec(buf, val);
                    assert_eq!(
                        core::str::from_utf8_unchecked(&*buf),
                        format!("{}", val)
                    );
                }

                let mut buf = Vec::with_capacity(<$type>::MAX_LEN);
                unsafe {
                    $(
                        test_write($value as $type, &mut buf);
                    )*
                }
            }
        }
    }

    // boundary tests
    make_test!(test_u8, u8, 0, 1, 9, 10, 99, 100, 254, 255);
    make_test!(test_u16, u16, 0, 9, 10, 99, 100, 999, 1000, 9999, 10000, 65535);
    make_test!(
        test_u32, u32, 0, 9, 10, 99, 100, 999, 1000, 9999, 10000, 99999, 100000, 999999,
        1000000, 9999999, 10000000, 99999999, 100000000, 999999999, 1000000000,
        4294967295
    );
    make_test!(
        test_u64,
        u64,
        0,
        9,
        10,
        99,
        100,
        999,
        1000,
        9999,
        10000,
        99999,
        100000,
        999999,
        1000000,
        9999999,
        10000000,
        99999999,
        100000000,
        999999999,
        1000000000,
        9999999999,
        10000000000,
        99999999999,
        100000000000,
        999999999999,
        1000000000000,
        9999999999999,
        10000000000000,
        99999999999999,
        100000000000000,
        999999999999999,
        1000000000000000,
        9999999999999999,
        10000000000000000,
        99999999999999999,
        100000000000000000,
        999999999999999999,
        1000000000000000000,
        9999999999999999999,
        10000000000000000000,
        18446744073709551615
    );

    make_test!(
        test_u128,
        u128,
        0,
        9,
        10,
        99,
        100,
        999,
        1000,
        9999,
        10000,
        99999,
        100000,
        999999,
        1000000,
        9999999,
        10000000,
        99999999,
        100000000,
        999999999,
        1000000000,
        9999999999,
        10000000000,
        99999999999,
        100000000000,
        999999999999,
        1000000000000,
        9999999999999,
        10000000000000,
        99999999999999,
        100000000000000,
        999999999999999,
        1000000000000000,
        9999999999999999,
        10000000000000000,
        99999999999999999,
        100000000000000000,
        999999999999999999,
        1000000000000000000,
        9999999999999999999,
        10000000000000000000,
        99999999999999999999,
        100000000000000000000,
        999999999999999999999,
        1000000000000000000000,
        9999999999999999999999,
        10000000000000000000000,
        99999999999999999999999,
        100000000000000000000000,
        100000000000000000000000,
        999999999999999999999999,
        1000000000000000000000000,
        9999999999999999999999999,
        10000000000000000000000000,
        99999999999999999999999999,
        100000000000000000000000000,
        999999999999999999999999999,
        1000000000000000000000000000,
        9999999999999999999999999999,
        10000000000000000000000000000,
        99999999999999999999999999999,
        100000000000000000000000000000,
        999999999999999999999999999999,
        1000000000000000000000000000000,
        9999999999999999999999999999999,
        10000000000000000000000000000000,
        99999999999999999999999999999999,
        100000000000000000000000000000000,
        999999999999999999999999999999999,
        1000000000000000000000000000000000,
        9999999999999999999999999999999999,
        10000000000000000000000000000000000,
        99999999999999999999999999999999999,
        100000000000000000000000000000000000,
        999999999999999999999999999999999999,
        1000000000000000000000000000000000000,
        9999999999999999999999999999999999999,
        10000000000000000000000000000000000000,
        99999999999999999999999999999999999999,
        100000000000000000000000000000000000000,
        340282366920938463463374607431768211455
    );

    make_test!(test_i8, i8, core::i8::MIN, core::i8::MAX);
    make_test!(test_i16, i16, core::i16::MIN, core::i16::MAX);
    make_test!(test_i32, i32, core::i32::MIN, core::i32::MAX);
    make_test!(test_i64, i64, core::i64::MIN, core::i64::MAX);
    make_test!(test_i128, i128, core::i128::MIN, core::i128::MAX);
}
