use core::ptr;

const DEC_DIGITS_LUT: &[u8] = b"\
      0001020304050607080910111213141516171819\
      2021222324252627282930313233343536373839\
      4041424344454647484950515253545556575859\
      6061626364656667686970717273747576777879\
      8081828384858687888990919293949596979899";

#[inline]
pub unsafe fn lookup<T: Into<usize>>(idx: T) -> *const u8 {
    DEC_DIGITS_LUT.as_ptr().add((idx.into() as usize) << 1)
}

/// write integer smaller than 10000
#[inline]
pub unsafe fn write4(n: u16, buf: *mut u8) -> usize {
    debug_assert!(n < 10000);

    if n < 100 {
        if n < 10 {
            *buf = n as u8 + 0x30;
            1
        } else {
            ptr::copy_nonoverlapping(lookup(n), buf, 2);
            2
        }
    } else if n < 1000 {
        let d1 = (n / 100) as u8;
        let d2 = n % 100;
        *buf = d1 + 0x30;
        ptr::copy_nonoverlapping(lookup(d2), buf.add(1), 2);
        3
    } else {
        let d1 = n / 100;
        let d2 = n % 100;
        ptr::copy_nonoverlapping(lookup(d1), buf, 2);
        ptr::copy_nonoverlapping(lookup(d2), buf.add(2), 2);
        4
    }
}

/// write integer smaller than 10000 with 0 padding
#[inline]
pub unsafe fn write4_pad(n: u16, buf: *mut u8) {
    debug_assert!(n < 10000);

    let d1 = n / 100;
    let d2 = n % 100;

    ptr::copy_nonoverlapping(lookup(d1), buf, 2);
    ptr::copy_nonoverlapping(lookup(d2), buf.add(2), 2);
}

#[inline]
pub unsafe fn write8(n: u32, buf: *mut u8) -> usize {
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
pub unsafe fn write8_pad(n: u32, buf: *mut u8) {
    debug_assert!(n < 100_000_000);

    let c1 = (n / 10000) as u32;
    let c2 = (n % 10000) as u32;

    let d1 = (c1 / 100) as u16;
    let d2 = (c1 % 100) as u16;
    let d3 = (c2 / 100) as u16;
    let d4 = (c2 % 100) as u16;

    ptr::copy_nonoverlapping(lookup(d1), buf, 2);
    ptr::copy_nonoverlapping(lookup(d2), buf.add(2), 2);
    ptr::copy_nonoverlapping(lookup(d3), buf.add(4), 2);
    ptr::copy_nonoverlapping(lookup(d4), buf.add(6), 2);
}

pub unsafe fn write_u8(n: u8, buf: *mut u8) -> usize {
    if n < 10 {
        *buf = n + 0x30;
        1
    } else if n < 100 {
        ptr::copy_nonoverlapping(lookup(n), buf, 2);
        2
    } else {
        let d1 = n / 100;
        let d2 = n % 100;
        *buf = d1 + 0x30;
        ptr::copy_nonoverlapping(lookup(d2), buf.add(1), 2);
        3
    }
}

pub unsafe fn write_u16(n: u16, buf: *mut u8) -> usize {
    if n < 100 {
        if n < 10 {
            *buf = n as u8 + 0x30;
            1
        } else {
            ptr::copy_nonoverlapping(lookup(n), buf, 2);
            2
        }
    } else if n < 10000 {
        if n < 1000 {
            let d1 = (n / 100) as u8;
            let d2 = n % 100;
            *buf = d1 + 0x30;
            ptr::copy_nonoverlapping(lookup(d2), buf.add(1), 2);
            3
        } else {
            let d1 = n / 100;
            let d2 = n % 100;
            ptr::copy_nonoverlapping(lookup(d1), buf, 2);
            ptr::copy_nonoverlapping(lookup(d2), buf.add(2), 2);
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

/// Multiply unsigned 128 bit integers, return upper 128 bits of the result
#[inline]
fn u128_mulhi(x: u128, y: u128) -> u128 {
    let x_lo = x as u64;
    let x_hi = (x >> 64) as u64;
    let y_lo = y as u64;
    let y_hi = (y >> 64) as u64;

    // handle possibility of overflow
    let carry = (x_lo as u128 * y_lo as u128) >> 64;
    let m = x_lo as u128 * y_hi as u128 + carry;
    let high1 = m >> 64;

    let m_lo = m as u64;
    let high2 = x_hi as u128 * y_lo as u128 + m_lo as u128 >> 64;

    x_hi as u128 * y_hi as u128 + high1 + high2
}

/// Write u128 in decimal format
/// 
/// Integer division algorithm is based on the following paper:
///
///   T. Granlund and P. Montgomery, “Division by Invariant IntegersUsing Multiplication,”
///   in Proc. of the SIGPLAN94 Conference onProgramming Language Design and
///   Implementation, 1994, pp. 61–72
///
unsafe fn write_u128_big(mut n: u128, mut buf: *mut u8) -> usize {
    const DIV_FACTOR: u128 = 76624777043294442917917351357515459181;
    const DIV_SHIFT: u32 = 51;
    const POW_10_8: u64 = 100000000;
    const POW_10_16: u64 = 10000000000000000;

    debug_assert!(n > core::u64::MAX as u128);

    // hold per-8-digits results
    // i.e. result[0] holds n % 10^8, result[1] holds (n / 10^8) % 10^8, ...
    let mut result = [0u32; 5];

    {
        // performs n /= 10^16
        let quot = u128_mulhi(n, DIV_FACTOR) >> DIV_SHIFT;
        let rem = (n - quot * POW_10_16 as u128) as u64;
        debug_assert_eq!(quot, n / POW_10_16 as u128);
        debug_assert_eq!(rem as u128, n % POW_10_16 as u128);

        n = quot;

        result[1] = (rem / POW_10_8) as u32;
        result[0] = (rem % POW_10_8) as u32;

        debug_assert_ne!(n, 0);
        debug_assert!(n <= core::u128::MAX / POW_10_16 as u128);
    }

    let result_len = if n >= POW_10_16 as u128 {
        // performs n /= 10^16
        let quot = (n >> 16) as u64 / (POW_10_16 >> 16);
        let rem = (n - POW_10_16 as u128 * quot as u128) as u64;
        debug_assert_eq!(quot as u128, n / POW_10_16 as u128);
        debug_assert_eq!(rem as u128, n % POW_10_16 as u128);
        debug_assert!(quot <= 3402823);

        result[3] = (rem / POW_10_8) as u32;
        result[2] = (rem % POW_10_8) as u32;
        result[4] = quot as u32;
        4
    } else if (n as u64) >= POW_10_8 {
        result[3] = ((n as u64) / POW_10_8) as u32;
        result[2] = ((n as u64) % POW_10_8) as u32;
        3
    } else {
        result[2] = n as u32;
        2
    };

    let l = write8(*result.get_unchecked(result_len), buf);
    buf = buf.add(l);

    for i in (0..result_len).rev() {
        write8_pad(*result.get_unchecked(i), buf);
        buf = buf.add(8);
    }

    l + result_len * 8
}

#[inline]
pub unsafe fn write_u128(n: u128, buf: *mut u8) -> usize {
    if n <= core::u64::MAX as u128 {
        crate::write_u64(n as u64, buf)
    } else {
        write_u128_big(n, buf)
    }
}
