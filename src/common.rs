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
pub unsafe fn write_u128(n: u128, buf: *mut u8) -> usize {
    if n <= core::u64::MAX as u128 {
        crate::write_u64(n as u64, buf)
    } else {
        write_u128_big(n, buf)
    }
}
