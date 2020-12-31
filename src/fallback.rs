use core::ptr;

use crate::common::{write4, write4_pad, write8_pad, lookup};

pub unsafe fn write_u32(mut n: u32, buf: *mut u8) -> usize {
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
            ptr::copy_nonoverlapping(lookup(a as usize), buf, 2);
            2
        } else {
            *buf = a as u8 + 0x30;
            1
        };

        write8_pad(n, buf.add(l));
        l + 8
    }
}

pub unsafe fn write_u64(mut n: u64, buf: *mut u8) -> usize {
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
