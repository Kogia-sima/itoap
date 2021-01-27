use bencher::{benchmark_group, benchmark_main};

macro_rules! benches {
    (
        $(
            $(#[$attr:meta])*
            $name:ident($value:expr)
        ),*
    ) => {
        mod bench_itoap_write {
            use bencher::{Bencher, black_box};
            $(
                $(#[$attr])*
                pub fn $name(b: &mut Bencher) {
                    let mut buf = Vec::with_capacity(40);

                    b.iter(|| {
                        buf.clear();
                        itoap::write_to_vec(&mut buf, black_box($value))
                    });
                }
            )*
        }

        mod bench_itoap_ptr_write {
            use bencher::{Bencher, black_box};
            $(
                $(#[$attr])*
                pub fn $name(b: &mut Bencher) {
                    let mut buf = Vec::<u8>::with_capacity(40);

                    b.iter(|| unsafe {
                        itoap::write_to_ptr(buf.as_mut_ptr(), black_box($value))
                    });
                }
            )*
        }

        mod bench_itoa_write {
            use bencher::{Bencher, black_box};
            $(
                $(#[$attr])*
                pub fn $name(b: &mut Bencher) {
                    let mut buf = Vec::with_capacity(40);

                    b.iter(|| {
                        buf.clear();

                        let mut itoa_buf = itoa::Buffer::new();
                        let s = itoa_buf.format(black_box($value));
                        buf.extend_from_slice(s.as_bytes());
                        buf.len()
                    });
                }
            )*
        }

        mod bench_std_fmt {
            use bencher::{Bencher, black_box};
            $(
                $(#[$attr])*
                pub fn $name(b: &mut Bencher) {
                    use std::io::Write;

                    let mut buf = Vec::with_capacity(40);

                    b.iter(|| {
                        buf.clear();
                        write!(&mut buf, "{}", black_box($value)).unwrap()
                    });
                }
            )*
        }

        $(
            benchmark_group!(
                $name,
                bench_itoap_write::$name,
                bench_itoap_ptr_write::$name,
                bench_itoa_write::$name,
                bench_std_fmt::$name,
            );
        )*
    }
}

benches! {
    bench_u64_0(0u64),
    bench_u64_half(<u32>::max_value() as u64),
    bench_u64_max(<u64>::max_value()),
    bench_i16_0(0i16),
    bench_i16_min(<i16>::min_value()),
    bench_u128_0(0u128),
    bench_u128_max(<u128>::max_value())
}

benchmark_main!(
    bench_u64_0,
    bench_u64_half,
    bench_u64_max,
    bench_i16_0,
    bench_i16_min,
    bench_u128_0,
    bench_u128_max,
);
