use bencher::{benchmark_group, benchmark_main};

macro_rules! benches {
    (
        $(
            $(#[$attr:meta])*
            $name:ident($value:expr)
        ),*
    ) => {
        mod bench_itoap_write_to_vec {
            use bencher::{Bencher, black_box};
            $(
                $(#[$attr])*
                pub fn $name(b: &mut Bencher) {
                    let mut buf = Vec::with_capacity(40);

                    b.iter(|| {
                        buf.clear();
                        itoap::write_to_vec(&mut buf, black_box($value));
                        buf.len()
                    });
                }
            )*
        }

        mod bench_itoap_write {
            use bencher::{Bencher, black_box};
            $(
                $(#[$attr])*
                pub fn $name(b: &mut Bencher) {
                    let mut buf = Vec::<u8>::with_capacity(40);

                    b.iter(|| {
                        buf.clear();
                        let _ = itoap::write(&mut buf, black_box($value));
                        buf.len()
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

                        let _ = itoa::write(&mut buf, black_box($value));
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
                bench_itoap_write_to_vec::$name,
                bench_itoap_write::$name,
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
