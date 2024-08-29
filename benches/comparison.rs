#![allow(missing_docs)]

use std::hint::black_box;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{
    distributions::{Alphanumeric, DistString},
    Rng,
};

use gstr::GStr;

const STRING_MAX_LENGTH: usize = 256;
const STRINGS_COUNT: usize = 64;

fn random_string() -> (Vec<GStr>, Vec<String>) {
    let mut rng = rand::thread_rng();

    let strings: Vec<String> = (0..STRINGS_COUNT)
        .map(|_| {
            let len = rng.gen_range(0..=STRING_MAX_LENGTH);

            Alphanumeric.sample_string(&mut rng, len)
        })
        .collect();
    let gstrs = strings.iter().map(GStr::new).collect::<Vec<_>>();

    (gstrs, strings)
}

fn fixed_length_random_string() -> (Vec<GStr>, Vec<String>) {
    let mut rng = rand::thread_rng();

    let strings: Vec<String> = (0..STRINGS_COUNT)
        .map(|_| Alphanumeric.sample_string(&mut rng, STRING_MAX_LENGTH))
        .collect();
    let gstrs = strings.iter().map(GStr::new).collect::<Vec<_>>();

    (gstrs, strings)
}

fn fixed_string_access(c: &mut Criterion) {
    let mut group = c.benchmark_group("Fixed String Access");

    let strings: Vec<String> = vec![0usize, 4, 8, 12, 16, 32, 64, 128]
        .into_iter()
        .map(|len| (0..len).map(|_| 'a').collect())
        .collect();

    for string in strings {
        let gstr = GStr::new(&string);
        group.bench_with_input(BenchmarkId::new("GStr", gstr.len()), &gstr, |b, gstr| {
            b.iter(|| gstr.bytes().next());
        });

        group.bench_with_input(
            BenchmarkId::new("String", string.len()),
            &string,
            |b, string| b.iter(|| string.bytes().next()),
        );
    }
}

fn random_string_access(c: &mut Criterion) {
    let mut group = c.benchmark_group("Random String Access");
    let (gstrs, strings) = random_string();

    group.bench_with_input(BenchmarkId::new("GStr", ""), &gstrs, |b, gstrs| {
        b.iter(|| {
            for gstr in gstrs {
                black_box(gstr.bytes().next());
            }
        });
    });

    group.bench_with_input(BenchmarkId::new("String", ""), &strings, |b, strings| {
        b.iter(|| {
            for string in strings {
                black_box(string.bytes().next());
            }
        });
    });
}

fn random_string_equality(c: &mut Criterion) {
    let mut group = c.benchmark_group("Random String Equality");
    let (gstrs, strings) = random_string();

    group.bench_with_input(BenchmarkId::new("GStr", ""), &gstrs, |b, gstrs| {
        b.iter(|| {
            for i in 0..gstrs.len() {
                for j in i..gstrs.len() {
                    black_box(gstrs[i] == gstrs[j]);
                }
            }
        });
    });

    group.bench_with_input(BenchmarkId::new("String", ""), &strings, |b, strings| {
        b.iter(|| {
            for i in 0..strings.len() {
                for j in i..strings.len() {
                    black_box(strings[i] == strings[j]);
                }
            }
        });
    });

    group.bench_with_input(
        BenchmarkId::new("Gstr and String", ""),
        &(gstrs, strings),
        |b, (gstrs, strings)| {
            b.iter(|| {
                #[allow(clippy::needless_range_loop)]
                for i in 0..gstrs.len() {
                    for j in i..strings.len() {
                        black_box(gstrs[i] == strings[j]);
                    }
                }
            });
        },
    );
}

fn fixed_length_random_string_equality(c: &mut Criterion) {
    let mut group = c.benchmark_group("Fixed-Length Random String Equality");
    let (gstrs, strings) = fixed_length_random_string();

    group.bench_with_input(BenchmarkId::new("GStr", ""), &gstrs, |b, gstrs| {
        b.iter(|| {
            for i in 0..gstrs.len() {
                for j in i..gstrs.len() {
                    black_box(gstrs[i] == gstrs[j]);
                }
            }
        });
    });

    group.bench_with_input(BenchmarkId::new("String", ""), &strings, |b, strings| {
        b.iter(|| {
            for i in 0..strings.len() {
                for j in i..strings.len() {
                    black_box(strings[i] == strings[j]);
                }
            }
        });
    });

    group.bench_with_input(
        BenchmarkId::new("Gstr and String", ""),
        &(gstrs, strings),
        |b, (gstrs, strings)| {
            b.iter(|| {
                #[allow(clippy::needless_range_loop)]
                for i in 0..gstrs.len() {
                    for j in i..strings.len() {
                        black_box(gstrs[i] == strings[j]);
                    }
                }
            });
        },
    );
}

fn random_string_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("Random String Comparison");
    let (gstrs, strings) = random_string();

    group.bench_with_input(BenchmarkId::new("GStr", ""), &gstrs, |b, gstrs| {
        b.iter(|| {
            for i in 0..gstrs.len() {
                for j in i..gstrs.len() {
                    black_box(gstrs[i].cmp(&gstrs[j]));
                }
            }
        });
    });

    group.bench_with_input(BenchmarkId::new("String", ""), &strings, |b, strings| {
        b.iter(|| {
            for i in 0..strings.len() {
                for j in i..strings.len() {
                    black_box(strings[i].cmp(&strings[j]));
                }
            }
        });
    });

    group.bench_with_input(
        BenchmarkId::new("Gstr and String", ""),
        &(gstrs, strings),
        |b, (gstrs, strings)| {
            b.iter(|| {
                #[allow(clippy::needless_range_loop)]
                for i in 0..gstrs.len() {
                    for j in i..strings.len() {
                        black_box(gstrs[i].partial_cmp(&strings[j]));
                    }
                }
            });
        },
    );
}

criterion_group!(string_access, fixed_string_access, random_string_access);

criterion_group!(
    string_comparison,
    random_string_equality,
    fixed_length_random_string_equality,
    random_string_comparison
);

criterion_main!(string_access, string_comparison);
