use std::hint::black_box;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{
    distributions::{Alphanumeric, DistString},
    Rng,
};

use gstr::GStr;

fn fixed_string_access(c: &mut Criterion) {
    let mut group = c.benchmark_group("Fixed String Access");

    let words: Vec<String> = vec![0usize, 4, 8, 9, 12, 13, 64, 128]
        .into_iter()
        .map(|len| (0..len).map(|_| 'a').collect())
        .collect();

    for word in words {
        let gstr = GStr::new(&word);
        group.bench_with_input(BenchmarkId::new("GStr", gstr.len()), &gstr, |b, gstr| {
            b.iter(|| gstr.as_str());
        });

        let string = word.clone();
        group.bench_with_input(
            BenchmarkId::new("String", string.len()),
            &string,
            |b, string| b.iter(|| string.as_str()),
        );
    }
}

fn random_string_access(c: &mut Criterion) {
    const WORDS_COUNT: usize = 64;

    let mut group = c.benchmark_group("Random String Access");
    let mut rng = rand::thread_rng();

    let words_vec: Vec<(usize, Vec<String>)> = vec![4usize, 8, 9, 12, 13, 64, 128, 256]
        .into_iter()
        .map(|max_len| {
            let mut vec = Vec::with_capacity(WORDS_COUNT);
            for _ in 0..WORDS_COUNT {
                let len = rng.gen_range(0..=max_len);
                vec.push(Alphanumeric.sample_string(&mut rng, len));
            }

            (max_len, vec)
        })
        .collect();

    for (max_len, vec) in words_vec {
        let gstrs = vec.iter().map(GStr::new).collect::<Vec<_>>();
        let strings = vec.iter().map(String::from).collect::<Vec<_>>();

        group.bench_with_input(BenchmarkId::new("GStr", max_len), &gstrs, |b, gstrs| {
            b.iter(|| {
                for s in gstrs {
                    black_box(s.as_str());
                }
            });
        });

        group.bench_with_input(
            BenchmarkId::new("String", max_len),
            &strings,
            |b, strings| {
                b.iter(|| {
                    for s in strings {
                        black_box(s.as_str());
                    }
                });
            },
        );
    }
}

criterion_group!(string_access, fixed_string_access, random_string_access);
criterion_main!(string_access);
