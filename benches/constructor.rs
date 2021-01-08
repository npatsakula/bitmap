use criterion::{black_box, criterion_group, criterion_main, Criterion};
use dyn_bitmap::DynBitmap;

fn contained(n: usize) -> DynBitmap {
    let mut result = DynBitmap::contained(n);
    for index in 0..n {
        result.set(index, index % 2 == 0).unwrap();
    }
    result
}

fn manual_benchmark(c: &mut Criterion) {
    c.bench_function("contained_10", |b| b.iter(|| contained(black_box(10))));
    c.bench_function("contained_100", |b| b.iter(|| contained(black_box(100))));
    c.bench_function("contained_1000", |b| b.iter(|| contained(black_box(1000))));
}

fn from_iter(n: usize) -> DynBitmap {
    [true, false].iter().cloned().cycle().take(n).collect()
}

fn from_iter_benchmark(c: &mut Criterion) {
    c.bench_function("from_iter_10", |b| b.iter(|| from_iter(black_box(10))));
    c.bench_function("from_iter_100", |b| b.iter(|| from_iter(black_box(100))));
    c.bench_function("from_iter_1000", |b| b.iter(|| from_iter(black_box(1000))));
}

criterion_group!(manual, manual_benchmark);
criterion_group!(iter, from_iter_benchmark);

criterion_main!(manual, iter);
