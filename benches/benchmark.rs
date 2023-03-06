use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn criterion_benchmark(c: &mut Criterion) {
    let input = include_str!("anyhow_alternate_backtrace.log");
    c.bench_function("_all_frames(backtrace)", |b| {
        b.iter(|| backtrace_prune::_all_frames(black_box(input)))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
