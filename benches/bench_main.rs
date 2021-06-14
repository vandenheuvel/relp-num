use criterion::criterion_main;

mod criterion_benchmarks;

criterion_main! {
    criterion_benchmarks::primes::group,
    criterion_benchmarks::factors::group,
    criterion_benchmarks::rational_big::add::group,
}
