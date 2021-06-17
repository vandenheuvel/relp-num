use criterion::criterion_main;

pub mod primes;
pub mod factors;
pub mod rational_big;
pub mod rational_small;

criterion_main! {
    primes::group,
    factors::group,
    rational_big::add::group,
}
