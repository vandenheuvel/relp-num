use std::hint::black_box;
use criterion::{Criterion, criterion_group};

use relp_num::R64;

fn zero_with_small(c: &mut Criterion) {
    c.bench_function("Rational64: zero + small", |b| b.iter(|| {
        let x = black_box(R64!(0));
        let y = black_box(R64!(1));
        x + y
    }));
}

fn small_with_zero(c: &mut Criterion) {
    c.bench_function("Rational64: small + zero", |b| b.iter(|| {
        let x = black_box(R64!(1));
        let y = black_box(R64!(0));
        x + y
    }));
}

fn small_with_small_same_denominator(c: &mut Criterion) {
    c.bench_function("Rational64: small + small, same denominator", |b| b.iter(|| {
        let x = black_box(R64!(3, 16));
        let y = black_box(R64!(2, 16));
        x + y
    }));
}

fn small_with_small_other_denominator(c: &mut Criterion) {
    c.bench_function("Rational64: small + small, other denominator", |b| b.iter(|| {
        let x = black_box(R64!(3, 16));
        let y = black_box(R64!(2, 17));
        x + y
    }));
}

criterion_group!(group,
    zero_with_small,
    small_with_zero,
    small_with_small_same_denominator,
    small_with_small_other_denominator,
);
