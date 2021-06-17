use criterion::{black_box, Criterion, criterion_group};

use relp_num::RB;

fn small_with_zero(c: &mut Criterion) {
    c.bench_function("RationalBig: small + zero", |b| b.iter(|| {
        let x = black_box(RB!(1));
        let y = black_box(RB!(0));
        x + y
    }));
}

fn zero_with_small(c: &mut Criterion) {
    c.bench_function("RationalBig: zero + small", |b| b.iter(|| {
        let x = black_box(RB!(0));
        let y = black_box(RB!(1));
        x + y
    }));
}

fn int_with_int(c: &mut Criterion) {
    c.bench_function("int + int", |b| b.iter(|| {
        let x = black_box(1);
        let y = black_box(0);
        x + y
    }));
}

fn small_with_small_same_denominator(c: &mut Criterion) {
    c.bench_function("RationalBig: small + small, same denominator", |b| b.iter(|| {
        let x = black_box(RB!(3, 16));
        let y = black_box(RB!(2, 16));
        x + y
    }));
}

fn small_with_small_other_denominator(c: &mut Criterion) {
    c.bench_function("RationalBig: small + small, other denominator", |b| b.iter(|| {
        let x = black_box(RB!(3, 16));
        let y = black_box(RB!(2, 17));
        x + y
    }));
}

criterion_group!(group,
    zero_with_small,
    small_with_zero,
    small_with_small_same_denominator,
    small_with_small_other_denominator,
    int_with_int,
);
