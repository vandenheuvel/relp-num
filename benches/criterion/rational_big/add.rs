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

fn large_with_large_other_denominator(c: &mut Criterion) {
    c.bench_function("RationalBig: large + large, other denominator", |b| b.iter(|| {
        let x = black_box(RationalBig::from_str("6168468435984654684986468468465846854869699989985/5648654685465465464684846546846856725").unwrap());
        let y = black_box(RationalBig::from_str("616846843598465468438574687768468765846854869699989985/564846898987498778846546846856725").unwrap());
        x + y
    }));
}

criterion_group!(group,
    zero_with_small,
    small_with_zero,
    small_with_small_same_denominator,
    small_with_small_other_denominator,
    int_with_int,
    large_with_large_other_denominator,
);
