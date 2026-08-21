//! What acting through [`Absorb`] costs against writing the operation out by hand.
//!
//! Every case is measured as a pair, so the two numbers that matter are compared under the same
//! clock. Absolute times drift with the machine's thermal state; the ratio between the two halves
//! of a pair does not, which is what makes this readable without a quiet machine.
//!
//! The accumulator is the wide, state carrying value that a basis inverse is built out of, and the
//! narrow value is what a matrix provider hands over. Three accumulator widths are measured,
//! because the shortcuts being checked are the ones whose absence grows with the operand.

use std::hint::black_box;
use std::str::FromStr;

use std::time::Duration;

use criterion::{BatchSize, Criterion, criterion_group};

use relp_num::fixed::{Binary, One, SignedOne, Zero};
use relp_num::{Absorb, Rational8, Rational32, Rational64, RationalBig};

use super::constants::{W1, W4, W16};


/// The accumulator is rebuilt for every iteration, so the clone is kept out of the measurement.
fn add_pair(
    c: &mut Criterion, id: &str, base: &RationalBig,
    widen: impl Fn(&mut RationalBig), direct: impl Fn(&mut RationalBig),
) {
    c.bench_function(&format!("absorb: add/{id}/widen"), |b| {
        b.iter_batched_ref(|| base.clone(), |acc| widen(black_box(acc)), BatchSize::SmallInput)
    });
    c.bench_function(&format!("absorb: add/{id}/direct"), |b| {
        b.iter_batched_ref(|| base.clone(), |acc| direct(black_box(acc)), BatchSize::SmallInput)
    });
}

fn mul_pair(
    c: &mut Criterion, id: &str, base: &RationalBig,
    widen: impl Fn(&RationalBig) -> RationalBig, direct: impl Fn(&RationalBig) -> RationalBig,
) {
    c.bench_function(&format!("absorb: mul/{id}/widen"), |b| {
        b.iter(|| black_box(widen(black_box(base))))
    });
    c.bench_function(&format!("absorb: mul/{id}/direct"), |b| {
        b.iter(|| black_box(direct(black_box(base))))
    });
}

fn matrix(c: &mut Criterion) {
    let sizes = [
        ("1w", RationalBig::from_str(W1).unwrap()),
        ("4w", RationalBig::from_str(W4).unwrap()),
        ("16w", RationalBig::from_str(W16).unwrap()),
    ];

    let i8_value: i8 = 7;
    let i32_value: i32 = 70_001;
    let i64_value: i64 = 4_000_000_007;
    let rational_8 = Rational8::new(3, 4).unwrap();
    let rational_32 = Rational32::new(70_001, 65_537).unwrap();
    let rational_64 = Rational64::new(4_000_000_007, 2_147_483_647).unwrap();
    let big = RationalBig::from_str(W1).unwrap();

    for (size, accumulator) in &sizes {
        add_pair(c, &format!("{size}/Zero"), accumulator, |a| a.add_narrow(&Zero), |a| *a += Zero);
        add_pair(c, &format!("{size}/One"), accumulator, |a| a.add_narrow(&One), |a| *a += One);
        add_pair(c, &format!("{size}/Binary"), accumulator,
            |a| a.add_narrow(&Binary::One), |a| *a += Binary::One);
        add_pair(c, &format!("{size}/SignedOne"), accumulator,
            |a| a.add_narrow(&SignedOne::MinusOne), |a| *a -= One);
        add_pair(c, &format!("{size}/i8"), accumulator, |a| a.add_narrow(&i8_value), |a| *a += i8_value);
        add_pair(c, &format!("{size}/i32"), accumulator, |a| a.add_narrow(&i32_value), |a| *a += i32_value);
        add_pair(c, &format!("{size}/i64"), accumulator, |a| a.add_narrow(&i64_value), |a| *a += i64_value);
        add_pair(c, &format!("{size}/R8"), accumulator, |a| a.add_narrow(&rational_8), |a| *a += rational_8);
        add_pair(c, &format!("{size}/R32"), accumulator, |a| a.add_narrow(&rational_32), |a| *a += rational_32);
        add_pair(c, &format!("{size}/R64"), accumulator, |a| a.add_narrow(&rational_64), |a| *a += rational_64);
        add_pair(c, &format!("{size}/Big"), accumulator, |a| a.add_narrow(&big), |a| *a += &big);

        mul_pair(c, &format!("{size}/One"), accumulator, |a| a.mul_narrow(&One), |a| a * One);
        mul_pair(c, &format!("{size}/Binary"), accumulator,
            |a| a.mul_narrow(&Binary::One), |a| a * Binary::One);
        mul_pair(c, &format!("{size}/SignedOne"), accumulator,
            |a| a.mul_narrow(&SignedOne::MinusOne), |a| -a.clone());
        mul_pair(c, &format!("{size}/i8"), accumulator, |a| a.mul_narrow(&i8_value), |a| a * i8_value);
        mul_pair(c, &format!("{size}/i32"), accumulator, |a| a.mul_narrow(&i32_value), |a| a * i32_value);
        mul_pair(c, &format!("{size}/i64"), accumulator, |a| a.mul_narrow(&i64_value), |a| a * i64_value);
        mul_pair(c, &format!("{size}/R8"), accumulator, |a| a.mul_narrow(&rational_8), |a| a * &rational_8);
        mul_pair(c, &format!("{size}/R32"), accumulator, |a| a.mul_narrow(&rational_32), |a| a * &rational_32);
        mul_pair(c, &format!("{size}/R64"), accumulator, |a| a.mul_narrow(&rational_64), |a| a * &rational_64);
        mul_pair(c, &format!("{size}/Big"), accumulator, |a| a.mul_narrow(&big), |a| a * &big);
    }

    // The accumulator is `3^161 / 5^110`, so a factor five in the narrow value has to be cancelled
    // and a denominator sharing one forces a reduction. These are the cases that separate a gcd
    // that is skipped, one that runs over a single word, and one that runs over every word.
    let accumulator = RationalBig::from_str(W4).unwrap();
    let shared_denominator = Rational64::new(3, 25).unwrap();
    let coprime_denominator = Rational64::new(3, 7).unwrap();
    let cancelling = Rational64::new(25, 7).unwrap();
    let cancelling_integer: i64 = 25;

    add_pair(c, "norm/R64-shared-den", &accumulator,
        |a| a.add_narrow(&shared_denominator), |a| *a += shared_denominator);
    add_pair(c, "norm/R64-coprime-den", &accumulator,
        |a| a.add_narrow(&coprime_denominator), |a| *a += coprime_denominator);
    mul_pair(c, "norm/R64-cancels", &accumulator,
        |a| a.mul_narrow(&cancelling), |a| a * &cancelling);
    mul_pair(c, "norm/i64-cancels", &accumulator,
        |a| a.mul_narrow(&cancelling_integer), |a| a * cancelling_integer);
}

// The matrix is well over a hundred pairs, which at the default sample count takes long enough
// that it stops being run. The measured spread between a pair is orders of magnitude, so a shorter
// measurement still separates the cases this is here to separate.
/// The shape a sparse inner product has: a column of narrow coefficients against a dense vector of
/// wide ones, accumulated into a wide total.
///
/// The two spellings differ in whether the product is built and then added, or added as it is
/// formed. For a coefficient of one there is no product to build at all.
fn inner_product(c: &mut Criterion) {
    // A shared denominator, so accumulating stays on the cheap equal-denominator path and what is
    // measured is the per-term work rather than the accumulator's growth.
    let pi: Vec<RationalBig> = (1..=32)
        .map(|i| RationalBig::from_str(W4).unwrap() * Rational64::new(i, 1).unwrap())
        .collect();

    fn pair<N>(c: &mut Criterion, id: &str, column: &[(usize, N)], pi: &[RationalBig])
    where
        RationalBig: Absorb<N>,
    {
        c.bench_function(&format!("absorb: inner/{id}/two-step"), |b| b.iter(|| {
            let mut total = RationalBig::from(0);
            for (i, value) in black_box(column) {
                total += pi[*i].mul_narrow(value);
            }
            black_box(total)
        }));
        c.bench_function(&format!("absorb: inner/{id}/fused"), |b| b.iter(|| {
            let mut total = RationalBig::from(0);
            for (i, value) in black_box(column) {
                total.add_mul_narrow(value, &pi[*i]);
            }
            black_box(total)
        }));
    }

    let ones: Vec<(usize, One)> = (0..32).map(|i| (i, One)).collect();
    pair(c, "One", &ones, &pi);
    let signed: Vec<(usize, SignedOne)> = (0..32)
        .map(|i| (i, if i % 2 == 0 { SignedOne::PlusOne } else { SignedOne::MinusOne }))
        .collect();
    pair(c, "SignedOne", &signed, &pi);
    let rationals: Vec<(usize, Rational64)> = (0..32)
        .map(|i| (i, Rational64::new(i as i64 + 1, 7).unwrap()))
        .collect();
    pair(c, "R64", &rationals, &pi);
    let integers: Vec<(usize, i64)> = (0..32).map(|i| (i, i as i64 + 1)).collect();
    pair(c, "i64", &integers, &pi);
}

criterion_group! {
    name = group;
    config = Criterion::default()
        .measurement_time(Duration::from_millis(700))
        .warm_up_time(Duration::from_millis(200))
        .sample_size(50);
    targets = matrix, inner_product
}
