//! # The greatest common divisor of two arbitrary precision rationals
use smallvec::SmallVec;

use crate::integer::big::ops::normalize::{gcd, simplify_fraction_without_info};
use crate::integer::big::{NonZeroUbig, Ubig};
use crate::rational::big::Big;
use crate::sign::Sign;
use crate::traits::Gcd;

/// Never fails: the numerator of the result divides both numerators and the denominator is a
/// product of the two denominators, and neither can run out of room.
impl<const S: usize> Gcd for Big<S> {
    fn gcd(&self, other: &Self) -> Option<Self> {
        Some(match (self.sign, other.sign) {
            (Sign::Zero, Sign::Zero) => <Self as num_traits::Zero>::zero(),
            // Every integer multiple of a value is a multiple of it, and zero is one of them, so
            // the other value divides the pair. Only its magnitude does the dividing.
            (Sign::Zero, _) => Self {
                sign: Sign::Positive,
                numerator: other.numerator.clone(),
                denominator: other.denominator.clone(),
            },
            (_, Sign::Zero) => Self {
                sign: Sign::Positive,
                numerator: self.numerator.clone(),
                denominator: self.denominator.clone(),
            },
            _ => Self {
                sign: Sign::Positive,
                numerator: numerator_gcd(&self.numerator, &other.numerator),
                denominator: denominator_lcm(&self.denominator, &other.denominator),
            },
        })
    }
}

/// The greatest common divisor of two values that are not zero.
///
/// The routine this calls refuses the cases that cost it an allocation to no purpose, so they are
/// answered here.
fn numerator_gcd<const S: usize>(left: &Ubig<S>, right: &Ubig<S>) -> Ubig<S> {
    if num_traits::One::is_one(left) || num_traits::One::is_one(right) {
        return Ubig::new(1);
    }
    if **left == **right {
        return left.clone();
    }

    // SAFETY: Both are well formed and not empty, neither is one, and they differ.
    unsafe { Ubig::from_inner_unchecked(gcd(left, right)) }
}

/// The least common multiple of two values that are not zero.
///
/// Written as `(left / gcd(left, right)) * right`, which is the order that keeps the intermediate
/// no larger than the answer.
fn denominator_lcm<const S: usize>(left: &NonZeroUbig<S>, right: &NonZeroUbig<S>) -> NonZeroUbig<S> {
    let mut reduced = SmallVec::<[usize; S]>::from_slice(left);
    let mut other = SmallVec::<[usize; S]>::from_slice(right);
    // SAFETY: Both are well formed and not zero.
    unsafe { simplify_fraction_without_info(&mut reduced, &mut other) };

    // SAFETY: Dividing a value that is not zero by something that divides it leaves it not zero,
    // and well formed.
    let reduced = unsafe { NonZeroUbig::from_inner_unchecked(reduced) };
    reduced * right.clone()
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::{Gcd, RationalBig, RB};

    fn big(value: &str) -> RationalBig {
        RationalBig::from_str(value).unwrap()
    }

    #[test]
    fn integers_get_the_ordinary_answer() {
        assert_eq!(RB!(4).gcd(&RB!(6)), Some(RB!(2)));
        assert_eq!(RB!(7).gcd(&RB!(13)), Some(RB!(1)));
        assert_eq!(RB!(12).gcd(&RB!(12)), Some(RB!(12)));
        assert_eq!(RB!(1).gcd(&RB!(9)), Some(RB!(1)));
        assert_eq!(RB!(9).gcd(&RB!(1)), Some(RB!(1)));
    }

    #[test]
    fn the_sign_of_the_operands_says_nothing_about_what_divides_them() {
        assert_eq!(RB!(-4).gcd(&RB!(6)), Some(RB!(2)));
        assert_eq!(RB!(-4).gcd(&RB!(-6)), Some(RB!(2)));
    }

    #[test]
    fn zero_is_a_multiple_of_everything() {
        assert_eq!(RB!(0).gcd(&RB!(0)), Some(RB!(0)));
        assert_eq!(RB!(0).gcd(&RB!(-6)), Some(RB!(6)));
        assert_eq!(RB!(6, 5).gcd(&RB!(0)), Some(RB!(6, 5)));
    }

    /// `gcd(p1 / q1, p2 / q2) = gcd(p1, p2) / lcm(q1, q2)`.
    #[test]
    fn fractions_take_the_numerator_gcd_over_the_denominator_lcm() {
        assert_eq!(RB!(1, 2).gcd(&RB!(1, 3)), Some(RB!(1, 6)));
        assert_eq!(RB!(2, 3).gcd(&RB!(4, 9)), Some(RB!(2, 9)));
        assert_eq!(RB!(3, 4).gcd(&RB!(5, 6)), Some(RB!(1, 12)));
        assert_eq!(RB!(1, 2).gcd(&RB!(1, 2)), Some(RB!(1, 2)));
    }

    /// Dividing by the answer has to leave integers, and integers with nothing left in common.
    #[test]
    fn dividing_by_it_leaves_coprime_integers() {
        for (left, right) in [
            (RB!(1, 2), RB!(1, 3)),
            (RB!(3, 4), RB!(5, 6)),
            (RB!(-7, 15), RB!(14, 25)),
            (RB!(9), RB!(6)),
        ] {
            let divisor = left.gcd(&right).unwrap();
            let one = &left / &divisor;
            let other = &right / &divisor;

            assert_eq!(&one * &divisor, left);
            assert_eq!(&other * &divisor, right);
            assert_eq!(one.gcd(&other), Some(RB!(1)));
        }
    }

    /// Against the definition, over every small fraction pair.
    ///
    /// The answer has to divide both, and nothing larger may: a candidate twice as large fails to
    /// divide one of them, or the answer was not the greatest.
    #[test]
    fn every_small_pair_against_the_definition() {
        // A value in lowest terms is an integer exactly when its denominator is one.
        let divides = |value: &RationalBig, divisor: &RationalBig| {
            num_traits::One::is_one(&(value / divisor).denominator)
        };

        for p1 in 1..10_i64 {
            for q1 in 1..10_i64 {
                for p2 in 1..10_i64 {
                    for q2 in 1..10_i64 {
                        let left = RationalBig::from((p1, q1));
                        let right = RationalBig::from((p2, q2));
                        let divisor = left.gcd(&right).unwrap();

                        assert!(divides(&left, &divisor), "{left} / {divisor}");
                        assert!(divides(&right, &divisor), "{right} / {divisor}");

                        // Anything strictly larger has to fail on one of the two, or the answer
                        // was not the greatest common one.
                        for multiple in [2_i64, 3, 5] {
                            let larger = &divisor * &RationalBig::from(multiple);
                            assert!(
                                !divides(&left, &larger) || !divides(&right, &larger),
                                "{larger} divides both {left} and {right}",
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn values_that_do_not_fit_in_a_word() {
        let left = big("340282366920938463463374607431768211456"); // 2 ** 128
        let right = big("170141183460469231731687303715884105728"); // 2 ** 127
        assert_eq!(left.gcd(&right), Some(right.clone()));

        let third = &RationalBig::from(1) / &left;
        assert_eq!(third.gcd(&third), Some(third));
    }
}
