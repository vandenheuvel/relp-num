//! # The greatest common divisor of two fixed width rationals
//!
//! The denominator of the answer is the least common multiple of the two denominators, which is
//! larger than either of them, so this is the one place where a fixed width answer can fail to
//! exist. It is reported rather than wrapped.
use crate::rational::Ratio;
use crate::rational::small::ops::building_blocks::{
    gcd8, gcd16, gcd32, gcd64, gcd128, gcd_usize,
};
use crate::sign::Sign;
use crate::traits::Gcd;
use crate::{
    Rational8, Rational16, Rational32, Rational64, Rational128, RationalUsize,
};

macro_rules! gcd_small {
    ($($name:ty => $unsigned:ty, $gcd:ident);+ $(;)?) => {$(
        impl Gcd for $name {
            fn gcd(&self, other: &Self) -> Option<Self> {
                // The routine below refuses one as an operand, which costs it an allocation in the
                // arbitrary precision case and is answered here rather than there.
                fn divisor(left: $unsigned, right: $unsigned) -> $unsigned {
                    if left == 1 || right == 1 { 1 } else { $gcd(left, right) }
                }

                Some(match (self.sign, other.sign) {
                    (Sign::Zero, Sign::Zero) => Ratio {
                        sign: Sign::Zero,
                        numerator: 0,
                        denominator: 1,
                    },
                    // Zero is an integer multiple of every value, so the other one divides the
                    // pair. Only its magnitude does the dividing.
                    (Sign::Zero, _) => Ratio { sign: Sign::Positive, ..*other },
                    (_, Sign::Zero) => Ratio { sign: Sign::Positive, ..*self },
                    _ => {
                        let shared = divisor(self.denominator, other.denominator);
                        Ratio {
                            sign: Sign::Positive,
                            numerator: divisor(self.numerator, other.numerator),
                            denominator: (self.denominator / shared)
                                .checked_mul(other.denominator)?,
                        }
                    }
                })
            }
        }
    )+}
}

gcd_small!(
    Rational8 => u8, gcd8;
    Rational16 => u16, gcd16;
    Rational32 => u32, gcd32;
    Rational64 => u64, gcd64;
    Rational128 => u128, gcd128;
    RationalUsize => usize, gcd_usize;
);

#[cfg(test)]
mod test {
    use crate::{Gcd, Rational8, R8, R64};

    #[test]
    fn the_same_answers_as_the_wide_type() {
        assert_eq!(R8!(4).gcd(&R8!(6)), Some(R8!(2)));
        assert_eq!(R8!(1, 2).gcd(&R8!(1, 3)), Some(R8!(1, 6)));
        assert_eq!(R8!(3, 4).gcd(&R8!(5, 6)), Some(R8!(1, 12)));
        assert_eq!(R8!(-4).gcd(&R8!(6)), Some(R8!(2)));
        assert_eq!(R8!(0).gcd(&R8!(0)), Some(R8!(0)));
        assert_eq!(R8!(0).gcd(&R8!(-6)), Some(R8!(6)));
        assert_eq!(R64!(9, 10).gcd(&R64!(6, 25)), Some(R64!(3, 50)));
    }

    /// The one case the wide type does not have.
    #[test]
    fn a_result_that_does_not_fit_is_reported() {
        // 1/200 and 1/3 have 600 as the least common multiple of their denominators.
        assert_eq!(R8!(1, 200).gcd(&R8!(1, 3)), None);
        // The same pair fits once there is room for it.
        assert_eq!(R64!(1, 200).gcd(&R64!(1, 3)), Some(R64!(1, 600)));
    }

    #[test]
    fn dividing_by_it_leaves_coprime_integers() {
        for (left, right) in [
            (R8!(1, 2), R8!(1, 3)),
            (R8!(3, 4), R8!(5, 6)),
            (R8!(9), R8!(6)),
        ] {
            let divisor: Rational8 = left.gcd(&right).unwrap();
            let one = left / divisor;
            let other = right / divisor;

            assert_eq!(one * divisor, left);
            assert_eq!(other * divisor, right);
            assert_eq!(one.gcd(&other), Some(R8!(1)));
        }
    }
}
