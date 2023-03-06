//! # Rational types of fixed size
use std::fmt;
use std::fmt::Formatter;
use std::io::Write;
use std::ops::Neg;
use std::num::{NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroIsize};
use std::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize};
use num_traits::{One, Zero};

use paste::paste;

use crate::integer::big::ops::normalize::gcd_scalar;
use crate::{NonZero};
use crate::sign::{Sign, Signed, NonZeroSign, NonZeroSigned, NonNegativeSign, NonNegativelySigned, PositiveSign, PositivelySigned};

mod io;
mod convert;
pub(crate) mod ops;

/// Ratio between two numbers.
#[derive(Copy, Clone, Eq, PartialEq)]
struct Ratio<N, D: NonZero> {
    numerator: N,
    denominator: D,
}

macro_rules! all {
    ($name:ident, $nty:ty, $dty:ty, $size:expr) => {
        #[doc = "A `"]
        #[doc = stringify!($name)]
        #[doc = "` number represented by two integers of size"]
        #[doc = stringify!($size)]
        #[doc = "."]
        /// A signed ratio between two fixed-size integers.
        pub type $name = Ratio<$nty, $dty>;
    }
}
macro_rules! implement_all {
    [$($size:expr,)*] => {
        $(
            paste::paste! {
                all!([<Rational $size>], [<i $size:lower>], [<NonZeroI $size:lower>], $size);
                all!([<NonZeroRational $size>], [<NonZeroI $size:lower>], [<NonZeroI $size:lower>], $size);
                all!([<NonNegativeRational $size>], [<u $size:lower>], [<NonZeroU $size:lower>], $size);
                all!([<PositiveRational $size>], [<NonZeroU $size:lower>], [<NonZeroU $size:lower>], $size);
            }
        )*
    }
}
implement_all![8, 16, 32, 64, 128, "Size",];

impl<N: Signed, D: NonZero> Signed for Ratio<N, D> where Self: NonZeroSigned {
    fn signum(&self) -> Sign {
        self.numerator.signum()
    }
}

impl<N: NonZero, D: NonZero> NonZero for Ratio<N, D> {
    fn is_not_zero(&self) -> bool {
        self.numerator.is_not_zero()
    }
}

impl<N: Zero, D: NonZero> Default for Ratio<N, D> {
    fn default() -> Self {
        Self::zero()
    }
}

macro_rules! can_be_negative {
    ($name:ident, $nty:ty, $dty:ty) => {

    }
}
macro_rules! implement_can_be_negative {
    [$($size:expr,)*] => {
        $(
            paste::paste! {
                can_be_negative!([<Rational $size>], [<i $size:lower>], [<NonZeroI $size:lower>]);
                can_be_negative!([<NonZeroRational $size>], [<NonZeroI $size:lower>], [<NonZeroI $size:lower>]);
            }
        )*
    }
}
implement_can_be_negative![8, 16, 32, 64, 128, Size,];
impl<N: Neg, D: NonZero> Neg for Ratio<N, D> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn neg(mut self) -> Self::Output {
        Self {
            numerator: self.numerator.neg(),
            denominator: self.denominator,
        }
    }
}

// macro_rules! rational {
//     [$($size:expr,)*] => {
//         $(
//             paste! {
//
//             }
//         )*
//     }
// }
// rational![8, 16, 32, 64, 128, "Size",];

// macro_rules! non_zero_rational {
//     [$($size:expr,)*] => {
//         $(
//
//         )*
//     }
// }
// non_zero_rational![8, 16, 32, 64, 128, Size,];
impl<N: NonZeroSigned, D: NonZero> NonZeroSigned for Ratio<N, D> {
    fn signum(&self) -> NonZeroSign {
        self.numerator.signum()
    }
}

// macro_rules! non_negative_rational {
//     [$($size:expr,)*] => {
//         $(
//             paste! {
//
//             }
//         )*
//     }
// }
// non_negative_rational![8, 16, 32, 64, 128, Size,];
impl<N: NonNegativelySigned, D: NonZero> NonNegativelySigned for Ratio<N, D> where Self: NonNegativelySigned {
    fn signum(&self) -> NonNegativeSign {
        self.numerator.signum()
    }
}

// macro_rules! positive_rational {
//     [$($size:expr,)*] => {
//         $(
//             paste! {\
//
//             }
//         )*
//     }
// }
// positive_rational![8, 16, 32, 64, 128, Size,];

impl<N: PositivelySigned, D: NonZero> PositivelySigned for Ratio<N, D> {
    fn signum(&self) -> PositiveSign {
        self.numerator.signum()
    }
}


#[cfg(test)]
mod test {
    use std::cmp::Ordering;
    use std::num::NonZeroI8;
    use std::str::FromStr;

    use num_traits::{FromPrimitive, One, Zero};

    use crate::{NonZero, NonZeroSign, NonZeroSigned, Rational128};
    use crate::{R16, R32, R64, R8};
    use crate::rational::small::Ratio;
    use crate::rational::{Rational16, Rational32, Rational64, Rational8, Sign};

    #[test]
    fn test_new() {
        assert_eq!(R8!(0, 2), Ratio { numerator: 0_i8, denominator: NonZeroI8::new(1).unwrap() });
        assert_eq!(R8!(2, 2), Ratio { numerator: 1_i8, denominator: NonZeroI8::new(1).unwrap() });
        assert_eq!(R8!(6, 2), Ratio { numerator: 3_i8, denominator: NonZeroI8::new(1).unwrap() });
        assert_eq!(R8!(-6, 2), Ratio { numerator: 3_i8, denominator: NonZeroI8::new(1).unwrap() });
    }

    #[test]
    fn test_from() {
        assert_eq!(<Rational8 as From<_>>::from(1_u8), Rational8::one());
        assert_eq!(<Rational32 as From<_>>::from(1), Rational32::one());

        assert_eq!(FromPrimitive::from_u64(16), Some(R8!(16)));
        assert_eq!(FromPrimitive::from_u16(0), Some(Rational8::zero()));
        assert_eq!(<Rational16 as FromPrimitive>::from_u32(u32::MAX), None);
        assert_eq!(FromPrimitive::from_i32(i32::MAX), Some(R32!(i32::MAX, 1)));
        assert_eq!(<Rational64 as FromPrimitive>::from_i128(i128::MAX), None);
        assert_eq!(FromPrimitive::from_i16(-1), Some(R8!(-2, 2)));

        assert_eq!(<Rational128 as FromPrimitive>::from_f64(f64::NAN), None);
        assert_eq!(<Rational64 as FromPrimitive>::from_f64(f64::INFINITY), None);
        assert_eq!(<Rational32 as FromPrimitive>::from_f64(f64::NEG_INFINITY), None);
        assert_eq!(FromPrimitive::from_f64(-0_f64), Some(Rational8::zero()));
        // u128::MAX gets rounded upwards in f64 conversion
        assert!(<Rational128 as FromPrimitive>::from_f64(u128::MAX as f64).is_none());

        assert_eq!(<Rational32 as FromPrimitive>::from_i64(i64::MAX), None);

        assert_eq!(Rational64::from((-1, 2)), R64!(-1, 2));
    }

    #[test]
    fn test_nonzero() {
        assert!(!Rational8::zero().is_not_zero());
        assert_eq!(Rational16::zero().is_zero(), !Rational16::zero().is_not_zero());

        assert_eq!(R8!(1).non_zero_signum(), NonZeroSign::Positive);
    }

    #[test]
    #[should_panic]
    fn test_sign_panic() {
        R8!(0).non_zero_signum();
    }

    #[test]
    fn test_one() {
        assert!(Rational64::zero() < Rational64::one());
        assert!(Rational64::one().is_one());
        let mut x = Rational32::zero();
        x.set_one();
        assert_eq!(x, Rational32::one());
    }

    #[test]
    fn test_cmp() {
        assert!(R8!(12) < R8!(13));
        assert!(R8!(1, 2) > R8!(1, 3));
        assert_eq!(R8!(7, 11), R8!(7, 11));
        assert!(R8!(3, 4) < R8!(5, 6));
        assert!(R8!(13) > R8!(12));
        assert_eq!(R32!(0), R32!(0));
        assert_eq!(R32!(0).partial_cmp(&R32!(0)), Some(Ordering::Equal));
        assert_eq!(R32!(12, 5).partial_cmp(&R32!(23, 10)), Some(Ordering::Greater));
        assert!(!(R32!(7, 11) < R32!(7, 11)));
        assert!(R64!(-3, 11) < R64!(3, 11));
        assert_ne!(R64!(-9, 4), R64!(9, 4));

        assert!(R8!(-3) < R8!(-2));
        assert!(R8!(-3) < R8!(0));
        assert!(R8!(-3) < R8!(2));
        assert!(R8!(-3) < R8!(3));

        assert!(Rational8::from_str("255/2").unwrap() < R8!(128));
    }

    #[test]
    fn test_eq() {
        assert_eq!(R8!(3), R8!(3));
        assert_eq!(R8!(0), R8!(0));
        assert_eq!(R8!(-1), R8!(-1));
        assert_ne!(R8!(-1), R8!(0));
        assert_ne!(R8!(-1), R8!(1));
        assert_ne!(R8!(0), R8!(1));
    }

    #[test]
    fn test_add() {
        assert_eq!(Rational64::one() + Rational64::one(), R64!(2));
        assert_eq!(R64!(3, 2) + R64!(3, 2), R64!(3));
        assert_eq!(R64!(-3, 2) + R64!(3, 2), Rational64::zero());
        assert_eq!(R64!(948, 64) + Rational64::zero(), R64!(948, 64));
        assert_eq!(-Rational64::one() + Rational64::one(), Rational64::zero());
        assert_eq!(Rational128::zero() + Rational128::one(), Rational128::one());
        assert_eq!(Rational128::zero() + -Rational128::one(), -Rational128::one());

        assert_eq!(&R32!(3, 9) + &R32!(-1, 3), R32!(0));
        assert_eq!(R8!(4, 5) + R8!(1, 5), R8!(1));
        assert_eq!(R8!(5, 1) + R8!(3, 2), R8!(13, 2));
        assert_eq!(R8!(3, 4) + R8!(3), R8!(15, 4));
        assert_eq!(R8!(3, 4) + R8!(17, 5), R8!(83, 20));
        assert_eq!(R32!(3, 4) + R32!(3, 32), R32!(27, 32));
        assert_eq!(R32!(-10) + R32!(9), R32!(-1));

        let limit = 10;
        for a in -limit..limit {
            for b in 1..limit {
                for c in -limit..limit {
                    for d in 1..limit {
                        assert_eq!(R32!(a, b as u32) + R32!(c, d as u32), R32!(a * d + c * b, b as u32 * d as u32), "{} / {} + {} / {}", a, b, c, d);
                    }
                }
            }
        }
    }

    #[test]
    fn test_sum() {
        assert_eq!((0..10).map(Rational32::from).sum::<Rational32>(), R32!(45));
        assert_eq!((0_i16..10).map(|i| Rational16::new(i, 2).unwrap()).sum::<Rational16>(), R16!(45, 2));
        let vs = vec![
            (R32!(23, 31), R32!(-699, 65)),
            (R32!(29, 31), R32!(-30736, 1885)),
        ];
        let product = vs.into_iter().map(|(a, b)| &a * &b).sum::<Rational32>();
        let constant = R32!(-2826, 155);
        assert_eq!(constant - product, R32!(5));
    }

    #[test]
    fn test_sub() {
        assert_eq!(Rational64::one() - Rational64::one(), R64!(0));
        assert_eq!(R64!(3, 2) - R64!(3, 2), R64!(0));
        assert_eq!(R64!(-3, 2) - R64!(3, 2), -R64!(3));
        assert_eq!(R64!(948, 64) - Rational64::zero(), R64!(948, 64));
        assert_eq!(-Rational64::one() - Rational64::one(), -R64!(2));
        assert_eq!(Rational64::one() - Rational64::one(), -R64!(0));
        assert_eq!(Rational128::zero() - Rational128::one(), -Rational128::one());
        assert_eq!(Rational128::zero() - -Rational128::one(), Rational128::one());

        assert_eq!(&R32!(3, 9) - &R32!(1, 3), R32!(0));
        assert_eq!(R8!(4, 5) - R8!(1, 5), R8!(3, 5));
        assert_eq!(R8!(5, 1) - R8!(3, 2), R8!(7, 2));
        assert_eq!(R8!(3, 4) - R8!(3), R8!(-9, 4));
        assert_eq!(R8!(3, 4) - R8!(17, 5), R8!(15 - 4 * 17, 20));
        assert_eq!(R8!(17, 5) - R8!(3, 4), R8!(4 * 17 - 15, 20));

        assert_eq!(R32!(3601, 155) - R32!(2826, 155), R32!(5));
        assert_eq!(R32!(-2826, 155) - R32!(-3601, 155), R32!(5));

        let limit = 10;
        for a in -limit..limit {
            for b in 1..limit {
                for c in -limit..limit {
                    for d in 1..limit {
                        assert_eq!(R32!(a, b as u32) - R32!(c, d as u32), R32!(a * d - c * b, b as u32 * d as u32), "{} / {} - {} / {}", a, b, c, d);
                    }
                }
            }
        }
    }

    #[test]
    fn test_mul() {
        assert_eq!(Rational64::one() * Rational64::one(), R64!(1));
        assert_eq!(R64!(3, 2) * R64!(3, 2), R64!(9, 4));
        assert_eq!(R64!(-3, 2) * R64!(3, 2), -R64!(9, 4));
        assert_eq!(R64!(948, 64) * Rational64::zero(), R64!(0));
        assert_eq!(-Rational64::one() * Rational64::one(), -R64!(1));
        assert_eq!(Rational64::one() * Rational64::one(), R64!(1));
        assert_eq!(Rational128::zero() * Rational128::one(), -Rational128::zero());
        assert_eq!(Rational128::zero() * -Rational128::one(), Rational128::zero());

        assert_eq!(R8!(3, 2) * R8!(4, 9), R8!(2, 3));
        assert_eq!(R32!(27, 32) * R32!(2), R32!(27, 16));

        let limit = 10;
        for a in -limit..limit {
            for b in 1..limit {
                for c in -limit..limit {
                    for d in 1..limit {
                        assert_eq!(R32!(a, b as u32) * R32!(c, d as u32), R32!(a * c, b as u32 * d as u32), "{} / {} * {} / {}", a, b, c, d);
                    }
                }
            }
        }
    }

    #[test]
    fn test_div() {
        assert_eq!(Rational64::one() / Rational64::one(), R64!(1));
        assert_eq!(R64!(3, 2) / R64!(3, 2), R64!(1));
        assert_eq!(R64!(-3, 2) / R64!(3, 2), -R64!(1));
        assert_eq!(-Rational64::one() / Rational64::one(), -R64!(1));
        assert_eq!(Rational128::zero() / Rational128::one(), -Rational128::zero());
        assert_eq!(Rational128::zero() / -Rational128::one(), Rational128::zero());
    }

    #[test]
    fn test_new_signed() {
        assert_eq!(Rational64::new_signed(Sign::Positive, 6, 18), R64!(1, 3));
        assert_eq!(Rational64::new_signed(Sign::Zero, 0, 6), R64!(0));
        assert_eq!(Rational64::new_signed(Sign::Negative, 9, 18), -R64!(1, 2));
    }

    #[test]
    #[should_panic]
    fn test_new_signed_panic_1() {
        Rational64::new_signed(Sign::Zero, 1, 1);
    }

    #[test]
    #[should_panic]
    fn test_new_signed_panic_2() {
        Rational64::new_signed(Sign::Positive, 0, 1);
    }

    #[test]
    fn test_display() {
        assert_eq!(Rational64::one().to_string(), "1");
        assert_eq!(Rational64::zero().to_string(), "0");
        assert_eq!(R64!(1, 2).to_string(), "1/2");
        assert_eq!(R64!(-1, 2).to_string(), "-1/2");
    }

    #[test]
    fn test_from_str() {
        assert_eq!(Rational8::from_str("8"), Ok(R8!(8)));
        assert_eq!(Rational8::from_str("-8"), Ok(-R8!(8)));
        assert_eq!(Rational16::from_str("-16/3"), Ok(R16!(-16, 3)));
        assert_eq!(Rational16::from_str("16/4"), Ok(R16!(16, 4)));
        assert_eq!(Rational32::from_str("4294967297"), Err("value was too large for this type"));
    }
}
