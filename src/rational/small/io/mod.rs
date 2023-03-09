use std::convert::TryInto;
use std::ops::{Add, Mul};
use std::str::FromStr;

use paste::paste;
use crate::NonZero;
use std::num::{NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroIsize};
use std::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize};
use num_traits::One;

use crate::sign::{NonZeroSign, PositivelySigned};
use crate::rational::big::Big;
use crate::rational::small::{Ratio};
use crate::rational::small::{Rational128, Rational16, Rational32, Rational64, Rational8, RationalSize};
use crate::rational::small::{PositiveRational128, PositiveRational16, PositiveRational32, PositiveRational64, PositiveRational8, PositiveRationalSize};
use crate::rational::small::{NonZeroRational128, NonZeroRational16, NonZeroRational32, NonZeroRational64, NonZeroRational8, NonZeroRationalSize};
use crate::rational::small::{NonNegativeRational128, NonNegativeRational16, NonNegativeRational32, NonNegativeRational64, NonNegativeRational8, NonNegativeRationalSize};
use crate::rational::small::gcd_scalar;
use crate::rational::small::ops::building_block::{simplify_128, simplify_16, simplify_32, simplify_64, simplify_8, simplify_size};
use crate::sign::{Sign, Signed};


mod fmt;
mod zero_one;

macro_rules! rational {
    [$($size:expr,)*] => {
        $(
            paste! {
                impl [<Rational $size:camel>]
                {
                    #[must_use]
                    pub fn new(numerator: [<i $size>], mut denominator: [<i $size>]) -> Option<Self> {
                        [<NonZeroI $size>]::new(denominator).map(|denominator| {
                            if numerator == 0 {
                                <Self as num_traits::Zero>::zero()
                            } else if numerator == denominator.get() {
                                <Self as num_traits::One>::one()
                            } else {
                                if numerator != 1 && denominator.get() != 1 {
                                    // TODO: Avoid this casting
                                    let gcd = gcd_scalar(numerator.unsigned_abs() as usize, denominator.get() as usize) as [<i $size>];

                                    numerator /= gcd;
                                    denominator = [<NonZeroI $size>]::new(denominator.get() / gcd).unwrap();
                                }

                                Self {
                                    numerator,
                                    denominator,
                                }
                            }
                        })
                    }
                }

                impl FromStr for [<Rational $size:camel>] {
                    type Err = &'static str;

                    fn from_str(from: &str) -> Result<Self, Self::Err> {
                        Big::<8>::from_str(from)
                            .map(TryFrom::try_from)
                            .flatten()
                    }
                }

                impl<const S: usize> TryFrom<Big<S>> for [<Rational $size:camel>] {
                    type Error = &'static str;

                    fn try_from(value: Big<S>) -> Result<Self, Self::Error> {
                        if num_traits::Zero::is_zero(&value) {
                            return Ok(<Self as num_traits::Zero>::zero());
                        }

                        if value.numerator.len() == 1 && value.denominator.len() == 1 {
                            let numerator = value.numerator[0];
                            let denominator = value.denominator[0];

                            if numerator <= [<i $size>]::MAX as usize && denominator <= [<NonZeroI $size>]::MAX.get() as usize {
                                // TODO: Use sign of value
                                return Ok(Self {
                                    numerator: numerator as [<i $size>],
                                    denominator: [<NonZeroI $size>]::new(denominator as [<i $size>]).unwrap(),
                                });
                            }
                        }

                        Err("value was too large for this type")
                    }
                }

                impl From<&Self> for [<Rational $size:camel>] {
                    #[must_use]
                    #[inline]
                    fn from(other: &Self) -> Self {
                        *other
                    }
                }
            }
        )*
    }
}
rational![8, 16, 32, 64, 128, "size",];

// TODO: Once the NonZeroI* types implement One, use a generic trait impl
// impl<N, D: One + NonZero> From<N> for Ratio<N, D> {
//     #[must_use]
//     #[inline]
//     fn from(value: N) -> Self {
//         Self {
//             numerator: value,
//             denominator: One::one(),
//         }
//     }
// }
// impl<N: Copy, D: One + NonZero> From<&N> for Ratio<N, D> {
//     #[must_use]
//     #[inline]
//     fn from(value: &N) -> Self {
//         From::from(value.copy())
//     }
// }

macro_rules! triangle {
    ($target:ident, []) => {};
    ($target:ident, [$largest_size:expr, $($smaller_sizes:tt)*]) => {
        $target!($largest_size, [$($smaller_sizes)*]);
        triangle!($target, [$($smaller_sizes)*]);
    };
}

macro_rules! from_single_rational {
    ($size:expr, $other_signedness:expr, [$($other_size:expr,)*]) => {
        $(
            paste! {
                impl From<[<$other_signedness $other_size>]> for [<Rational $size>] {
                    #[must_use]
                    #[inline]
                    fn from(other: [<$other_signedness $other_size>]) -> Self {
                        Self {
                            numerator: other as [<i $size>],
                            denominator: [<NonZeroI $size>]::new(1).unwrap(),
                        }
                    }
                }
                impl From<&[<$other_signedness $other_size>]> for [<Rational $size>] {
                    #[must_use]
                    #[inline]
                    fn from(value: &[<$other_signedness $other_size>]) -> Self {
                        From::from(*value)
                    }
                }
            }
        )*
    }
}
macro_rules! from_tuple_rational {
    ($size:expr, $smaller_size:expr) => {
        paste! {
            impl From<([<i $smaller_size>], [<i $smaller_size>])> for [<Rational $size>] {
                #[must_use]
                #[inline]
                fn from(value: ([<i $smaller_size>], [<i $smaller_size>])) -> Self {
                    assert_ne!(value.1, 0, "attempt to divide by zero");

                    let (numerator, denominator) = [<simplify_ $smaller_size>](value.0.unsigned_abs(), value.1.unsigned_abs());

                    Self {
                        numerator: (numerator as [<i $smaller_size>] * value.0.signum() * value.1.signum()) as [<i $size>],
                        denominator: [<NonZeroI $size>]::new(denominator as [<i $size>]).unwrap(),
                    }
                }
            }
        }
    }
}
macro_rules! size_dependent_rational {
    ($size:expr, [$($smaller_size:expr,)*]) => {
        from_single_rational!($size, "i", [$size,]);
        from_single_rational!($size, "i", [$($smaller_size,)*]);
        from_single_rational!($size, "u", [$($smaller_size,)*]);
        from_tuple_rational!($size, $size);
        $(
            from_tuple_rational!($size, $smaller_size);
        )*
    }
}
triangle!(size_dependent_rational, [128, 64, 32, 16, 8,]);

macro_rules! from_single_non_zero_rational {
    ($size:expr, $other_signedness:expr, [$($other_size:expr,)*]) => {
        $(
            paste! {
                impl From<[<$other_signedness $other_size>]> for [<NonZeroRational $size>] {
                    #[must_use]
                    #[inline]
                    fn from(value: [<$other_signedness $other_size>]) -> Self {
                        assert_ne!(value, 0, "attempt to initialize a non-zero typed variable with a zero value");

                        Self {
                            numerator: [<NonZeroI $size>]::new(value as [<i $size>]).unwrap(),
                            denominator: [<NonZeroI $size>]::new(1).unwrap(),
                        }
                    }
                }
                impl From<&[<$other_signedness $other_size>]> for [<NonZeroRational $size>] {
                    #[must_use]
                    #[inline]
                    fn from(value: &[<$other_signedness $other_size>]) -> Self {
                        From::from(*value)
                    }
                }
            }
        )*
    }
}
macro_rules! from_tuple_non_zero_rational {
    ($size:expr, $smaller_size:expr) => {
        paste! {
            impl From<([<i $smaller_size>], [<i $smaller_size>])> for [<NonZeroRational $size>] {
                #[must_use]
                #[inline]
                fn from(value: ([<i $smaller_size>], [<i $smaller_size>])) -> Self {
                    assert_ne!(value.0, 0, "attempt to initialize a non-zero typed variable with a zero value");
                    assert_ne!(value.1, 0, "attempt to divide by zero");

                    let (numerator, denominator) = [<simplify_ $smaller_size>](value.0.unsigned_abs(), value.1.unsigned_abs());

                    Self {
                        numerator: [<NonZeroI $size>]::new(
                            (numerator as [<i $smaller_size>] * value.0.signum() * value.1.signum()) as [<i $size>]
                        ).unwrap(),
                        denominator: [<NonZeroI $size>]::new(denominator as [<i $size>]).unwrap(),
                    }
                }
            }
        }
    }
}
macro_rules! size_dependent_non_zero_rational {
    ($size:expr, [$($smaller_size:expr,)*]) => {
        from_single_non_zero_rational!($size, "i", [$size,]);
        from_single_non_zero_rational!($size, "i", [$($smaller_size,)*]);
        from_single_non_zero_rational!($size, "u", [$($smaller_size,)*]);
        from_tuple_non_zero_rational!($size, $size);
        $(
            from_tuple_non_zero_rational!($size, $smaller_size);
        )*
    }
}
triangle!(size_dependent_non_zero_rational, [128, 64, 32, 16, 8,]);

macro_rules! from_single_non_negative_rational {
    ($size:expr, $other_signedness:expr, [$($other_size:expr,)*]) => {
        $(
            paste! {
                impl From<[<$other_signedness $other_size>]> for [<NonNegativeRational $size>] {
                    #[must_use]
                    #[inline]
                    fn from(value: [<$other_signedness $other_size>]) -> Self {
                        assert!(value >= 0, "attempt to initialize a non-negatively typed variable with a negative value");

                        Self {
                            numerator: value as [<u $size>],
                            denominator: [<NonZeroU $size>]::new(1).unwrap(),
                        }
                    }
                }
                impl From<&[<$other_signedness $other_size>]> for [<NonNegativeRational $size>] {
                    #[must_use]
                    #[inline]
                    fn from(value: &[<$other_signedness $other_size>]) -> Self {
                        From::from(*value)
                    }
                }
            }
        )*
    }
}
macro_rules! from_tuple_non_negative_rational {
    ($size:expr, $smaller_size:expr) => {
        paste! {
            impl From<([<u $smaller_size>], [<u $smaller_size>])> for [<NonNegativeRational $size>] {
                #[must_use]
                #[inline]
                fn from(value: ([<u $smaller_size>], [<u $smaller_size>])) -> Self {
                    assert_ne!(value.1, 0, "attempt to divide by zero");

                    let (numerator, denominator) = [<simplify_ $smaller_size>](value.0, value.1);

                    Self {
                        numerator: numerator as [<u $size>],
                        denominator: [<NonZeroU $size>]::new(denominator as [<u $size>]).unwrap(),
                    }
                }
            }
        }
    }
}
macro_rules! size_dependent_non_negative_rational {
    ($size:expr, [$($smaller_size:expr,)*]) => {
        from_single_non_negative_rational!($size, "i", [$size,]);
        from_single_non_negative_rational!($size, "i", [$($smaller_size,)*]);
        from_single_non_negative_rational!($size, "u", [$size,]);
        from_single_non_negative_rational!($size, "u", [$($smaller_size,)*]);
        from_tuple_non_negative_rational!($size, $size);
        $(
            from_tuple_non_negative_rational!($size, $smaller_size);
        )*
    }
}
triangle!(size_dependent_non_negative_rational, [128, 64, 32, 16, 8,]);

macro_rules! from_single_positive_rational {
    ($size:expr, $other_signedness:expr, [$($other_size:expr,)*]) => {
        $(
            paste! {
                impl From<[<$other_signedness $other_size>]> for [<PositiveRational $size>] {
                    #[must_use]
                    #[inline]
                    fn from(value: [<$other_signedness $other_size>]) -> Self {
                        assert!(value > 0, "attempt to initialize a positively typed variable with a zero or negative value");

                        Self {
                            numerator: [<NonZeroU $size>]::new(value as [<u $size>]).unwrap(),
                            denominator: [<NonZeroU $size>]::new(1).unwrap(),
                        }
                    }
                }
                impl From<&[<$other_signedness $other_size>]> for [<PositiveRational $size>] {
                    #[must_use]
                    #[inline]
                    fn from(value: &[<$other_signedness $other_size>]) -> Self {
                        From::from(*value)
                    }
                }
            }
        )*
    }
}
macro_rules! from_tuple_positive_rational {
    ($size:expr, $smaller_size:expr) => {
        paste! {
            impl From<([<u $smaller_size>], [<u $smaller_size>])> for [<PositiveRational $size>] {
                #[must_use]
                #[inline]
                fn from(value: ([<u $smaller_size>], [<u $smaller_size>])) -> Self {
                    assert_ne!(value.1, 0, "attempt to divide by zero");

                    let (numerator, denominator) = [<simplify_ $smaller_size>](value.0, value.1);

                    Self {
                        numerator: [<NonZeroU $size>]::new(numerator as [<u $size>]).unwrap(),
                        denominator: [<NonZeroU $size>]::new(denominator as [<u $size>]).unwrap(),
                    }
                }
            }
        }
    }
}
macro_rules! size_dependent_positive_rational {
    ($size:expr, [$($smaller_size:expr,)*]) => {
        from_single_positive_rational!($size, "i", [$size,]);
        from_single_positive_rational!($size, "i", [$($smaller_size,)*]);
        from_single_positive_rational!($size, "u", [$size,]);
        from_single_positive_rational!($size, "u", [$($smaller_size,)*]);
        from_tuple_positive_rational!($size, $size);
        $(
            from_tuple_positive_rational!($size, $smaller_size);
        )*
    }
}
triangle!(size_dependent_positive_rational, [128, 64, 32, 16, 8,]);


#[cfg(test)]
mod test {
    use std::num::NonZeroU8;
    use num_traits::ToPrimitive;

    use crate::{NonNegativeRational8, R16, R32, R64, R8, Rational16, Rational32, Rational8};

    #[test]
    fn test_debug() {
        assert_eq!(format!("{:?}", R8!(2, 3)), "2 / 3");
        assert_eq!(format!("{:?}", R8!(0)), "0");
        assert_eq!(format!("{:?}", R8!(-1)), "-1");
        assert_eq!(format!("{:?}", R8!(-0)), "0");
        assert_eq!(format!("{:?}", -R8!(2, 3)), "-2 / 3");
    }

    #[test]
    fn test_from() {
        assert_eq!(Rational16::from(4_u8), R16!(4));
        assert_eq!(Rational16::from(-4_i8), R16!(-4));
        assert_eq!(NonNegativeRational8::from(&4_u8), NonNegativeRational8 { numerator: 4, denominator: NonZeroU8::new(1).unwrap() });
        assert_eq!(Rational16::from(&-4_i8), R16!(-4));
        assert_eq!(Rational16::from((-4_i8, 2_i8)), R16!(-2));
        assert_eq!(Rational16::from((4_i8, 2_i8)), R16!(2));
    }

    #[test]
    fn test_to_primitive() {
        assert_eq!(R8!(0).to_u8(), Some(0));
        assert_eq!(R8!(1, 2).to_u8(), Some(0));
        assert_eq!(R8!(3, 4).to_i8(), Some(0));
        assert_eq!(R8!(3, 2).to_i8(), Some(1));
        assert_eq!(R8!(-0).to_i8(), Some(0));
        assert_eq!(R8!(-1, 2).to_i8(), Some(0));
        assert_eq!(R8!(-3, 4).to_i8(), Some(0));
        assert_eq!(R8!(-3, 2).to_i8(), Some(-1));

        assert_eq!(Rational8::new(1, 1).unwrap().to_i32(), Some(1));
        assert_eq!(R8!(-10).to_i32(), Some(-10));
        assert_eq!(R8!(-11).to_u16(), None);
        assert_eq!(R64!(2_u64.pow(63) + 2_u64.pow(20)).to_i64(), None);
        assert_eq!(R8!(0).to_i64(), Some(0));
        assert_eq!(R8!(0).to_u64(), Some(0));
        assert_eq!(R8!(1, 2).to_u64(), Some(0));
        assert_eq!(R8!(8).to_u64(), Some(8));

        assert_eq!(R8!(0).to_f64(), Some(0_f64));
        assert_eq!(R32!(-156, 99).to_f64(), Some(-156_f64 / 99_f64));
        assert_eq!(R8!(3, 2).to_f64(), Some(1.5_f64));
        assert_eq!(R8!(-0).to_f64(), Some(0_f64));
        assert_eq!(R8!(-3, 2).to_f64(), Some(-1.5_f64));
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn test_from_div_zero() {
        Rational32::from((4, 0));
    }
}
