use std::convert::TryInto;
use std::fmt;
use std::str::FromStr;

use num_traits::{One, Zero};
use num_traits::ToPrimitive;

use crate::non_zero::NonZeroSign;
use crate::NonZero;
use crate::rational::big::Big;
use crate::rational::small::{Rational128, Rational16, Rational32, Rational64, Rational8};
use crate::rational::small::{NonZeroRational128, NonZeroRational16, NonZeroRational32, NonZeroRational64, NonZeroRational8};
use crate::rational::small::gcd_scalar;
use crate::rational::small::ops::building_blocks::{simplify128, simplify16, simplify32, simplify64, simplify8};
use crate::sign::{Sign, Signed};

macro_rules! signed_floor {
    ($value:expr, $target:ty) => {
        {
            let floor = $value.numerator / $value.denominator;
            floor.try_into().ok()
                .map(|value: $target| match $value.sign {
                    Sign::Zero | Sign::Positive => value,
                    Sign::Negative => -value,
                })
        }
    }
}

macro_rules! unsigned_floor {
    ($value:expr) => {
        {
            match $value.sign {
                Sign::Zero | Sign::Positive => {
                    let floor = $value.numerator / $value.denominator;
                    floor.try_into().ok()
                }
                Sign::Negative => None,
            }
        }
    }
}

macro_rules! float {
    ($value:expr, $target:ty) => {
        {
            let ratio = $value.numerator as $target / $value.denominator as $target;
            let signed_ratio = match $value.sign {
                Sign::Zero | Sign::Positive => ratio,
                Sign::Negative => -ratio,
            };

            Some(signed_ratio)
        }
    }
}

macro_rules! creation {
    ($name:ident, $ity:ty, $uty:ty, $gcd_name:ident, $simplify_name:ident) => {
        impl $name {
            #[must_use]
            pub fn new(numerator: $ity, mut denominator: $uty) -> Option<Self> {
                if denominator.is_zero() {
                    None
                } else {
                    Some({
                        let mut numerator_abs = numerator.unsigned_abs();
                        if numerator == 0 {
                            <Self as num_traits::Zero>::zero()
                        } else if numerator_abs == denominator {
                            Self {
                                sign: Signed::signum(&numerator),
                                numerator: 1,
                                denominator: 1,
                            }
                        } else {
                            if numerator_abs != 1 && denominator != 1 {
                                let gcd = gcd_scalar(numerator_abs as usize, denominator as usize) as $uty;

                                numerator_abs /= gcd;
                                denominator /= gcd;
                            }

                            Self {
                                sign: Signed::signum(&numerator),
                                numerator: numerator_abs,
                                denominator,
                            }
                        }
                    })
                }
            }
            pub fn new_signed<T: Into<Sign>>(sign: T, numerator: $uty, denominator: $uty) -> Self {
                debug_assert_ne!(denominator, 0);
                let sign = sign.into();
                debug_assert!((numerator == 0) == (sign == Sign::Zero));

                match sign {
                    Sign::Positive => debug_assert_ne!(numerator, 0),
                    Sign::Zero => {
                        debug_assert_eq!(numerator, 0);
                        return <Self as num_traits::Zero>::zero();
                    },
                    Sign::Negative => {}
                }

                let (numerator, denominator) = $simplify_name(numerator, denominator);

                Self {
                    sign,
                    numerator,
                    denominator,
                }
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self.sign {
                    Sign::Positive => {}
                    Sign::Zero => return f.write_str("0"),
                    Sign::Negative => f.write_str("-")?,
                }

                fmt::Debug::fmt(&self.numerator, f)?;
                if !self.denominator.is_one() {
                    f.write_str(" / ")?;
                    fmt::Debug::fmt(&self.denominator, f)?;
                }

                Ok(())
            }
        }

        impl num_traits::FromPrimitive for $name {
            #[must_use]
            #[inline]
            fn from_i64(n: i64) -> Option<Self> {
                if n.unsigned_abs() <= <$uty>::MAX as u64 {
                    Some(Self {
                        sign: Signed::signum(&n),
                        numerator: n.unsigned_abs() as $uty,
                        denominator: 1,
                    })
                } else {
                    None
                }
            }

            #[must_use]
            #[inline]
            fn from_u64(n: u64) -> Option<Self> {
                if n <= <$uty>::MAX as u64 {
                    Some(Self {
                        sign: Signed::signum(&n),
                        numerator: n as $uty,
                        denominator: 1,
                    })
                } else {
                    None
                }
            }

            #[must_use]
            #[inline]
            fn from_f32(n: f32) -> Option<Self> {
                Big::<8>::from_f32(n).map(Self::from_big_if_it_fits).flatten()
            }

            #[must_use]
            #[inline]
            fn from_f64(n: f64) -> Option<Self> {
                Big::<16>::from_f64(n).map(Self::from_big_if_it_fits).flatten()
            }
        }

        impl ToPrimitive for $name {
            fn to_isize(&self) -> Option<isize> {
                signed_floor!(self, isize)
            }

            fn to_i8(&self) -> Option<i8> {
                signed_floor!(self, i8)
            }

            fn to_i16(&self) -> Option<i16> {
                signed_floor!(self, i16)
            }

            fn to_i32(&self) -> Option<i32> {
                signed_floor!(self, i32)
            }

            fn to_i64(&self) -> Option<i64> {
                signed_floor!(self, i64)
            }

            fn to_i128(&self) -> Option<i128> {
                signed_floor!(self, i128)
            }

            fn to_usize(&self) -> Option<usize> {
                unsigned_floor!(self)
            }

            fn to_u8(&self) -> Option<u8> {
                unsigned_floor!(self)
            }

            fn to_u16(&self) -> Option<u16> {
                unsigned_floor!(self)
            }

            fn to_u32(&self) -> Option<u32> {
                unsigned_floor!(self)
            }

            fn to_u64(&self) -> Option<u64> {
                unsigned_floor!(self)
            }

            fn to_u128(&self) -> Option<u128> {
                unsigned_floor!(self)
            }

            fn to_f32(&self) -> Option<f32> {
                float!(self, f32)
            }

            fn to_f64(&self) -> Option<f64> {
                float!(self, f64)
            }
        }

        impl FromStr for $name {
            type Err = &'static str;

            fn from_str(from: &str) -> Result<Self, Self::Err> {
                Big::<8>::from_str(from)
                    .map(|big| match Self::from_big_if_it_fits(big) {
                        Some(value) => Ok(value),
                        None => Err("value was too large for this type"),
                    })
                    .flatten()
            }
        }

        impl $name {
            fn from_big_if_it_fits<const S: usize>(big: Big<S>) -> Option<Self> {
                if num_traits::Zero::is_zero(&big) {
                    return Some(<Self as num_traits::Zero>::zero());
                }

                if big.numerator.len() == 1 && big.denominator.len() == 1 {
                    if big.numerator[0] <= <$uty>::MAX as usize && big.denominator[0] <= <$uty>::MAX as usize {
                        return Some(Self {
                            sign: big.sign,
                            numerator: big.numerator[0] as $uty,
                            denominator: big.denominator[0] as $uty,
                        })
                    }
                }

                None
            }
        }

        impl From<&$name> for $name {
            #[must_use]
            #[inline]
            fn from(other: &$name) -> Self {
                *other
            }
        }

        impl NonZero for $name {
            #[must_use]
            #[inline]
            fn is_not_zero(&self) -> bool {
                self.numerator != 0
            }
        }

        impl num_traits::Zero for $name {
            #[must_use]
            #[inline]
            fn zero() -> Self {
                Self {
                    sign: Sign::Zero,
                    numerator: 0,
                    denominator: 1,
                }
            }

            #[inline]
            fn set_zero(&mut self) {
                self.sign = Sign::Zero;
                self.numerator = 0;
                self.denominator = 1;
            }

            #[must_use]
            #[inline]
            fn is_zero(&self) -> bool {
                self.sign == Sign::Zero
            }
        }
    }
}

creation!(Rational8, i8, u8, gcd8, simplify8);
creation!(Rational16, i16, u16, gcd16, simplify16);
creation!(Rational32, i32, u32, gcd32, simplify32);
creation!(Rational64, i64, u64, gcd64, simplify64);
creation!(Rational128, i128, u128, gcd128, simplify128);


macro_rules! creation_non_zero {
    ($name:ident, $ity:ty, $uty:ty, $gcd_name:ident, $simplify_name:ident) => {
        impl NonZero for $name {
            #[must_use]
            #[inline]
            fn is_not_zero(&self) -> bool {
                true
            }
        }
    }
}

creation_non_zero!(NonZeroRational8, i8, u8, gcd8, simplify8);
creation_non_zero!(NonZeroRational16, i16, u16, gcd16, simplify16);
creation_non_zero!(NonZeroRational32, i32, u32, gcd32, simplify32);
creation_non_zero!(NonZeroRational64, i64, u64, gcd64, simplify64);
creation_non_zero!(NonZeroRational128, i128, u128, gcd128, simplify128);

macro_rules! impl_one {
    ($name:ident, $sign:ident) => {
        impl num_traits::One for $name {
            #[must_use]
            #[inline]
            fn one() -> Self {
                Self {
                    sign: $sign::Positive,
                    numerator: 1,
                    denominator: 1,
                }
            }

            #[inline]
            fn set_one(&mut self) {
                self.sign = $sign::Positive;
                self.numerator = 1;
                self.denominator = 1;
            }

            #[must_use]
            #[inline]
            fn is_one(&self) -> bool {
                self.numerator == 1 && self.denominator == 1 && self.sign == $sign::Positive
            }
        }
    }
}
impl_one!(Rational8, Sign);
impl_one!(Rational16, Sign);
impl_one!(Rational32, Sign);
impl_one!(Rational64, Sign);
impl_one!(Rational128, Sign);
impl_one!(NonZeroRational8, NonZeroSign);
impl_one!(NonZeroRational16, NonZeroSign);
impl_one!(NonZeroRational32, NonZeroSign);
impl_one!(NonZeroRational64, NonZeroSign);
impl_one!(NonZeroRational128, NonZeroSign);

macro_rules! size_dependent_unsigned {
    ($name:ty, $uty:ty, $other:ty, $simplify:ident) => {
        impl From<$other> for $name {
            #[must_use]
            #[inline]
            fn from(other: $other) -> Self {
                Self {
                    sign: Signed::signum(&other),
                    numerator: other as $uty,
                    denominator: 1,
                }
            }
        }
        impl From<&$other> for $name {
            #[must_use]
            #[inline]
            fn from(other: &$other) -> Self {
                Self {
                    sign: Signed::signum(other),
                    numerator: *other as $uty,
                    denominator: 1,
                }
            }
        }
        impl From<($other, $other)> for $name {
            #[must_use]
            #[inline]
            fn from(other: ($other, $other)) -> Self {
                assert_ne!(other.1, 0, "attempt to divide by zero");

                let (numerator, denominator) = $simplify(other.0, other.1);

                Self {
                    sign: Signed::signum(&other.0) * Signed::signum(&other.1),
                    numerator: numerator as $uty,
                    denominator: denominator as $uty,
                }
            }
        }
    }
}

size_dependent_unsigned!(Rational8, u8, u8, simplify8);
size_dependent_unsigned!(Rational16, u16, u8, simplify8);
size_dependent_unsigned!(Rational16, u16, u16, simplify16);
size_dependent_unsigned!(Rational32, u32, u8, simplify8);
size_dependent_unsigned!(Rational32, u32, u16, simplify16);
size_dependent_unsigned!(Rational32, u32, u32, simplify32);
size_dependent_unsigned!(Rational64, u64, u8, simplify8);
size_dependent_unsigned!(Rational64, u64, u16, simplify16);
size_dependent_unsigned!(Rational64, u64, u32, simplify32);
size_dependent_unsigned!(Rational64, u64, u64, simplify64);
size_dependent_unsigned!(Rational128, u128, u8, simplify8);
size_dependent_unsigned!(Rational128, u128, u16, simplify16);
size_dependent_unsigned!(Rational128, u128, u32, simplify32);
size_dependent_unsigned!(Rational128, u128, u64, simplify64);
size_dependent_unsigned!(Rational128, u128, u128, simplify128);

macro_rules! size_dependent_signed {
    ($name:ty, $uty:ty, $other_signed:ty, $simplify:ident) => {
        impl From<$other_signed> for $name {
            #[must_use]
            #[inline]
            fn from(other: $other_signed) -> Self {
                Self {
                    sign: Signed::signum(&other),
                    numerator: other.unsigned_abs() as $uty,
                    denominator: 1,
                }
            }
        }
        impl From<&$other_signed> for $name {
            #[must_use]
            #[inline]
            fn from(other: &$other_signed) -> Self {
                Self {
                    sign: Signed::signum(other),
                    numerator: other.unsigned_abs() as $uty,
                    denominator: 1,
                }
            }
        }
        impl From<($other_signed, $other_signed)> for $name {
            #[must_use]
            #[inline]
            fn from(other: ($other_signed, $other_signed)) -> Self {
                assert_ne!(other.1, 0, "attempt to divide by zero");

                let (numerator, denominator) = $simplify(other.0.unsigned_abs(), other.1.unsigned_abs());

                Self {
                    sign: Signed::signum(&other.0) * Signed::signum(&other.1),
                    numerator: numerator as $uty,
                    denominator: denominator as $uty,
                }
            }
        }
    }
}

size_dependent_signed!(Rational8, u8, i8, simplify8);
size_dependent_signed!(Rational16, u16, i8, simplify8);
size_dependent_signed!(Rational16, u16, i16, simplify16);
size_dependent_signed!(Rational32, u32, i8, simplify8);
size_dependent_signed!(Rational32, u32, i16, simplify16);
size_dependent_signed!(Rational32, u32, i32, simplify32);
size_dependent_signed!(Rational64, u64, i8, simplify8);
size_dependent_signed!(Rational64, u64, i16, simplify16);
size_dependent_signed!(Rational64, u64, i32, simplify32);
size_dependent_signed!(Rational64, u64, i64, simplify64);
size_dependent_signed!(Rational128, u128, i8, simplify8);
size_dependent_signed!(Rational128, u128, i16, simplify16);
size_dependent_signed!(Rational128, u128, i32, simplify32);
size_dependent_signed!(Rational128, u128, i64, simplify64);
size_dependent_signed!(Rational128, u128, i128, simplify128);

#[cfg(test)]
mod test {
    use num_traits::ToPrimitive;

    use crate::{R16, R32, R64, R8, Rational16, Rational32, Rational8};

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
        assert_eq!(Rational8::from(4_u8), R8!(4));
        assert_eq!(Rational16::from(-4_i8), R16!(-4));
        assert_eq!(Rational8::from(&4_u8), R8!(4));
        assert_eq!(Rational16::from(&-4_i8), R16!(-4));
        assert_eq!(Rational16::from((-4_i8, 2_i8)), R16!(-2));
        assert_eq!(Rational16::from((4_u8, 2_u8)), R16!(2));
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
    fn test_from_div_zero() {
        Rational32::from((4, 0));
    }
}
