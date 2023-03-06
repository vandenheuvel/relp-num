use std::cmp::Ordering;
use std::iter::Sum;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};
use std::ops::Neg;
use paste::paste;

use crate::non_zero::NonZero;
use crate::sign::{Sign, NonZeroSign, NonNegativeSign};
use crate::rational::small::{Ratio, Rational128, Rational16, Rational32, Rational64, Rational8, RationalSize};
use crate::rational::small::{NonZeroRational128, NonZeroRational16, NonZeroRational32, NonZeroRational64, NonZeroRational8, NonZeroRationalSize};
use crate::rational::small::{NonNegativeRational128, NonNegativeRational16, NonNegativeRational32, NonNegativeRational64, NonNegativeRational8, NonNegativeRationalSize};
use crate::rational::small::ops::building_blocks::{add_128, add_16, add_32, add_64, add_8, add_size};
use crate::rational::small::ops::building_blocks::{sub_128, sub_16, sub_32, sub_64, sub_8, sub_size};
use crate::rational::small::ops::building_blocks::{mul_128, mul_16, mul_32, mul_64, mul_8, mul_size};
use crate::rational::small::ops::building_blocks::SignChange;

mod forwards;

macro_rules! rational {
    [$($size:expr,)*] => {
        $(
            paste! {
                impl AddAssign<&Self> for [<Rational $size>] {
                    #[inline]
                    fn add_assign(&mut self, rhs: &Self) {
                        match (self.sign, rhs.sign) {
                            (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => {
                                [<add_ $size>](
                                    &mut self.numerator,
                                    &mut self.denominator,
                                    rhs.numerator,
                                    rhs.denominator,
                                )
                            }
                            (Sign::Positive, Sign::Negative) | (Sign::Negative, Sign::Positive) => {
                                [<sub_ $size>](
                                    &mut self.numerator,
                                    &mut self.denominator,
                                    rhs.numerator,
                                    rhs.denominator,
                                );
                            }
                            (_, Sign::Zero) => {},
                            (Sign::Zero, _) => {
                                *self = Self {
                                    numerator: rhs.numerator,
                                    denominator: rhs.denominator,
                                };
                            },
                        }
                    }
                }

                impl SubAssign<&Self> for [<Rational $size>] {
                    #[inline]
                    fn sub_assign(&mut self, rhs: &Self) {
                        match (self.sign, rhs.sign) {
                            (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => {
                                [<sub_ $size>](
                                    &mut self.numerator,
                                    &mut self.denominator,
                                    rhs.numerator,
                                    rhs.denominator,
                                );
                            }
                            (Sign::Positive, Sign::Negative) | (Sign::Negative, Sign::Positive) => {
                                [<add_ $size>](
                                    &mut self.numerator,
                                    &mut self.denominator,
                                    rhs.numerator,
                                    rhs.denominator,
                                )
                            }
                            (_, Sign::Zero) => {}
                            (Sign::Zero, _) => {
                                *self = Self {
                                    numerator: rhs.numerator,
                                    denominator: rhs.denominator,
                                };
                            }
                        }
                    }
                }

                impl Sum for [<Rational $size>] {
                    fn sum<I: Iterator<Item=Self>>(mut iter: I) -> Self {
                        let first_value = iter.next();
                        match first_value {
                            None => <Self as num_traits::Zero>::zero(),
                            Some(mut total) => {
                                while let Some(next_value) = iter.next() {
                                    total += next_value;
                                }

                                total
                            }
                        }
                    }
                }

                impl MulAssign<&Self> for [<Rational $size>] {
                    #[inline]
                    fn mul_assign(&mut self, rhs: &Self) {
                        match (self.sign, rhs.sign) {
                            (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                                self.sign *= rhs.sign;
                                [<mul_ $size>](&mut self.numerator, &mut self.denominator, rhs.numerator, rhs.denominator);
                            }
                            (Sign::Zero, _) => {}
                            (_, Sign::Zero) => <Self as num_traits::Zero>::set_zero(self),
                        }
                    }
                }

                impl Div<[<Rational $size>]> for &[<Rational $size>] {
                    type Output = [<Rational $size>];

                    #[must_use]
                    #[inline]
                    fn div(self, mut rhs: [<Rational $size>]) -> Self::Output {
                        match (self.sign, rhs.sign) {
                            (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                                let sign = self.sign * rhs.sign;
                                [<mul_ $size>](&mut rhs.numerator, &mut rhs.denominator, self.denominator, self.numerator);
                                Self::Output {
                                    sign,
                                    numerator: rhs.denominator,
                                    denominator: rhs.numerator,
                                }
                            }
                            (_, Sign::Zero) => panic!(),
                            (Sign::Zero, _) => {
                                <[<Rational $size>] as num_traits::Zero>::set_zero(&mut rhs);
                                rhs
                            }
                        }
                    }
                }

                impl DivAssign<&Self> for [<Rational $size>] {
                    #[inline]
                    fn div_assign(&mut self, rhs: &Self) {
                        match (self.sign, rhs.sign) {
                            (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                                self.sign *= rhs.sign;
                                [<mul_ $size>](&mut self.numerator, &mut self.denominator, rhs.denominator, rhs.numerator);
                            }
                            (_, Sign::Zero) => panic!(),
                            (Sign::Zero, _) => {}
                        }
                    }
                }
            }
        )*
    }
}
rational![8, 16, 32, 64, 128, "Size",];

macro_rules! rational_non_zero {
    [$($size:expr,)*] => {
        $(
            paste! {
                impl AddAssign<&Self> for [<NonZeroRational $size>] {
                    #[inline]
                    fn add_assign(&mut self, rhs: &Self) {
                        match (self.sign, rhs.sign) {
                            (NonZeroSign::Positive, NonZeroSign::Positive) | (NonZeroSign::Negative, NonZeroSign::Negative) => {
                                [<add_ $size>](
                                    &mut self.numerator,
                                    &mut self.denominator,
                                    rhs.numerator,
                                    rhs.denominator,
                                )
                            }
                            (NonZeroSign::Positive, NonZeroSign::Negative) | (NonZeroSign::Negative, NonZeroSign::Positive) => {
                                let sign_change = [<sub_ $size>](
                                    &mut self.numerator,
                                    &mut self.denominator,
                                    rhs.numerator,
                                    rhs.denominator,
                                );
                                match sign_change {
                                    SignChange::None => {}
                                    SignChange::Flip => self.sign.negate(),
                                    SignChange::Zero => panic!("attempt to add with overflow"),
                                }
                            }
                        }
                    }
                }
                impl SubAssign<&Self> for [<NonZeroRational $size>] {
                    #[inline]
                    fn sub_assign(&mut self, rhs: &Self) {
                        match (self.sign, rhs.sign) {
                            (NonZeroSign::Positive, NonZeroSign::Positive) | (NonZeroSign::Negative, NonZeroSign::Negative) => {
                                let sign_change = [<sub_ $size>](
                                    &mut self.numerator,
                                    &mut self.denominator,
                                    rhs.numerator,
                                    rhs.denominator,
                                );
                                match sign_change {
                                    SignChange::None => {}
                                    SignChange::Flip => self.sign.negate(),
                                    SignChange::Zero => panic!("attempt to subtract with overflow"),
                                }
                            }
                            (NonZeroSign::Positive, NonZeroSign::Negative) | (NonZeroSign::Negative, NonZeroSign::Positive) => {
                                [<add_ $size>](
                                    &mut self.numerator,
                                    &mut self.denominator,
                                    rhs.numerator,
                                    rhs.denominator,
                                )
                            }
                        }
                    }
                }
                impl MulAssign<&Self> for [<NonZeroRational $size>] {
                    #[inline]
                    fn mul_assign(&mut self, rhs: &Self) {
                        self.sign *= rhs.sign;
                        [<mul_ $size>](&mut self.numerator, &mut self.denominator, rhs.numerator, rhs.denominator);
                    }
                }
                impl Div<[<NonZeroRational $size>]> for &[<NonZeroRational $size>] {
                    type Output = [<NonZeroRational $size>];

                    #[must_use]
                    #[inline]
                    fn div(self, mut rhs: [<NonZeroRational $size>]) -> Self::Output {
                        let sign = self.sign * rhs.sign;
                        [<mul_ $size>](&mut rhs.numerator, &mut rhs.denominator, self.denominator, self.numerator);
                        Self::Output {
                            sign,
                            numerator: rhs.denominator,
                            denominator: rhs.numerator,
                        }
                    }
                }
                impl DivAssign<&Self> for [<NonZeroRational $size>] {
                    #[inline]
                    fn div_assign(&mut self, rhs: &Self) {
                        self.sign *= rhs.sign;
                        [<mul_ $size>](&mut self.numerator, &mut self.denominator, rhs.denominator, rhs.numerator);
                    }
                }
            }
        )*
    }
}
rational_non_zero![8, 16, 32, 64, 128, "Size",];

macro_rules! rational_non_negative {
    [$($size:expr,)*] => {
        $(
            paste! {
                impl AddAssign<&Self> for [<NonNegativeRational $size>] {
                    #[inline]
                    fn add_assign(&mut self, rhs: &Self) {
                        [<add_ $size>](
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        )
                    }
                }
                impl SubAssign<&Self> for [<NonNegativeRational $size>] {
                    #[inline]
                    fn sub_assign(&mut self, rhs: &Self) {
                        let sign_change = [<sub_ $size>](
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        );
                        if sign_change == SignChange::Flip {
                            panic!("attempt to subtract with overflow");
                        }
                    }
                }
                impl MulAssign<&Self> for [<NonNegativeRational $size>] {
                    #[inline]
                    fn mul_assign(&mut self, rhs: &Self) {
                        [<mul_ $size>](&mut self.numerator, &mut self.denominator, rhs.numerator, rhs.denominator);
                    }
                }
                impl Div<[<NonNegativeRational $size>]> for &[<NonNegativeRational $size>] {
                    type Output = [<NonNegativeRational $size>];

                    #[must_use]
                    #[inline]
                    fn div(self, mut rhs: [<NonNegativeRational $size>]) -> Self::Output {
                        if rhs.is_zero() {
                            panic!("attempt to divide by zero");
                        }

                        [<mul_ $size>](&mut rhs.numerator, &mut rhs.denominator, self.denominator, self.numerator);
                        Self::Output {
                            numerator: rhs.denominator,
                            denominator: rhs.numerator,
                        }
                    }
                }
                impl DivAssign<&Self> for [<NonNegativeRational $size>] {
                    #[inline]
                    fn div_assign(&mut self, rhs: &Self) {
                        [<mul_ $size>](&mut self.numerator, &mut self.denominator, rhs.denominator, rhs.numerator);
                    }
                }
            }
        )*
    }
}
rational_non_negative![8, 16, 32, 64, 128, "Size",];

macro_rules! rational_requiring_wide {
    ($name:ident, $uty:ty, $BITS:literal, $wide:ty, $sign:ident) => {
        impl Ord for $name {
            #[must_use]
            #[inline]
            fn cmp(&self, other: &Self) -> Ordering {
                self.partial_cmp(other).unwrap()
            }
        }

        impl PartialOrd for $name {
            #[must_use]
            #[inline]
            #[allow(unreachable_patterns)]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                self.sign.partial_cmp(&other.sign).or_else(|| {
                    debug_assert_eq!(self.sign, other.sign);
                    debug_assert!(self.is_not_zero());

                    let widening_mul = |left, right| {
                        let wide = unsafe { (left as $wide).unchecked_mul(right as $wide) };
                        ((wide >> $BITS) as $uty, wide as $uty)
                    };

                    let ad = widening_mul(self.numerator, other.denominator);
                    let bc = widening_mul(self.denominator, other.numerator);

                    Some(match (ad.cmp(&bc), self.sign) {
                        (Ordering::Less, $sign::Positive) | (Ordering::Greater, $sign::Negative) => Ordering::Less,
                        (Ordering::Equal, _) => Ordering::Equal,
                        (Ordering::Greater, $sign::Positive) | (Ordering::Less, $sign::Negative) => Ordering::Greater,
                        _ => panic!("Zero case would have been equal or nonzero type"),
                    })
                })
            }
        }
    }
}
rational_requiring_wide!(Rational8, u8, 8, u16, Sign);
rational_requiring_wide!(Rational16, u16, 16, u32, Sign);
rational_requiring_wide!(Rational32, u32, 32, u64, Sign);
rational_requiring_wide!(Rational64, u64, 64, u128, Sign);
rational_requiring_wide!(NonZeroRational8, u8, 8, u16, NonZeroSign);
rational_requiring_wide!(NonZeroRational16, u16, 16, u32, NonZeroSign);
rational_requiring_wide!(NonZeroRational32, u32, 32, u64, NonZeroSign);
rational_requiring_wide!(NonZeroRational64, u64, 64, u128, NonZeroSign);
rational_requiring_wide!(NonNegativeRational8, u8, 8, u16, NonNegativeSign);
rational_requiring_wide!(NonNegativeRational16, u16, 16, u32, NonNegativeSign);
rational_requiring_wide!(NonNegativeRational32, u32, 32, u64, NonNegativeSign);
rational_requiring_wide!(NonNegativeRational64, u64, 64, u128, NonNegativeSign);
