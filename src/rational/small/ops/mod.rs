use std::cmp::Ordering;
use std::iter::Sum;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};
use std::ops::Neg;

use crate::non_zero::NonZero;
use crate::non_zero::NonZeroSign;
use crate::rational::small::{Rational128, Rational16, Rational32, Rational64, Rational8};
use crate::rational::small::{NonZeroRational128, NonZeroRational16, NonZeroRational32, NonZeroRational64, NonZeroRational8};
use crate::rational::small::ops::building_blocks::{add128, add16, add32, add64, add8};
use crate::rational::small::ops::building_blocks::{sub128, sub16, sub32, sub64, sub8};
use crate::rational::small::ops::building_blocks::{mul128, mul16, mul32, mul64, mul8};
use crate::rational::small::ops::building_blocks::SignChange;
use crate::sign::Sign;

pub(crate) mod building_blocks;
mod with_int;
mod with_one;

#[cfg(test)]
mod test;

macro_rules! rational {
    ($name:ident, $add_name:ident, $sub_name:ident, $mul_name:ident) => {
        impl AddAssign<&$name> for $name {
            #[inline]
            fn add_assign(&mut self, rhs: &Self) {
                match (self.sign, rhs.sign) {
                    (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => {
                        $add_name(
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        )
                    }
                    (Sign::Positive, Sign::Negative) | (Sign::Negative, Sign::Positive) => {
                        let sign_change = $sub_name(
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        );
                        match sign_change {
                            SignChange::None => {}
                            SignChange::Flip => self.sign = !self.sign,
                            SignChange::Zero => self.sign = Sign::Zero,
                        }
                    }
                    (_, Sign::Zero) => {},
                    (Sign::Zero, _) => {
                        *self = Self {
                            sign: rhs.sign,
                            numerator: rhs.numerator,
                            denominator: rhs.denominator,
                        };
                    },
                }
            }
        }

        impl SubAssign<&$name> for $name {
            #[inline]
            fn sub_assign(&mut self, rhs: &Self) {
                match (self.sign, rhs.sign) {
                    (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => {
                        let sign_change = $sub_name(
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        );
                        match sign_change {
                            SignChange::None => {}
                            SignChange::Flip => self.sign = !self.sign,
                            SignChange::Zero => self.sign = Sign::Zero,
                        }
                    }
                    (Sign::Positive, Sign::Negative) | (Sign::Negative, Sign::Positive) => {
                        $add_name(
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        )
                    }
                    (_, Sign::Zero) => {}
                    (Sign::Zero, _) => {
                        *self = Self {
                            sign: !rhs.sign,
                            numerator: rhs.numerator,
                            denominator: rhs.denominator,
                        };
                    }
                }
            }
        }

        impl Sum for $name {
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

        impl MulAssign<&$name> for $name {
            #[inline]
            fn mul_assign(&mut self, rhs: &Self) {
                match (self.sign, rhs.sign) {
                    (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                        self.sign *= rhs.sign;
                        $mul_name(&mut self.numerator, &mut self.denominator, rhs.numerator, rhs.denominator);
                    }
                    (Sign::Zero, _) => {}
                    (_, Sign::Zero) => <Self as num_traits::Zero>::set_zero(self),
                }
            }
        }

        impl Div<$name> for &$name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn div(self, mut rhs: $name) -> Self::Output {
                match (self.sign, rhs.sign) {
                    (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                        let sign = self.sign * rhs.sign;
                        $mul_name(&mut rhs.numerator, &mut rhs.denominator, self.denominator, self.numerator);
                        Self::Output {
                            sign,
                            numerator: rhs.denominator,
                            denominator: rhs.numerator,
                        }
                    }
                    (_, Sign::Zero) => panic!(),
                    (Sign::Zero, _) => {
                        <$name as num_traits::Zero>::set_zero(&mut rhs);
                        rhs
                    }
                }
            }
        }

        impl DivAssign<&$name> for $name {
            #[inline]
            fn div_assign(&mut self, rhs: &Self) {
                match (self.sign, rhs.sign) {
                    (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                        self.sign *= rhs.sign;
                        $mul_name(&mut self.numerator, &mut self.denominator, rhs.denominator, rhs.numerator);
                    }
                    (_, Sign::Zero) => panic!(),
                    (Sign::Zero, _) => {}
                }
            }
        }
    }
}

rational!(Rational8, add8, sub8, mul8);
rational!(Rational16, add16, sub16, mul16);
rational!(Rational32, add32, sub32, mul32);
rational!(Rational64, add64, sub64, mul64);
rational!(Rational128, add128, sub128, mul128);

macro_rules! rational_non_zero {
    ($name:ident, $add_name:ident, $sub_name:ident, $mul_name:ident) => {
        impl AddAssign<&$name> for $name {
            #[inline]
            fn add_assign(&mut self, rhs: &Self) {
                match (self.sign, rhs.sign) {
                    (NonZeroSign::Positive, NonZeroSign::Positive) | (NonZeroSign::Negative, NonZeroSign::Negative) => {
                        $add_name(
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        )
                    }
                    (NonZeroSign::Positive, NonZeroSign::Negative) | (NonZeroSign::Negative, NonZeroSign::Positive) => {
                        let sign_change = $sub_name(
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        );
                        match sign_change {
                            SignChange::None => {}
                            SignChange::Flip => self.sign = !self.sign,
                            SignChange::Zero => panic!("attempt to add with overflow"),
                        }
                    }
                }
            }
        }
        impl SubAssign<&$name> for $name {
            #[inline]
            fn sub_assign(&mut self, rhs: &Self) {
                match (self.sign, rhs.sign) {
                    (NonZeroSign::Positive, NonZeroSign::Positive) | (NonZeroSign::Negative, NonZeroSign::Negative) => {
                        let sign_change = $sub_name(
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        );
                        match sign_change {
                            SignChange::None => {}
                            SignChange::Flip => self.sign = !self.sign,
                            SignChange::Zero => panic!("attempt to subtract with overflow"),
                        }
                    }
                    (NonZeroSign::Positive, NonZeroSign::Negative) | (NonZeroSign::Negative, NonZeroSign::Positive) => {
                        $add_name(
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        )
                    }
                }
            }
        }
        impl MulAssign<&$name> for $name {
            #[inline]
            fn mul_assign(&mut self, rhs: &Self) {
                self.sign *= rhs.sign;
                $mul_name(&mut self.numerator, &mut self.denominator, rhs.numerator, rhs.denominator);
            }
        }
        impl Div<$name> for &$name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn div(self, mut rhs: $name) -> Self::Output {
                let sign = self.sign * rhs.sign;
                $mul_name(&mut rhs.numerator, &mut rhs.denominator, self.denominator, self.numerator);
                Self::Output {
                    sign,
                    numerator: rhs.denominator,
                    denominator: rhs.numerator,
                }
            }
        }
        impl DivAssign<&$name> for $name {
            #[inline]
            fn div_assign(&mut self, rhs: &Self) {
                self.sign *= rhs.sign;
                $mul_name(&mut self.numerator, &mut self.denominator, rhs.denominator, rhs.numerator);
            }
        }

        impl Neg for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn neg(mut self) -> Self::Output {
                self.sign = !self.sign;
                self
            }
        }

        impl Neg for &$name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn neg(self) -> Self::Output {
                Self::Output {
                    sign: !self.sign,
                    numerator: self.numerator,
                    denominator: self.denominator,
                }
            }
        }
    }
}
rational_non_zero!(NonZeroRational8, add8, sub8, mul8);
rational_non_zero!(NonZeroRational16, add16, sub16, mul16);
rational_non_zero!(NonZeroRational32, add32, sub32, mul32);
rational_non_zero!(NonZeroRational64, add64, sub64, mul64);
rational_non_zero!(NonZeroRational128, add128, sub128, mul128);

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

macro_rules! rational_forward {
    ($name:ident) => {
        impl<'a> Add<&'a $name> for &'a $name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn add(self, rhs: Self) -> Self::Output {
                Add::add(self.clone(), rhs)
            }
        }

        impl Add for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn add(mut self, rhs: Self) -> Self::Output {
                AddAssign::add_assign(&mut self, rhs);
                self
            }
        }

        impl Add<&$name> for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn add(mut self, rhs: &Self) -> Self::Output {
                AddAssign::add_assign(&mut self, rhs);
                self
            }
        }

        impl Add<$name> for &$name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn add(self, rhs: $name) -> Self::Output {
                Add::add(rhs, self)
            }
        }

        impl AddAssign for $name {
            #[inline]
            fn add_assign(&mut self, rhs: Self) {
                AddAssign::add_assign(self, &rhs);
            }
        }

        impl Sub for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn sub(mut self, rhs: Self) -> Self::Output {
                SubAssign::sub_assign(&mut self, rhs);
                self
            }
        }

        impl<'a> Sub<&'a $name> for &'a $name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn sub(self, rhs: Self) -> Self::Output {
                Sub::sub(self.clone(), rhs)
            }
        }

        impl Sub<&$name> for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn sub(mut self, rhs: &Self) -> Self::Output {
                SubAssign::sub_assign(&mut self, rhs);
                self
            }
        }

        impl Sub<$name> for &$name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn sub(self, rhs: $name) -> Self::Output {
                -Sub::sub(rhs, self)
            }
        }

        impl SubAssign for $name {
            #[inline]
            fn sub_assign(&mut self, rhs: Self) {
                SubAssign::sub_assign(self, &rhs)
            }
        }

        impl Mul<&$name> for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn mul(mut self, rhs: &Self) -> Self::Output {
                MulAssign::mul_assign(&mut self, rhs);
                self
            }
        }

        impl<'a> Mul<&'a $name> for &'a $name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn mul(self, rhs: Self) -> Self::Output {
                Mul::mul(self.clone(), rhs)
            }
        }

        impl Mul for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn mul(mut self, rhs: Self) -> Self::Output {
                MulAssign::mul_assign(&mut self, rhs);
                self
            }
        }

        impl MulAssign for $name {
            #[inline]
            fn mul_assign(&mut self, rhs: Self) {
                MulAssign::mul_assign(self, &rhs);
            }
        }

        impl Mul<$name> for &$name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn mul(self, rhs: $name) -> Self::Output {
                Mul::mul(rhs, self)
            }
        }

        impl Div for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn div(mut self, rhs: Self) -> Self::Output {
                DivAssign::div_assign(&mut self, rhs);
                self
            }
        }

        impl Div<&$name> for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn div(mut self, rhs: &Self) -> Self::Output {
                DivAssign::div_assign(&mut self, rhs);
                self
            }
        }

        impl<'a> Div<&'a $name> for &'a $name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn div(self, rhs: Self) -> Self::Output {
                Div::div(self.clone(), rhs)
            }
        }

        impl DivAssign for $name {
            #[inline]
            fn div_assign(&mut self, rhs: Self) {
                DivAssign::div_assign(self, &rhs);
            }
        }
    }
}

rational_forward!(Rational8);
rational_forward!(Rational16);
rational_forward!(Rational32);
rational_forward!(Rational64);
rational_forward!(Rational128);
rational_forward!(NonZeroRational8);
rational_forward!(NonZeroRational16);
rational_forward!(NonZeroRational32);
rational_forward!(NonZeroRational64);
rational_forward!(NonZeroRational128);
