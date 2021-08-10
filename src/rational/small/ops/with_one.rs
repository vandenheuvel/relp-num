use std::cmp::Ordering;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

use num_traits::Zero;

use crate::{Rational128, Rational16, Rational32, Rational64, Rational8, Sign};
use crate::one::One;

macro_rules! impls {
    ($name:ty) => {
        impl From<One> for $name {
            #[inline]
            #[must_use]
            fn from(_: One) -> Self {
                num_traits::One::one()
            }
        }

        impl From<&One> for $name {
            #[inline]
            #[must_use]
            fn from(_: &One) -> Self {
                num_traits::One::one()
            }
        }

        impl Add<One> for $name {
            type Output = Self;

            #[inline]
            #[must_use]
            fn add(mut self, _: One) -> Self::Output {
                AddAssign::add_assign(&mut self, One);
                self
            }
        }

        impl Add<&One> for $name {
            type Output = Self;

            #[inline]
            #[must_use]
            fn add(mut self, _: &One) -> Self::Output {
                AddAssign::add_assign(&mut self, &One);
                self
            }
        }

        impl AddAssign<One> for $name {
            #[inline]
            fn add_assign(&mut self, _: One) {
                AddAssign::add_assign(self, &One);
            }
        }

        impl AddAssign<&One> for $name {
            #[inline]
            fn add_assign(&mut self, _: &One) {
                match self.sign {
                    Sign::Positive => self.numerator += self.denominator,
                    Sign::Zero => {
                        self.sign = Sign::Positive;
                        debug_assert!(self.numerator.is_zero());
                        num_traits::One::set_one(&mut self.numerator);
                        debug_assert!(num_traits::One::is_one(&self.denominator));
                    }
                    Sign::Negative => {
                        if self.numerator != 1 || self.denominator != 1 {
                            match self.numerator.cmp(&self.denominator) {
                                Ordering::Less => {
                                    self.numerator = self.denominator - self.numerator;
                                    self.sign = Sign::Positive;
                                }
                                Ordering::Equal => panic!(),
                                Ordering::Greater => self.numerator -= self.denominator,
                            }
                        } else {
                            self.set_zero();
                        }
                    }
                }
            }
        }

        impl Sub<One> for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn sub(mut self, _: One) -> Self::Output {
                SubAssign::sub_assign(&mut self, One);
                self
            }
        }

        impl Sub<&One> for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn sub(mut self, _: &One) -> Self::Output {
                SubAssign::sub_assign(&mut self, One);
                self
            }
        }

        impl SubAssign<One> for $name {
            #[inline]
            fn sub_assign(&mut self, _: One) {
                SubAssign::sub_assign(self, &One);
            }
        }

        impl SubAssign<&One> for $name {
            #[inline]
            fn sub_assign(&mut self, _: &One) {
                match self.sign {
                    Sign::Positive => {
                        if self.numerator != 1 || self.denominator != 1 {
                            match self.numerator.cmp(&self.denominator) {
                                Ordering::Less => {
                                    self.numerator = self.denominator - self.numerator;
                                    self.sign = Sign::Negative;
                                }
                                Ordering::Equal => panic!(),
                                Ordering::Greater => self.numerator -= self.denominator,
                            }
                        } else {
                            self.set_zero();
                        }
                    }
                    Sign::Zero => {
                        self.sign = Sign::Negative;
                        debug_assert_eq!(self.numerator, 0);
                        self.numerator = 1;
                        debug_assert_eq!(self.denominator, 1);
                    }
                    Sign::Negative => self.numerator += self.denominator,
                }
            }
        }

        impl Mul<One> for $name {
            type Output = Self;

            #[inline]
            #[must_use]
            fn mul(self, _: One) -> Self::Output {
                self
            }
        }

        impl Mul<&One> for $name {
            type Output = Self;

            #[inline]
            #[must_use]
            fn mul(self, _: &One) -> Self::Output {
                self
            }
        }

        impl Mul<&One> for &$name {
            type Output = $name;

            #[inline]
            #[must_use]
            fn mul(self, _: &One) -> Self::Output {
                self.clone()
            }
        }

        impl Mul<One> for &$name {
            type Output = $name;

            #[inline]
            #[must_use]
            fn mul(self, _: One) -> Self::Output {
                self.clone()
            }
        }

        impl MulAssign<One> for $name {
            #[inline]
            fn mul_assign(&mut self, _: One) {
                MulAssign::mul_assign(self, &One);
            }
        }

        impl MulAssign<&One> for $name {
            #[inline]
            fn mul_assign(&mut self, _: &One) {
            }
        }

        impl Div<One> for $name {
            type Output = Self;

            #[inline]
            #[must_use]
            fn div(self, _: One) -> Self::Output {
                self
            }
        }

        impl Div<&One> for $name {
            type Output = Self;

            #[inline]
            #[must_use]
            fn div(self, _: &One) -> Self::Output {
                self
            }
        }

        impl Div<&One> for &$name {
            type Output = $name;

            #[inline]
            #[must_use]
            fn div(self, _: &One) -> Self::Output {
                self.clone()
            }
        }

        impl Div<One> for &$name {
            type Output = $name;

            #[inline]
            #[must_use]
            fn div(self, _: One) -> Self::Output {
                self.clone()
            }
        }

        impl DivAssign<One> for $name {
            #[inline]
            fn div_assign(&mut self, _: One) {
                DivAssign::div_assign(self, &One);
            }
        }

        impl DivAssign<&One> for $name {
            #[inline]
            fn div_assign(&mut self, _: &One) {
            }
        }
    }
}

impls!(Rational8);
impls!(Rational16);
impls!(Rational32);
impls!(Rational64);
impls!(Rational128);

#[cfg(test)]
mod test {
    use crate::{One, R8};

    #[test]
    fn test_add_sub() {
        assert_eq!(R8!(1) + One, R8!(2));
        assert_eq!(R8!(0) + One, R8!(1));
        assert_eq!(R8!(0) - One, R8!(-1));
        assert_eq!(R8!(1) - One, R8!(0));
        assert_eq!(R8!(1, 2) - One, R8!(-1, 2));
        assert_eq!(R8!(-1, 2) + One, R8!(1, 2));
        assert_eq!(R8!(-1, 2) - One, R8!(-3, 2));

        assert_eq!(R8!(1) * &One, R8!(1));
        assert_eq!(R8!(1) / &One, R8!(1));
    }
}
