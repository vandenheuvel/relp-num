use std::ops::{Div, DivAssign, Mul, MulAssign};

use crate::{Rational128, Rational16, Rational32, Rational64, Rational8};
use crate::rational::small::ops::building_blocks::{gcd128, gcd16, gcd32, gcd64, gcd8};
use crate::Sign;

macro_rules! rational {
    ($name:ident, $uty:ty, $mul_name:ident, $gcd_name:ident) => {
        #[inline]
        fn $mul_name(left_numerator: &mut $uty, left_denominator: &mut $uty, right: $uty) {
            debug_assert_ne!(right, 0);

            if right != 1 {
                if *left_denominator != 1 {
                    let gcd = $gcd_name(*left_denominator, right);
                    *left_numerator *= right / gcd;
                    *left_denominator /= gcd;
                } else {
                    *left_numerator *= right;
                }
            }
        }

        impl Mul<&$uty> for $name {
            type Output = Self;

            #[inline]
            #[must_use]
            fn mul(mut self, rhs: &$uty) -> Self::Output {
                MulAssign::mul_assign(&mut self, rhs);
                self
            }
        }

        impl Mul<$uty> for $name {
            type Output = Self;

            #[inline]
            #[must_use]
            fn mul(mut self, rhs: $uty) -> Self::Output {
                MulAssign::mul_assign(&mut self, rhs);
                self
            }
        }

        impl MulAssign<&$uty> for $name {
            #[inline]
            fn mul_assign(&mut self, rhs: &$uty) {
                MulAssign::mul_assign(self, *rhs);
            }
        }

        impl MulAssign<$uty> for $name {
            #[inline]
            fn mul_assign(&mut self, rhs: $uty) {
                if rhs != 0 {
                    match self.sign {
                        Sign::Positive | Sign::Negative => {
                            $mul_name(&mut self.numerator, &mut self.denominator, rhs);
                        }
                        Sign::Zero => {}
                    }
                } else {
                    <Self as num_traits::Zero>::set_zero(self);
                }
            }
        }

        impl Div<&$uty> for $name {
            type Output = Self;

            #[inline]
            #[must_use]
            fn div(mut self, rhs: &$uty) -> Self::Output {
                DivAssign::div_assign(&mut self, rhs);
                self
            }
        }

        impl Div<$uty> for $name {
            type Output = Self;

            #[inline]
            #[must_use]
            fn div(mut self, rhs: $uty) -> Self::Output {
                DivAssign::div_assign(&mut self, rhs);
                self
            }
        }

        impl DivAssign<&$uty> for $name {
            #[inline]
            fn div_assign(&mut self, rhs: &$uty) {
                DivAssign::div_assign(self, *rhs);
            }
        }

        impl DivAssign<$uty> for $name {
            #[inline]
            fn div_assign(&mut self, rhs: $uty) {
                if rhs != 0 {
                    match self.sign {
                        Sign::Positive | Sign::Negative => {
                            $mul_name(&mut self.denominator, &mut self.numerator, rhs);
                        }
                        Sign::Zero => {}
                    }
                } else {
                    panic!("attempt to divide by zero");
                }
            }
        }
    }
}

rational!(Rational8, u8, mul8, gcd8);
rational!(Rational16, u16, mul16, gcd16);
rational!(Rational32, u32, mul32, gcd32);
rational!(Rational64, u64, mul64, gcd64);
rational!(Rational128, u128, mul128, gcd128);

#[cfg(test)]
mod test {
    use crate::R16;

    #[test]
    fn test_mul() {
        let mut x = R16!(1);
        x /= &19_u16;
        assert_eq!(x, R16!(1, 19));

        assert_eq!(R16!(1) / &19_u16, R16!(1, 19));
        assert_eq!(R16!(1) * &19_u16, R16!(19));
        assert_eq!(R16!(3) * &19, R16!(19 * 3));
        assert_eq!(R16!(3) / &19, R16!(3, 19));
        assert_eq!(R16!(3) * &6, R16!(3 * 6));
        assert_eq!(R16!(3) / &6, R16!(3, 6));
        assert_eq!(R16!(3) * 0, R16!(0));
        assert_eq!(R16!(3) / &6, R16!(3, 6));
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn test_mul_by_zero() {
        R16!(3) / &0;
    }
}
