//! # Interactions with fixed size ratios
use std::ops::{Add, AddAssign, Div, Mul};

use smallvec::smallvec;

use crate::rational::{Rational16, Rational32, Rational64, Rational8};
use crate::rational::big::ops::{add_assign, add_assign_single, mul, mul_assign_single};
use crate::rational::big::ops::building_blocks::shr;
use crate::rational::big::ops::div::{div, div_assign_one_word};
use crate::rational::big::ops::normalize::lcm_single;
use crate::rational::big::ops::normalize::simplify_fraction_gcd_single;
use crate::sign::Sign;

use super::Big;

impl<const S: usize> Big<S> {
    #[inline]
    fn add_small(&mut self, rhs_numerator: usize, rhs_denominator: usize) {
        debug_assert!(!self.numerator.is_empty());

        if rhs_denominator == self.denominator[0] && self.denominator.len() == 1 {
            add_assign_single(&mut self.numerator, rhs_numerator);
        } else {
            if rhs_denominator == 1 {
                let mut right_numerator = self.denominator.clone();
                mul_assign_single(&mut right_numerator, rhs_numerator);
                add_assign(&mut self.numerator, &right_numerator);
            } else if self.denominator[0] == 1 && self.denominator.len() == 1 {
                mul_assign_single(&mut self.numerator, rhs_denominator);
                add_assign_single(&mut self.numerator, rhs_numerator);
                self.denominator.truncate(1);
                self.denominator[0] = rhs_denominator;
            } else {
                let lcm = lcm_single(&self.denominator, rhs_denominator);

                let left_numerator = div(&lcm, &self.denominator);
                self.numerator = mul(&self.numerator, &left_numerator);
                let zero_bits = rhs_denominator.trailing_zeros();
                let mut right_numerator = shr(&lcm, 0, zero_bits);
                div_assign_one_word(&mut right_numerator, rhs_denominator >> zero_bits);

                add_assign(&mut self.numerator, &right_numerator);
                self.denominator = lcm;
            }
        }
    }
    #[inline]
    fn sub_small(&mut self, rhs_nominator: usize, rhs_denominator: usize) {
        debug_assert!(!self.numerator.is_empty());

        if rhs_denominator == self.denominator[0] && self.denominator.len() == 1 {
            todo!();
        } else {
            if rhs_denominator == 1 {
                todo!();
            } else if self.denominator[0] == 1 && self.denominator.len() == 1 {
                todo!();
                self.denominator.truncate(1);
                self.denominator[0] = rhs_denominator;
            } else {
                todo!();
            }
        }
    }
    #[inline]
    fn mul_small(&mut self, mut rhs_numerator: usize, mut rhs_denominator: usize) {
        debug_assert!(!self.numerator.is_empty());

        let lhs_numerator_one = self.numerator.len() == 1 && self.numerator[0] == 1;
        if rhs_denominator != 1 && !lhs_numerator_one {
            rhs_denominator = simplify_fraction_gcd_single(&mut self.numerator, rhs_denominator)
        }

        let lhs_denominator_one = self.denominator[0] == 1 && self.denominator.len() == 1;
        if rhs_numerator != 1 && !lhs_denominator_one {
            rhs_numerator = simplify_fraction_gcd_single(&mut self.denominator, rhs_numerator)
        }

        mul_assign_single(&mut self.numerator, rhs_numerator);
        mul_assign_single(&mut self.denominator, rhs_denominator);
    }
}

macro_rules! define_interations {
    ($small:ident, $module_name:ident) => {
        mod $module_name {
            use super::*;

            mod creation {
                use super::*;

                impl<const S: usize> From<$small> for Big<S> {
                    #[must_use]
                    #[inline]
                    fn from(value: $small) -> Self {
                        Self {
                            sign: value.sign,
                            numerator: smallvec![value.numerator as usize],
                            denominator: smallvec![value.denominator as usize],
                        }
                    }
                }

                impl<const S: usize> From<&$small> for Big<S> {
                    #[must_use]
                    #[inline]
                    fn from(value: &$small) -> Self {
                        Self {
                            sign: value.sign,
                            numerator: smallvec![value.numerator as usize],
                            denominator: smallvec![value.denominator as usize],
                        }
                    }
                }
            }
            
            mod compare {
                use super::*;

                impl<const S: usize> PartialEq<$small> for Big<S> {
                    #[inline]
                    fn eq(&self, other: &$small) -> bool {
                        // Compare first with the denominator, we don't have to do a bounds check
                        // and the probability that its equal is small
                        self.denominator[0] == other.denominator as usize &&
                            match self.sign {
                                Sign::Zero => other.sign == Sign::Zero,
                                Sign::Positive | Sign::Negative => {
                                    self.numerator.len() == 1 &&
                                    self.numerator[0] == other.numerator as usize &&
                                    self.denominator.len() == 1
                                }
                            }
                    }
                }
            }

            mod field {
                use super::*;
            
                mod add {
                    use crate::sign::Sign;
            
                    use super::*;
            
                    impl<const S: usize> Add<&$small> for Big<S> {
                        type Output = Self;

                        #[must_use]
                        #[inline]
                        fn add(mut self, rhs: &$small) -> Self::Output {
                            AddAssign::add_assign(&mut self, rhs);
                            self
                        }
                    }
            
                    impl<const S: usize> Add<Option<&$small>> for Big<S> {
                        type Output = Self;

                        #[must_use]
                        #[inline]
                        fn add(self, rhs: Option<&$small>) -> Self::Output {
                            match rhs {
                                None => self,
                                Some(rhs) => Add::add(self, rhs),
                            }
                        }
                    }
            
                    impl<const S: usize> Add<&$small> for &Big<S> {
                        type Output = Big<S>;

                        #[must_use]
                        #[inline]
                        fn add(self, rhs: &$small) -> Self::Output {
                            // TODO(PERFORMANCE): Make sure that this is just as efficient as a native algorithm.
                            let mut cloned = self.clone();
                            AddAssign::add_assign(&mut cloned, rhs);
                            cloned
                        }
                    }
            
                    impl<const S: usize> Add<Option<&$small>> for &Big<S> {
                        type Output = Big<S>;

                        #[must_use]
                        #[inline]
                        fn add(self, rhs: Option<&$small>) -> Self::Output {
                            // TODO(PERFORMANCE): Make sure that this is just as efficient as a native algorithm.
                            let copy = self.clone();
                            match rhs {
                                None => copy,
                                Some(rhs) => Add::add(copy, rhs),
                            }
                        }
                    }
            
                    impl<const S: usize> AddAssign<$small> for Big<S> {
                        #[inline]
                        fn add_assign(&mut self, rhs: $small) {
                            AddAssign::add_assign(self, &rhs);
                        }
                    }
            
                    impl<const S: usize> AddAssign<&$small> for Big<S> {
                        #[inline]
                        fn add_assign(&mut self, rhs: &$small) {
                            match (self.sign, rhs.sign) {
                                (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => {
                                    self.add_small(rhs.numerator as usize, rhs.denominator as usize);
                                },
                                (Sign::Negative, Sign::Positive) | (Sign::Positive, Sign::Negative) => {
                                    self.sub_small(rhs.numerator as usize, rhs.denominator as usize);
                                }
                                (_, Sign::Zero) => {}
                                (Sign::Zero, _) => {
                                    debug_assert_eq!(self.sign, Sign::Zero);
                                    self.sign = rhs.sign;
                                    debug_assert_eq!(self.numerator.len(), 0);
                                    self.numerator.push(rhs.numerator as usize);
                                    debug_assert_eq!(self.denominator.len(), 1);
                                    debug_assert_eq!(self.denominator[0], 1);
                                    self.denominator[0] = rhs.denominator as usize;
                                }
                            }
                        }
                    }
                }
            
                mod mul {
                    use super::*;

                    impl<const S: usize> Mul<&$small> for Big<S> {
                        type Output = Big<S>;

                        #[must_use]
                        #[inline]
                        fn mul(mut self, rhs: &$small) -> Self::Output {
                            match (self.sign, rhs.sign) {
                                (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                                    self.sign *= rhs.sign;
                                    self.mul_small(rhs.numerator as usize, rhs.denominator as usize);
                                }
                                (Sign::Positive | Sign::Negative, Sign::Zero) => {
                                    <Self as num_traits::Zero>::set_zero(&mut self);
                                }
                                (Sign::Zero, _) => {}
                            }

                            self
                        }
                    }
            
                    impl<const S: usize> Mul<&$small> for &Big<S> {
                        type Output = Big<S>;

                        #[must_use]
                        #[inline]
                        fn mul(self, rhs: &$small) -> Self::Output {
                            // TODO(PERFORMANCE): Make sure that this is just as efficient as a native algorithm.
                            self.clone() * rhs
                        }
                    }
            
                    impl<const S: usize> Mul<Option<&$small>> for Big<S> {
                        type Output = Big<S>;

                        #[must_use]
                        #[inline]
                        fn mul(mut self, rhs: Option<&$small>) -> Self::Output {
                            match rhs {
                                None => {
                                    <Self as num_traits::Zero>::set_zero(&mut self);
                                    self
                                },
                                Some(rhs) => Mul::mul(self, rhs),
                            }
                        }
                    }
            
                    impl<const S: usize> Mul<Option<&$small>> for &Big<S> {
                        type Output = Big<S>;

                        #[must_use]
                        #[inline]
                        fn mul(self, rhs: Option<&$small>) -> Self::Output {
                            match rhs {
                                None => <Self::Output as num_traits::Zero>::zero(),
                                Some(rhs) => Mul::mul(self, rhs),
                            }
                        }
                    }
                }
            
                mod div {
                    use super::*;
            
                    impl<const S: usize> Div<&$small> for Big<S> {
                        type Output = Big<S>;

                        #[must_use]
                        #[inline]
                        fn div(mut self, rhs: &$small) -> Self::Output {
                            debug_assert_ne!(rhs.sign, Sign::Zero);

                            match (self.sign, rhs.sign) {
                                (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                                    self.sign *= rhs.sign;
                                    self.mul_small(rhs.denominator as usize, rhs.numerator as usize);
                                }
                                (Sign::Positive | Sign::Negative, Sign::Zero) => panic!(),
                                (Sign::Zero, _) => {}
                            }

                            self
                        }
                    }
                }
            }
        }
    }
}

define_interations!(Rational8, rational8);
define_interations!(Rational16, rational16);
define_interations!(Rational32, rational32);
define_interations!(Rational64, rational64);
