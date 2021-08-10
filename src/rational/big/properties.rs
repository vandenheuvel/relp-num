use std::cmp::Ordering;

use num_traits::{One, Zero};

use crate::{NonZero, NonZeroSign, Sign};
use crate::integer::big::ops::non_zero::mul_non_zero;
use crate::integer::big::ops::normalize::simplify_fraction_without_info;
use crate::integer::big::properties::cmp;
use crate::rational::big::{Big, NonZeroBig};

impl<const S: usize> Big<S> {
    #[allow(unused)]
    pub(crate) unsafe fn is_well_formed(&self) -> bool {
        if !self.numerator.is_well_formed() {
            return false;
        }
        if !self.denominator.is_well_formed() {
            return false;
        }

        match self.sign {
            Sign::Zero => {
                self.numerator.is_zero() && self.denominator.is_one()
            }
            Sign::Positive | Sign::Negative => {
                if self.numerator.is_zero() {
                    return false;
                }
                if !self.denominator.is_not_zero() {
                    return false;
                }

                let mut n_clone = self.numerator.clone();
                let mut d_clone = self.denominator.clone();
                simplify_fraction_without_info(n_clone.inner_mut(), d_clone.inner_mut());

                n_clone == self.numerator && d_clone == self.denominator
            }
        }
    }
}

#[inline]
pub fn cmp_single(large: &[usize], small: usize) -> Ordering {
    debug_assert!(!large.is_empty());

    if large.len() > 1 {
        Ordering::Greater
    } else {
        large[0].cmp(&small)
    }
}

impl<const S: usize> PartialEq for Big<S> {
    #[must_use]
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match (self.sign, other.sign) {
            (Sign::Positive, Sign::Negative) |
            (Sign::Negative, Sign::Positive) => false,
            (Sign::Zero, Sign::Zero) => true,
            (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => {
                self.numerator == other.numerator && self.denominator == other.denominator
            }
            (Sign::Zero, Sign::Positive | Sign::Negative) |
            (Sign::Positive | Sign::Negative, Sign::Zero) => false,
        }
    }
}
impl<const S: usize> Eq for Big<S> {}

impl<const S: usize> PartialEq for NonZeroBig<S> {
    #[must_use]
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.sign == other.sign && self.numerator == other.numerator && self.denominator == other.denominator
    }
}
impl<const S: usize> Eq for NonZeroBig<S> {}

macro_rules! rational {
    ($name:ident, $sign:ident) => {
        impl<const S: usize> Ord for $name<S> {
            #[must_use]
            #[inline]
            fn cmp(&self, other: &Self) -> Ordering {
                self.partial_cmp(other).unwrap()
            }
        }

        impl<const S: usize> PartialOrd for $name<S> {
            #[must_use]
            #[inline]
            #[allow(unreachable_patterns)]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                let by_sign = self.sign.partial_cmp(&other.sign);

                let by_length = by_sign.or_else(|| {
                    debug_assert_eq!(self.sign, other.sign);
                    debug_assert!(self.sign.is_not_zero());

                    let left = self.numerator.len() + other.denominator.len();
                    let right = other.numerator.len() + self.denominator.len();
                    if left > right + 1 {
                        Some(match self.sign {
                            $sign::Positive => Ordering::Greater,
                            $sign::Negative => Ordering::Less,
                            _ => panic!("bug: sign can't be zero"),
                        })
                    } else if right > left + 1 {
                        Some(match self.sign {
                            $sign::Positive => Ordering::Less,
                            $sign::Negative => Ordering::Greater,
                            _ => panic!("bug: sign can't be zero"),
                        })
                    } else {
                        None
                    }
                });

                let by_product = by_length.unwrap_or_else(|| {
                    if self.numerator == other.numerator && self.denominator == other.denominator {
                        Ordering::Equal
                    } else {
                        debug_assert_eq!(self.sign, other.sign);
                        debug_assert!(self.sign.is_not_zero());

                        let (ad, bc) = unsafe {
                            // SAFETY: All values are non zero
                            let ad = mul_non_zero::<S>(&self.numerator, &other.denominator);
                            let bc = mul_non_zero::<S>(&other.numerator, &self.denominator);

                            (ad, bc)
                        };

                        match (cmp(&ad, &bc), self.sign) {
                            (Ordering::Less, $sign::Positive) | (Ordering::Greater, $sign::Negative) => Ordering::Less,
                            (Ordering::Equal, _) => Ordering::Equal,
                            (Ordering::Greater, $sign::Positive) | (Ordering::Less, $sign::Negative) => Ordering::Greater,
                            _ => panic!("bug: sign can't be zero"),
                        }
                    }
                });

                Some(by_product)
            }
        }
    }
}

rational!(Big, Sign);
rational!(NonZeroBig, NonZeroSign);
