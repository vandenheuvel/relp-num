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
        // SAFETY: Both of these only read the last word of the value they are asked about; they are
        // `unsafe` as a marker on the invariant they report on, and impose nothing on the caller.
        if !unsafe { self.numerator.is_well_formed() } {
            return false;
        }
        // SAFETY: As above.
        if !unsafe { self.denominator.is_well_formed() } {
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
                // SAFETY: The two `inner_mut` calls hand out mutable access to the words of copies
                // that are dropped at the end of this block, so nothing observes a broken invariant
                // even though this is what those accessors are `unsafe` for. Both copies are well
                // formed by the two checks at the top and non zero by the two just above, which is
                // what the simplification requires.
                unsafe {
                    simplify_fraction_without_info(n_clone.inner_mut(), d_clone.inner_mut());
                }

                n_clone == self.numerator && d_clone == self.denominator
            }
        }
    }
}

impl<const S: usize> PartialEq for Big<S> {
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
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.sign == other.sign && self.numerator == other.numerator && self.denominator == other.denominator
    }
}
impl<const S: usize> Eq for NonZeroBig<S> {}

macro_rules! rational {
    ($name:ident, $sign:ident) => {
        impl<const S: usize> PartialOrd for $name<S> {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        impl<const S: usize> Ord for $name<S> {
            #[inline]
            #[allow(unreachable_patterns)]
            fn cmp(&self, other: &Self) -> Ordering {
                match self.sign.cmp(&other.sign) {
                    Ordering::Less => return Ordering::Less,
                    Ordering::Greater => return Ordering::Greater,
                    // Both zero, or both nonzero with the same sign; compare the magnitudes.
                    Ordering::Equal => {}
                }

                if !self.sign.is_not_zero() {
                    // Equal signs and the sign is zero, so both values are zero.
                    return Ordering::Equal;
                }

                // When one cross product needs at least two more limbs than the other, the
                // comparison is decided without computing either product.
                let left = self.numerator.len() + other.denominator.len();
                let right = other.numerator.len() + self.denominator.len();
                if left > right + 1 {
                    return match self.sign {
                        $sign::Positive => Ordering::Greater,
                        $sign::Negative => Ordering::Less,
                        _ => unreachable!("sign was checked to be nonzero"),
                    };
                }
                if right > left + 1 {
                    return match self.sign {
                        $sign::Positive => Ordering::Less,
                        $sign::Negative => Ordering::Greater,
                        _ => unreachable!("sign was checked to be nonzero"),
                    };
                }

                if self.numerator == other.numerator && self.denominator == other.denominator {
                    return Ordering::Equal;
                }

                let (ad, bc) = unsafe {
                    // SAFETY: All values are non zero
                    (
                        mul_non_zero::<S>(&self.numerator, &other.denominator),
                        mul_non_zero::<S>(&other.numerator, &self.denominator),
                    )
                };

                match (cmp(&ad, &bc), self.sign) {
                    (Ordering::Less, $sign::Positive) | (Ordering::Greater, $sign::Negative) => Ordering::Less,
                    (Ordering::Equal, _) => Ordering::Equal,
                    (Ordering::Greater, $sign::Positive) | (Ordering::Less, $sign::Negative) => Ordering::Greater,
                    _ => unreachable!("sign was checked to be nonzero"),
                }
            }
        }
    }
}

rational!(Big, Sign);
rational!(NonZeroBig, NonZeroSign);
