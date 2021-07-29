use std::ops::{Div, DivAssign, Mul, MulAssign};

use num_traits::Zero;
use smallvec::SmallVec;

use crate::{NonZero, NonZeroUbig, Ubig};
use crate::integer::big::ops::building_blocks::is_well_formed_non_zero;
use crate::integer::big::ops::non_zero::{is_one_non_zero, mul_assign_single_non_zero, mul_non_zero};
use crate::integer::big::ops::normalize::{simplify_fraction_gcd_single, simplify_fraction_without_info};
use crate::rational::big::{Big, NonZeroBig};

impl<const S: usize> Mul<Ubig<S>> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn mul(mut self, rhs: Ubig<S>) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> MulAssign<Ubig<S>> for Big<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: Ubig<S>) {
        if !rhs.is_zero() {
            if self.is_not_zero() {
                unsafe {
                    mul_assign_int_owning(
                        self.numerator.inner_mut(),
                        self.denominator.inner_mut(),
                        rhs.into_inner(),
                    );
                }
            }
        } else {
            self.set_zero();
        }
    }
}

impl<const S: usize> Mul<NonZeroUbig<S>> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn mul(mut self, rhs: NonZeroUbig<S>) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> MulAssign<NonZeroUbig<S>> for Big<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: NonZeroUbig<S>) {
        if self.is_not_zero() {
            unsafe {
                mul_assign_int_owning(
                    self.numerator.inner_mut(),
                    self.denominator.inner_mut(),
                    rhs.into_inner(),
                );
            }
        }
    }
}

impl<const S: usize> Mul<NonZeroUbig<S>> for NonZeroBig<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn mul(mut self, rhs: NonZeroUbig<S>) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> MulAssign<NonZeroUbig<S>> for NonZeroBig<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: NonZeroUbig<S>) {
        unsafe {
            mul_assign_int_owning(
                self.numerator.inner_mut(),
                self.denominator.inner_mut(),
                rhs.into_inner(),
            );
        }
    }
}

impl<const S: usize> Mul<&NonZeroUbig<S>> for NonZeroBig<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn mul(mut self, rhs: &NonZeroUbig<S>) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> MulAssign<&NonZeroUbig<S>> for NonZeroBig<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: &NonZeroUbig<S>) {
        unsafe {
            mul_assign_int(
                self.numerator.inner_mut(),
                self.denominator.inner_mut(),
                rhs.inner(),
            );
        }
    }
}

impl<const S: usize> MulAssign<&NonZeroUbig<S>> for Big<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: &NonZeroUbig<S>) {
        if self.is_not_zero() {
            unsafe {
                mul_assign_int(
                    self.numerator.inner_mut(),
                    self.denominator.inner_mut(),
                    rhs.inner(),
                );
            }
        }
    }
}

impl<const S: usize> Div<NonZeroUbig<S>> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn div(mut self, rhs: NonZeroUbig<S>) -> Self::Output {
        DivAssign::div_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> DivAssign<NonZeroUbig<S>> for Big<S> {
    #[inline]
    fn div_assign(&mut self, rhs: NonZeroUbig<S>) {
        if self.is_not_zero() {
            unsafe {
                mul_assign_int_owning(
                    self.denominator.inner_mut(),
                    self.numerator.inner_mut(),
                    rhs.into_inner(),
                );
            }
        }
    }
}

impl<const S: usize> DivAssign<&NonZeroUbig<S>> for Big<S> {
    #[inline]
    fn div_assign(&mut self, rhs: &NonZeroUbig<S>) {
        if self.is_not_zero() {
            unsafe {
                mul_assign_int(
                    self.denominator.inner_mut(),
                    self.numerator.inner_mut(),
                    rhs.inner(),
                );
            }
        }
    }
}

impl<const S: usize> Div<Ubig<S>> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn div(mut self, rhs: Ubig<S>) -> Self::Output {
        DivAssign::div_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> DivAssign<Ubig<S>> for Big<S> {
    #[inline]
    fn div_assign(&mut self, rhs: Ubig<S>) {
        if !rhs.is_zero() {
            unsafe {
                mul_assign_int_owning(
                    self.denominator.inner_mut(),
                    self.numerator.inner_mut(),
                    rhs.into_inner(),
                );
            }
        } else {
            panic!("attempt to divide by zero");
        }
    }
}

impl<const S: usize> Div<NonZeroUbig<S>> for NonZeroBig<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn div(mut self, rhs: NonZeroUbig<S>) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> DivAssign<NonZeroUbig<S>> for NonZeroBig<S> {
    #[inline]
    fn div_assign(&mut self, rhs: NonZeroUbig<S>) {
        unsafe {
            mul_assign_int_owning(
                self.denominator.inner_mut(),
                self.numerator.inner_mut(),
                rhs.into_inner(),
            );
        }
    }
}

impl<const S: usize> Div<&NonZeroUbig<S>> for NonZeroBig<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn div(mut self, rhs: &NonZeroUbig<S>) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> DivAssign<&NonZeroUbig<S>> for NonZeroBig<S> {
    #[inline]
    fn div_assign(&mut self, rhs: &NonZeroUbig<S>) {
        unsafe {
            mul_assign_int(
                self.denominator.inner_mut(),
                self.numerator.inner_mut(),
                rhs.inner(),
            );
        }
    }
}

#[inline]
unsafe fn mul_assign_int<const S: usize>(
    left_numerator: &mut SmallVec<[usize; S]>, left_denominator: &mut SmallVec<[usize; S]>,
    right: &[usize],
) {
    debug_assert!(is_well_formed_non_zero(left_numerator));
    debug_assert!(is_well_formed_non_zero(left_denominator));
    debug_assert!(is_well_formed_non_zero(right));

    *left_numerator = mul_non_zero(left_numerator, right);
    simplify_fraction_without_info(left_numerator, left_denominator);
}

#[inline]
unsafe fn mul_assign_int_owning<const S: usize>(
    left_numerator: &mut SmallVec<[usize; S]>, left_denominator: &mut SmallVec<[usize; S]>,
    mut right: SmallVec<[usize; S]>,
) {
    debug_assert!(is_well_formed_non_zero(left_numerator));
    debug_assert!(is_well_formed_non_zero(left_denominator));
    debug_assert!(is_well_formed_non_zero(&right));

    simplify_fraction_without_info(left_denominator, &mut right);
    *left_numerator = mul_non_zero(left_numerator, &right);
}

impl<const S: usize> MulAssign<&usize> for Big<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: &usize) {
        MulAssign::mul_assign(self, *rhs);
    }
}

impl<const S: usize> MulAssign<usize> for Big<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: usize) {
        if !self.is_zero() {
            if rhs != 0 {
                unsafe {
                    // SAFETY: The numerator is not zero, rhs is not zero or one
                    // SAFETY: Denominator can't become zero
                    mul_assign_usize(
                        self.numerator.inner_mut(),
                        self.denominator.inner_mut(),
                        rhs,
                    );
                }
            } else {
                self.set_zero()
            }
        }
    }
}

impl<const S: usize> DivAssign<&usize> for Big<S> {
    #[inline]
    fn div_assign(&mut self, rhs: &usize) {
        DivAssign::div_assign(self, *rhs);
    }
}

impl<const S: usize> DivAssign<usize> for Big<S> {
    #[inline]
    fn div_assign(&mut self, rhs: usize) {
        if rhs != 0 {
            if !self.is_zero() {
                unsafe {
                    // SAFETY: The numerator is not zero, rhs is not zero or one
                    // SAFETY: Denominator can't become zero
                    mul_assign_usize(
                        self.denominator.inner_mut(),
                        self.numerator.inner_mut(),
                        rhs,
                    );
                }
            }
        } else {
            panic!("attempt to divide by zero");
        }
    }
}

impl<const S: usize> MulAssign<&usize> for NonZeroBig<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: &usize) {
        MulAssign::mul_assign(self, *rhs);
    }
}

impl<const S: usize> MulAssign<usize> for NonZeroBig<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: usize) {
        if rhs != 0 {
            unsafe {
                // SAFETY: The numerator is not zero, rhs is not zero or one
                // SAFETY: Denominator can't become zero
                mul_assign_usize(
                    self.numerator.inner_mut(),
                    self.denominator.inner_mut(),
                    rhs,
                );
            }
        } else {
            panic!("attempt to multiply by zero")
        }
    }
}

impl<const S: usize> DivAssign<&usize> for NonZeroBig<S> {
    #[inline]
    fn div_assign(&mut self, rhs: &usize) {
        DivAssign::div_assign(self, *rhs);
    }
}

impl<const S: usize> DivAssign<usize> for NonZeroBig<S> {
    #[inline]
    fn div_assign(&mut self, rhs: usize) {
        if rhs != 0 {
            unsafe {
                // SAFETY: The numerator is not zero, rhs is not zero or one
                // SAFETY: Denominator can't become zero
                mul_assign_usize(
                    self.denominator.inner_mut(),
                    self.numerator.inner_mut(),
                    rhs,
                );
            }
        } else {
            panic!("attempt to divide by zero");
        }
    }
}

#[inline]
unsafe fn mul_assign_usize<const S: usize>(
    left_numerator: &mut SmallVec<[usize; S]>, left_denominator: &mut SmallVec<[usize; S]>,
    mut rhs: usize,
) {
    debug_assert!(is_well_formed_non_zero(left_numerator));
    debug_assert!(is_well_formed_non_zero(left_denominator));
    debug_assert_ne!(rhs, 0);

    if rhs != 1 {
        if !is_one_non_zero(left_denominator) {
            rhs = simplify_fraction_gcd_single(left_denominator, rhs)
        }
        mul_assign_single_non_zero(left_numerator, rhs);
    }
}


#[cfg(test)]
mod test {
    use num_traits::{One, Zero};

    use crate::{NonZeroUbig, RationalBig, Ubig};
    use crate::RB;

    #[test]
    fn mul_assign() {
        assert_eq!(RB!(2, 3) * NonZeroUbig::new(2).unwrap(), RB!(4, 3));
        assert_eq!(RB!(2, 3) * Ubig::zero(), RB!(0));
        assert_eq!(RB!(2, 3) / NonZeroUbig::new(2).unwrap(), RB!(1, 3));
        assert_eq!(RB!(0) * NonZeroUbig::one(), RB!(0));
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn mul_panic() {
        RationalBig::one() / Ubig::zero();
    }
}
