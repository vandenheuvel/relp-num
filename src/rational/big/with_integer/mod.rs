use std::cmp::Ordering;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

use num_traits::{One, Zero};
use smallvec::SmallVec;

use crate::{Negateable, NonZero, NonZeroUbig, Sign, Ubig};
use crate::integer::big::ops::building_blocks::is_well_formed_non_zero;
use crate::integer::big::ops::non_zero::{add_assign, mul_non_zero, subtracting_cmp};
use crate::integer::big::ops::normalize::simplify_fraction_without_info;
use crate::rational::big::{Big, NonZeroBig};

mod small;

impl<const S: usize> Add<Ubig<S>> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn add(mut self, rhs: Ubig<S>) -> Self::Output {
        AddAssign::add_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Add<&Ubig<S>> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn add(mut self, rhs: &Ubig<S>) -> Self::Output {
        AddAssign::add_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> AddAssign<Ubig<S>> for Big<S> {
    #[inline]
    fn add_assign(&mut self, rhs: Ubig<S>) {
        // TODO(PERFORMANCE): Utilize ownership of `rhs`.
        AddAssign::add_assign(self, &rhs);
    }
}

impl<const S: usize> AddAssign<&Ubig<S>> for Big<S> {
    #[inline]
    fn add_assign(&mut self, rhs: &Ubig<S>) {
        if rhs.is_not_zero() {
            unsafe {
                // SAFETY: rhs is non zero
                self.add_assign_int_non_zero(rhs);
            }
        }
    }
}

impl<const S: usize> Add<NonZeroUbig<S>> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn add(mut self, rhs: NonZeroUbig<S>) -> Self::Output {
        AddAssign::add_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Add<&NonZeroUbig<S>> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn add(mut self, rhs: &NonZeroUbig<S>) -> Self::Output {
        AddAssign::add_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> AddAssign<NonZeroUbig<S>> for Big<S> {
    #[inline]
    fn add_assign(&mut self, rhs: NonZeroUbig<S>) {
        // TODO(PERFORMANCE): Utilize ownership of `rhs`.
        AddAssign::add_assign(self, &rhs);
    }
}

impl<const S: usize> AddAssign<&NonZeroUbig<S>> for Big<S> {
    #[inline]
    fn add_assign(&mut self, rhs: &NonZeroUbig<S>) {
        unsafe {
            // SAFETY: rhs is non zero
            self.add_assign_int_non_zero(rhs);
        }
    }
}

impl<const S: usize> Big<S> {
    #[inline]
    unsafe fn add_assign_int_non_zero(&mut self, rhs: &[usize]) {
        debug_assert!(is_well_formed_non_zero(rhs));

        match self.sign {
            Sign::Positive => {
                let difference = mul_non_zero::<S>(&self.denominator, rhs);
                add_assign(self.numerator.inner_mut(), &difference)
            },
            Sign::Zero => {
                *self.numerator.inner_mut() = SmallVec::from_slice(rhs);
                debug_assert!(self.denominator.is_one());
            }
            Sign::Negative => {
                let difference = mul_non_zero::<S>(&self.denominator, rhs);
                let ordering = subtracting_cmp(self.numerator.inner_mut(), &difference);

                // ordering can't be equal
                if ordering == Ordering::Less {
                    self.sign.negate();
                }
            }
        }
    }
}

impl<const S: usize> Sub<Ubig<S>> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn sub(mut self, rhs: Ubig<S>) -> Self::Output {
        SubAssign::sub_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Sub<&Ubig<S>> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn sub(mut self, rhs: &Ubig<S>) -> Self::Output {
        SubAssign::sub_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> SubAssign<Ubig<S>> for Big<S> {
    #[inline]
    fn sub_assign(&mut self, rhs: Ubig<S>) {
        // TODO(PERFORMANCE): Utilize ownership of `rhs`.
        SubAssign::sub_assign(self, &rhs);
    }
}

impl<const S: usize> SubAssign<&Ubig<S>> for Big<S> {
    #[inline]
    fn sub_assign(&mut self, rhs: &Ubig<S>) {
        if rhs.is_not_zero() {
            unsafe {
                // SAFETY: rhs is non zero
                self.sub_assign_int_non_zero(rhs);
            }
        }
    }
}

impl<const S: usize> Sub<NonZeroUbig<S>> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn sub(mut self, rhs: NonZeroUbig<S>) -> Self::Output {
        SubAssign::sub_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Sub<&NonZeroUbig<S>> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn sub(mut self, rhs: &NonZeroUbig<S>) -> Self::Output {
        SubAssign::sub_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> SubAssign<NonZeroUbig<S>> for Big<S> {
    #[inline]
    fn sub_assign(&mut self, rhs: NonZeroUbig<S>) {
        // TODO(PERFORMANCE): Utilize ownership of `rhs`.
        SubAssign::sub_assign(self, &rhs);
    }
}

impl<const S: usize> SubAssign<&NonZeroUbig<S>> for Big<S> {
    #[inline]
    fn sub_assign(&mut self, rhs: &NonZeroUbig<S>) {
        unsafe {
            // SAFETY: rhs is non zero
            self.sub_assign_int_non_zero(rhs);
        }
    }
}

impl<const S: usize> Big<S> {
    #[inline]
    unsafe fn sub_assign_int_non_zero(&mut self, rhs: &[usize]) {
        debug_assert!(is_well_formed_non_zero(rhs));

        match self.sign {
            Sign::Positive => {
                let difference = mul_non_zero::<S>(&self.denominator, rhs);
                let ordering = subtracting_cmp(self.numerator.inner_mut(), &difference);

                // ordering can't be equal
                if ordering == Ordering::Less {
                    self.sign.negate();
                }
            }
            Sign::Zero => {
                *self.numerator.inner_mut() = SmallVec::from_slice(rhs);
                self.sign = Sign::Negative;
                debug_assert!(self.denominator.is_one());
            }
            Sign::Negative => {
                let difference = mul_non_zero::<S>(&self.denominator, rhs);
                add_assign(self.numerator.inner_mut(), &difference)
            },
        }
    }
}

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

#[cfg(test)]
mod test {
    use num_traits::{One, Zero};

    use crate::{NonZeroUbig, RationalBig, Ubig};
    use crate::RB;

    #[test]
    fn add() {
        assert_eq!(RB!(2, 3) + NonZeroUbig::new(2).unwrap(), RB!(8, 3));
        assert_eq!(RB!(-2, 3) + NonZeroUbig::new(2).unwrap(), RB!(4, 3));
        assert_eq!(RB!(2, 3) + Ubig::zero(), RB!(2, 3));
        assert_eq!(RB!(2, 3) - NonZeroUbig::new(2).unwrap(), RB!(-4, 3));
        assert_eq!(RB!(0) - NonZeroUbig::one(), RB!(-1));
        assert_eq!(RB!(-2, 3) - NonZeroUbig::new(2).unwrap(), RB!(-8, 3));
    }

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
