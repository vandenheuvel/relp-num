use std::ops::{Add, AddAssign, Sub, SubAssign};

use crate::{Negateable, NonZero, Sign};
use crate::rational::big::Big;
use crate::rational::big::ops::building_blocks::{add_assign_fraction_non_zero, SignChange, sub_assign_fraction_non_zero};

impl<const S: usize> Big<S> {
    /// Subtract the magnitude of `rhs`, then fold the resulting sign change into `self.sign`.
    ///
    /// # Safety
    ///
    /// Neither value may be zero; the caller dispatches on the two signs to establish that.
    unsafe fn sub_assign_update_sign(&mut self, rhs: &Self) {
        // SAFETY: These four only read the last word of the value they are asked about; they are
        // `unsafe` as a marker on the invariant they report on, and impose nothing on the caller.
        unsafe {
            debug_assert!(self.numerator.is_well_formed());
            debug_assert!(self.denominator.is_well_formed());
            debug_assert!(rhs.numerator.is_well_formed());
            debug_assert!(rhs.denominator.is_well_formed());
        }
        debug_assert!(self.numerator.is_not_zero());
        debug_assert!(self.denominator.is_not_zero());
        debug_assert!(rhs.numerator.is_not_zero());
        debug_assert!(rhs.denominator.is_not_zero());

        // SAFETY: Both fractions are well formed, non zero by this function's contract, and in
        // lowest terms because that is the invariant every `Big` upholds, which is what the
        // subtraction needs. The two `inner_mut` calls hand out mutable access to the words behind
        // that invariant; the subtraction restores it before returning, and the sign is brought
        // back in line with the new magnitude just below.
        let sign_change = unsafe {
            sub_assign_fraction_non_zero(
                self.numerator.inner_mut(),
                self.denominator.inner_mut(),
                &rhs.numerator,
                &rhs.denominator,
            )
        };
        match sign_change {
            SignChange::None => {}
            SignChange::Flip => self.sign.negate(),
            SignChange::Zero => self.sign = Sign::Zero,
        }
    }
}

impl<const S: usize> Add for Big<S> {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: Big<S>) -> Self::Output {
        match (self.sign, rhs.sign) {
            (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => {
                // TODO(PERFORMANCE): Can the ownership of rhs be utilized?
                unsafe {
                    // SAFETY: All values are non zero
                    add_assign_fraction_non_zero(
                        self.numerator.inner_mut(),
                        self.denominator.inner_mut(),
                        &rhs.numerator,
                        &rhs.denominator,
                    )
                }
                self
            },
            (Sign::Positive, Sign::Negative) | (Sign::Negative, Sign::Positive) => {
                // TODO(PERFORMANCE): Can the ownership of rhs be utilized?
                unsafe {
                    // SAFETY: All values are non zero
                    self.sub_assign_update_sign(&rhs);
                }
                self
            },
            (_, Sign::Zero) => self,
            (Sign::Zero, _) => rhs,
        }
    }
}

impl<const S: usize> Add<Big<S>> for &Big<S> {
    type Output = Big<S>;

    #[inline]
    fn add(self, rhs: Big<S>) -> Self::Output {
        Add::add(rhs, self)
    }
}

impl<const S: usize> Add<&Big<S>> for Big<S> {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: &Big<S>) -> Self::Output {
        self += rhs;
        self
    }
}

impl<const S: usize> Add for &Big<S> {
    type Output = Big<S>;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        // TODO(PERFORMANCE): Which one should be cloned?
        let x = self.clone();
        x + rhs
    }
}

impl<const S: usize> AddAssign for Big<S> {
    #[inline]
    fn add_assign(&mut self, rhs: Big<S>) {
        // TODO(PERFORMANCE): Utilize ownership somehow?
        AddAssign::add_assign(self, &rhs);
    }
}

impl<const S: usize> AddAssign<&Big<S>> for Big<S> {
    #[inline]
    fn add_assign(&mut self, rhs: &Big<S>) {
        match (self.sign, rhs.sign) {
            (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => {
                unsafe {
                    // SAFETY: All values are non zero
                    add_assign_fraction_non_zero(
                        self.numerator.inner_mut(),
                        self.denominator.inner_mut(),
                        &rhs.numerator,
                        &rhs.denominator,
                    )
                }
            },
            (Sign::Positive, Sign::Negative) | (Sign::Negative, Sign::Positive) => {
                unsafe {
                    // SAFETY: All values are non zero
                    self.sub_assign_update_sign(rhs);
                }
            },
            (_, Sign::Zero) => {},
            (Sign::Zero, _) => *self = rhs.clone(),
        }
    }
}

impl<const S: usize> Sub for Big<S> {
    type Output = Self;

    #[inline]
    fn sub(mut self, mut rhs: Big<S>) -> Self::Output {
        match (self.sign, rhs.sign) {
            (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => {
                unsafe {
                    // SAFETY: All values are non zero
                    self.sub_assign_update_sign(&rhs);
                }
                self
            },
            (Sign::Positive, Sign::Negative) | (Sign::Negative, Sign::Positive) => {
                unsafe {
                    // SAFETY: All values are non zero
                    add_assign_fraction_non_zero(
                        self.numerator.inner_mut(),
                        self.denominator.inner_mut(),
                        &rhs.numerator,
                        &rhs.denominator,
                    );
                }
                self
            },
            (_, Sign::Zero) => self,
            (Sign::Zero, _) => {
                rhs.sign = !rhs.sign;
                rhs
            },
        }
    }
}

impl<const S: usize> Sub<&Big<S>> for Big<S> {
    type Output = Self;

    #[inline]
    fn sub(mut self, rhs: &Big<S>) -> Self::Output {
        SubAssign::sub_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Sub<Big<S>> for &Big<S> {
    type Output = Big<S>;

    #[inline]
    fn sub(self, rhs: Big<S>) -> Self::Output {
        -Sub::sub(rhs, self)
    }
}

impl<const S: usize> Sub for &Big<S> {
    type Output = Big<S>;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        // TODO(PERFORMANCE): Which one should be cloned?
        Sub::sub(self.clone(), rhs)
    }
}

impl<const S: usize> SubAssign<Big<S>> for Big<S> {
    // TODO(PERFORMANCE): Utilize ownership somehow?
    #[inline]
    fn sub_assign(&mut self, rhs: Big<S>) {
        SubAssign::sub_assign(self, &rhs);
    }
}

impl<const S: usize> SubAssign<&Big<S>> for Big<S> {
    #[inline]
    fn sub_assign(&mut self, rhs: &Big<S>) {
        match (self.sign, rhs.sign) {
            (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => {
                unsafe {
                    // SAFETY: All values are non zero
                    self.sub_assign_update_sign(rhs);
                }
            },
            (Sign::Positive, Sign::Negative) | (Sign::Negative, Sign::Positive) => unsafe {
                add_assign_fraction_non_zero(
                    self.numerator.inner_mut(),
                    self.denominator.inner_mut(),
                    &rhs.numerator,
                    &rhs.denominator,
                );
            },
            (_, Sign::Zero) => {},
            (Sign::Zero, _) => {
                *self = Self {
                    sign: !rhs.sign,
                    numerator: rhs.numerator.clone(),
                    denominator: rhs.denominator.clone(),
                };
            },
        }
    }
}

#[cfg(test)]
mod test {
    use crate::RB;

    #[test]
    fn test_add() {
        let mut x = RB!(3, 4);
        x += RB!(-5, 6);
        assert_eq!(x, RB!(3 * 6 - 5 * 4, 4 * 6));

        let mut x = RB!(3, 4);
        x += RB!(5, 6);
        assert_eq!(x, RB!(3 * 6 + 5 * 4, 4 * 6));

        let mut x = RB!(0);
        x += &RB!(-5, 6);
        assert_eq!(x, RB!(-5, 6));

        let mut x = RB!(-5, 6);
        x += RB!(0);
        assert_eq!(x, RB!(-5, 6));
    }

    #[test]
    fn test_sub() {
        let mut x = RB!(3, 4);
        x -= RB!(-5, 6);
        assert_eq!(x, RB!(3 * 6 + 5 * 4, 4 * 6));

        let mut x = RB!(3, 4);
        x -= RB!(5, 6);
        assert_eq!(x, RB!(3 * 6 - 5 * 4, 4 * 6));

        let mut x = RB!(0);
        x -= RB!(-5, 6);
        assert_eq!(x, RB!(5, 6));

        let mut x = RB!(-5, 6);
        x -= &RB!(0);
        assert_eq!(x, RB!(-5, 6));
    }
}
