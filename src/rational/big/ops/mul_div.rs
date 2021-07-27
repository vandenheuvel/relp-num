use std::ops::{Div, DivAssign, Mul, MulAssign};

use num_traits::Zero;

use crate::rational::big::{Big, NonZeroBig};
use crate::rational::big::ops::building_blocks::mul_assign_fraction_non_zero;
use crate::Sign;

impl<const S: usize> Mul for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn mul(mut self, rhs: Self) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Mul for NonZeroBig<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn mul(mut self, rhs: Self) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Mul<&Big<S>> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn mul(mut self, rhs: &Big<S>) -> Self::Output {
        // TODO(PERFORMANCE): Should cloning be avoided?
        MulAssign::mul_assign(&mut self, rhs.clone());
        self
    }
}

impl<const S: usize> Mul<Big<S>> for &Big<S> {
    type Output = Big<S>;

    #[must_use]
    #[inline]
    fn mul(self, rhs: Big<S>) -> Self::Output {
        Mul::mul(rhs, self)
    }
}

impl<const S: usize> Mul<&Big<S>> for &Big<S> {
    type Output = Big<S>;

    #[must_use]
    #[inline]
    fn mul(self, rhs: &Big<S>) -> Self::Output {
        let mut x = self.clone();
        // TODO(PERFORMANCE): Should cloning be avoided?
        MulAssign::mul_assign(&mut x, rhs.clone());
        x
    }
}

impl<const S: usize> MulAssign for Big<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        match (self.sign, rhs.sign) {
            (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                self.sign *= rhs.sign;
                unsafe {
                    // SAFETY: All values are non zero
                    mul_assign_fraction_non_zero(
                        self.numerator.inner_mut(),
                        self.denominator.inner_mut(),
                        rhs.numerator.inner().clone(),
                        rhs.denominator.inner().clone(),
                    );
                }
            }
            (Sign::Positive | Sign::Negative, Sign::Zero) => {
                self.set_zero();
            }
            (Sign::Zero, _) => {}
        }
    }
}

impl<const S: usize> MulAssign for NonZeroBig<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        self.sign *= rhs.sign;
        unsafe {
            // SAFETY: All values are non zero
            mul_assign_fraction_non_zero(
                self.numerator.inner_mut(),
                self.denominator.inner_mut(),
                rhs.numerator.inner().clone(),
                rhs.denominator.inner().clone(),
            );
        }
    }
}

impl<const S: usize> Mul<&NonZeroBig<S>> for NonZeroBig<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn mul(mut self, rhs: &NonZeroBig<S>) -> Self::Output {
        // TODO(PERFORMANCE): Should cloning be avoided?
        MulAssign::mul_assign(&mut self, rhs.clone());
        self
    }
}

impl<const S: usize> Mul<&NonZeroBig<S>> for &NonZeroBig<S> {
    type Output = NonZeroBig<S>;

    #[must_use]
    #[inline]
    fn mul(self, rhs: &NonZeroBig<S>) -> Self::Output {
        let mut x = self.clone();
        // TODO(PERFORMANCE): Should cloning be avoided?
        MulAssign::mul_assign(&mut x, rhs.clone());
        x
    }
}

impl<const S: usize> MulAssign<&NonZeroBig<S>> for NonZeroBig<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: &Self) {
        self.sign *= rhs.sign;
        unsafe {
            // SAFETY: All values are non zero
            mul_assign_fraction_non_zero(
                self.numerator.inner_mut(),
                self.denominator.inner_mut(),
                rhs.numerator.inner().clone(),
                rhs.denominator.inner().clone(),
            );
        }
    }
}

impl<const S: usize> MulAssign<&Big<S>> for Big<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: &Self) {
        match (self.sign, rhs.sign) {
            (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                self.sign *= rhs.sign;
                unsafe {
                    // SAFETY: All values are non zero
                    mul_assign_fraction_non_zero(
                        self.numerator.inner_mut(),
                        self.denominator.inner_mut(),
                        rhs.numerator.inner().clone(),
                        rhs.denominator.inner().clone(),
                    );
                }
            }
            (Sign::Positive | Sign::Negative, Sign::Zero) => {
                self.set_zero();
            }
            (Sign::Zero, _) => {}
        }
    }
}
impl<const S: usize> Div<Big<S>> for Big<S> {
    type Output = Big<S>;

    #[inline]
    fn div(mut self, rhs: Big<S>) -> Self::Output {
        DivAssign::div_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Div<&Big<S>> for Big<S> {
    type Output = Big<S>;

    #[inline]
    fn div(mut self, rhs: &Big<S>) -> Self::Output {
        DivAssign::div_assign(&mut self, rhs.clone());
        self
    }
}

impl<const S: usize> Div<Big<S>> for &Big<S> {
    type Output = Big<S>;

    #[inline]
    fn div(self, rhs: Big<S>) -> Self::Output {
        let mut x = self.clone();
        // TODO(PERFORMANCE): Should cloning be avoided?
        DivAssign::div_assign(&mut x, rhs);
        x
    }
}

impl<const S: usize> Div<&Big<S>> for &Big<S> {
    type Output = Big<S>;

    #[inline]
    fn div(self, rhs: &Big<S>) -> Self::Output {
        let mut x = self.clone();
        // TODO(PERFORMANCE): Should cloning be avoided?
        DivAssign::div_assign(&mut x, rhs.clone());
        x
    }
}

impl<const S: usize> DivAssign<&Big<S>> for Big<S> {
    #[inline]
    fn div_assign(&mut self, rhs: &Big<S>) {
        DivAssign::div_assign(self, rhs.clone());
    }
}

impl<const S: usize> Div<&NonZeroBig<S>> for &NonZeroBig<S> {
    type Output = NonZeroBig<S>;

    #[must_use]
    #[inline]
    fn div(self, rhs: &NonZeroBig<S>) -> Self::Output {
        let mut x = self.clone();
        // TODO(PERFORMANCE): Should cloning be avoided?
        DivAssign::div_assign(&mut x, rhs.clone());
        x
    }
}

impl<const S: usize> DivAssign for Big<S> {
    #[inline]
    fn div_assign(&mut self, rhs: Self) {
        match (self.sign, rhs.sign) {
            (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                self.sign *= rhs.sign;
                unsafe {
                    // SAFETY: All values are non zero
                    mul_assign_fraction_non_zero(
                        self.numerator.inner_mut(),
                        self.denominator.inner_mut(),
                        rhs.denominator.into_inner(),
                        rhs.numerator.into_inner(),
                    );
                }
            }
            (Sign::Positive | Sign::Negative, Sign::Zero) => panic!("attempt to divide by zero"),
            (Sign::Zero, _) => {}
        }
    }
}

impl<const S: usize> DivAssign for NonZeroBig<S> {
    #[inline]
    fn div_assign(&mut self, rhs: Self) {
        self.sign *= rhs.sign;
        unsafe {
            // SAFETY: All values are non zero
            mul_assign_fraction_non_zero(
                self.numerator.inner_mut(),
                self.denominator.inner_mut(),
                rhs.denominator.into_inner(),
                rhs.numerator.into_inner(),
            );
        }
    }
}

impl<const S: usize> DivAssign<&NonZeroBig<S>> for NonZeroBig<S> {
    #[inline]
    fn div_assign(&mut self, rhs: &Self) {
        self.sign *= rhs.sign;
        unsafe {
            // SAFETY: All values are non zero
            mul_assign_fraction_non_zero(
                self.numerator.inner_mut(),
                self.denominator.inner_mut(),
                rhs.denominator.inner().clone(),
                rhs.numerator.inner().clone(),
            );
        }
    }
}


#[cfg(test)]
mod test {
    use crate::RB;

    #[test]
    fn test_mul() {
        let mut x = RB!(3, 4);
        x *= RB!(-5, 6);
        assert_eq!(x, RB!(-3 * 5, 4 * 6));

        let mut x = RB!(3, 4);
        x *= RB!(5, 6);
        assert_eq!(x, RB!(3 * 5, 4 * 6));

        let mut x = RB!(0);
        x *= &RB!(-5, 6);
        assert_eq!(x, RB!(0));

        let mut x = RB!(-5, 6);
        x *= RB!(0);
        assert_eq!(x, RB!(0));
    }

    #[test]
    fn test_div() {
        let mut x = RB!(3, 4);
        x /= RB!(-5, 6);
        assert_eq!(x, RB!(-3 * 6, 5 * 4));

        let mut x = RB!(3, 4);
        x /= &RB!(5, 6);
        assert_eq!(x, RB!(3 * 6, 5 * 4));

        let mut x = RB!(0);
        x /= RB!(-5, 6);
        assert_eq!(x, RB!(0));
    }

    #[test]
    #[should_panic]
    fn test_div_by_zero() {
        let mut x = RB!(-5, 6);
        x /= RB!(0);
        assert_eq!(x, RB!(-5, 6));
    }
}
