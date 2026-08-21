use std::cmp::Ordering;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

use num_traits::Zero;

use crate::Sign;
use crate::fixed::One;
use crate::integer::big::ops::non_zero::{add_assign, is_one_non_zero, subtracting_cmp};
use crate::rational::big::Big;

impl<const S: usize> From<One> for Big<S> {
    #[inline]
    fn from(_: One) -> Self {
        num_traits::One::one()
    }
}

impl<const S: usize> From<&One> for Big<S> {
    #[inline]
    fn from(_: &One) -> Self {
        num_traits::One::one()
    }
}

impl<const S: usize> Add<One> for Big<S> {
    type Output = Self;

    #[inline]
    fn add(mut self, _: One) -> Self::Output {
        <Self as AddAssign<One>>::add_assign(&mut self, One);
        self
    }
}

impl<const S: usize> Add<&One> for Big<S> {
    type Output = Self;

    #[inline]
    fn add(mut self, _: &One) -> Self::Output {
        <Self as AddAssign<&One>>::add_assign(&mut self, &One);
        self
    }
}

impl<const S: usize> AddAssign<One> for Big<S> {
    #[inline]
    fn add_assign(&mut self, _: One) {
        AddAssign::add_assign(self, &One);
    }
}

impl<const S: usize> AddAssign<&One> for Big<S> {
    #[inline]
    fn add_assign(&mut self, _: &One) {
        match self.sign {
            Sign::Positive => unsafe {
                // SAFETY: Well formed and non zero
                add_assign(self.numerator.inner_mut(), self.denominator.inner());
            },
            Sign::Zero => {
                self.sign = Sign::Positive;
                debug_assert!(self.numerator.is_zero());
                num_traits::One::set_one(&mut self.numerator);
                debug_assert!(num_traits::One::is_one(&self.denominator));
            }
            Sign::Negative => {
                // `-a/b + 1 == 0` requires `a == b`, which in lowest terms means both are one.
                // Testing only one of the two would cancel values such as `-1/2` and `-2`.
                let is_minus_one = unsafe {
                    // SAFETY: Both are well formed and non zero
                    is_one_non_zero(self.numerator.inner())
                        && is_one_non_zero(self.denominator.inner())
                };
                if is_minus_one {
                    self.set_zero();
                } else {
                    unsafe {
                        let sign_change = subtracting_cmp(
                            self.numerator.inner_mut(), self.denominator.inner(),
                        );
                        debug_assert_ne!(
                            sign_change, Ordering::Equal,
                            "only -1 + 1 cancels, and that was handled above",
                        );
                        if sign_change == Ordering::Less {
                            self.sign = Sign::Positive;
                        }
                    }
                }
            }
        }
    }
}

impl<const S: usize> Sub<One> for Big<S> {
    type Output = Self;

    #[inline]
    fn sub(mut self, _: One) -> Self::Output {
        SubAssign::sub_assign(&mut self, One);
        self
    }
}

impl<const S: usize> Sub<&One> for Big<S> {
    type Output = Self;

    #[inline]
    fn sub(mut self, _: &One) -> Self::Output {
        SubAssign::sub_assign(&mut self, One);
        self
    }
}

impl<const S: usize> SubAssign<One> for Big<S> {
    #[inline]
    fn sub_assign(&mut self, _: One) {
        SubAssign::sub_assign(self, &One);
    }
}

impl<const S: usize> SubAssign<&One> for Big<S> {
    #[inline]
    fn sub_assign(&mut self, _: &One) {
        match self.sign {
            Sign::Positive => {
                let numerator_is_one = unsafe { is_one_non_zero(self.numerator.inner()) };
                if !numerator_is_one || !num_traits::One::is_one(&self.denominator) {
                    let direction = unsafe {
                        subtracting_cmp(self.numerator.inner_mut(), self.denominator.inner())
                    };
                    if direction == Ordering::Less {
                        self.sign = Sign::Negative;
                    }
                } else {
                    self.set_zero();
                }
            }
            Sign::Zero => {
                self.sign = Sign::Negative;
                debug_assert!(self.numerator.is_empty());
                unsafe {
                    // SAFETY: Value was empty before
                    self.numerator.inner_mut().push(1);
                }
                debug_assert_eq!(self.denominator[0], 1);
                debug_assert_eq!(self.denominator.len(), 1);
            }
            Sign::Negative => unsafe {
                // SAFETY: Both are well-formed and non zero
                add_assign(self.numerator.inner_mut(), &self.denominator)
            },
        }
    }
}

impl<const S: usize> Mul<One> for Big<S> {
    type Output = Self;

    #[inline]
    fn mul(self, _: One) -> Self::Output {
        self
    }
}

impl<const S: usize> Mul<&One> for Big<S> {
    type Output = Self;

    #[inline]
    fn mul(self, _: &One) -> Self::Output {
        self
    }
}

impl<const S: usize> Mul<One> for &Big<S> {
    type Output = Big<S>;

    #[inline]
    fn mul(self, _: One) -> Self::Output {
        self.clone()
    }
}

impl<const S: usize> Mul<&One> for &Big<S> {
    type Output = Big<S>;

    #[inline]
    fn mul(self, _: &One) -> Self::Output {
        self.clone()
    }
}

impl<const S: usize> MulAssign<One> for Big<S> {
    #[inline]
    fn mul_assign(&mut self, _: One) {
    }
}

impl<const S: usize> MulAssign<&One> for Big<S> {
    #[inline]
    fn mul_assign(&mut self, _: &One) {
    }
}

impl<const S: usize> Div<One> for Big<S> {
    type Output = Self;

    #[inline]
    fn div(self, _: One) -> Self::Output {
        self
    }
}

impl<const S: usize> Div<&One> for Big<S> {
    type Output = Self;

    #[inline]
    fn div(self, _: &One) -> Self::Output {
        self
    }
}

impl<const S: usize> Div<One> for &Big<S> {
    type Output = Big<S>;

    #[inline]
    fn div(self, _: One) -> Self::Output {
        self.clone()
    }
}

impl<const S: usize> Div<&One> for &Big<S> {
    type Output = Big<S>;

    #[inline]
    fn div(self, _: &One) -> Self::Output {
        self.clone()
    }
}

impl<const S: usize> DivAssign<One> for Big<S> {
    #[inline]
    fn div_assign(&mut self, _: One) {
    }
}

impl<const S: usize> DivAssign<&One> for Big<S> {
    #[inline]
    fn div_assign(&mut self, _: &One) {
    }
}

#[cfg(test)]
mod test {
    use crate::fixed::One;
    use crate::{R8, RB, Rational8, RationalBig};

    /// `-a/b + 1` is zero only when `a == b == 1`; every other negative value must survive.
    ///
    /// The guard used to fire whenever the numerator *or* the denominator was one, so values
    /// such as `-1/2` and `-2` were silently collapsed to zero.
    #[test]
    fn add_one_to_negative() {
        assert_eq!(RB!(-1) + One, RB!(0));
        assert_eq!(RB!(-1, 2) + One, RB!(1, 2));
        assert_eq!(RB!(-2) + One, RB!(-1));
        assert_eq!(RB!(-3) + One, RB!(-2));
        assert_eq!(RB!(-3, 2) + One, RB!(-1, 2));
        assert_eq!(RB!(-1, 3) + One, RB!(2, 3));
        assert_eq!(RB!(-5, 4) + One, RB!(-1, 4));
        assert_eq!(RB!(-7, 3) + One, RB!(-4, 3));
    }

    /// The arbitrary precision and the fixed size implementations must agree.
    #[test]
    fn add_one_agrees_with_small() {
        for numerator in -6_i8..=6 {
            for denominator in 1_u8..=6 {
                let small = Rational8::new(numerator, denominator).unwrap();
                assert_eq!(
                    RationalBig::from(small) + One,
                    RationalBig::from(small + One),
                    "{numerator}/{denominator} + 1",
                );
            }
        }
        assert_eq!(RB!(-1, 2) + One, RationalBig::from(R8!(-1, 2) + One));
    }
}
