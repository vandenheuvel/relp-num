use std::cmp::Ordering;
use std::ops::{Add, AddAssign, Div, Mul, Sub, SubAssign};

use num_traits::Zero;

use crate::{One, Sign};
use crate::integer::big::ops::non_zero::{add_assign, both_not_one_non_zero, is_one_non_zero, subtracting_cmp};
use crate::rational::big::Big;

impl<const S: usize> From<One> for Big<S> {
    fn from(_: One) -> Self {
        num_traits::One::one()
    }
}

impl<const S: usize> From<&One> for Big<S> {
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
                debug_assert!(num_traits::One::is_one(&mut self.denominator));
            }
            Sign::Negative => {
                let both_not_one = unsafe {
                    // SAFETY: Both are non zero
                    both_not_one_non_zero(&self.numerator, &self.denominator)
                };
                if both_not_one {
                    unsafe {
                        let sign_change = subtracting_cmp(
                            self.numerator.inner_mut(), self.denominator.inner(),
                        );
                        match sign_change {
                            Ordering::Less => self.sign = !self.sign,
                            Ordering::Greater => {}
                            Ordering::Equal => panic!(),
                        }
                    }
                } else {
                    self.set_zero();
                }
            }
        }
    }
}

impl<const S: usize> AddAssign<One> for Big<S> {
    #[inline]
    fn add_assign(&mut self, _: One) {
        AddAssign::add_assign(self, &One);
    }
}

impl<const S: usize> Sub<One> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn sub(mut self, _: One) -> Self::Output {
        <Self as SubAssign<One>>::sub_assign(&mut self, One);
        self
    }
}

impl<const S: usize> SubAssign<One> for Big<S> {
    #[inline]
    fn sub_assign(&mut self, _: One) {
        match self.sign {
            Sign::Positive => {
                let numerator_is_one = unsafe { is_one_non_zero(&self.numerator.inner_mut()) };
                if !numerator_is_one || !num_traits::One::is_one(&self.denominator) {
                    match unsafe { subtracting_cmp(self.numerator.inner_mut(), self.denominator.inner()) } {
                        Ordering::Less => self.sign = !self.sign,
                        Ordering::Greater => {}
                        Ordering::Equal => {}
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

impl<const S: usize> Mul<&One> for &Big<S> {
    type Output = Big<S>;

    #[inline]
    fn mul(self, _: &One) -> Self::Output {
        self.clone()
    }
}

impl<const S: usize> Div<&One> for Big<S> {
    type Output = Self;

    #[inline]
    fn div(self, _: &One) -> Self::Output {
        self
    }
}
