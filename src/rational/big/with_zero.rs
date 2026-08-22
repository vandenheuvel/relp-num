use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

use crate::rational::big::Big;
use crate::fixed::Zero;

impl<const S: usize> From<Zero> for Big<S> {
    #[inline]
    fn from(_: Zero) -> Self {
        num_traits::Zero::zero()
    }
}

impl<const S: usize> From<&Zero> for Big<S> {
    #[inline]
    fn from(_: &Zero) -> Self {
        num_traits::Zero::zero()
    }
}

impl<const S: usize> Add<Zero> for Big<S> {
    type Output = Self;

    #[inline]
    fn add(self, _: Zero) -> Self::Output {
        self
    }
}

impl<const S: usize> Add<&Zero> for Big<S> {
    type Output = Self;

    #[inline]
    fn add(self, _: &Zero) -> Self::Output {
        self
    }
}

impl<const S: usize> AddAssign<Zero> for Big<S> {
    #[inline]
    fn add_assign(&mut self, _: Zero) {
    }
}

impl<const S: usize> AddAssign<&Zero> for Big<S> {
    #[inline]
    fn add_assign(&mut self, _: &Zero) {
    }
}

impl<const S: usize> Sub<Zero> for Big<S> {
    type Output = Self;

    #[inline]
    fn sub(self, _: Zero) -> Self::Output {
        self
    }
}

impl<const S: usize> Sub<&Zero> for Big<S> {
    type Output = Self;

    #[inline]
    fn sub(self, _: &Zero) -> Self::Output {
        self
    }
}

impl<const S: usize> SubAssign<Zero> for Big<S> {
    #[inline]
    fn sub_assign(&mut self, _: Zero) {
    }
}

impl<const S: usize> SubAssign<&Zero> for Big<S> {
    #[inline]
    fn sub_assign(&mut self, _: &Zero) {
    }
}

impl<const S: usize> Mul<Zero> for Big<S> {
    type Output = Self;

    #[inline]
    fn mul(mut self, _: Zero) -> Self::Output {
        MulAssign::mul_assign(&mut self, Zero);
        self
    }
}

impl<const S: usize> Mul<&Zero> for Big<S> {
    type Output = Self;

    #[inline]
    fn mul(mut self, _: &Zero) -> Self::Output {
        MulAssign::mul_assign(&mut self, Zero);
        self
    }
}

impl<const S: usize> Mul<Zero> for &Big<S> {
    type Output = Big<S>;

    #[inline]
    fn mul(self, _: Zero) -> Self::Output {
        num_traits::Zero::zero()
    }
}

impl<const S: usize> Mul<&Zero> for &Big<S> {
    type Output = Big<S>;

    #[inline]
    fn mul(self, _: &Zero) -> Self::Output {
        num_traits::Zero::zero()
    }
}

impl<const S: usize> MulAssign<Zero> for Big<S> {
    #[inline]
    fn mul_assign(&mut self, _: Zero) {
        MulAssign::mul_assign(self, &Zero);
    }
}

impl<const S: usize> MulAssign<&Zero> for Big<S> {
    #[inline]
    fn mul_assign(&mut self, _: &Zero) {
        num_traits::Zero::set_zero(self);
    }
}
