use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

use crate::binary::Binary;
use crate::one::One;
use crate::rational::big::Big;

impl<const S: usize> From<Binary> for Big<S> {
    #[must_use]
    #[inline]
    fn from(from: Binary) -> Self {
        <Self as From<&Binary>>::from(&from)
    }
}

impl<const S: usize> From<&Binary> for Big<S> {
    #[must_use]
    #[inline]
    fn from(from: &Binary) -> Self {
        match from {
            Binary::Zero => <Self as num_traits::Zero>::zero(),
            Binary::One => <Self as num_traits::One>::one(),
        }
    }
}

impl<const S: usize> Add<Binary> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn add(mut self, rhs: Binary) -> Self::Output {
        AddAssign::add_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Add<&Binary> for Big<S> {
    type Output = Big<S>;

    #[must_use]
    #[inline]
    fn add(mut self, rhs: &Binary) -> Self::Output {
        AddAssign::add_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> AddAssign<Binary> for Big<S> {
    #[inline]
    fn add_assign(&mut self, rhs: Binary) {
        AddAssign::add_assign(self, &rhs);
    }
}

impl<const S: usize> AddAssign<&Binary> for Big<S> {
    #[inline]
    fn add_assign(&mut self, rhs: &Binary) {
        match rhs {
            Binary::Zero => {}
            Binary::One => *self += One,
        }
    }
}

impl<const S: usize> Sub<Binary> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn sub(mut self, rhs: Binary) -> Self::Output {
        SubAssign::sub_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Sub<&Binary> for Big<S> {
    type Output = Big<S>;

    #[must_use]
    #[inline]
    fn sub(mut self, rhs: &Binary) -> Self::Output {
        SubAssign::sub_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> SubAssign<Binary> for Big<S> {
    #[inline]
    fn sub_assign(&mut self, rhs: Binary) {
        SubAssign::sub_assign(self, &rhs);
    }
}

impl<const S: usize> SubAssign<&Binary> for Big<S> {
    #[inline]
    fn sub_assign(&mut self, rhs: &Binary) {
        match rhs {
            Binary::Zero => {}
            Binary::One => *self -= One,
        }
    }
}

impl<const S: usize> Mul<Binary> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn mul(mut self, rhs: Binary) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Mul<&Binary> for Big<S> {
    type Output = Big<S>;

    #[must_use]
    #[inline]
    fn mul(mut self, rhs: &Binary) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Mul<Binary> for &Big<S> {
    type Output = Big<S>;

    #[must_use]
    #[inline]
    fn mul(self, rhs: Binary) -> Self::Output {
        Mul::mul(self, &rhs)
    }
}

impl<const S: usize> Mul<&Binary> for &Big<S> {
    type Output = Big<S>;

    #[must_use]
    #[inline]
    fn mul(self, rhs: &Binary) -> Self::Output {
        match rhs {
            Binary::Zero => num_traits::Zero::zero(),
            Binary::One => self.clone(),
        }
    }
}

impl<const S: usize> MulAssign<Binary> for Big<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: Binary) {
        MulAssign::mul_assign(self, &rhs);
    }
}

impl<const S: usize> MulAssign<&Binary> for Big<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: &Binary) {
        match rhs {
            Binary::Zero => num_traits::Zero::set_zero(self),
            Binary::One => {},
        }
    }
}
