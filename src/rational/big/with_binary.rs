use std::ops::{Add, AddAssign, Mul};

use num_traits;

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
    fn add(self, rhs: Binary) -> Self::Output {
        match rhs {
            Binary::Zero => self,
            Binary::One => self.add(One),
        }
    }
}

impl<const S: usize> Add<&Binary> for Big<S> {
    type Output = Big<S>;

    #[must_use]
    #[inline]
    fn add(self, rhs: &Binary) -> Self::Output {
        match rhs {
            Binary::Zero => self,
            Binary::One => self + One,
        }
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

impl<const S: usize> Mul<&Binary> for Big<S> {
    type Output = Big<S>;

    #[must_use]
    #[inline]
    fn mul(mut self, rhs: &Binary) -> Self::Output {
        match rhs {
            Binary::Zero => {
                num_traits::Zero::set_zero(&mut self);
                self
            },
            Binary::One => self,
        }
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

impl<const S: usize> Mul<Binary> for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn mul(self, rhs: Binary) -> Self::Output {
        match rhs {
            Binary::Zero => <Self::Output as num_traits::Zero>::zero(),
            Binary::One => self,
        }
    }
}

impl<const S: usize> Mul<Binary> for &Big<S> {
    type Output = Big<S>;

    #[must_use]
    #[inline]
    fn mul(self, rhs: Binary) -> Self::Output {
        match rhs {
            Binary::Zero => <Self::Output as num_traits::Zero>::zero(),
            Binary::One => self.clone(),
        }
    }
}
