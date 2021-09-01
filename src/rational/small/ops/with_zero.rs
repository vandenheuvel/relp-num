use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

use crate::{Rational128, Rational16, Rational32, Rational64, Rational8};
use crate::zero::Zero;

macro_rules! impls {
    ($name:ty) => {
        impl From<Zero> for $name {
            #[inline]
            #[must_use]
            fn from(_: Zero) -> Self {
                num_traits::Zero::zero()
            }
        }

        impl From<&Zero> for $name {
            #[inline]
            #[must_use]
            fn from(_: &Zero) -> Self {
                num_traits::Zero::zero()
            }
        }

        impl Add<Zero> for $name {
            type Output = Self;

            #[inline]
            #[must_use]
            fn add(mut self, _: Zero) -> Self::Output {
                AddAssign::add_assign(&mut self, Zero);
                self
            }
        }

        impl Add<&Zero> for $name {
            type Output = Self;

            #[inline]
            #[must_use]
            fn add(mut self, _: &Zero) -> Self::Output {
                AddAssign::add_assign(&mut self, &Zero);
                self
            }
        }

        impl AddAssign<&Zero> for $name {
            #[inline]
            fn add_assign(&mut self, _: &Zero) {
            }
        }

        impl AddAssign<Zero> for $name {
            #[inline]
            fn add_assign(&mut self, _: Zero) {
            }
        }

        impl Sub<Zero> for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn sub(mut self, _: Zero) -> Self::Output {
                SubAssign::sub_assign(&mut self, Zero);
                self
            }
        }

        impl Sub<&Zero> for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn sub(mut self, _: &Zero) -> Self::Output {
                SubAssign::sub_assign(&mut self, Zero);
                self
            }
        }

        impl SubAssign<Zero> for $name {
            #[inline]
            fn sub_assign(&mut self, _: Zero) {
            }
        }

        impl Mul<Zero> for $name {
            type Output = Self;

            #[inline]
            #[must_use]
            fn mul(mut self, _: Zero) -> Self::Output {
                MulAssign::mul_assign(&mut self, Zero);
                self
            }
        }

        impl Mul<&Zero> for $name {
            type Output = Self;

            #[inline]
            #[must_use]
            fn mul(mut self, _: &Zero) -> Self::Output {
                MulAssign::mul_assign(&mut self, Zero);
                self
            }
        }

        impl Mul<&Zero> for &$name {
            type Output = $name;

            #[inline]
            #[must_use]
            fn mul(self, _: &Zero) -> Self::Output {
                num_traits::Zero::zero()
            }
        }

        impl Mul<Zero> for &$name {
            type Output = $name;

            #[inline]
            #[must_use]
            fn mul(self, _: Zero) -> Self::Output {
                num_traits::Zero::zero()
            }
        }

        impl MulAssign<Zero> for $name {
            #[inline]
            fn mul_assign(&mut self, _: Zero) {
                MulAssign::mul_assign(self, &Zero)
            }
        }

        impl MulAssign<&Zero> for $name {
            #[inline]
            fn mul_assign(&mut self, _: &Zero) {
                num_traits::Zero::set_zero(self);
            }
        }
    }
}

impls!(Rational8);
impls!(Rational16);
impls!(Rational32);
impls!(Rational64);
impls!(Rational128);
