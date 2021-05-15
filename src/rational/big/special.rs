//! # Non-standard impl<const S: usize>ementations
//!
//! Operations with specific types from this crate.
mod creation {
    use crate::one::One;
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
}

mod field {
    use num_traits;

    mod add {
        use std::ops::{Add, AddAssign, Sub, SubAssign};

        use num_traits::Zero;

        use crate::binary::Binary;
        use crate::one::One;
        use crate::rational::big::Big;
        use crate::rational::big::ops::{add_assign, subtracting_cmp_ne, UnequalOrdering};
        use crate::sign::Sign;

        use super::*;

        impl<const S: usize> Add<Binary> for Big<S> {
            type Output = Self;

            #[inline]
            fn add(self, rhs: Binary) -> Self::Output {
                match rhs {
                    Binary::Zero => self,
                    Binary::One => self.add(One),
                }
            }
        }

        impl<const S: usize> Add<Option<&Big<S>>> for Big<S> {
            type Output = Self;

            #[inline]
            fn add(self, rhs: Option<&Big<S>>) -> Self::Output {
                // TODO(PERFORMANCE): Make sure that this is just as efficient as a native algorithm.
                match rhs {
                    None => self,
                    Some(rhs) => Add::add(self, rhs),
                }
            }
        }

        impl<const S: usize> Add<Option<&Big<S>>> for &Big<S> {
            type Output = Big<S>;

            #[inline]
            fn add(self, rhs: Option<&Big<S>>) -> Self::Output {
                // TODO(PERFORMANCE): Make sure that this is just as efficient as a native algorithm.
                let copy = self.clone();
                match rhs {
                    None => copy,
                    Some(rhs) => Add::add(copy, rhs),
                }
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
                if self.sign == Sign::Negative && self.numerator.len() == 1 && self.numerator[0] == 1 {
                    self.set_zero();
                } else {
                    add_assign(&mut self.numerator, &self.denominator);
                    // No need to normalize; can't be zero and numerator and denominator are
                    // already coprime
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
                if self.sign == Sign::Positive && self.numerator.len() == 1 && self.numerator[0] == 1 {
                    self.set_zero();
                } else {
                    match subtracting_cmp_ne(&mut self.numerator, &self.denominator) {
                        UnequalOrdering::Less => self.sign = !self.sign,
                        UnequalOrdering::Greater => {}
                    }
                    // No need to normalize; can't be zero and numerator and denominator are
                    // already coprime
                }
            }
        }
    }

    mod mul {
        use std::ops::Mul;

        use crate::binary::Binary;
        use crate::one::One;
        use crate::rational::big::Big;

        use super::*;

        impl<const S: usize> Mul<Binary> for Big<S> {
            type Output = Self;

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

            #[inline]
            fn mul(self, rhs: Binary) -> Self::Output {
                match rhs {
                    Binary::Zero => <Self::Output as num_traits::Zero>::zero(),
                    Binary::One => self.clone(),
                }
            }
        }

        impl<const S: usize> Mul<Option<&Big<S>>> for Big<S> {
            type Output = Self;

            #[inline]
            fn mul(self, rhs: Option<&Big<S>>) -> Self::Output {
                match rhs {
                    None => <Self as num_traits::Zero>::zero(),
                    Some(rhs) => Mul::mul(self, rhs),
                }
            }
        }

        impl<const S: usize> Mul<Option<&Big<S>>> for &Big<S> {
            type Output = Big<S>;

            #[inline]
            fn mul(self, rhs: Option<&Big<S>>) -> Self::Output {
                match rhs {
                    None => <Big<S> as num_traits::Zero>::zero(),
                    Some(rhs) => Mul::mul(self, rhs)
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
    }

    mod div {
        use std::ops::Div;

        use crate::one::One;
        use crate::rational::big::Big;

        impl<const S: usize> Div<&One> for Big<S> {
            type Output = Self;

            #[inline]
            fn div(self, _: &One) -> Self::Output {
                self
            }
        }
    }
}
