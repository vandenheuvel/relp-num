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
        use crate::rational::big::ops::{add_assign, subtracting_cmp};
        use crate::sign::Sign;

        use super::*;
        use std::cmp::Ordering;

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
                match self.sign {
                    Sign::Positive => add_assign(&mut self.numerator, &self.denominator),
                    Sign::Zero => {
                        self.sign = Sign::Positive;
                        debug_assert!(self.numerator.is_empty());
                        self.numerator.push(1);
                        debug_assert_eq!(self.denominator[0], 1);
                        debug_assert_eq!(self.denominator.len(), 1);
                    }
                    Sign::Negative => {
                        if self.numerator[0] == 1 && self.denominator[0] == 1 && self.numerator.len() == 1 && self.denominator.len() == 1 {
                            self.set_zero();
                        } else {
                            match subtracting_cmp(&mut self.numerator, &self.denominator) {
                                Ordering::Less => self.sign = !self.sign,
                                Ordering::Greater => {}
                                Ordering::Equal => panic!(),
                            }
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
                        if self.numerator[0] == 1 && self.denominator[0] == 1 && self.numerator.len() == 1 && self.denominator.len() == 1 {
                            self.set_zero();
                        } else {
                            match subtracting_cmp(&mut self.numerator, &self.denominator) {
                                Ordering::Less => self.sign = !self.sign,
                                Ordering::Greater => {}
                                Ordering::Equal => {}
                            }
                        }
                    }
                    Sign::Zero => {
                        self.sign = Sign::Negative;
                        debug_assert!(self.numerator.is_empty());
                        self.numerator.push(1);
                        debug_assert_eq!(self.denominator[0], 1);
                        debug_assert_eq!(self.denominator.len(), 1);
                    }
                    Sign::Negative => add_assign(&mut self.numerator, &self.denominator),
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

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::{Binary, One};
    use crate::rational::big::Big8;
    use crate::RB;

    #[test]
    fn test_one() {
        assert_eq!(RB!(0) + One, RB!(1));
        assert_eq!(RB!(0) - One, RB!(-1));
        assert_eq!(RB!(1) + One, RB!(2));
        assert_eq!(RB!(-1) + One, RB!(0));
        assert_eq!(RB!(-1) - One, RB!(-2));
        assert_eq!(RB!(1) - One, RB!(0));
        assert_eq!(RB!(1, 2) - One, RB!(-1, 2));
        assert_eq!(RB!(1, 2) + One, RB!(3, 2));
        assert_eq!(RB!(618, 648) / &One, RB!(618, 648));

        let x = Big8::from_str("68498984987984986896468746354684684684968/68468465468464168545346854646").unwrap();
        let expected = Big8::from_str("68498984988053455361937210523230031539614/68468465468464168545346854646").unwrap();
        assert_eq!(x + One, expected);

        let x = Big8::from_str("68468465468464168545346854645/68468465468464168545346854646").unwrap();
        let expected = Big8::from_str("-1/68468465468464168545346854646").unwrap();
        assert_eq!(x - One, expected);

        let x = Big8::from_str("-6868468468468465168186546846416565994998987468465468464168545346854644/6868468468468465168186546846416565994998987468465468464168545346854645").unwrap();
        let expected = Big8::from_str("1/6868468468468465168186546846416565994998987468465468464168545346854645").unwrap();
        assert_eq!(x + One, expected);
    }

    #[test]
    fn test_binary() {
        assert_eq!(RB!(135, 6848) * Binary::Zero, RB!(0));
        assert_eq!(RB!(135, 6848) * Binary::One, RB!(135, 6848));
        assert_eq!(RB!(135, 6848) + Binary::One, RB!(135 + 6848, 6848));
        assert_eq!(RB!(135, 6848) + Binary::Zero, RB!(135, 6848));
        assert_eq!(RB!(0) + Binary::Zero, RB!(0));
    }
}
