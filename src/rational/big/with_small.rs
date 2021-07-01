//! # Interactions with fixed size ratios
use std::ops::{Add, AddAssign, Div, Mul, Sub, SubAssign};

use crate::NonZeroUbig;
use crate::rational::{Rational16, Rational32, Rational64, Rational8};
use crate::rational::big::ops::building_blocks::{add_small, mul_small, SignChange, sub_small};
use crate::sign::Sign;
use crate::Ubig;

use super::Big;

macro_rules! define_interations {
    ($small:ident, $module_name:ident) => {
        mod $module_name {
            use super::*;

            mod creation {
                use super::*;

                impl<const S: usize> From<$small> for Big<S> {
                    #[must_use]
                    #[inline]
                    fn from(value: $small) -> Self {
                        Self {
                            sign: value.sign,
                            numerator: Ubig::new(value.numerator as usize),
                            denominator: unsafe {
                                // SAFETY: Input denominator is nonzero
                                NonZeroUbig::new_unchecked(value.denominator as usize)
                            },
                        }
                    }
                }

                impl<const S: usize> From<&$small> for Big<S> {
                    #[must_use]
                    #[inline]
                    fn from(value: &$small) -> Self {
                        Self {
                            sign: value.sign,
                            numerator: Ubig::new(value.numerator as usize),
                            denominator: unsafe {
                                // SAFETY: Input denominator is nonzero
                                NonZeroUbig::new_unchecked(value.denominator as usize)
                            },
                        }
                    }
                }
            }

            mod compare {
                use super::*;

                impl<const S: usize> PartialEq<$small> for Big<S> {
                    #[inline]
                    fn eq(&self, other: &$small) -> bool {
                        // Compare first with the denominator, we don't have to do a bounds check
                        // and the probability that its equal is small
                        *self.denominator.first() == other.denominator as usize &&
                            match self.sign {
                                Sign::Zero => other.sign == Sign::Zero,
                                Sign::Positive | Sign::Negative => {
                                    self.numerator[0] == other.numerator as usize &&
                                    self.numerator.len() == 1 &&
                                    self.denominator.len() == 1
                                }
                            }
                    }
                }
            }

            mod field {
                use crate::sign::Sign;
                use super::*;

                mod add {

                    use super::*;

                    impl<const S: usize> Add<$small> for Big<S> {
                        type Output = Self;

                        #[must_use]
                        #[inline]
                        fn add(mut self, rhs: $small) -> Self::Output {
                            AddAssign::add_assign(&mut self, &rhs);
                            self
                        }
                    }

                    impl<const S: usize> Add<&$small> for Big<S> {
                        type Output = Self;

                        #[must_use]
                        #[inline]
                        fn add(mut self, rhs: &$small) -> Self::Output {
                            AddAssign::add_assign(&mut self, rhs);
                            self
                        }
                    }

                    impl<const S: usize> Add<Option<&$small>> for Big<S> {
                        type Output = Self;

                        #[must_use]
                        #[inline]
                        fn add(self, rhs: Option<&$small>) -> Self::Output {
                            match rhs {
                                None => self,
                                Some(rhs) => Add::add(self, rhs),
                            }
                        }
                    }

                    impl<const S: usize> Add<&$small> for &Big<S> {
                        type Output = Big<S>;

                        #[must_use]
                        #[inline]
                        fn add(self, rhs: &$small) -> Self::Output {
                            // TODO(PERFORMANCE): Make sure that this is just as efficient as a native algorithm.
                            let mut cloned = self.clone();
                            AddAssign::add_assign(&mut cloned, rhs);
                            cloned
                        }
                    }

                    impl<const S: usize> Add<Option<&$small>> for &Big<S> {
                        type Output = Big<S>;

                        #[must_use]
                        #[inline]
                        fn add(self, rhs: Option<&$small>) -> Self::Output {
                            // TODO(PERFORMANCE): Make sure that this is just as efficient as a native algorithm.
                            let copy = self.clone();
                            match rhs {
                                None => copy,
                                Some(rhs) => Add::add(copy, rhs),
                            }
                        }
                    }

                    impl<const S: usize> AddAssign<$small> for Big<S> {
                        #[inline]
                        fn add_assign(&mut self, rhs: $small) {
                            AddAssign::add_assign(self, &rhs);
                        }
                    }

                    impl<const S: usize> AddAssign<&$small> for Big<S> {
                        #[inline]
                        fn add_assign(&mut self, rhs: &$small) {
                            match (self.sign, rhs.sign) {
                                (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => {
                                    unsafe {
                                        // SAFETY: The numbers are non zero
                                        add_small(
                                            self.numerator.inner_mut(),
                                            self.denominator.inner_mut(),
                                            rhs.numerator as usize,
                                            rhs.denominator as usize,
                                        );
                                    }
                                },
                                (Sign::Negative, Sign::Positive) | (Sign::Positive, Sign::Negative) => {
                                    unsafe {
                                        // SAFETY: The numbers are non zero
                                        let sign_change = sub_small(
                                            self.numerator.inner_mut(),
                                            self.denominator.inner_mut(),
                                            rhs.numerator as usize,
                                            rhs.denominator as usize,
                                        );
                                        match sign_change {
                                            SignChange::None => {}
                                            SignChange::Flip => self.sign = !self.sign,
                                            SignChange::Zero => self.sign = Sign::Zero,
                                        }
                                    }
                                }
                                (_, Sign::Zero) => {}
                                (Sign::Zero, _) => {
                                    self.sign = rhs.sign;
                                    debug_assert_eq!(self.numerator.len(), 0);
                                    unsafe {
                                        // SAFETY: Value was empty before and rhs.numerator is non zero
                                        self.numerator.inner_mut().push(rhs.numerator as usize);
                                    }
                                    debug_assert_eq!(self.denominator.len(), 1);
                                    debug_assert_eq!(self.denominator[0], 1);
                                    unsafe {
                                        // SAFETY: Value was one before and rhs.denominator is non zero
                                        *self.denominator.first_mut() = rhs.denominator as usize;
                                    }
                                }
                            }
                        }
                    }
                }

                mod sub {
                    use super::*;

                    impl<const S: usize> Sub<$small> for Big<S> {
                        type Output = Self;

                        #[must_use]
                        #[inline]
                        fn sub(mut self, rhs: $small) -> Self::Output {
                            SubAssign::sub_assign(&mut self, &rhs);
                            self
                        }
                    }

                    impl<const S: usize> Sub<&$small> for Big<S> {
                        type Output = Self;

                        #[must_use]
                        #[inline]
                        fn sub(mut self, rhs: &$small) -> Self::Output {
                            SubAssign::sub_assign(&mut self, rhs);
                            self
                        }
                    }

                    impl<const S: usize> Sub<Option<&$small>> for Big<S> {
                        type Output = Self;

                        #[must_use]
                        #[inline]
                        fn sub(self, rhs: Option<&$small>) -> Self::Output {
                            match rhs {
                                None => self,
                                Some(rhs) => Sub::sub(self, rhs),
                            }
                        }
                    }

                    impl<const S: usize> Sub<&$small> for &Big<S> {
                        type Output = Big<S>;

                        #[must_use]
                        #[inline]
                        fn sub(self, rhs: &$small) -> Self::Output {
                            // TODO(PERFORMANCE): Make sure that this is just as efficient as a native algorithm.
                            let mut cloned = self.clone();
                            SubAssign::sub_assign(&mut cloned, rhs);
                            cloned
                        }
                    }

                    impl<const S: usize> Sub<Option<&$small>> for &Big<S> {
                        type Output = Big<S>;

                        #[must_use]
                        #[inline]
                        fn sub(self, rhs: Option<&$small>) -> Self::Output {
                            // TODO(PERFORMANCE): Make sure that this is just as efficient as a native algorithm.
                            let copy = self.clone();
                            match rhs {
                                None => copy,
                                Some(rhs) => Sub::sub(copy, rhs),
                            }
                        }
                    }

                    impl<const S: usize> SubAssign<$small> for Big<S> {
                        #[inline]
                        fn sub_assign(&mut self, rhs: $small) {
                            SubAssign::sub_assign(self, &rhs);
                        }
                    }

                    impl<const S: usize> SubAssign<&$small> for Big<S> {
                        #[inline]
                        fn sub_assign(&mut self, rhs: &$small) {
                            match (self.sign, rhs.sign) {
                                (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => {
                                    unsafe {
                                        // SAFETY: The numbers are non zero
                                        let sign_change = sub_small(
                                            self.numerator.inner_mut(),
                                            self.denominator.inner_mut(),
                                            rhs.numerator as usize,
                                            rhs.denominator as usize,
                                        );
                                        match sign_change {
                                            SignChange::None => {}
                                            SignChange::Flip => self.sign = !self.sign,
                                            SignChange::Zero => self.sign = Sign::Zero,
                                        }
                                    }
                                }
                                (Sign::Negative, Sign::Positive) | (Sign::Positive, Sign::Negative) => {
                                    unsafe {
                                        // SAFETY: The numbers are non zero
                                        add_small(
                                            self.numerator.inner_mut(),
                                            self.denominator.inner_mut(),
                                            rhs.numerator as usize,
                                            rhs.denominator as usize,
                                        );
                                    }
                                }
                                (_, Sign::Zero) => {}
                                (Sign::Zero, _) => {
                                    self.sign = -rhs.sign;
                                    debug_assert_eq!(self.numerator.len(), 0);
                                    unsafe {
                                        // SAFETY: The rhs numerator is not zero
                                        self.numerator.inner_mut().push(rhs.numerator as usize)
                                    };
                                    debug_assert_eq!(self.denominator.len(), 1);
                                    debug_assert_eq!(self.denominator[0], 1);
                                    unsafe {
                                        // SAFETY: The rhs denominator is not zero
                                        *self.denominator.first_mut() = rhs.denominator as usize;
                                    }
                                }
                            }
                        }
                    }
                }

                mod mul {
                    use super::*;

                    impl<const S: usize> Mul<$small> for Big<S> {
                        type Output = Self;

                        #[must_use]
                        #[inline]
                        fn mul(self, rhs: $small) -> Self::Output {
                            Mul::mul(self, &rhs)
                        }
                    }

                    impl<const S: usize> Mul<&$small> for Big<S> {
                        type Output = Self;

                        #[must_use]
                        #[inline]
                        fn mul(mut self, rhs: &$small) -> Self::Output {
                            match (self.sign, rhs.sign) {
                                (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                                    self.sign *= rhs.sign;
                                    unsafe {
                                        mul_small(
                                            self.numerator.inner_mut(),
                                            self.denominator.inner_mut(),
                                            rhs.numerator as usize,
                                            rhs.denominator as usize,
                                        )
                                    }
                                }
                                (Sign::Positive | Sign::Negative, Sign::Zero) => {
                                    <Self as num_traits::Zero>::set_zero(&mut self);
                                }
                                (Sign::Zero, _) => {}
                            }

                            self
                        }
                    }

                    impl<const S: usize> Mul<&$small> for &Big<S> {
                        type Output = Big<S>;

                        #[must_use]
                        #[inline]
                        fn mul(self, rhs: &$small) -> Self::Output {
                            // TODO(PERFORMANCE): Make sure that this is just as efficient as a native algorithm.
                            self.clone() * rhs
                        }
                    }

                    impl<const S: usize> Mul<Option<&$small>> for Big<S> {
                        type Output = Big<S>;

                        #[must_use]
                        #[inline]
                        fn mul(mut self, rhs: Option<&$small>) -> Self::Output {
                            match rhs {
                                None => {
                                    <Self as num_traits::Zero>::set_zero(&mut self);
                                    self
                                },
                                Some(rhs) => Mul::mul(self, rhs),
                            }
                        }
                    }

                    impl<const S: usize> Mul<Option<&$small>> for &Big<S> {
                        type Output = Big<S>;

                        #[must_use]
                        #[inline]
                        fn mul(self, rhs: Option<&$small>) -> Self::Output {
                            match rhs {
                                None => <Self::Output as num_traits::Zero>::zero(),
                                Some(rhs) => Mul::mul(self, rhs),
                            }
                        }
                    }
                }

                mod div {
                    use super::*;

                    impl<const S: usize> Div<&$small> for Big<S> {
                        type Output = Big<S>;

                        #[must_use]
                        #[inline]
                        fn div(mut self, rhs: &$small) -> Self::Output {
                            debug_assert_ne!(rhs.sign, Sign::Zero);

                            match (self.sign, rhs.sign) {
                                (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                                    self.sign *= rhs.sign;
                                    unsafe {
                                        mul_small(
                                            self.numerator.inner_mut(),
                                            self.denominator.inner_mut(),
                                            rhs.denominator as usize,
                                            rhs.numerator as usize,
                                        );
                                    }
                                }
                                (Sign::Positive | Sign::Negative, Sign::Zero) => panic!(),
                                (Sign::Zero, _) => {}
                            }

                            self
                        }
                    }
                }
            }
        }
    }
}

define_interations!(Rational8, rational8);
define_interations!(Rational16, rational16);
define_interations!(Rational32, rational32);
define_interations!(Rational64, rational64);

#[cfg(test)]
mod test {
    use num_traits::One;
    use smallvec::smallvec;

    use crate::{R16, R32, R64, R8, RationalBig, RB, Sign, Ubig};
    use crate::integer::big::NonZeroUbig;

    #[test]
    fn test_eq() {
        assert_eq!(RB!(0), R64!(0));
        assert_eq!(RB!(-2), R64!(-2));
        assert_eq!(RB!(854984, 6868468468), R64!(854984, 6868468468));
        assert_eq!(RB!(-989888, 4968468421), R64!(-989888, 4968468421));
        assert_ne!(RB!(668468498646846546846546898997987_u128), R8!(1));
        assert_ne!(RB!(668468498646846546846546898997987.4385484_f64), R8!(1, 2));
    }

    #[test]
    fn test_add_sub() {
        assert_eq!(RB!(0) + R8!(0), RB!(0));
        assert_eq!(RB!(89) + R8!(1), RB!(90));
        assert_eq!(RB!(89) - R16!(1), RB!(88));

        assert_eq!(RB!(2, 3) + R16!(4, 9), RB!(10, 9));
        assert_eq!(RB!(989, 141) + R8!(1, 141), RB!(990, 141));
        assert_eq!(RB!(-84, 3) + R8!(1, 3), RB!(-83, 3));
        assert_eq!(RB!(1, 2) + R8!(1, 2), RB!(1));
        assert_eq!(RB!(-1, 2) + R8!(1, 2), RB!(0));
        assert_eq!(RB!(-1, 2) + R8!(1), RB!(1, 2));
        assert_eq!(RB!(7, 2) + R8!(5, 2), RB!(6));
        assert_eq!(RB!(-7, 2) + R8!(5, 2), RB!(-1));
        assert_eq!(RB!(-7, 2) - R8!(5, 2), RB!(-6));
        assert_eq!(
            RationalBig {
                sign: Sign::Positive,
                numerator: unsafe { Ubig::from_inner_unchecked(smallvec![1, 1]) },
                denominator: unsafe { NonZeroUbig::from_inner_unchecked(smallvec![2]) },
            } + R8!(1, 2),
            RationalBig {
                sign: Sign::Positive,
                numerator: unsafe { Ubig::from_inner_unchecked(smallvec![(1 << 63) + 1]) },
                denominator: NonZeroUbig::one(),
            },
        );

        assert_eq!(RB!(2, 3) + R8!(8, 1), RB!(8 * 3 + 2, 3));
        assert_eq!(RB!(8) + R8!(16, 3), RB!(8 * 3 + 16, 3));
        assert_eq!(RB!(3, 5) + R16!(2, 5), RB!(1));

        assert_eq!(RB!(5) - R32!(7), RB!(-2));
        assert_eq!(
            RationalBig {
                sign: Sign::Positive,
                numerator: unsafe { Ubig::from_inner_unchecked(smallvec![1, 1]) },
                denominator: unsafe { NonZeroUbig::from_inner_unchecked(smallvec![2]) },
            } - R8!(1, 2),
            RationalBig {
                sign: Sign::Positive,
                numerator: unsafe { Ubig::from_inner_unchecked(smallvec![1 << 63]) },
                denominator: NonZeroUbig::one(),
            },
        );
        assert_eq!(RB!(5, 2) - R8!(2), RB!(1, 2));
        assert_eq!(RB!(3) - R8!(1, 2), RB!(5, 2));
        assert_eq!(RB!(16, 3) - R8!(11, 4), RB!(16 * 4 - 11 * 3, 12));

        assert_eq!(RB!(0) + R8!(1, 2), RB!(1, 2));
        assert_eq!(RB!(0) - R8!(3, 4), RB!(-3, 4));
        assert_eq!(RB!(-10, 4) + R8!(-10, 8), RB!(-15, 4));
        assert_eq!(RB!(-10, 4) + R64!(1, 4), RB!(-9, 4));
        assert_eq!(RB!(-10, 8) + R64!(-10, 9), RB!(-5 * 17, 3 * 3 * 2 * 2));
        assert_eq!(RB!(-5, 4) + R64!(-5, 4), RB!(-5, 2));
        assert_eq!(RB!(-7, 6) + R64!(-7, 6), RB!(-7, 3));

        let limit = 10;
        for a in -limit..limit {
            for b in 1..limit {
                for c in -limit..limit {
                    for d in 1..limit {
                        assert_eq!(RB!(a, b as u64) + R64!(c, d as u64), RB!(a * d + c * b, b as u64 * d as u64), "{} / {} - {} / {}", a, b, c, d);
                    }
                }
            }
        }
    }

    #[test]
    fn test_mul_div() {
        assert_eq!(RB!(0) * R8!(18), RB!(0));
        assert_eq!(RB!(1) * R8!(6), RB!(6));
        assert_eq!(RB!(-1) * R64!(65488846), -RB!(65488846));
        assert_eq!(RB!(7, 11) * R8!(11, 7), RB!(1));
        assert_eq!(RB!(7, 11) * R16!(22, 7), RB!(2));
        assert_eq!(RB!(14, 33) * R32!(3, 2), RB!(7, 11));
        assert_eq!(RB!(4, 3) * R64!(0), RB!(0));

        let limit = 10;
        for a in -limit..limit {
            for b in 1..limit {
                for c in -limit..limit {
                    for d in 1..limit {
                        assert_eq!(RB!(a, b as u64) * R64!(c, d as u64), RB!(a * c, (b * d) as u64), "{} / {} * {} / {}", a, b, c, d);
                    }
                }
            }
        }
    }
}
