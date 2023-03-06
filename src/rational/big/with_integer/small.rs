use std::cmp::Ordering;
use std::num::{NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize};
use std::num::{NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

use num_traits::{One, Zero};
use smallvec::{smallvec, SmallVec};

use crate::{NonZeroSign, NonZeroSigned, Signed};
use crate::{NonZero, Sign};
use crate::integer::big::ops::building_blocks::is_well_formed_non_zero;
use crate::integer::big::ops::non_zero::{add_assign, is_one_non_zero, mul_assign_single_non_zero, subtracting_cmp};
use crate::integer::big::ops::normalize::simplify_fraction_gcd_single;
use crate::rational::big::{Big, NonZeroBig};

macro_rules! forwards {
    ($ty:ty, $large:ty) => {
        impl<const S: usize> Add<$ty> for $large {
            type Output = Self;

            #[must_use]
            #[inline]
            fn add(mut self, rhs: $ty) -> Self::Output {
                AddAssign::add_assign(&mut self, rhs);
                self
            }
        }

        impl<const S: usize> Add<&$ty> for $large {
            type Output = Self;

            #[must_use]
            #[inline]
            fn add(mut self, rhs: &$ty) -> Self::Output {
                AddAssign::add_assign(&mut self, rhs);
                self
            }
        }

        impl<const S: usize> Add<$ty> for &$large {
            type Output = $large;

            #[must_use]
            #[inline]
            fn add(self, rhs: $ty) -> Self::Output {
                Add::add(self.clone(), rhs)
            }
        }

        impl<const S: usize> Add<&$ty> for &$large {
            type Output = $large;

            #[must_use]
            #[inline]
            fn add(self, rhs: &$ty) -> Self::Output {
                Add::add(self, *rhs)
            }
        }

        impl<const S: usize> AddAssign<&$ty> for $large {
            #[inline]
            fn add_assign(&mut self, rhs: &$ty) {
                AddAssign::add_assign(self, *rhs);
            }
        }

        impl<const S: usize> Sub<$ty> for $large {
            type Output = Self;

            #[must_use]
            #[inline]
            fn sub(mut self, rhs: $ty) -> Self::Output {
                SubAssign::sub_assign(&mut self, rhs);
                self
            }
        }

        impl<const S: usize> Sub<&$ty> for $large {
            type Output = Self;

            #[must_use]
            #[inline]
            fn sub(mut self, rhs: &$ty) -> Self::Output {
                SubAssign::sub_assign(&mut self, rhs);
                self
            }
        }

        impl<const S: usize> Sub<$ty> for &$large {
            type Output = $large;

            #[must_use]
            #[inline]
            fn sub(self, rhs: $ty) -> Self::Output {
                Sub::sub(self.clone(), rhs)
            }
        }

        impl<const S: usize> Sub<&$ty> for &$large {
            type Output = $large;

            #[must_use]
            #[inline]
            fn sub(self, rhs: &$ty) -> Self::Output {
                Sub::sub(self, *rhs)
            }
        }

        impl<const S: usize> SubAssign<&$ty> for $large {
            #[inline]
            fn sub_assign(&mut self, rhs: &$ty) {
                SubAssign::sub_assign(self, *rhs);
            }
        }

        impl<const S: usize> Mul<$ty> for $large {
            type Output = Self;

            #[must_use]
            #[inline]
            fn mul(mut self, rhs: $ty) -> Self::Output {
                MulAssign::mul_assign(&mut self, rhs);
                self
            }
        }

        impl<const S: usize> Mul<&$ty> for $large {
            type Output = Self;

            #[must_use]
            #[inline]
            fn mul(mut self, rhs: &$ty) -> Self::Output {
                MulAssign::mul_assign(&mut self, rhs);
                self
            }
        }

        impl<const S: usize> Mul<$ty> for &$large {
            type Output = $large;

            #[must_use]
            #[inline]
            fn mul(self, rhs: $ty) -> Self::Output {
                Mul::mul(self.clone(), rhs)
            }
        }

        impl<const S: usize> Mul<&$ty> for &$large {
            type Output = $large;

            #[must_use]
            #[inline]
            fn mul(self, rhs: &$ty) -> Self::Output {
                Mul::mul(self, *rhs)
            }
        }

        impl<const S: usize> MulAssign<&$ty> for $large {
            #[inline]
            fn mul_assign(&mut self, rhs: &$ty) {
                MulAssign::mul_assign(self, *rhs);
            }
        }

        impl<const S: usize> Div<$ty> for $large {
            type Output = Self;

            #[must_use]
            #[inline]
            fn div(mut self, rhs: $ty) -> Self::Output {
                DivAssign::div_assign(&mut self, rhs);
                self
            }
        }

        impl<const S: usize> Div<&$ty> for $large {
            type Output = Self;

            #[must_use]
            #[inline]
            fn div(mut self, rhs: &$ty) -> Self::Output {
                DivAssign::div_assign(&mut self, rhs);
                self
            }
        }

        impl<const S: usize> Div<$ty> for &$large {
            type Output = $large;

            #[must_use]
            #[inline]
            fn div(self, rhs: $ty) -> Self::Output {
                Div::div(self.clone(), rhs)
            }
        }

        impl<const S: usize> Div<&$ty> for &$large {
            type Output = $large;

            #[must_use]
            #[inline]
            fn div(self, rhs: &$ty) -> Self::Output {
                Div::div(self, *rhs)
            }
        }

        impl<const S: usize> DivAssign<&$ty> for $large {
            #[inline]
            fn div_assign(&mut self, rhs: &$ty) {
                DivAssign::div_assign(self, *rhs);
            }
        }
    }
}

forwards!(u8, Big<S>);
forwards!(u16, Big<S>);
forwards!(u32, Big<S>);
forwards!(u64, Big<S>);
forwards!(usize, Big<S>);
forwards!(NonZeroU8, Big<S>);
forwards!(NonZeroU16, Big<S>);
forwards!(NonZeroU32, Big<S>);
forwards!(NonZeroU64, Big<S>);
forwards!(NonZeroUsize, Big<S>);
forwards!(i8, Big<S>);
forwards!(i16, Big<S>);
forwards!(i32, Big<S>);
forwards!(i64, Big<S>);
forwards!(isize, Big<S>);
forwards!(NonZeroI8, Big<S>);
forwards!(NonZeroI16, Big<S>);
forwards!(NonZeroI32, Big<S>);
forwards!(NonZeroI64, Big<S>);
forwards!(NonZeroIsize, Big<S>);

forwards!(u8, NonZeroBig<S>);
forwards!(u16, NonZeroBig<S>);
forwards!(u32, NonZeroBig<S>);
forwards!(u64, NonZeroBig<S>);
forwards!(usize, NonZeroBig<S>);
forwards!(NonZeroU8, NonZeroBig<S>);
forwards!(NonZeroU16, NonZeroBig<S>);
forwards!(NonZeroU32, NonZeroBig<S>);
forwards!(NonZeroU64, NonZeroBig<S>);
forwards!(NonZeroUsize, NonZeroBig<S>);
forwards!(i8, NonZeroBig<S>);
forwards!(i16, NonZeroBig<S>);
forwards!(i32, NonZeroBig<S>);
forwards!(i64, NonZeroBig<S>);
forwards!(isize, NonZeroBig<S>);
forwards!(NonZeroI8, NonZeroBig<S>);
forwards!(NonZeroI16, NonZeroBig<S>);
forwards!(NonZeroI32, NonZeroBig<S>);
forwards!(NonZeroI64, NonZeroBig<S>);
forwards!(NonZeroIsize, NonZeroBig<S>);

macro_rules! impls {
    ($ty:ty, $nzty:ty, $sty:ty, $nzsty:ty, $large:ty) => {
        impl<const S: usize> AddAssign<$ty> for $large {
            #[inline]
            fn add_assign(&mut self, rhs: $ty) {
                if rhs.is_not_zero() {
                    unsafe {
                        // SAFETY: rhs is non zero
                        self.add_assign_single_int_non_zero(rhs as usize);
                    }
                }
            }
        }

        impl<const S: usize> AddAssign<$nzty> for $large {
            #[inline]
            fn add_assign(&mut self, rhs: $nzty) {
                unsafe {
                    // SAFETY: rhs is non zero
                    self.add_assign_single_int_non_zero(rhs.get() as usize);
                }
            }
        }

        impl<const S: usize> AddAssign<$sty> for $large {
            #[inline]
            fn add_assign(&mut self, rhs: $sty) {
                match Signed::signum(&rhs) {
                    Sign::Positive => unsafe {
                        // SAFETY: rhs is non zero
                        self.add_assign_single_int_non_zero(rhs as usize);
                    }
                    Sign::Zero => {}
                    Sign::Negative => unsafe {
                        // SAFETY: rhs is non zero
                        self.sub_assign_single_int_non_zero(rhs.unsigned_abs() as usize);
                    }
                }
            }
        }

        impl<const S: usize> AddAssign<$nzsty> for $large {
            #[inline]
            fn add_assign(&mut self, rhs: $nzsty) {
                match NonZeroSigned::non_zero_signum(&rhs) {
                    NonZeroSign::Positive => unsafe {
                        // SAFETY: rhs is non zero
                        self.add_assign_single_int_non_zero(rhs.get() as usize);
                    }
                    NonZeroSign::Negative => unsafe {
                        // SAFETY: rhs is non zero
                        self.sub_assign_single_int_non_zero(rhs.get().unsigned_abs() as usize);
                    }
                }
            }
        }

        impl<const S: usize> SubAssign<$ty> for $large {
            #[inline]
            fn sub_assign(&mut self, rhs: $ty) {
                if rhs.is_not_zero() {
                    unsafe {
                        // SAFETY: rhs is non zero
                        self.sub_assign_single_int_non_zero(rhs as usize);
                    }
                }
            }
        }

        impl<const S: usize> SubAssign<$nzty> for $large {
            #[inline]
            fn sub_assign(&mut self, rhs: $nzty) {
                unsafe {
                    // SAFETY: rhs is non zero
                    self.sub_assign_single_int_non_zero(rhs.get() as usize);
                }
            }
        }

        impl<const S: usize> SubAssign<$sty> for $large {
            #[inline]
            fn sub_assign(&mut self, rhs: $sty) {
                match Signed::signum(&rhs) {
                    Sign::Positive => unsafe {
                        // SAFETY: rhs is non zero
                        self.sub_assign_single_int_non_zero(rhs as usize);
                    }
                    Sign::Zero => {}
                    Sign::Negative => unsafe {
                        // SAFETY: rhs is non zero
                        self.add_assign_single_int_non_zero(rhs.unsigned_abs() as usize);
                    }
                }
            }
        }

        impl<const S: usize> SubAssign<$nzsty> for $large {
            #[inline]
            fn sub_assign(&mut self, rhs: $nzsty) {
                match NonZeroSigned::non_zero_signum(&rhs) {
                    NonZeroSign::Positive => unsafe {
                        // SAFETY: rhs is non zero
                        self.sub_assign_single_int_non_zero(rhs.get() as usize);
                    }
                    NonZeroSign::Negative => unsafe {
                        // SAFETY: rhs is non zero
                        self.add_assign_single_int_non_zero(rhs.get().unsigned_abs() as usize);
                    }
                }
            }
        }

        impl<const S: usize> MulAssign<$nzty> for $large {
            #[inline]
            fn mul_assign(&mut self, rhs: $nzty) {
                if self.is_not_zero() {
                    unsafe {
                        // SAFETY: self and rhs are non zero
                        mul_assign_single_int_non_zero(
                            self.numerator.inner_mut(),
                            self.denominator.inner_mut(),
                            rhs.get() as usize,
                        );
                    }
                }
            }
        }

        impl<const S: usize> MulAssign<$nzsty> for $large {
            #[inline]
            fn mul_assign(&mut self, rhs: $nzsty) {
                if self.is_not_zero() {
                    unsafe {
                        // SAFETY: self and rhs are non zero
                        mul_assign_single_int_non_zero(
                            self.numerator.inner_mut(),
                            self.denominator.inner_mut(),
                            rhs.get().unsigned_abs() as usize,
                        );
                    }

                    if rhs.is_negative() {
                        self.sign.negate();
                    }
                }
            }
        }

        impl<const S: usize> DivAssign<$ty> for $large {
            #[inline]
            fn div_assign(&mut self, rhs: $ty) {
                if rhs.is_not_zero() {
                    if self.is_not_zero() {
                        unsafe {
                            // SAFETY: self and rhs are non zero
                            mul_assign_single_int_non_zero(
                                self.denominator.inner_mut(),
                                self.numerator.inner_mut(),
                                rhs as usize,
                            );
                        }
                    }
                } else {
                    panic!("attempt to divide by zero");
                }
            }
        }

        impl<const S: usize> DivAssign<$nzty> for $large {
            #[inline]
            fn div_assign(&mut self, rhs: $nzty) {
                if self.is_not_zero() {
                    unsafe {
                        // SAFETY: self and rhs are non zero
                        mul_assign_single_int_non_zero(
                            self.denominator.inner_mut(),
                            self.numerator.inner_mut(),
                            rhs.get() as usize,
                        );
                    }
                }
            }
        }

        impl<const S: usize> DivAssign<$sty> for $large {
            #[inline]
            fn div_assign(&mut self, rhs: $sty) {
                if rhs.is_not_zero() {
                    if self.is_not_zero() {
                        unsafe {
                            // SAFETY: self and rhs are non zero
                            mul_assign_single_int_non_zero(
                                self.denominator.inner_mut(),
                                self.numerator.inner_mut(),
                                rhs.unsigned_abs() as usize,
                            );
                        }

                        if rhs.is_negative() {
                            self.sign.negate();
                        }
                    }
                } else {
                    panic!("attempt to divide by zero");
                }
            }
        }

        impl<const S: usize> DivAssign<$nzsty> for $large {
            #[inline]
            fn div_assign(&mut self, rhs: $nzsty) {
                if self.is_not_zero() {
                    unsafe {
                        // SAFETY: self and rhs are non zero
                        mul_assign_single_int_non_zero(
                            self.denominator.inner_mut(),
                            self.numerator.inner_mut(),
                            rhs.get().unsigned_abs() as usize,
                        );
                    }

                    if rhs.is_negative() {
                        self.sign.negate();
                    }
                }
            }
        }
    }
}

impls!(u8, NonZeroU8, i8, NonZeroI8, Big<S>);
impls!(u16, NonZeroU16, i16, NonZeroI16, Big<S>);
impls!(u32, NonZeroU32, i32, NonZeroI32, Big<S>);
impls!(u64, NonZeroU64, i64, NonZeroI64, Big<S>);
impls!(usize, NonZeroUsize, isize, NonZeroIsize, Big<S>);

impls!(u8, NonZeroU8, i8, NonZeroI8, NonZeroBig<S>);
impls!(u16, NonZeroU16, i16, NonZeroI16, NonZeroBig<S>);
impls!(u32, NonZeroU32, i32, NonZeroI32, NonZeroBig<S>);
impls!(u64, NonZeroU64, i64, NonZeroI64, NonZeroBig<S>);
impls!(usize, NonZeroUsize, isize, NonZeroIsize, NonZeroBig<S>);

macro_rules! impls_set_zero {
    ($ty:ty, $sty:ty) => {
        impl<const S: usize> MulAssign<$ty> for Big<S> {
            #[inline]
            fn mul_assign(&mut self, rhs: $ty) {
                if self.is_not_zero() {
                    if rhs.is_not_zero() {
                        unsafe {
                            // SAFETY: self and rhs are non zero
                            mul_assign_single_int_non_zero(
                                self.numerator.inner_mut(),
                                self.denominator.inner_mut(),
                                rhs as usize,
                            );
                        }
                    } else {
                        self.set_zero();
                    }
                }
            }
        }

        impl<const S: usize> MulAssign<$sty> for Big<S> {
            #[inline]
            fn mul_assign(&mut self, rhs: $sty) {
                if self.is_not_zero() {
                    match Signed::signum(&rhs) {
                        Sign::Positive => unsafe {
                            // SAFETY: self and rhs are non zero
                            mul_assign_single_int_non_zero(
                                self.numerator.inner_mut(),
                                self.denominator.inner_mut(),
                                rhs as usize,
                            );
                        }
                        Sign::Zero => self.set_zero(),
                        Sign::Negative => {
                            unsafe {
                                // SAFETY: self and rhs are non zero
                                mul_assign_single_int_non_zero(
                                    self.numerator.inner_mut(),
                                    self.denominator.inner_mut(),
                                    rhs.unsigned_abs() as usize,
                                );
                            }
                            self.sign.negate();
                        }
                    }
                }
            }
        }
    }
}

impls_set_zero!(u8, i8);
impls_set_zero!(u16, i16);
impls_set_zero!(u32, i32);
impls_set_zero!(u64, i64);
impls_set_zero!(usize, isize);

macro_rules! impls_not_become_zero {
    ($ty:ty, $sty:ty) => {
        impl<const S: usize> MulAssign<$ty> for NonZeroBig<S> {
            #[inline]
            fn mul_assign(&mut self, rhs: $ty) {
                if self.is_not_zero() {
                    if rhs.is_not_zero() {
                        unsafe {
                            // SAFETY: self and rhs are non zero
                            mul_assign_single_int_non_zero(
                                self.numerator.inner_mut(),
                                self.denominator.inner_mut(),
                                rhs as usize,
                            );
                        }
                    } else {
                        panic!("attempt to multiply by zero");
                    }
                }
            }
        }

        impl<const S: usize> MulAssign<$sty> for NonZeroBig<S> {
            #[inline]
            fn mul_assign(&mut self, rhs: $sty) {
                if self.is_not_zero() {
                    match Signed::signum(&rhs) {
                        Sign::Positive => unsafe {
                            // SAFETY: self and rhs are non zero
                            mul_assign_single_int_non_zero(
                                self.numerator.inner_mut(),
                                self.denominator.inner_mut(),
                                rhs as usize,
                            );
                        }
                        Sign::Zero => panic!("attempt to multiply by zero"),
                        Sign::Negative => {
                            unsafe {
                                // SAFETY: self and rhs are non zero
                                mul_assign_single_int_non_zero(
                                    self.numerator.inner_mut(),
                                    self.denominator.inner_mut(),
                                    rhs.unsigned_abs() as usize,
                                );
                            }
                            self.sign.negate();
                        }
                    }
                }
            }
        }
    }
}

impls_not_become_zero!(u8, i8);
impls_not_become_zero!(u16, i16);
impls_not_become_zero!(u32, i32);
impls_not_become_zero!(u64, i64);
impls_not_become_zero!(usize, isize);

impl<const S: usize> Big<S> {
    unsafe fn add_assign_single_int_non_zero(&mut self, rhs: usize) {
        debug_assert!(rhs.is_not_zero());

        match self.sign {
            Sign::Positive => {
                let mut difference = self.denominator.inner().clone();
                mul_assign_single_non_zero(&mut difference, rhs);
                add_assign(self.numerator.inner_mut(), &difference)
            },
            Sign::Zero => {
                *self.numerator.inner_mut() = smallvec![rhs];
                debug_assert!(self.denominator.is_one());
            }
            Sign::Negative => {
                let mut difference = self.denominator.inner().clone();
                mul_assign_single_non_zero(&mut difference, rhs);
                let ordering = subtracting_cmp(self.numerator.inner_mut(), &difference);

                // ordering can't be equal
                if ordering == Ordering::Less {
                    self.sign.negate();
                }
            }
        }
    }

    #[inline]
    unsafe fn sub_assign_single_int_non_zero(&mut self, rhs: usize) {
        debug_assert!(rhs.is_not_zero());

        match self.sign {
            Sign::Positive => {
                let mut difference = self.denominator.inner().clone();
                mul_assign_single_non_zero(&mut difference, rhs);
                let ordering = subtracting_cmp(self.numerator.inner_mut(), &difference);

                // ordering can't be equal
                if ordering == Ordering::Less {
                    self.sign.negate();
                }
            }
            Sign::Zero => {
                *self.numerator.inner_mut() = smallvec![rhs];
                self.sign = Sign::Negative;
                debug_assert!(self.denominator.is_one());
            }
            Sign::Negative => {
                let mut difference = self.denominator.inner().clone();
                mul_assign_single_non_zero(&mut difference, rhs);
                add_assign(self.numerator.inner_mut(), &difference)
            },
        }
    }
}

impl<const S: usize> NonZeroBig<S> {
    unsafe fn add_assign_single_int_non_zero(&mut self, rhs: usize) {
        debug_assert!(rhs.is_not_zero());

        let mut difference = self.denominator.inner().clone();
        mul_assign_single_non_zero(&mut difference, rhs);

        match self.sign {
            NonZeroSign::Positive => {
                add_assign(self.numerator.inner_mut(), &difference)
            },
            NonZeroSign::Negative => {
                let ordering = subtracting_cmp(self.numerator.inner_mut(), &difference);

                match ordering {
                    Ordering::Less => self.sign.negate(),
                    Ordering::Equal => panic!("attempt to add resulting in zero"),
                    Ordering::Greater => {}
                }
            }
        }
    }

    #[inline]
    unsafe fn sub_assign_single_int_non_zero(&mut self, rhs: usize) {
        debug_assert!(rhs.is_not_zero());

        match self.sign {
            NonZeroSign::Positive => {
                let mut difference = self.denominator.inner().clone();
                mul_assign_single_non_zero(&mut difference, rhs);
                let ordering = subtracting_cmp(self.numerator.inner_mut(), &difference);

                match ordering {
                    Ordering::Less => self.sign.negate(),
                    Ordering::Equal => panic!("attempt to subtract resulting in zero"),
                    Ordering::Greater => {}
                }
            }
            NonZeroSign::Negative => {
                let mut difference = self.denominator.inner().clone();
                mul_assign_single_non_zero(&mut difference, rhs);
                add_assign(self.numerator.inner_mut(), &difference)
            },
        }
    }
}

#[inline]
unsafe fn mul_assign_single_int_non_zero<const S: usize>(
    numerator: &mut SmallVec<[usize; S]>,
    denominator: &mut SmallVec<[usize; S]>,
    mut rhs: usize,
) {
    debug_assert!(rhs.is_not_zero());
    debug_assert!(is_well_formed_non_zero(numerator));
    debug_assert!(is_well_formed_non_zero(denominator));

    if !rhs.is_one() {
        if !is_one_non_zero(denominator) {
            rhs = simplify_fraction_gcd_single(denominator, rhs);
        }
        mul_assign_single_non_zero(numerator, rhs);
    }
}

#[cfg(test)]
mod test {
    use num_traits::One;

    use crate::RB;
    use crate::rational::big::NonZeroBig;

    #[test]
    fn add() {
        assert_eq!(RB!(2, 3) + 2, RB!(8, 3));
        assert_eq!(RB!(5, 6) + 7, RB!(7 * 6 + 5, 6));
        assert_eq!(RB!(5, 6) - 7, RB!(-7 * 6 + 5, 6));
        assert_eq!(RB!(5, 6) + (-7) as i32, RB!(-7 * 6 + 5, 6));
        assert_eq!(RB!(-5, 6) + 7, RB!(7 * 6 - 5, 6));
        assert_eq!(RB!(-5, 6) + (-7), -RB!(7 * 6 + 5, 6));
        assert_eq!(RB!(-2, 3) + 2, RB!(4, 3));
        assert_eq!(RB!(2, 3) + 0, RB!(2, 3));
        assert_eq!(RB!(2, 3) - 2, RB!(-4, 3));
        assert_eq!(RB!(0) - 1, RB!(-1));
        assert_eq!(RB!(-2, 3) - 2, RB!(-8, 3));
    }

    #[test]
    fn mul() {
        assert_eq!(RB!(2, 3) * 2, RB!(4, 3));
        assert_eq!(RB!(-2, 3) * 2, RB!(-4, 3));
        assert_eq!(RB!(2, 3) * 0, RB!(0));
        assert_eq!(RB!(2, 3) / 2, RB!(1, 3));
        assert_eq!(RB!(-1) / 1, RB!(-1));
        assert_eq!(RB!(-2, 3) / 2, RB!(-1, 3));
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn mul_zero() {
        NonZeroBig::<1>::one() * 0_i64;
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn add_zero() {
        NonZeroBig::<1>::one() - 1;
    }
}
