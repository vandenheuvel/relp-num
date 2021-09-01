use std::cmp::Ordering;
use std::num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize};
use std::num::{NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

use num_traits::{One, Zero};

use crate::{Rational128, Rational16, Rational32, Rational64, Rational8, RationalUsize};
use crate::non_zero::NonZero;
use crate::NonZeroSign;
use crate::NonZeroSigned;
use crate::rational::small::ops::building_blocks::{gcd128, gcd16, gcd32, gcd64, gcd8, gcd_usize};
use crate::Sign;
use crate::sign::Negateable;
use crate::Signed;

macro_rules! forwards {
    ($ty:ty, $large:ty) => {
        impl Add<$ty> for $large {
            type Output = Self;

            #[must_use]
            #[inline]
            fn add(mut self, rhs: $ty) -> Self::Output {
                AddAssign::add_assign(&mut self, rhs);
                self
            }
        }

        impl Add<&$ty> for $large {
            type Output = Self;

            #[must_use]
            #[inline]
            fn add(mut self, rhs: &$ty) -> Self::Output {
                AddAssign::add_assign(&mut self, rhs);
                self
            }
        }

        impl Add<$ty> for &$large {
            type Output = $large;

            #[must_use]
            #[inline]
            fn add(self, rhs: $ty) -> Self::Output {
                Add::add(self.clone(), rhs)
            }
        }

        impl Add<&$ty> for &$large {
            type Output = $large;

            #[must_use]
            #[inline]
            fn add(self, rhs: &$ty) -> Self::Output {
                Add::add(self, *rhs)
            }
        }

        impl AddAssign<&$ty> for $large {
            #[inline]
            fn add_assign(&mut self, rhs: &$ty) {
                AddAssign::add_assign(self, *rhs);
            }
        }

        impl Sub<$ty> for $large {
            type Output = Self;

            #[must_use]
            #[inline]
            fn sub(mut self, rhs: $ty) -> Self::Output {
                SubAssign::sub_assign(&mut self, rhs);
                self
            }
        }

        impl Sub<&$ty> for $large {
            type Output = Self;

            #[must_use]
            #[inline]
            fn sub(mut self, rhs: &$ty) -> Self::Output {
                SubAssign::sub_assign(&mut self, rhs);
                self
            }
        }

        impl Sub<$ty> for &$large {
            type Output = $large;

            #[must_use]
            #[inline]
            fn sub(self, rhs: $ty) -> Self::Output {
                Sub::sub(self.clone(), rhs)
            }
        }

        impl Sub<&$ty> for &$large {
            type Output = $large;

            #[must_use]
            #[inline]
            fn sub(self, rhs: &$ty) -> Self::Output {
                Sub::sub(self, *rhs)
            }
        }

        impl SubAssign<&$ty> for $large {
            #[inline]
            fn sub_assign(&mut self, rhs: &$ty) {
                SubAssign::sub_assign(self, *rhs);
            }
        }

        impl Mul<$ty> for $large {
            type Output = Self;

            #[must_use]
            #[inline]
            fn mul(mut self, rhs: $ty) -> Self::Output {
                MulAssign::mul_assign(&mut self, rhs);
                self
            }
        }

        impl Mul<&$ty> for $large {
            type Output = Self;

            #[must_use]
            #[inline]
            fn mul(mut self, rhs: &$ty) -> Self::Output {
                MulAssign::mul_assign(&mut self, rhs);
                self
            }
        }

        impl Mul<$ty> for &$large {
            type Output = $large;

            #[must_use]
            #[inline]
            fn mul(self, rhs: $ty) -> Self::Output {
                Mul::mul(self.clone(), rhs)
            }
        }

        impl Mul<&$ty> for &$large {
            type Output = $large;

            #[must_use]
            #[inline]
            fn mul(self, rhs: &$ty) -> Self::Output {
                Mul::mul(self, *rhs)
            }
        }

        impl MulAssign<&$ty> for $large {
            #[inline]
            fn mul_assign(&mut self, rhs: &$ty) {
                MulAssign::mul_assign(self, *rhs);
            }
        }

        impl Div<$ty> for $large {
            type Output = Self;

            #[must_use]
            #[inline]
            fn div(mut self, rhs: $ty) -> Self::Output {
                DivAssign::div_assign(&mut self, rhs);
                self
            }
        }

        impl Div<&$ty> for $large {
            type Output = Self;

            #[must_use]
            #[inline]
            fn div(mut self, rhs: &$ty) -> Self::Output {
                DivAssign::div_assign(&mut self, rhs);
                self
            }
        }

        impl Div<$ty> for &$large {
            type Output = $large;

            #[must_use]
            #[inline]
            fn div(self, rhs: $ty) -> Self::Output {
                Div::div(self.clone(), rhs)
            }
        }

        impl Div<&$ty> for &$large {
            type Output = $large;

            #[must_use]
            #[inline]
            fn div(self, rhs: &$ty) -> Self::Output {
                Div::div(self, *rhs)
            }
        }

        impl DivAssign<&$ty> for $large {
            #[inline]
            fn div_assign(&mut self, rhs: &$ty) {
                DivAssign::div_assign(self, *rhs);
            }
        }
    }
}

forwards!(u8, Rational8);
forwards!(NonZeroU8, Rational8);
forwards!(i8, Rational8);
forwards!(NonZeroI8, Rational8);

forwards!(u8, Rational16);
forwards!(u16, Rational16);
forwards!(NonZeroU8, Rational16);
forwards!(NonZeroU16, Rational16);
forwards!(i8, Rational16);
forwards!(i16, Rational16);
forwards!(NonZeroI8, Rational16);
forwards!(NonZeroI16, Rational16);

forwards!(u8, Rational32);
forwards!(u16, Rational32);
forwards!(u32, Rational32);
forwards!(NonZeroU8, Rational32);
forwards!(NonZeroU16, Rational32);
forwards!(NonZeroU32, Rational32);
forwards!(i8, Rational32);
forwards!(i16, Rational32);
forwards!(i32, Rational32);
forwards!(NonZeroI8, Rational32);
forwards!(NonZeroI16, Rational32);
forwards!(NonZeroI32, Rational32);

forwards!(u8, Rational64);
forwards!(u16, Rational64);
forwards!(u32, Rational64);
forwards!(u64, Rational64);
forwards!(usize, Rational64);
forwards!(NonZeroU8, Rational64);
forwards!(NonZeroU16, Rational64);
forwards!(NonZeroU32, Rational64);
forwards!(NonZeroU64, Rational64);
forwards!(NonZeroUsize, Rational64);
forwards!(i8, Rational64);
forwards!(i16, Rational64);
forwards!(i32, Rational64);
forwards!(i64, Rational64);
forwards!(isize, Rational64);
forwards!(NonZeroI8, Rational64);
forwards!(NonZeroI16, Rational64);
forwards!(NonZeroI32, Rational64);
forwards!(NonZeroI64, Rational64);
forwards!(NonZeroIsize, Rational64);

forwards!(u8, Rational128);
forwards!(u16, Rational128);
forwards!(u32, Rational128);
forwards!(u64, Rational128);
forwards!(u128, Rational128);
forwards!(usize, Rational128);
forwards!(NonZeroU8, Rational128);
forwards!(NonZeroU16, Rational128);
forwards!(NonZeroU32, Rational128);
forwards!(NonZeroU64, Rational128);
forwards!(NonZeroU128, Rational128);
forwards!(NonZeroUsize, Rational128);
forwards!(i8, Rational128);
forwards!(i16, Rational128);
forwards!(i32, Rational128);
forwards!(i64, Rational128);
forwards!(i128, Rational128);
forwards!(isize, Rational128);
forwards!(NonZeroI8, Rational128);
forwards!(NonZeroI16, Rational128);
forwards!(NonZeroI32, Rational128);
forwards!(NonZeroI64, Rational128);
forwards!(NonZeroI128, Rational128);
forwards!(NonZeroIsize, Rational128);

macro_rules! impls {
    ($name:ident, $large: ty, $ty:ty, $nzty:ty, $sty:ty, $nzsty:ty, $mul_name:ident, $gcd_name:ident) => {
        impl AddAssign<$ty> for $name {
            #[inline]
            fn add_assign(&mut self, rhs: $ty) {
                self.add_assign(rhs as $large);
            }
        }

        impl AddAssign<$nzty> for $name {
            #[inline]
            fn add_assign(&mut self, rhs: $nzty) {
                self.add_assign(rhs.get() as $large);
            }
        }

        impl AddAssign<$sty> for $name {
            #[inline]
            fn add_assign(&mut self, rhs: $sty) {
                let unsigned = rhs.unsigned_abs() as $large;
                match Signed::signum(&rhs) {
                    Sign::Positive => self.add_assign(unsigned),
                    Sign::Zero => (),
                    Sign::Negative => self.sub_assign(unsigned),
                }
            }
        }

        impl AddAssign<$nzsty> for $name {
            #[inline]
            fn add_assign(&mut self, rhs: $nzsty) {
                let unsigned = rhs.get().unsigned_abs() as $large;
                match NonZeroSigned::non_zero_signum(&rhs) {
                    NonZeroSign::Positive => self.add_assign(unsigned),
                    NonZeroSign::Negative => self.sub_assign(unsigned),
                }
            }
        }

        impl SubAssign<$ty> for $name {
            #[inline]
            fn sub_assign(&mut self, rhs: $ty) {
                self.sub_assign(rhs as $large);
            }
        }

        impl SubAssign<$nzty> for $name {
            #[inline]
            fn sub_assign(&mut self, rhs: $nzty) {
                self.sub_assign(rhs.get() as $large);
            }
        }

        impl SubAssign<$sty> for $name {
            #[inline]
            fn sub_assign(&mut self, rhs: $sty) {
                let unsigned = rhs.unsigned_abs() as $large;
                match Signed::signum(&rhs) {
                    Sign::Positive => self.sub_assign(unsigned),
                    Sign::Zero => (),
                    Sign::Negative => self.add_assign(unsigned),
                }
            }
        }

        impl SubAssign<$nzsty> for $name {
            #[inline]
            fn sub_assign(&mut self, rhs: $nzsty) {
                let unsigned = rhs.get().unsigned_abs() as $large;
                match NonZeroSigned::non_zero_signum(&rhs) {
                    NonZeroSign::Positive => self.sub_assign(unsigned),
                    NonZeroSign::Negative => self.add_assign(unsigned),
                }
            }
        }

        impl MulAssign<$ty> for $name {
            #[inline]
            fn mul_assign(&mut self, rhs: $ty) {
                if rhs.is_not_zero() {
                    $mul_name(&mut self.numerator, &mut self.denominator, rhs as $large);
                } else {
                    self.set_zero();
                }
            }
        }

        impl MulAssign<$nzty> for $name {
            #[inline]
            fn mul_assign(&mut self, rhs: $nzty) {
                $mul_name(&mut self.numerator, &mut self.denominator, rhs.get() as $large);
            }
        }

        impl MulAssign<$sty> for $name {
            #[inline]
            fn mul_assign(&mut self, rhs: $sty) {
                if rhs.is_not_zero() {
                    $mul_name(&mut self.numerator, &mut self.denominator, rhs.unsigned_abs() as $large);

                    if rhs.is_negative() {
                        self.negate();
                    }
                } else {
                    self.set_zero();
                }
            }
        }

        impl MulAssign<$nzsty> for $name {
            #[inline]
            fn mul_assign(&mut self, rhs: $nzsty) {
                $mul_name(&mut self.numerator, &mut self.denominator, rhs.get().unsigned_abs() as $large);

                if rhs.is_negative() {
                    self.negate();
                }
            }
        }

        impl DivAssign<$ty> for $name {
            #[inline]
            fn div_assign(&mut self, rhs: $ty) {
                if rhs.is_not_zero() {
                    match self.sign {
                        Sign::Positive | Sign::Negative => {
                            $mul_name(&mut self.denominator, &mut self.numerator, rhs as $large);
                        }
                        Sign::Zero => {}
                    }
                } else {
                    panic!("attempt to divide by zero");
                }
            }
        }

        impl DivAssign<$nzty> for $name {
            #[inline]
            fn div_assign(&mut self, rhs: $nzty) {
                match self.sign {
                    Sign::Positive | Sign::Negative => {
                        $mul_name(&mut self.denominator, &mut self.numerator, rhs.get() as $large);
                    }
                    Sign::Zero => {}
                }
            }
        }

        impl DivAssign<$sty> for $name {
            #[inline]
            fn div_assign(&mut self, rhs: $sty) {
                if rhs.is_not_zero() {
                    match self.sign {
                        Sign::Positive | Sign::Negative => {
                            $mul_name(&mut self.denominator, &mut self.numerator, rhs.unsigned_abs() as $large);
                        }
                        Sign::Zero => {}
                    }

                    if rhs.is_negative() {
                        self.negate();
                    }
                } else {
                    panic!("attempt to divide by zero");
                }
            }
        }

        impl DivAssign<$nzsty> for $name {
            #[inline]
            fn div_assign(&mut self, rhs: $nzsty) {
                match self.sign {
                    Sign::Positive | Sign::Negative => {
                        $mul_name(&mut self.denominator, &mut self.numerator, rhs.get().unsigned_abs() as $large);
                    }
                    Sign::Zero => {}
                }

                if rhs.is_negative() {
                    self.negate();
                }
            }
        }
    }
}

impls!(Rational8, u8, u8, NonZeroU8, i8, NonZeroI8, mul8, gcd8);

impls!(Rational16, u16, u8, NonZeroU8, i8, NonZeroI8, mul16, gcd16);
impls!(Rational16, u16, u16, NonZeroU16, i16, NonZeroI16, mul16, gcd16);

impls!(Rational32, u32, u8, NonZeroU8, i8, NonZeroI8, mul32, gcd32);
impls!(Rational32, u32, u16, NonZeroU16, i16, NonZeroI16, mul32, gcd32);
impls!(Rational32, u32, u32, NonZeroU32, i32, NonZeroI32, mul32, gcd32);

impls!(Rational64, u64, u8, NonZeroU8, i8, NonZeroI8, mul64, gcd64);
impls!(Rational64, u64, u16, NonZeroU16, i16, NonZeroI16, mul64, gcd64);
impls!(Rational64, u64, u32, NonZeroU32, i32, NonZeroI32, mul64, gcd64);
impls!(Rational64, u64, u64, NonZeroU64, i64, NonZeroI64, mul64, gcd64);
impls!(Rational64, u64, usize, NonZeroUsize, isize, NonZeroIsize, mul64, gcd64);

impls!(Rational128, u128, u8, NonZeroU8, i8, NonZeroI8, mul128, gcd128);
impls!(Rational128, u128, u16, NonZeroU16, i16, NonZeroI16, mul128, gcd128);
impls!(Rational128, u128, u32, NonZeroU32, i32, NonZeroI32, mul128, gcd128);
impls!(Rational128, u128, u64, NonZeroU64, i64, NonZeroI64, mul128, gcd128);
impls!(Rational128, u128, usize, NonZeroUsize, isize, NonZeroIsize, mul128, gcd128);
impls!(Rational128, u128, u128, NonZeroU128, i128, NonZeroI128, mul128, gcd128);

impls!(RationalUsize, usize, u8, NonZeroU8, i8, NonZeroI8, mul_usize, gcd_usize);
impls!(RationalUsize, usize, u16, NonZeroU16, i16, NonZeroI16, mul_usize, gcd_usize);
impls!(RationalUsize, usize, u32, NonZeroU32, i32, NonZeroI32, mul_usize, gcd_usize);
impls!(RationalUsize, usize, u64, NonZeroU64, i64, NonZeroI64, mul_usize, gcd_usize);
impls!(RationalUsize, usize, usize, NonZeroUsize, isize, NonZeroIsize, mul_usize, gcd_usize);

macro_rules! shared {
    ($ty:ty, $large:ty, $mul_name:ident, $gcd_name:ident) => {
        impl $ty {
            #[inline]
            fn add_assign(&mut self, rhs: $large) {
                match self.signum() {
                    Sign::Positive => self.numerator += rhs * self.denominator,
                    Sign::Zero => {
                        self.numerator = rhs as $large;
                        debug_assert!(self.denominator.is_one());
                    }
                    Sign::Negative => {
                        let difference = rhs * self.denominator;
                        match self.numerator.cmp(&difference) {
                            Ordering::Less => {
                                self.numerator = difference - self.numerator;
                                self.sign = Sign::Positive;
                            }
                            Ordering::Equal => self.set_zero(),
                            Ordering::Greater => self.numerator -= difference,
                        }
                    }
                }
            }
            #[inline]
            fn sub_assign(&mut self, rhs: $large) {
                match self.signum() {
                    Sign::Positive => {
                        let difference = rhs * self.denominator;
                        match self.numerator.cmp(&difference) {
                            Ordering::Less => {
                                self.numerator = difference - self.numerator;
                                self.sign = Sign::Negative;
                            }
                            Ordering::Equal => self.set_zero(),
                            Ordering::Greater => self.numerator -= difference,
                        }
                    },
                    Sign::Zero => {
                        self.numerator = rhs as $large;
                        debug_assert!(self.denominator.is_one());
                        self.sign = Sign::Negative;
                    }
                    Sign::Negative => self.numerator += rhs * self.denominator,
                }
            }
        }

        #[inline]
        fn $mul_name(left_numerator: &mut $large, left_denominator: &mut $large, right: $large) {
            debug_assert_ne!(right, 0);

            if right != 1 {
                if *left_denominator != 1 {
                    let gcd = $gcd_name(*left_denominator, right);
                    *left_numerator *= right / gcd;
                    *left_denominator /= gcd;
                } else {
                    *left_numerator *= right;
                }
            }
        }
    }
}

shared!(Rational8, u8, mul8, gcd8);
shared!(Rational16, u16, mul16, gcd16);
shared!(Rational32, u32, mul32, gcd32);
shared!(Rational64, u64, mul64, gcd64);
shared!(Rational128, u128, mul128, gcd128);
shared!(RationalUsize, usize, mul_usize, gcd_usize);

#[cfg(test)]
mod test {
    use crate::{R16, R32, R64};
    
    #[test]
    fn test_add() {
        assert_eq!(R64!(2, 3) + 2, R64!(8, 3));
        assert_eq!(R64!(5, 6) + 7, R64!(7 * 6 + 5, 6));
        assert_eq!(R64!(5, 6) - 7, R64!(-7 * 6 + 5, 6));
        assert_eq!(R64!(5, 6) + (-7) as i32, R64!(-7 * 6 + 5, 6));
        assert_eq!(R64!(-5, 6) + 7, R64!(7 * 6 - 5, 6));
        assert_eq!(R64!(-5, 6) + (-7), -R64!(7 * 6 + 5, 6));
        assert_eq!(R64!(-2, 3) + 2, R64!(4, 3));
        assert_eq!(R64!(2, 3) + 0, R64!(2, 3));
        assert_eq!(R64!(2, 3) - 2, R64!(-4, 3));
        assert_eq!(R64!(0) - 1, R64!(-1));
        assert_eq!(R64!(-2, 3) - 2, R64!(-8, 3));
    }

    #[test]
    fn test_mul() {
        let mut x = R16!(1);
        x /= &19_u16;
        assert_eq!(x, R16!(1, 19));

        assert_eq!(R16!(1) / &19_u16, R16!(1, 19));
        assert_eq!(R16!(1) * &19_u16, R16!(19));
        assert_eq!(R32!(3) * &19, R32!(19 * 3));
        assert_eq!(R32!(3) / &19, R32!(3, 19));
        assert_eq!(R32!(3) * &6, R32!(3 * 6));
        assert_eq!(R32!(3) / &6, R32!(3, 6));
        assert_eq!(R32!(3) / &(-6), R32!(-3, 6));
        assert_eq!(R32!(3) * 0, R32!(0));
        assert_eq!(R32!(3) / &6, R32!(3, 6));
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn test_div_by_zero() {
        R32!(3) / &0;
    }
}
