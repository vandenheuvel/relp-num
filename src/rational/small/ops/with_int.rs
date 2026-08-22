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

            #[inline]
            fn add(mut self, rhs: $ty) -> Self::Output {
                AddAssign::add_assign(&mut self, rhs);
                self
            }
        }

        impl Add<&$ty> for $large {
            type Output = Self;

            #[inline]
            fn add(mut self, rhs: &$ty) -> Self::Output {
                AddAssign::add_assign(&mut self, rhs);
                self
            }
        }

        impl Add<$ty> for &$large {
            type Output = $large;

            #[inline]
            fn add(self, rhs: $ty) -> Self::Output {
                Add::add(self.clone(), rhs)
            }
        }

        impl Add<&$ty> for &$large {
            type Output = $large;

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

            #[inline]
            fn sub(mut self, rhs: $ty) -> Self::Output {
                SubAssign::sub_assign(&mut self, rhs);
                self
            }
        }

        impl Sub<&$ty> for $large {
            type Output = Self;

            #[inline]
            fn sub(mut self, rhs: &$ty) -> Self::Output {
                SubAssign::sub_assign(&mut self, rhs);
                self
            }
        }

        impl Sub<$ty> for &$large {
            type Output = $large;

            #[inline]
            fn sub(self, rhs: $ty) -> Self::Output {
                Sub::sub(self.clone(), rhs)
            }
        }

        impl Sub<&$ty> for &$large {
            type Output = $large;

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

            #[inline]
            fn mul(mut self, rhs: $ty) -> Self::Output {
                MulAssign::mul_assign(&mut self, rhs);
                self
            }
        }

        impl Mul<&$ty> for $large {
            type Output = Self;

            #[inline]
            fn mul(mut self, rhs: &$ty) -> Self::Output {
                MulAssign::mul_assign(&mut self, rhs);
                self
            }
        }

        impl Mul<$ty> for &$large {
            type Output = $large;

            #[inline]
            fn mul(self, rhs: $ty) -> Self::Output {
                Mul::mul(self.clone(), rhs)
            }
        }

        impl Mul<&$ty> for &$large {
            type Output = $large;

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

            #[inline]
            fn div(mut self, rhs: $ty) -> Self::Output {
                DivAssign::div_assign(&mut self, rhs);
                self
            }
        }

        impl Div<&$ty> for $large {
            type Output = Self;

            #[inline]
            fn div(mut self, rhs: &$ty) -> Self::Output {
                DivAssign::div_assign(&mut self, rhs);
                self
            }
        }

        impl Div<$ty> for &$large {
            type Output = $large;

            #[inline]
            fn div(self, rhs: $ty) -> Self::Output {
                Div::div(self.clone(), rhs)
            }
        }

        impl Div<&$ty> for &$large {
            type Output = $large;

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

        impl PartialEq<$large> for $ty {
            #[inline]
            fn eq(&self, rhs: &$large) -> bool {
                PartialEq::eq(rhs, self)
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
                // The inherent method assumes a non zero right hand side: a zero would be given a
                // sign, breaking the invariant that only a zero numerator has sign `Sign::Zero`.
                if rhs.is_not_zero() {
                    self.add_assign(rhs as $large);
                }
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
                // The inherent method assumes a non zero right hand side: a zero would be given a
                // sign, breaking the invariant that only a zero numerator has sign `Sign::Zero`.
                if rhs.is_not_zero() {
                    self.sub_assign(rhs as $large);
                }
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

        impl PartialEq<$ty> for $name {
            #[inline]
            fn eq(&self, rhs: &$ty) -> bool {
                // A zero has sign `Sign::Zero`, not `Sign::Positive`, so the sign of the right hand
                // side has to be compared rather than assumed.
                self.numerator == *rhs as $large && self.denominator.is_one() && self.sign == Signed::signum(rhs)
            }
        }

        impl PartialEq<$nzty> for $name {
            #[inline]
            fn eq(&self, rhs: &$nzty) -> bool {
                self.numerator == rhs.get() as $large && self.denominator.is_one() && self.sign == Signed::signum(rhs)
            }
        }

        impl PartialEq<$sty> for $name {
            #[inline]
            fn eq(&self, rhs: &$sty) -> bool {
                self.numerator == rhs.unsigned_abs() as $large && self.denominator.is_one() && self.sign == Signed::signum(rhs)
            }
        }

        impl PartialEq<$nzsty> for $name {
            #[inline]
            fn eq(&self, rhs: &$nzsty) -> bool {
                self.numerator == rhs.get().unsigned_abs() as $large && self.denominator.is_one() && self.sign == Signed::signum(rhs)
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
    ($ty:ty, $large:ty, $wide:ty, $mul_name:ident, $gcd_name:ident) => {
        impl $ty {
            /// Add a non zero integer.
            ///
            /// The caller guarantees that `rhs` is not zero, because a zero would be given a sign
            /// in the `Sign::Zero` arm.
            #[inline]
            fn add_assign(&mut self, rhs: $large) {
                match self.signum() {
                    Sign::Positive => self.numerator += rhs * self.denominator,
                    Sign::Zero => {
                        self.numerator = rhs;
                        self.sign = Sign::Positive;
                        debug_assert!(self.denominator.is_one());
                    }
                    Sign::Negative => self.sub_assign_magnitude(rhs),
                }
            }
            /// Subtract a non zero integer.
            ///
            /// The caller guarantees that `rhs` is not zero, because a zero would be given a sign
            /// in the `Sign::Zero` arm.
            #[inline]
            fn sub_assign(&mut self, rhs: $large) {
                match self.signum() {
                    Sign::Positive => self.sub_assign_magnitude(rhs),
                    Sign::Zero => {
                        self.numerator = rhs;
                        self.sign = Sign::Negative;
                        debug_assert!(self.denominator.is_one());
                    }
                    Sign::Negative => self.numerator += rhs * self.denominator,
                }
            }
            /// Subtract the integer `rhs` from the magnitude of a non zero `self`.
            ///
            /// The sign is negated when `rhs` is the larger of the two, that is, when the value
            /// moves past zero.
            ///
            /// The product `rhs * denominator` is computed in a wider type where one exists, so
            /// that a product too large for the numerator still compares correctly, and so that a
            /// result which does fit is exact. Only for the widest type can the product itself
            /// overflow, and such a product is by definition larger than any representable
            /// numerator, which is enough to get the sign right. The magnitude can then not be
            /// represented; debug builds panic on the assertions, release builds truncate.
            #[inline]
            fn sub_assign_magnitude(&mut self, rhs: $large) {
                let product = (rhs as $wide).checked_mul(self.denominator as $wide);
                debug_assert!(product.is_some(), "attempt to multiply with overflow");

                match product {
                    Some(product) => {
                        let numerator = self.numerator as $wide;
                        match numerator.cmp(&product) {
                            Ordering::Less => {
                                let difference = product - numerator;
                                debug_assert!(
                                    difference <= <$large>::MAX as $wide,
                                    "attempt to subtract with overflow",
                                );
                                self.numerator = difference as $large;
                                self.sign.negate();
                            }
                            Ordering::Equal => self.set_zero(),
                            // Smaller than the numerator, so it fits.
                            Ordering::Greater => self.numerator -= product as $large,
                        }
                    }
                    None => {
                        self.numerator = rhs.wrapping_mul(self.denominator)
                            .wrapping_sub(self.numerator);
                        self.sign.negate();
                    }
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

// The third type is the one the intermediate products are computed in. It is twice as wide as the
// second, except for the widest type, which has nothing to widen into.
shared!(Rational8, u8, u16, mul8, gcd8);
shared!(Rational16, u16, u32, mul16, gcd16);
shared!(Rational32, u32, u64, mul32, gcd32);
shared!(Rational64, u64, u128, mul64, gcd64);
shared!(Rational128, u128, u128, mul128, gcd128);
shared!(RationalUsize, usize, u128, mul_usize, gcd_usize);

#[cfg(test)]
mod test {
    use std::num::NonZeroU32;

    use num_traits::Zero;

    use crate::{NonZero, Rational16, Rational8, Sign, Signed};
    use crate::{R16, R32, R64};

    #[test]
    fn test_add() {
        assert_eq!(R64!(2, 3) + 2, R64!(8, 3));
        assert_eq!(R64!(5, 6) + 7, R64!(7 * 6 + 5, 6));
        assert_eq!(R64!(5, 6) - 7, R64!(-7 * 6 + 5, 6));
        assert_eq!(R64!(5, 6) + -7_i32, R64!(-7 * 6 + 5, 6));
        assert_eq!(R64!(-5, 6) + 7, R64!(7 * 6 - 5, 6));
        assert_eq!(R64!(-5, 6) + (-7), -R64!(7 * 6 + 5, 6));
        assert_eq!(R64!(-2, 3) + 2, R64!(4, 3));
        assert_eq!(R64!(2, 3) + 0, R64!(2, 3));
        assert_eq!(R64!(2, 3) - 2, R64!(-4, 3));
        assert_eq!(R64!(0) - 1, R64!(-1));
        assert_eq!(R64!(-2, 3) - 2, R64!(-8, 3));
    }

    /// Adding an integer to zero has to set the sign as well as the numerator.
    #[test]
    fn test_add_to_zero() {
        assert_eq!(R64!(0) + 1_u64, R64!(1));
        assert_eq!(R64!(0) + 1_i32, R64!(1));
        assert_eq!(R64!(0) - 1_u64, R64!(-1));
        assert_eq!(R64!(0) - 1_i32, R64!(-1));

        let value = R64!(0) + 1_u64;
        assert!(!value.is_zero());
        assert!(value.is_not_zero());
        assert_eq!(value.signum(), Sign::Positive);
    }

    /// A zero right hand side leaves the value alone; in particular, it doesn't create a zero with
    /// a sign, which would break the invariant that only a zero numerator has sign `Sign::Zero`.
    #[test]
    fn test_add_zero_integer() {
        for value in [R64!(0), R64!(2, 3), R64!(-2, 3)] {
            assert_eq!(value + 0_u64, value);
            assert_eq!(value - 0_u64, value);
            assert_eq!(value + 0_i64, value);
            assert_eq!(value - 0_i64, value);
        }

        let zero = R64!(0) - 0_u64;
        assert_eq!(zero, R64!(0));
        assert!(zero.is_zero());
        assert!(!zero.is_not_zero());
        assert_eq!(zero.signum(), Sign::Zero);
    }

    /// A zero has sign `Sign::Zero`, so comparing with an integer can't assume `Sign::Positive`.
    #[test]
    fn test_eq_integer() {
        assert_eq!(R32!(0), 0_u32);
        assert_eq!(0_u32, R32!(0));
        assert_eq!(R32!(0), 0_i32);
        assert_eq!(R32!(3), 3_u32);
        assert_eq!(R32!(3), NonZeroU32::new(3).unwrap());
        assert_ne!(R32!(3), 0_u32);
        assert_ne!(R32!(0), 3_u32);
        assert_ne!(R32!(-3), 3_u32);
        assert_ne!(R32!(3, 2), 3_u32);
    }

    /// The product of the integer with the denominator decides the sign of the result, so it may
    /// not silently wrap: it is computed in a wider type.
    #[test]
    fn test_add_integer_wide_intermediate() {
        // `130 * 2` doesn't fit in a `u8`, while the result `-5 / 2` does.
        let value = Rational8::new_signed(Sign::Positive, 255, 2).unwrap();
        assert_eq!(value - 130_u8, Rational8::new_signed(Sign::Negative, 5, 2).unwrap());
        assert_eq!(-value + 130_u8, Rational8::new_signed(Sign::Positive, 5, 2).unwrap());
        assert_eq!(value - 128_u8, Rational8::new_signed(Sign::Negative, 1, 2).unwrap());
        assert_eq!(value - 127_u8, Rational8::new_signed(Sign::Positive, 1, 2).unwrap());

        // `10_000 * 7` doesn't fit in a `u16`, while the result `-40_000 / 7` does.
        let value = Rational16::new_signed(Sign::Positive, 30_000, 7).unwrap();
        assert_eq!(value - 10_000_u16, Rational16::new_signed(Sign::Negative, 40_000, 7).unwrap());
        assert_eq!(-value + 10_000_u16, Rational16::new_signed(Sign::Positive, 40_000, 7).unwrap());
    }

    /// The widest type has nothing to widen into, so a product that overflows can't be represented.
    /// The sign of the result can be, and has to be right.
    #[cfg(not(debug_assertions))]
    #[test]
    fn test_add_integer_widest_intermediate() {
        use crate::Rational128;

        // `2^127 * 2` wraps to zero, which is smaller than any numerator: without the check on the
        // product, the subtraction would look like it doesn't pass zero at all. Only the sign of
        // the result is guaranteed; its magnitude can't be represented in general.
        let value = Rational128::new_signed(Sign::Positive, u128::MAX, 2).unwrap();
        assert!((value - (1_u128 << 127)).is_negative());
        assert!((-value + (1_u128 << 127)).is_positive());
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
