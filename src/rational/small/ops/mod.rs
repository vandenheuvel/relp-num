use std::cmp::Ordering;
use std::iter::Sum;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};
use std::ops::Neg;

use crate::Negateable;
use crate::non_zero::NonZero;
use crate::non_zero::NonZeroSign;
use crate::rational::small::{Rational128, Rational16, Rational32, Rational64, Rational8, RationalUsize};
use crate::rational::small::{NonZeroRational128, NonZeroRational16, NonZeroRational32, NonZeroRational64, NonZeroRational8, NonZeroRationalUsize};
use crate::rational::small::ops::building_blocks::{add128, add16, add32, add64, add8, add_usize};
use crate::rational::small::ops::building_blocks::{sub128, sub16, sub32, sub64, sub8, sub_usize};
use crate::rational::small::ops::building_blocks::{mul128, mul16, mul32, mul64, mul8, mul_usize};
use crate::rational::small::ops::building_blocks::SignChange;
use crate::sign::Sign;

pub(crate) mod building_blocks;
mod with_int;
mod with_one;
mod with_zero;

#[cfg(test)]
mod test;

macro_rules! rational {
    ($name:ident, $add_name:ident, $sub_name:ident, $mul_name:ident) => {
        impl AddAssign<&$name> for $name {
            #[inline]
            fn add_assign(&mut self, rhs: &Self) {
                match (self.sign, rhs.sign) {
                    (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => {
                        $add_name(
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        )
                    }
                    (Sign::Positive, Sign::Negative) | (Sign::Negative, Sign::Positive) => {
                        let sign_change = $sub_name(
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        );
                        match sign_change {
                            SignChange::None => {}
                            SignChange::Flip => self.sign.negate(),
                            SignChange::Zero => self.sign = Sign::Zero,
                        }
                    }
                    (_, Sign::Zero) => {},
                    (Sign::Zero, _) => {
                        *self = Self {
                            sign: rhs.sign,
                            numerator: rhs.numerator,
                            denominator: rhs.denominator,
                        };
                    },
                }
            }
        }

        impl SubAssign<&$name> for $name {
            #[inline]
            fn sub_assign(&mut self, rhs: &Self) {
                match (self.sign, rhs.sign) {
                    (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => {
                        let sign_change = $sub_name(
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        );
                        match sign_change {
                            SignChange::None => {}
                            SignChange::Flip => self.sign.negate(),
                            SignChange::Zero => self.sign = Sign::Zero,
                        }
                    }
                    (Sign::Positive, Sign::Negative) | (Sign::Negative, Sign::Positive) => {
                        $add_name(
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        )
                    }
                    (_, Sign::Zero) => {}
                    (Sign::Zero, _) => {
                        *self = Self {
                            sign: !rhs.sign,
                            numerator: rhs.numerator,
                            denominator: rhs.denominator,
                        };
                    }
                }
            }
        }

        impl Sum for $name {
            fn sum<I: Iterator<Item=Self>>(mut iter: I) -> Self {
                let first_value = iter.next();
                match first_value {
                    None => <Self as num_traits::Zero>::zero(),
                    Some(mut total) => {

                        while let Some(next_value) = iter.next() {
                            total += next_value;
                        }

                        total
                    }
                }
            }
        }

        impl MulAssign<&$name> for $name {
            #[inline]
            fn mul_assign(&mut self, rhs: &Self) {
                match (self.sign, rhs.sign) {
                    (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                        self.sign *= rhs.sign;
                        $mul_name(&mut self.numerator, &mut self.denominator, rhs.numerator, rhs.denominator);
                    }
                    (Sign::Zero, _) => {}
                    (_, Sign::Zero) => <Self as num_traits::Zero>::set_zero(self),
                }
            }
        }

        // The sign of a quotient is the product of the signs, so `*` is correct here.
        #[allow(clippy::suspicious_arithmetic_impl)]
        impl Div<$name> for &$name {
            type Output = $name;

            #[inline]
            fn div(self, mut rhs: $name) -> Self::Output {
                match (self.sign, rhs.sign) {
                    (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                        let sign = self.sign * rhs.sign;
                        $mul_name(&mut rhs.numerator, &mut rhs.denominator, self.denominator, self.numerator);
                        Self::Output {
                            sign,
                            numerator: rhs.denominator,
                            denominator: rhs.numerator,
                        }
                    }
                    (_, Sign::Zero) => panic!(),
                    (Sign::Zero, _) => {
                        <$name as num_traits::Zero>::set_zero(&mut rhs);
                        rhs
                    }
                }
            }
        }

        // The sign of a quotient is the product of the signs, so `*` is correct here.
        #[allow(clippy::suspicious_op_assign_impl)]
        impl DivAssign<&$name> for $name {
            #[inline]
            fn div_assign(&mut self, rhs: &Self) {
                match (self.sign, rhs.sign) {
                    (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                        self.sign *= rhs.sign;
                        $mul_name(&mut self.numerator, &mut self.denominator, rhs.denominator, rhs.numerator);
                    }
                    (_, Sign::Zero) => panic!(),
                    (Sign::Zero, _) => {}
                }
            }
        }
    }
}

rational!(Rational8, add8, sub8, mul8);
rational!(Rational16, add16, sub16, mul16);
rational!(Rational32, add32, sub32, mul32);
rational!(Rational64, add64, sub64, mul64);
rational!(Rational128, add128, sub128, mul128);
rational!(RationalUsize, add_usize, sub_usize, mul_usize);

macro_rules! rational_non_zero {
    ($name:ident, $add_name:ident, $sub_name:ident, $mul_name:ident) => {
        impl AddAssign<&$name> for $name {
            #[inline]
            fn add_assign(&mut self, rhs: &Self) {
                match (self.sign, rhs.sign) {
                    (NonZeroSign::Positive, NonZeroSign::Positive) | (NonZeroSign::Negative, NonZeroSign::Negative) => {
                        $add_name(
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        )
                    }
                    (NonZeroSign::Positive, NonZeroSign::Negative) | (NonZeroSign::Negative, NonZeroSign::Positive) => {
                        let sign_change = $sub_name(
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        );
                        match sign_change {
                            SignChange::None => {}
                            SignChange::Flip => self.sign.negate(),
                            SignChange::Zero => panic!("attempt to add with overflow"),
                        }
                    }
                }
            }
        }
        impl SubAssign<&$name> for $name {
            #[inline]
            fn sub_assign(&mut self, rhs: &Self) {
                match (self.sign, rhs.sign) {
                    (NonZeroSign::Positive, NonZeroSign::Positive) | (NonZeroSign::Negative, NonZeroSign::Negative) => {
                        let sign_change = $sub_name(
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        );
                        match sign_change {
                            SignChange::None => {}
                            SignChange::Flip => self.sign.negate(),
                            SignChange::Zero => panic!("attempt to subtract with overflow"),
                        }
                    }
                    (NonZeroSign::Positive, NonZeroSign::Negative) | (NonZeroSign::Negative, NonZeroSign::Positive) => {
                        $add_name(
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        )
                    }
                }
            }
        }
        impl MulAssign<&$name> for $name {
            #[inline]
            fn mul_assign(&mut self, rhs: &Self) {
                self.sign *= rhs.sign;
                $mul_name(&mut self.numerator, &mut self.denominator, rhs.numerator, rhs.denominator);
            }
        }
        // The sign of a quotient is the product of the signs, so `*` is correct here.
        #[allow(clippy::suspicious_arithmetic_impl)]
        impl Div<$name> for &$name {
            type Output = $name;

            #[inline]
            fn div(self, mut rhs: $name) -> Self::Output {
                let sign = self.sign * rhs.sign;
                $mul_name(&mut rhs.numerator, &mut rhs.denominator, self.denominator, self.numerator);
                Self::Output {
                    sign,
                    numerator: rhs.denominator,
                    denominator: rhs.numerator,
                }
            }
        }
        // The sign of a quotient is the product of the signs, so `*` is correct here.
        #[allow(clippy::suspicious_op_assign_impl)]
        impl DivAssign<&$name> for $name {
            #[inline]
            fn div_assign(&mut self, rhs: &Self) {
                self.sign *= rhs.sign;
                $mul_name(&mut self.numerator, &mut self.denominator, rhs.denominator, rhs.numerator);
            }
        }

        impl Neg for $name {
            type Output = Self;

            #[inline]
            fn neg(mut self) -> Self::Output {
                self.sign.negate();
                self
            }
        }

        impl Neg for &$name {
            type Output = $name;

            #[inline]
            fn neg(self) -> Self::Output {
                Self::Output {
                    sign: !self.sign,
                    numerator: self.numerator,
                    denominator: self.denominator,
                }
            }
        }
    }
}
rational_non_zero!(NonZeroRational8, add8, sub8, mul8);
rational_non_zero!(NonZeroRational16, add16, sub16, mul16);
rational_non_zero!(NonZeroRational32, add32, sub32, mul32);
rational_non_zero!(NonZeroRational64, add64, sub64, mul64);
rational_non_zero!(NonZeroRational128, add128, sub128, mul128);
rational_non_zero!(NonZeroRationalUsize, add_usize, sub_usize, mul_usize);

/// Compare two ratios by cross multiplication.
///
/// `$widening_mul` computes the exact product of two magnitudes as a tuple that orders like the
/// number it represents: the most significant half first. Comparing the two tuples
/// lexicographically therefore compares `a * d` against `b * c` exactly, which is the comparison
/// of `a / b` against `c / d` because both denominators are positive.
macro_rules! rational_ord {
    ($name:ident, $sign:ident, $widening_mul:expr) => {
        impl PartialOrd for $name {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        impl Ord for $name {
            #[inline]
            #[allow(unreachable_patterns)]
            fn cmp(&self, other: &Self) -> Ordering {
                match self.sign.cmp(&other.sign) {
                    Ordering::Less => return Ordering::Less,
                    Ordering::Greater => return Ordering::Greater,
                    // Both zero, or both nonzero with the same sign; compare the magnitudes.
                    Ordering::Equal => {}
                }

                if !self.sign.is_not_zero() {
                    // Equal signs and the sign is zero, so both values are zero.
                    return Ordering::Equal;
                }

                let widening_mul = $widening_mul;

                let ad = widening_mul(self.numerator, other.denominator);
                let bc = widening_mul(self.denominator, other.numerator);

                match (ad.cmp(&bc), self.sign) {
                    (Ordering::Less, $sign::Positive) | (Ordering::Greater, $sign::Negative) => Ordering::Less,
                    (Ordering::Equal, _) => Ordering::Equal,
                    (Ordering::Greater, $sign::Positive) | (Ordering::Less, $sign::Negative) => Ordering::Greater,
                    _ => unreachable!("sign was checked to be nonzero"),
                }
            }
        }
    }
}

/// Order a ratio whose magnitudes fit a doubled width integer.
macro_rules! rational_requiring_wide {
    ($name:ident, $uty:ty, $BITS:expr, $wide:ty, $sign:ident) => {
        rational_ord!($name, $sign, |left: $uty, right: $uty| {
            // The product of two `$uty` values always fits `$wide`, so this never overflows.
            let wide = unsafe { (left as $wide).unchecked_mul(right as $wide) };
            ((wide >> $BITS) as $uty, wide as $uty)
        });
    }
}

/// Order a ratio of `u128` magnitudes, for which no doubled width integer exists.
///
/// The 256 bit products are computed as `(high, low)` pairs with [`u128::carrying_mul`] instead.
/// That mirrors `rational_requiring_wide!` one width down, which forms the same pair by shifting a
/// doubled width product, so both orders are the same cross multiplication and only the way the
/// pair is obtained differs.
///
/// Comparing by the continued fraction expansion of the two ratios would avoid the wide product
/// altogether, but it costs a division per term of the expansion rather than a single
/// multiplication, and the number of terms is not bounded by anything better than the width.
macro_rules! rational_widest {
    ($name:ident, $sign:ident) => {
        rational_ord!($name, $sign, |left: u128, right: u128| {
            // `carrying_mul` returns the low half first; a zero carry makes it a widening multiply.
            let (low, high) = left.carrying_mul(right, 0);
            (high, low)
        });
    }
}

rational_requiring_wide!(Rational8, u8, 8, u16, Sign);
rational_requiring_wide!(Rational16, u16, 16, u32, Sign);
rational_requiring_wide!(Rational32, u32, 32, u64, Sign);
rational_requiring_wide!(Rational64, u64, 64, u128, Sign);
rational_requiring_wide!(RationalUsize, usize, usize::BITS, u128, Sign);
rational_widest!(Rational128, Sign);
rational_requiring_wide!(NonZeroRational8, u8, 8, u16, NonZeroSign);
rational_requiring_wide!(NonZeroRational16, u16, 16, u32, NonZeroSign);
rational_requiring_wide!(NonZeroRational32, u32, 32, u64, NonZeroSign);
rational_requiring_wide!(NonZeroRational64, u64, 64, u128, NonZeroSign);
rational_requiring_wide!(NonZeroRationalUsize, usize, usize::BITS, u128, NonZeroSign);
rational_widest!(NonZeroRational128, NonZeroSign);

macro_rules! rational_forward {
    ($name:ident) => {
        impl<'a> Add<&'a $name> for &'a $name {
            type Output = $name;

            #[inline]
            fn add(self, rhs: Self) -> Self::Output {
                Add::add(self.clone(), rhs)
            }
        }

        impl Add for $name {
            type Output = Self;

            #[inline]
            fn add(mut self, rhs: Self) -> Self::Output {
                AddAssign::add_assign(&mut self, rhs);
                self
            }
        }

        impl Add<&$name> for $name {
            type Output = Self;

            #[inline]
            fn add(mut self, rhs: &Self) -> Self::Output {
                AddAssign::add_assign(&mut self, rhs);
                self
            }
        }

        impl Add<$name> for &$name {
            type Output = $name;

            #[inline]
            fn add(self, rhs: $name) -> Self::Output {
                Add::add(rhs, self)
            }
        }

        impl AddAssign for $name {
            #[inline]
            fn add_assign(&mut self, rhs: Self) {
                AddAssign::add_assign(self, &rhs);
            }
        }

        impl Sub for $name {
            type Output = Self;

            #[inline]
            fn sub(mut self, rhs: Self) -> Self::Output {
                SubAssign::sub_assign(&mut self, rhs);
                self
            }
        }

        impl<'a> Sub<&'a $name> for &'a $name {
            type Output = $name;

            #[inline]
            fn sub(self, rhs: Self) -> Self::Output {
                Sub::sub(self.clone(), rhs)
            }
        }

        impl Sub<&$name> for $name {
            type Output = Self;

            #[inline]
            fn sub(mut self, rhs: &Self) -> Self::Output {
                SubAssign::sub_assign(&mut self, rhs);
                self
            }
        }

        impl Sub<$name> for &$name {
            type Output = $name;

            #[inline]
            fn sub(self, rhs: $name) -> Self::Output {
                -Sub::sub(rhs, self)
            }
        }

        impl SubAssign for $name {
            #[inline]
            fn sub_assign(&mut self, rhs: Self) {
                SubAssign::sub_assign(self, &rhs)
            }
        }

        impl Mul<&$name> for $name {
            type Output = Self;

            #[inline]
            fn mul(mut self, rhs: &Self) -> Self::Output {
                MulAssign::mul_assign(&mut self, rhs);
                self
            }
        }

        impl<'a> Mul<&'a $name> for &'a $name {
            type Output = $name;

            #[inline]
            fn mul(self, rhs: Self) -> Self::Output {
                Mul::mul(self.clone(), rhs)
            }
        }

        impl Mul for $name {
            type Output = Self;

            #[inline]
            fn mul(mut self, rhs: Self) -> Self::Output {
                MulAssign::mul_assign(&mut self, rhs);
                self
            }
        }

        impl MulAssign for $name {
            #[inline]
            fn mul_assign(&mut self, rhs: Self) {
                MulAssign::mul_assign(self, &rhs);
            }
        }

        impl Mul<$name> for &$name {
            type Output = $name;

            #[inline]
            fn mul(self, rhs: $name) -> Self::Output {
                Mul::mul(rhs, self)
            }
        }

        impl Div for $name {
            type Output = Self;

            #[inline]
            fn div(mut self, rhs: Self) -> Self::Output {
                DivAssign::div_assign(&mut self, rhs);
                self
            }
        }

        impl Div<&$name> for $name {
            type Output = Self;

            #[inline]
            fn div(mut self, rhs: &Self) -> Self::Output {
                DivAssign::div_assign(&mut self, rhs);
                self
            }
        }

        impl<'a> Div<&'a $name> for &'a $name {
            type Output = $name;

            #[inline]
            fn div(self, rhs: Self) -> Self::Output {
                Div::div(self.clone(), rhs)
            }
        }

        impl DivAssign for $name {
            #[inline]
            fn div_assign(&mut self, rhs: Self) {
                DivAssign::div_assign(self, &rhs);
            }
        }
    }
}

rational_forward!(Rational8);
rational_forward!(Rational16);
rational_forward!(Rational32);
rational_forward!(Rational64);
rational_forward!(Rational128);
rational_forward!(RationalUsize);
rational_forward!(NonZeroRational8);
rational_forward!(NonZeroRational16);
rational_forward!(NonZeroRational32);
rational_forward!(NonZeroRational64);
rational_forward!(NonZeroRational128);
rational_forward!(NonZeroRationalUsize);

#[cfg(test)]
mod order_test {
    use std::cmp::Ordering;

    use crate::{Field, OrderedField};
    use crate::non_zero::NonZeroSign;
    use crate::rational::Ratio;
    use crate::rational::small::{NonZeroRational128, NonZeroRationalUsize, Rational128, RationalUsize};
    use crate::sign::Sign;

    /// Build a value directly, to reach magnitudes that the `new` constructors can't take.
    ///
    /// The caller is responsible for the invariants: lowest terms, nonzero denominator and a sign
    /// that is zero exactly when the numerator is.
    fn ratio128(sign: Sign, numerator: u128, denominator: u128) -> Rational128 {
        Ratio { sign, numerator, denominator }
    }

    fn ratio_usize(sign: Sign, numerator: usize, denominator: usize) -> RationalUsize {
        Ratio { sign, numerator, denominator }
    }

    /// The widest types used to have no total order, and so were not fields either.
    #[test]
    fn test_ordered_field() {
        fn assert_field<T: Field>() {}
        fn assert_ordered_field<T: OrderedField>() {}
        fn assert_ord<T: Ord>() {}

        assert_field::<Rational128>();
        assert_ordered_field::<Rational128>();
        assert_field::<RationalUsize>();
        assert_ordered_field::<RationalUsize>();

        assert_ord::<NonZeroRational128>();
        assert_ord::<NonZeroRationalUsize>();

        // `Abs` is implemented for ratios that are ordered.
        assert_eq!(crate::Abs::abs(ratio128(Sign::Negative, u128::MAX, 2)), ratio128(Sign::Positive, u128::MAX, 2));
        assert_eq!(crate::Abs::abs(ratio_usize(Sign::Negative, usize::MAX, 2)), ratio_usize(Sign::Positive, usize::MAX, 2));
    }

    /// All pairs and triples of a small range, against an exact `f64` reference.
    #[test]
    fn test_order_usize_brute_force() {
        let mut values = Vec::new();
        for numerator in -5_isize..=5 {
            for denominator in 1_usize..=5 {
                let value = RationalUsize::new(numerator, denominator).unwrap();
                values.push((value, numerator as f64 / denominator as f64));
            }
        }

        for &(left, left_float) in &values {
            for &(right, right_float) in &values {
                let expected = left_float.partial_cmp(&right_float).unwrap();

                assert_eq!(left.cmp(&right), expected, "{:?} <=> {:?}", left, right);
                assert_eq!(left.partial_cmp(&right), Some(expected));
                // Antisymmetry.
                assert_eq!(right.cmp(&left), expected.reverse(), "{:?} <=> {:?}", right, left);
                // Agreement with `PartialEq`.
                assert_eq!(left == right, expected == Ordering::Equal, "{:?} == {:?}", left, right);
            }
        }

        // Transitivity.
        for &(left, _) in &values {
            for &(middle, _) in &values {
                if left > middle {
                    continue;
                }

                for &(right, _) in &values {
                    if middle <= right {
                        assert!(left <= right, "{:?} <= {:?} <= {:?}", left, middle, right);
                    }
                }
            }
        }
    }

    /// Products that don't fit a `usize`, which is why the comparison multiplies into a `u128`.
    #[test]
    fn test_order_usize_wide_product() {
        // `(2 ^ (usize::BITS - 1) + 1) * 2` wraps to `2` in a `usize`, which is less than `1 * 3`,
        // so a comparison that multiplies at the width of the type gets this pair backwards.
        let large = ratio_usize(Sign::Positive, (1 << (usize::BITS - 1)) + 1, 1);
        let small = ratio_usize(Sign::Positive, 3, 2);
        assert!(large > small);
        assert!(small < large);
        assert!(-large < -small);

        // The difference between these two is in the low half of the product.
        let left = ratio_usize(Sign::Positive, usize::MAX, usize::MAX - 1);
        let right = ratio_usize(Sign::Positive, usize::MAX - 1, usize::MAX - 2);
        assert!(left < right);
        assert!(right > left);
        assert_eq!(left.cmp(&left), Ordering::Equal);
        assert_eq!(right.cmp(&right), Ordering::Equal);
        assert_eq!(left.cmp(&right).reverse(), right.cmp(&left));
    }

    /// Magnitudes above `u64::MAX`, whose products need more than the 128 bits of a `u128`.
    #[test]
    fn test_order_128_above_64_bits() {
        // `(2 ^ 127 + 1) * 2` wraps to `2` in a `u128`, which is less than `1 * 3`.
        let large = ratio128(Sign::Positive, (1 << 127) + 1, 1);
        let small = ratio128(Sign::Positive, 3, 2);
        assert!(large > small);
        assert!(small < large);
        assert!(-large < -small);

        // `1 + 1 / 2 ^ 64` against `1 + 1 / (2 ^ 64 + 1)`; both cross products exceed a `u128`.
        let left = ratio128(Sign::Positive, (1 << 64) + 1, 1 << 64);
        let right = ratio128(Sign::Positive, (1 << 64) + 2, (1 << 64) + 1);
        assert!(left > right);
        assert!(right < left);

        // The two products are `2 ^ 254 - 2 ^ 128` and `2 ^ 254 - 2 ^ 128 + 1`: they share their
        // high 128 bits and differ in the last bit of the low half.
        let left = ratio128(Sign::Positive, 1 << 127, (1 << 127) - 1);
        let right = ratio128(Sign::Positive, (1 << 127) - 1, (1 << 127) - 2);
        assert!(left < right);
        assert!(right > left);
        assert_eq!(left.cmp(&left), Ordering::Equal);
        assert_eq!(left.cmp(&right).reverse(), right.cmp(&left));

        // Large values that differ only in the last bit of the numerator.
        let left = ratio128(Sign::Positive, u128::MAX, 2);
        let right = ratio128(Sign::Positive, u128::MAX - 2, 2);
        assert!(left > right);
        assert!(-left < -right);
    }

    #[test]
    fn test_order_128_signs() {
        let zero = ratio128(Sign::Zero, 0, 1);
        let positive = ratio128(Sign::Positive, u128::MAX, u128::MAX - 1);
        let negative = ratio128(Sign::Negative, 1, u128::MAX);

        assert_eq!(zero.cmp(&zero), Ordering::Equal);
        assert_eq!(zero.cmp(&positive), Ordering::Less);
        assert_eq!(positive.cmp(&zero), Ordering::Greater);
        assert_eq!(zero.cmp(&negative), Ordering::Greater);
        assert_eq!(negative.cmp(&zero), Ordering::Less);
        assert_eq!(negative.cmp(&positive), Ordering::Less);
        assert_eq!(positive.cmp(&negative), Ordering::Greater);
        assert_eq!(positive.cmp(&positive), Ordering::Equal);
        assert_eq!(negative.cmp(&negative), Ordering::Equal);

        // Negation reverses the order of the magnitudes.
        let left = ratio128(Sign::Negative, (1 << 100) + 1, (1 << 100) - 1);
        let right = ratio128(Sign::Negative, (1 << 100) + 3, (1 << 100) - 1);
        assert!(left > right);
        assert!(-left < -right);
    }

    /// Compare `a / b` against `c / d` by their continued fraction expansions.
    ///
    /// This never computes a product, so it is independent of the implementation under test.
    fn euclidean_cmp(mut a: u128, mut b: u128, mut c: u128, mut d: u128) -> Ordering {
        let mut reversed = false;

        loop {
            let (left_quotient, left_remainder) = (a / b, a % b);
            let (right_quotient, right_remainder) = (c / d, c % d);

            let ordering = if left_quotient != right_quotient {
                left_quotient.cmp(&right_quotient)
            } else {
                match (left_remainder == 0, right_remainder == 0) {
                    (true, true) => Ordering::Equal,
                    (true, false) => Ordering::Less,
                    (false, true) => Ordering::Greater,
                    (false, false) => {
                        // Recurse on the reciprocals of the remainders, which flips the order.
                        a = b;
                        b = left_remainder;
                        c = d;
                        d = right_remainder;
                        reversed = !reversed;
                        continue;
                    }
                }
            };

            return if reversed { ordering.reverse() } else { ordering };
        }
    }

    #[test]
    fn test_order_128_against_continued_fractions() {
        fn gcd(mut left: u128, mut right: u128) -> u128 {
            while right != 0 {
                let remainder = left % right;
                left = right;
                right = remainder;
            }
            left
        }

        // A linear congruential generator, so that the values are reproducible.
        let mut state = 0x2545_f491_4f6c_dd1d_u64;
        let mut next = || {
            let mut value = 0_u128;
            for _ in 0..2 {
                state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                value = (value << 64) | (state >> 1) as u128;
            }
            // Zero magnitudes are not representable in a nonzero ratio.
            value.max(1)
        };

        for _ in 0..200 {
            let (mut a, mut b, mut c, mut d) = (next(), next(), next(), next());
            let (left_gcd, right_gcd) = (gcd(a, b), gcd(c, d));
            a /= left_gcd;
            b /= left_gcd;
            c /= right_gcd;
            d /= right_gcd;

            let expected = euclidean_cmp(a, b, c, d);
            let left = ratio128(Sign::Positive, a, b);
            let right = ratio128(Sign::Positive, c, d);

            assert_eq!(left.cmp(&right), expected, "{} / {} <=> {} / {}", a, b, c, d);
            assert_eq!(right.cmp(&left), expected.reverse(), "{} / {} <=> {} / {}", c, d, a, b);
            assert_eq!((-left).cmp(&-right), expected.reverse());
            assert_eq!(left == right, expected == Ordering::Equal);
        }
    }

    /// Small values of the widest type, against an exact `f64` reference.
    #[test]
    fn test_order_128_brute_force() {
        let mut values = Vec::new();
        for numerator in -5_i128..=5 {
            for denominator in 1_u128..=5 {
                let value = Rational128::new(numerator, denominator).unwrap();
                values.push((value, numerator as f64 / denominator as f64));
            }
        }

        for &(left, left_float) in &values {
            for &(right, right_float) in &values {
                let expected = left_float.partial_cmp(&right_float).unwrap();

                assert_eq!(left.cmp(&right), expected, "{:?} <=> {:?}", left, right);
                assert_eq!(right.cmp(&left), expected.reverse());
                assert_eq!(left == right, expected == Ordering::Equal);
            }
        }
    }

    #[test]
    fn test_order_non_zero() {
        let left: NonZeroRational128 = Ratio { sign: NonZeroSign::Positive, numerator: (1 << 127) + 1, denominator: 1 };
        let right: NonZeroRational128 = Ratio { sign: NonZeroSign::Positive, numerator: 3, denominator: 2 };
        assert!(left > right);
        assert!(-left < -right);

        let left: NonZeroRationalUsize = Ratio { sign: NonZeroSign::Positive, numerator: usize::MAX, denominator: usize::MAX - 1 };
        let right: NonZeroRationalUsize = Ratio { sign: NonZeroSign::Positive, numerator: usize::MAX - 1, denominator: usize::MAX - 2 };
        assert!(left < right);
        assert_eq!(left.cmp(&left), Ordering::Equal);
        assert!(-left > -right);
    }
}
