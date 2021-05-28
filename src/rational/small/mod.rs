//! # Rational types of fixed size
use std::cmp::{min, Ordering};
use std::fmt;
use std::fmt::Display;
use std::iter::Sum;
use std::mem;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use num_traits;

use crate::non_zero::{NonZero, NonZeroSign, NonZeroSigned};
use crate::rational::big::Big;
use crate::rational::big::ops::normalize::gcd_scalar;
use crate::rational::Ratio;
use crate::sign::{Sign, Signed};

mod mixing_signs;

macro_rules! rational {
    ($name:ident, $ity:ty, $uty:ty, $gcd_name:ident, $simplify_name:ident) => {
        pub type $name = Ratio<$uty, $uty>;

        impl $name {
            #[must_use]
            pub fn new(numerator: $ity, mut denominator: $uty) -> Self {
                debug_assert_ne!(denominator, 0);

                let mut numerator_abs = numerator.unsigned_abs();
                if numerator == 0 {
                    <Self as num_traits::Zero>::zero()
                } else if numerator_abs == denominator {
                    Self {
                        sign: Signed::signum(&numerator),
                        numerator: 1,
                        denominator: 1,
                    }
                } else {
                    if numerator_abs != 1 && denominator != 1 {
                        let gcd = gcd_scalar(numerator_abs as usize, denominator as usize) as $uty;

                        numerator_abs /= gcd;
                        denominator /= gcd;
                    }

                    Self {
                        sign: Signed::signum(&numerator),
                        numerator: numerator_abs,
                        denominator,
                    }
                }
            }
            pub fn new_signed<T: Into<Sign>>(sign: T, numerator: $uty, denominator: $uty) -> Self {
                debug_assert_ne!(denominator, 0);
                let sign = sign.into();
                debug_assert!((numerator == 0) == (sign == Sign::Zero));

                match sign {
                    Sign::Positive => debug_assert_ne!(numerator, 0),
                    Sign::Zero => {
                        debug_assert_eq!(numerator, 0);
                        return <Self as num_traits::Zero>::zero();
                    },
                    Sign::Negative => {}
                }

                let (numerator, denominator) = $simplify_name(numerator, denominator);

                Self {
                    sign,
                    numerator,
                    denominator,
                }
            }
        }

        impl num_traits::FromPrimitive for $name {
            #[must_use]
            #[inline]
            fn from_i64(n: i64) -> Option<Self> {
                if n.unsigned_abs() <= <$uty>::MAX as u64 {
                    Some(Self {
                        sign: Signed::signum(&n),
                        numerator: n.unsigned_abs() as $uty,
                        denominator: 1,
                    })
                } else {
                    None
                }
            }

            #[must_use]
            #[inline]
            fn from_u64(n: u64) -> Option<Self> {
                if n <= <$uty>::MAX as u64 {
                    Some(Self {
                        sign: Signed::signum(&n),
                        numerator: n as $uty,
                        denominator: 1,
                    })
                } else {
                    None
                }
            }

            #[must_use]
            #[inline]
            fn from_f32(n: f32) -> Option<Self> {
                Big::<8>::from_f32(n).map(Self::from_big_if_it_fits).flatten()
            }

            #[must_use]
            #[inline]
            fn from_f64(n: f64) -> Option<Self> {
                Big::<16>::from_f64(n).map(Self::from_big_if_it_fits).flatten()
            }
        }

        impl $name {
            fn from_big_if_it_fits<const S: usize>(big: Big<S>) -> Option<Self> {
                if num_traits::Zero::is_zero(&big) {
                    return Some(<Self as num_traits::Zero>::zero());
                }

                if big.numerator.len() == 1 && big.denominator.len() == 1 {
                    if big.numerator[0] <= <$uty>::MAX as usize && big.denominator[0] <= <$uty>::MAX as usize {
                        return Some(Self {
                            sign: big.sign,
                            numerator: big.numerator[0] as $uty,
                            denominator: big.denominator[0] as $uty,
                        })
                    }
                }

                None
            }
        }

        impl num_traits::ToPrimitive for $name {
            fn to_i64(&self) -> Option<i64> {
                if self.denominator == 1 && self.numerator as u128 <= i64::MAX as u128 {
                    Some(match self.sign {
                        Sign::Positive => self.numerator as i64,
                        Sign::Zero => 0,
                        Sign::Negative => -(self.numerator as i64),
                    })
                } else { None }
            }

            fn to_u64(&self) -> Option<u64> {
                match self.sign {
                    Sign::Positive => {
                        if self.denominator == 1 {
                            if self.numerator as u128 <= u64::MAX as u128 {
                                Some(self.numerator as u64)
                            } else { None }
                        } else {
                            None
                        }
                    }
                    Sign::Zero => Some(0),
                    Sign::Negative => None,
                }
            }

            fn to_f64(&self) -> Option<f64> {
                Some(match self.sign {
                    Sign::Positive => self.numerator as f64 / self.denominator as f64,
                    Sign::Zero => 0_f64,
                    Sign::Negative => -(self.numerator as f64 / self.denominator as f64),
                })
            }
        }

        impl From<&$name> for $name {
            #[must_use]
            #[inline]
            fn from(other: &$name) -> Self {
                *other
            }
        }

        impl NonZero for $name {
            #[must_use]
            #[inline]
            fn is_not_zero(&self) -> bool {
                self.numerator != 0
            }
        }

        impl num_traits::Zero for $name {
            #[must_use]
            #[inline]
            fn zero() -> Self {
                Self {
                    sign: Sign::Zero,
                    numerator: 0,
                    denominator: 1,
                }
            }

            #[inline]
            fn set_zero(&mut self) {
                self.sign = Sign::Zero;
                self.numerator = 0;
                self.denominator = 1;
            }

            #[must_use]
            #[inline]
            fn is_zero(&self) -> bool {
                self.sign == Sign::Zero
            }
        }

        impl NonZeroSigned for $name {
            #[must_use]
            #[inline]
            fn signum(&self) -> NonZeroSign {
                self.sign.into()
            }
        }

        impl Ord for $name {
            #[must_use]
            #[inline]
            fn cmp(&self, other: &Self) -> Ordering {
                self.partial_cmp(other).unwrap()
            }
        }

        impl PartialOrd for $name {
            #[must_use]
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                self.sign.partial_cmp(&other.sign).or_else(|| {
                    let ad = self.numerator * other.denominator;
                    let bc = self.denominator * other.numerator;
                    Some(ad.cmp(&bc))
                })
            }
        }

        impl<'a> Add<&'a $name> for &'a $name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn add(self, rhs: Self) -> Self::Output {
                Add::add(self.clone(), rhs)
            }
        }

        impl Add for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn add(mut self, rhs: Self) -> Self::Output {
                AddAssign::add_assign(&mut self, rhs);
                self
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

        impl Add<&$name> for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn add(mut self, rhs: &Self) -> Self::Output {
                AddAssign::add_assign(&mut self, rhs);
                self
            }
        }

        impl Add<$name> for &$name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn add(self, rhs: $name) -> Self::Output {
                Add::add(rhs, self)
            }
        }

        impl AddAssign<&$name> for $name {
            #[inline]
            fn add_assign(&mut self, rhs: &Self) {
                match (self.sign, rhs.sign) {
                    (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => self.add(rhs),
                    (Sign::Positive, Sign::Negative) | (Sign::Negative, Sign::Positive) => self.sub(rhs),
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

        impl AddAssign for $name {
            #[inline]
            fn add_assign(&mut self, rhs: Self) {
                AddAssign::add_assign(self, &rhs);
            }
        }

        impl Sub for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn sub(mut self, rhs: Self) -> Self::Output {
                SubAssign::sub_assign(&mut self, rhs);
                self
            }
        }

        impl<'a> Sub<&'a $name> for &'a $name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn sub(self, rhs: Self) -> Self::Output {
                Sub::sub(self.clone(), rhs)
            }
        }

        impl Sub<&$name> for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn sub(mut self, rhs: &Self) -> Self::Output {
                SubAssign::sub_assign(&mut self, rhs);
                self
            }
        }

        impl Sub<$name> for &$name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn sub(self, rhs: $name) -> Self::Output {
                -Sub::sub(rhs, self)
            }
        }

        impl SubAssign<&$name> for $name {
            #[inline]
            fn sub_assign(&mut self, rhs: &Self) {
                match (self.sign, rhs.sign) {
                    (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => self.sub(rhs),
                    (Sign::Positive, Sign::Negative) | (Sign::Negative, Sign::Positive) => self.add(rhs),
                    (_, Sign::Zero) => {},
                    (Sign::Zero, _) => {
                        *self = Self {
                            sign: !rhs.sign,
                            numerator: rhs.numerator,
                            denominator: rhs.denominator,
                        };
                    },
                }
            }
        }

        impl SubAssign for $name {
            #[inline]
            fn sub_assign(&mut self, rhs: Self) {
                SubAssign::sub_assign(self, &rhs)
            }
        }

        impl $name {
            #[inline]
            fn add(&mut self, rhs: &Self) {
                if self.denominator == rhs.denominator {
                    self.numerator += rhs.numerator;

                    // Numerator can't be zero

                    if self.numerator == self.denominator {
                        self.numerator = 1;
                        self.denominator = 1;
                    } else if self.denominator != 1 {
                        // numerator can't be 1 because two positive things were added
                        let gcd = $gcd_name(self.numerator, self.denominator);
                        self.numerator /= gcd;
                        self.denominator /= gcd;
                    }
                } else {
                    if self.denominator == 1 {
                        self.numerator *= rhs.denominator;
                        self.numerator += rhs.numerator;
                        self.denominator = rhs.denominator;
                    } else if rhs.denominator == 1 {
                        self.numerator += rhs.numerator * self.denominator;
                    } else {
                        // Neither denominator is 1
                        let gcd = $gcd_name(self.denominator, rhs.denominator);

                        self.numerator *= rhs.denominator / gcd;
                        self.denominator /= gcd;

                        self.numerator += rhs.numerator * self.denominator;
                        self.denominator *= rhs.denominator;

                        let (n, d) = $simplify_name(self.numerator, self.denominator);
                        self.numerator = n;
                        self.denominator = d;
                    }
                }
            }
            #[inline]
            fn sub(&mut self, rhs: &Self) {
                if self.denominator == rhs.denominator {
                    self.sub_direction(rhs.numerator);

                    if self.numerator == self.denominator {
                        self.numerator = 1;
                        self.denominator = 1;
                    } else if self.denominator != 1 && self.numerator != 1 {
                        let gcd = $gcd_name(self.numerator, self.denominator);
                        self.numerator /= gcd;
                        self.denominator /= gcd;
                    }
                } else {
                    if self.denominator == 1 {
                        self.numerator *= rhs.denominator;
                        self.sub_direction(rhs.numerator);
                        self.denominator = rhs.denominator;
                    } else if rhs.denominator == 1 {
                        self.sub_direction(rhs.numerator * self.denominator);
                    } else {
                        // Neither denominator is 1
                        let gcd = $gcd_name(self.denominator, rhs.denominator);

                        self.numerator *= rhs.denominator / gcd;
                        self.denominator /= gcd;

                        let rhs_numerator = rhs.numerator * self.denominator;
                        if self.numerator < rhs_numerator {
                            self.sign = !self.sign;
                            self.numerator = rhs_numerator - self.numerator;
                        } else {
                            // larger than, not zero
                            self.numerator -= rhs_numerator;
                        }
                        self.denominator *= rhs.denominator;

                        let (n, d) = $simplify_name(self.numerator, self.denominator);
                        self.numerator = n;
                        self.denominator = d;
                    }
                }
            }
            #[inline]
            fn sub_direction(&mut self, rhs_numerator: $uty) {
                match self.numerator.cmp(&rhs_numerator) {
                    Ordering::Less => {
                        self.sign = !self.sign;
                        self.numerator = rhs_numerator - self.numerator;
                    }
                    Ordering::Equal => <Self as num_traits::Zero>::set_zero(self),
                    Ordering::Greater => {
                        self.numerator -= rhs_numerator;
                    }
                }
            }
        }

        impl num_traits::One for $name {
            #[must_use]
            #[inline]
            fn one() -> Self {
                Self {
                    sign: Sign::Positive,
                    numerator: 1,
                    denominator: 1,
                }
            }

            #[inline]
            fn set_one(&mut self) {
                self.sign = Sign::Positive;
                self.numerator = 1;
                self.denominator = 1;
            }

            #[must_use]
            #[inline]
            fn is_one(&self) -> bool {
                self.numerator == 1 && self.denominator == 1 && self.sign == Sign::Positive
            }
        }

        impl Mul<&$name> for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn mul(mut self, rhs: &Self) -> Self::Output {
                MulAssign::mul_assign(&mut self, rhs);
                self
            }
        }

        impl<'a> Mul<&'a $name> for &'a $name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn mul(self, rhs: Self) -> Self::Output {
                Mul::mul(self.clone(), rhs)
            }
        }

        impl Mul for $name {
            type Output = Self;

            #[must_use]
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

            #[must_use]
            #[inline]
            fn mul(self, rhs: $name) -> Self::Output {
                Mul::mul(rhs, self)
            }
        }

        impl MulAssign<&$name> for $name {
            #[inline]
            fn mul_assign(&mut self, rhs: &Self) {
                match (self.sign, rhs.sign) {
                    (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                        self.sign *= rhs.sign;
                        self.mul(rhs.numerator, rhs.denominator);
                    }
                    (Sign::Zero, _) => {}
                    (_, Sign::Zero) => <Self as num_traits::Zero>::set_zero(self),
                }
            }
        }

        impl Div for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn div(mut self, rhs: Self) -> Self::Output {
                DivAssign::div_assign(&mut self, rhs);
                self
            }
        }

        impl Div<&$name> for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn div(mut self, rhs: &Self) -> Self::Output {
                DivAssign::div_assign(&mut self, rhs);
                self
            }
        }

        impl<'a> Div<&'a $name> for &'a $name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn div(self, rhs: Self) -> Self::Output {
                Div::div(self.clone(), rhs)
            }
        }

        impl Div<$name> for &$name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn div(self, mut rhs: $name) -> Self::Output {
                match (self.sign, rhs.sign) {
                    (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                        let sign = self.sign * rhs.sign;
                        <$name>::mul(&mut rhs, self.denominator, self.numerator);
                        Self::Output {
                            sign,
                            numerator: rhs.denominator,
                            denominator: rhs.numerator,
                        }
                    }
                    (_, Sign::Zero) => panic!(),
                    (Sign::Zero, _) => {
                        <$name as num_traits::Zero>::zero()
                    }
                }
            }
        }

        impl DivAssign for $name {
            #[inline]
            fn div_assign(&mut self, rhs: Self) {
                DivAssign::div_assign(self, &rhs);
            }
        }

        impl DivAssign<&$name> for $name {
            #[inline]
            fn div_assign(&mut self, rhs: &Self) {
                match (self.sign, rhs.sign) {
                    (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                        self.sign *= rhs.sign;
                        self.mul(rhs.denominator, rhs.numerator);
                    }
                    (_, Sign::Zero) => panic!(),
                    (Sign::Zero, _) => {}
                }
            }
        }

        impl $name {
            #[inline]
            fn mul(&mut self, mut rhs_numerator: $uty, mut rhs_denominator: $uty) {
                if self.numerator != 1 && rhs_denominator != 1 {
                    if self.numerator == rhs_denominator {
                        self.numerator = rhs_numerator;
                        let (n, d) = $simplify_name(self.numerator, self.denominator);
                        self.numerator = n;
                        self.denominator = d;
                        return
                    }

                    let gcd_ad = $gcd_name(self.numerator, rhs_denominator);
                    debug_assert!(gcd_ad > 0);
                    self.numerator /= gcd_ad;
                    rhs_denominator /= gcd_ad;
                }

                if rhs_numerator != 1 && self.denominator != 1 {
                    if rhs_numerator == self.denominator {
                        self.denominator = rhs_denominator;
                        let (n, d) = $simplify_name(self.numerator, self.denominator);
                        self.numerator = n;
                        self.denominator = d;
                        return
                    }

                    let gcd_bc = $gcd_name(self.denominator, rhs_numerator);
                    debug_assert!(gcd_bc > 0);
                    rhs_numerator /= gcd_bc;
                    self.denominator /= gcd_bc;
                }

                self.numerator *= rhs_numerator;
                self.denominator *= rhs_denominator;
            }
        }

        impl Neg for $name {
            type Output = Self;

            #[must_use]
            #[inline]
            fn neg(mut self) -> Self::Output {
                self.sign = !self.sign;
                self
            }
        }

        impl Neg for &$name {
            type Output = $name;

            #[must_use]
            #[inline]
            fn neg(self) -> Self::Output {
                Self::Output {
                    sign: !self.sign,
                    numerator: self.numerator,
                    denominator: self.denominator,
                }
            }
        }

        #[inline]
        pub fn $simplify_name(numerator: $uty, denominator: $uty) -> ($uty, $uty) {
            debug_assert_ne!(numerator, 0);
            debug_assert_ne!(denominator, 0);

            if numerator == 1 || denominator == 1 {
                (numerator, denominator)
            } else {
                let gcd = $gcd_name(numerator, denominator);
                (numerator / gcd, denominator / gcd)
            }
        }

        #[inline]
        fn $gcd_name(mut left: $uty, mut right: $uty) -> $uty {
            debug_assert_ne!(left, 0);
            debug_assert_ne!(right, 0);
            debug_assert_ne!(left, 1);
            debug_assert_ne!(right, 1);

            let left_trailing = left.trailing_zeros();
            let right_trailing = right.trailing_zeros();
            let min_trailing = min(left_trailing, right_trailing);

            left >>= left_trailing;
            right >>= right_trailing;

            loop {
                debug_assert_eq!(left % 2, 1);
                debug_assert_eq!(left % 2, 1);

                if left == right {
                    break left << min_trailing
                }

                if left > right {
                    mem::swap(&mut left, &mut right);
                }

                right -= left;

                right >>= right.trailing_zeros();
            }
        }

        impl Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                match self.sign {
                    Sign::Positive => {}
                    Sign::Zero => return write!(f, "0"),
                    Sign::Negative => {
                        write!(f, "-")?;
                    }
                }

                write!(f, "{}", self.numerator)?;
                if self.denominator != 1 {
                    write!(f, "/")?;
                    write!(f, "{}", self.denominator)?;
                }

                fmt::Result::Ok(())
            }
        }
    }
}

rational!(Rational8, i8, u8, gcd8, simplify8);
rational!(Rational16, i16, u16, gcd16, simplify16);
rational!(Rational32, i32, u32, gcd32, simplify32);
rational!(Rational64, i64, u64, gcd64, simplify64);
rational!(Rational128, i128, u128, gcd128, simplify128);

macro_rules! size_depedent_unsigned {
    ($name:ty, $uty:ty, $other:ty) => {
        impl From<$other> for $name {
            #[must_use]
            #[inline]
            fn from(other: $other) -> Self {
                Self {
                    sign: Signed::signum(&other),
                    numerator: other as $uty,
                    denominator: 1,
                }
            }
        }
        impl From<&$other> for $name {
            #[must_use]
            #[inline]
            fn from(other: &$other) -> Self {
                Self {
                    sign: Signed::signum(other),
                    numerator: *other as $uty,
                    denominator: 1,
                }
            }
        }
        impl From<($other, $other)> for $name {
            #[must_use]
            #[inline]
            fn from(other: ($other, $other)) -> Self {
                debug_assert_ne!(other.1, 0);

                Self {
                    sign: Signed::signum(&other.0) * Signed::signum(&other.1),
                    numerator: other.0 as $uty,
                    denominator: other.1 as $uty,
                }
            }
        }
    }
}

size_depedent_unsigned!(Rational8, u8, u8);
size_depedent_unsigned!(Rational16, u16, u8);
size_depedent_unsigned!(Rational16, u16, u16);
size_depedent_unsigned!(Rational32, u32, u8);
size_depedent_unsigned!(Rational32, u32, u16);
size_depedent_unsigned!(Rational32, u32, u32);
size_depedent_unsigned!(Rational64, u64, u8);
size_depedent_unsigned!(Rational64, u64, u16);
size_depedent_unsigned!(Rational64, u64, u32);
size_depedent_unsigned!(Rational64, u64, u64);
size_depedent_unsigned!(Rational128, u128, u8);
size_depedent_unsigned!(Rational128, u128, u16);
size_depedent_unsigned!(Rational128, u128, u32);
size_depedent_unsigned!(Rational128, u128, u64);
size_depedent_unsigned!(Rational128, u128, u128);

macro_rules! size_depedent_signed {
    ($name:ty, $uty:ty, $other_signed:ty) => {
        impl From<$other_signed> for $name {
            #[must_use]
            #[inline]
            fn from(other: $other_signed) -> Self {
                Self {
                    sign: Signed::signum(&other),
                    numerator: other.unsigned_abs() as $uty,
                    denominator: 1,
                }
            }
        }
        impl From<&$other_signed> for $name {
            #[must_use]
            #[inline]
            fn from(other: &$other_signed) -> Self {
                Self {
                    sign: Signed::signum(other),
                    numerator: other.unsigned_abs() as $uty,
                    denominator: 1,
                }
            }
        }
        impl From<($other_signed, $other_signed)> for $name {
            #[must_use]
            #[inline]
            fn from(other: ($other_signed, $other_signed)) -> Self {
                debug_assert_ne!(other.1, 0);

                Self {
                    sign: Signed::signum(&other.0) * Signed::signum(&other.1),
                    numerator: other.0.unsigned_abs() as $uty,
                    denominator: other.1.unsigned_abs() as $uty,
                }
            }
        }
    }
}

size_depedent_signed!(Rational8, u8, i8);
size_depedent_signed!(Rational16, u16, i8);
size_depedent_signed!(Rational16, u16, i16);
size_depedent_signed!(Rational32, u32, i8);
size_depedent_signed!(Rational32, u32, i16);
size_depedent_signed!(Rational32, u32, i32);
size_depedent_signed!(Rational64, u64, i8);
size_depedent_signed!(Rational64, u64, i16);
size_depedent_signed!(Rational64, u64, i32);
size_depedent_signed!(Rational64, u64, i64);
size_depedent_signed!(Rational128, u128, i8);
size_depedent_signed!(Rational128, u128, i16);
size_depedent_signed!(Rational128, u128, i32);
size_depedent_signed!(Rational128, u128, i64);
size_depedent_signed!(Rational128, u128, i128);

#[cfg(test)]
mod test {
    use std::cmp::Ordering;

    use num_traits::{FromPrimitive, One, ToPrimitive, Zero};

    use crate::{NonZero, NonZeroSign, NonZeroSigned, Rational128};
    use crate::{R16, R32, R64, R8};
    use crate::rational::{Ratio, Rational16, Rational32, Rational64, Rational8, Sign};

    #[test]
    fn test_new() {
        let a = Rational8::new(0, 2);
        assert_eq!(a, Ratio { sign: Sign::Zero, numerator: 0_u8, denominator: 1 });

        let a = Rational16::new(2, 2);
        assert_eq!(a, Ratio { sign: Sign::Positive, numerator: 1, denominator: 1 });

        let a = Rational32::new(6, 2);
        assert_eq!(a, Ratio { sign: Sign::Positive, numerator: 3, denominator: 1 });

        let a = Rational64::new(-6, 2);
        assert_eq!(a, Ratio { sign: Sign::Negative, numerator: 3, denominator: 1 });
    }

    #[test]
    fn test_from() {
        assert_eq!(<Rational8 as From<_>>::from(1_u8), Rational8::one());
        assert_eq!(<Rational32 as From<_>>::from(1), Rational32::one());

        assert_eq!(FromPrimitive::from_u64(16), Some(Rational8::new(16, 1)));
        assert_eq!(FromPrimitive::from_u16(0), Some(Rational8::zero()));
        assert_eq!(<Rational16 as FromPrimitive>::from_u32(u32::MAX), None);
        assert_eq!(FromPrimitive::from_i32(i32::MAX), Some(Rational32::new(i32::MAX, 1)));
        assert_eq!(<Rational64 as FromPrimitive>::from_i128(i128::MAX), None);
        assert_eq!(FromPrimitive::from_i16(-1), Some(Rational8::new(-2, 2)));

        assert_eq!(<Rational128 as FromPrimitive>::from_f64(f64::NAN), None);
        assert_eq!(<Rational64 as FromPrimitive>::from_f64(f64::INFINITY), None);
        assert_eq!(<Rational32 as FromPrimitive>::from_f64(f64::NEG_INFINITY), None);
        assert_eq!(FromPrimitive::from_f64(-0_f64), Some(Rational8::zero()));
        // u128::MAX gets rounded upwards in f64 conversion
        assert!(<Rational128 as FromPrimitive>::from_f64(u128::MAX as f64).is_none());

        assert_eq!(<Rational32 as FromPrimitive>::from_i64(i64::MAX), None);

        assert_eq!(Rational64::from((-1, 2)), R64!(-1, 2));
    }

    #[test]
    fn test_to() {
        assert_eq!(Rational8::new(1, 1).to_i32(), Some(1));
        assert_eq!(R8!(-10).to_i32(), Some(-10));
        assert_eq!(R8!(-11).to_u16(), None);
        assert_eq!(R32!(-156, 99).to_f64(), Some(-156_f64 / 99_f64));
        assert_eq!(R64!(2_u64.pow(63) + 2_u64.pow(20)).to_i64(), None);
        assert_eq!(R8!(0).to_i64(), Some(0));
        assert_eq!(R8!(0).to_u64(), Some(0));
        assert_eq!(R8!(1, 2).to_u64(), None);
        assert_eq!(R8!(8).to_u64(), Some(8));
        assert_eq!(R8!(0).to_f64(), Some(0_f64));
    }

    #[test]
    fn test_nonzero() {
        assert!(!Rational8::zero().is_not_zero());
        assert_eq!(Rational16::zero().is_zero(), !Rational16::zero().is_not_zero());

        assert_eq!(R8!(1).signum(), NonZeroSign::Positive);
    }

    #[test]
    #[should_panic]
    fn test_sign_panic() {
        R8!(0).signum();
    }

    #[test]
    fn test_one() {
        assert!(Rational64::zero() < Rational64::one());
        assert!(Rational64::one().is_one());
        let mut x = Rational32::zero();
        x.set_one();
        assert_eq!(x, Rational32::one());
    }

    #[test]
    fn test_cmp() {
        assert!(R8!(12) < R8!(13));
        assert!(R8!(1, 2) > R8!(1, 3));
        assert_eq!(R8!(7, 11), R8!(7, 11));
        assert!(R8!(3, 4) < R8!(5, 6));
        assert!(R8!(13) > R8!(12));
        assert_eq!(R32!(0), R32!(0));
        assert_eq!(R32!(0).partial_cmp(&R32!(0)), Some(Ordering::Equal));
        assert_eq!(R32!(12, 5).partial_cmp(&R32!(23, 10)), Some(Ordering::Greater));
        assert!(!(R32!(7, 11) < R32!(7, 11)));
        assert!(R64!(-3, 11) < R64!(3, 11));
        assert_ne!(R64!(-9, 4), R64!(9, 4));
    }

    #[test]
    fn test_add() {
        assert_eq!(Rational64::one() + Rational64::one(), R64!(2));
        assert_eq!(R64!(3, 2) + R64!(3, 2), R64!(3));
        assert_eq!(R64!(-3, 2) + R64!(3, 2), Rational64::zero());
        assert_eq!(R64!(948, 64) + Rational64::zero(), R64!(948, 64));
        assert_eq!(-Rational64::one() + Rational64::one(), Rational64::zero());
        assert_eq!(Rational128::zero() + Rational128::one(), Rational128::one());
        assert_eq!(Rational128::zero() + -Rational128::one(), -Rational128::one());

        assert_eq!(&R32!(3, 9) + &R32!(-1, 3), R32!(0));
        assert_eq!(R8!(4, 5) + R8!(1, 5), R8!(1));
        assert_eq!(R8!(5, 1) + R8!(3, 2), R8!(13, 2));
        assert_eq!(R8!(3, 4) + R8!(3), R8!(15, 4));
        assert_eq!(R8!(3, 4) + R8!(17, 5), R8!(83, 20));
        assert_eq!(R32!(3, 4) + R32!(3, 32), R32!(27, 32));
        assert_eq!(R32!(-10) + R32!(9), R32!(-1));

        let limit = 10;
        for a in -limit..limit {
            for b in 1..limit {
                for c in -limit..limit {
                    for d in 1..limit {
                        assert_eq!(R32!(a, b as u32) + R32!(c, d as u32), R32!(a * d + c * b, b as u32 * d as u32), "{} / {} + {} / {}", a, b, c, d);
                    }
                }
            }
        }
    }

    #[test]
    fn test_sum() {
        assert_eq!((0..10).map(Rational32::from).sum::<Rational32>(), R32!(45));
        assert_eq!((0_i16..10).map(|i| Rational16::new(i, 2)).sum::<Rational16>(), R16!(45, 2));
        let vs = vec![
            (R32!(23, 31), R32!(-699, 65)),
            (R32!(29, 31), R32!(-30736, 1885)),
        ];
        let product = vs.into_iter().map(|(a, b)| &a * &b).sum::<Rational32>();
        let constant = R32!(-2826, 155);
        assert_eq!(constant - product, R32!(5));
    }

    #[test]
    fn test_sub() {
        assert_eq!(Rational64::one() - Rational64::one(), R64!(0));
        assert_eq!(R64!(3, 2) - R64!(3, 2), R64!(0));
        assert_eq!(R64!(-3, 2) - R64!(3, 2), -R64!(3));
        assert_eq!(R64!(948, 64) - Rational64::zero(), R64!(948, 64));
        assert_eq!(-Rational64::one() - Rational64::one(), -R64!(2));
        assert_eq!(Rational64::one() - Rational64::one(), -R64!(0));
        assert_eq!(Rational128::zero() - Rational128::one(), -Rational128::one());
        assert_eq!(Rational128::zero() - -Rational128::one(), Rational128::one());

        assert_eq!(&R32!(3, 9) - &R32!(1, 3), R32!(0));
        assert_eq!(R8!(4, 5) - R8!(1, 5), R8!(3, 5));
        assert_eq!(R8!(5, 1) - R8!(3, 2), R8!(7, 2));
        assert_eq!(R8!(3, 4) - R8!(3), R8!(-9, 4));
        assert_eq!(R8!(3, 4) - R8!(17, 5), R8!(15 - 4 * 17, 20));
        assert_eq!(R8!(17, 5) - R8!(3, 4), R8!(4 * 17 - 15, 20));

        assert_eq!(R32!(3601, 155) - R32!(2826, 155), R32!(5));
        assert_eq!(R32!(-2826, 155) - R32!(-3601, 155), R32!(5));

        let limit = 10;
        for a in -limit..limit {
            for b in 1..limit {
                for c in -limit..limit {
                    for d in 1..limit {
                        assert_eq!(R32!(a, b as u32) - R32!(c, d as u32), R32!(a * d - c * b, b as u32 * d as u32), "{} / {} - {} / {}", a, b, c, d);
                    }
                }
            }
        }
    }

    #[test]
    fn test_mul() {
        assert_eq!(Rational64::one() * Rational64::one(), R64!(1));
        assert_eq!(R64!(3, 2) * R64!(3, 2), R64!(9, 4));
        assert_eq!(R64!(-3, 2) * R64!(3, 2), -R64!(9, 4));
        assert_eq!(R64!(948, 64) * Rational64::zero(), R64!(0));
        assert_eq!(-Rational64::one() * Rational64::one(), -R64!(1));
        assert_eq!(Rational64::one() * Rational64::one(), R64!(1));
        assert_eq!(Rational128::zero() * Rational128::one(), -Rational128::zero());
        assert_eq!(Rational128::zero() * -Rational128::one(), Rational128::zero());

        assert_eq!(R8!(3, 2) * R8!(4, 9), R8!(2, 3));
        assert_eq!(R32!(27, 32) * R32!(2), R32!(27, 16));

        let limit = 10;
        for a in -limit..limit {
            for b in 1..limit {
                for c in -limit..limit {
                    for d in 1..limit {
                        assert_eq!(R32!(a, b as u32) * R32!(c, d as u32), R32!(a * c, b as u32 * d as u32), "{} / {} * {} / {}", a, b, c, d);
                    }
                }
            }
        }
    }

    #[test]
    fn test_div() {
        assert_eq!(Rational64::one() / Rational64::one(), R64!(1));
        assert_eq!(R64!(3, 2) / R64!(3, 2), R64!(1));
        assert_eq!(R64!(-3, 2) / R64!(3, 2), -R64!(1));
        assert_eq!(-Rational64::one() / Rational64::one(), -R64!(1));
        assert_eq!(Rational128::zero() / Rational128::one(), -Rational128::zero());
        assert_eq!(Rational128::zero() / -Rational128::one(), Rational128::zero());
    }

    #[test]
    fn test_new_signed() {
        assert_eq!(Rational64::new_signed(Sign::Positive, 6, 18), R64!(1, 3));
        assert_eq!(Rational64::new_signed(Sign::Zero, 0, 6), R64!(0));
        assert_eq!(Rational64::new_signed(Sign::Negative, 9, 18), -R64!(1, 2));
    }

    #[test]
    #[should_panic]
    fn test_new_signed_panic_1() {
        Rational64::new_signed(Sign::Zero, 1, 1);
    }

    #[test]
    #[should_panic]
    fn test_new_signed_panic_2() {
        Rational64::new_signed(Sign::Positive, 0, 1);
    }

    #[test]
    fn test_display() {
        assert_eq!(Rational64::one().to_string(), "1");
        assert_eq!(Rational64::zero().to_string(), "0");
        assert_eq!(R64!(1, 2).to_string(), "1/2");
        assert_eq!(R64!(-1, 2).to_string(), "-1/2");
    }
}
