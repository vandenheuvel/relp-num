//! # Rational types of fixed size
use std::cmp::{min, Ordering};
use std::fmt;
use std::fmt::Display;
use std::iter::Sum;
use std::mem;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::option::Option::Some;

use num_traits;

use crate::non_zero::{NonZero, NonZeroSign, NonZeroSigned};
use crate::rational::big::Big8;
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

                match sign {
                    Sign::Positive => debug_assert_ne!(numerator, 0),
                    Sign::Zero => debug_assert_eq!(numerator, 0),
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
                        sign: Sign::Positive,
                        numerator: n as $uty,
                        denominator: 1,
                    })
                } else {
                    None
                }
            }

            #[must_use]
            #[inline]
            fn from_f64(n: f64) -> Option<Self> {
                Big8::from_f64(n).map(|big| {
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
                }).flatten()
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
                Sub::sub(rhs, self)
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
                        <Self as num_traits::One>::set_one(self);
                    } else if self.denominator != 1 {
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
                        let gcd = $gcd_name(self.numerator, self.denominator);
                        let lcm = self.denominator * (rhs.denominator / gcd);

                        self.numerator *= lcm / self.denominator;
                        let rhs_numerator = rhs.numerator * (lcm / rhs.denominator);

                        self.numerator += rhs_numerator;
                        self.denominator = lcm;
                    }
                }
            }
            #[inline]
            fn sub(&mut self, rhs: &Self) {
                if self.denominator == rhs.denominator {
                    self.sub_direction(&rhs.numerator);

                    if self.numerator == self.denominator {
                        <Self as num_traits::One>::set_one(self);
                    } else if self.denominator != 1 {
                        let gcd = $gcd_name(self.numerator, self.denominator);
                        self.numerator /= gcd;
                        self.denominator /= gcd;
                    }
                } else {
                    if self.denominator == 1 {
                        self.numerator *= rhs.denominator;
                        self.sub_direction(&rhs.numerator);
                    } else if rhs.denominator == 1 {
                        self.sub_direction(&(rhs.numerator * self.denominator));
                    } else {
                        // Neither denominator is 1
                        let gcd = $gcd_name(self.numerator, self.denominator);
                        let lcm = self.denominator * (rhs.denominator / gcd);

                        self.numerator *= lcm / self.denominator;
                        let rhs_numerator = rhs.numerator * (lcm / rhs.denominator);

                        self.sub_direction(&rhs_numerator);
                        self.denominator = lcm;
                    }
                }
            }
            #[inline]
            fn sub_direction(&mut self, rhs_numerator: &$uty) {
                match self.numerator.cmp(rhs_numerator) {
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
                write!(f, "/")?;
                write!(f, "{}", self.denominator)
            }
        }
    }
}

rational!(Rational8, i8, u8, gcd8, simplify8);
rational!(Rational16, i16, u16, gcd16, simplify16);
rational!(Rational32, i32, u32, gcd32, simplify32);
rational!(Rational64, i64, u64, gcd64, simplify64);
rational!(Rational128, i128, u128, gcd128, simplify128);

#[cfg(test)]
mod test {
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
}
