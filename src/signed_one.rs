//! # Signed One
//!
//! A type that is always one or minus one.
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::{Negateable, NonZero, Sign, Signed};

/// # SignedOne
///
/// A number that is either `1` or `-1`, stored in a single byte.
///
/// Can be used when a type from the `MatrixProvider` can only have the value `1` or `-1`, such as
/// with some network problems, where an arc is either incoming or outgoing. The incidence matrix of
/// a network holds nothing but these two values, and storing a rational number for each of them
/// wastes both space and time. This type stores the coefficient in a byte and lets
/// [`Absorb`](crate::Absorb) apply it to a wide accumulator directly: multiplying by `PlusOne` is a
/// clone, multiplying by `MinusOne` is a clone and a sign flip, never a multiplication.
///
/// The variants are *not* declared in increasing numeric order, so the derived [`Ord`] would be
/// wrong; the impl below compares the discriminants instead, like [`Sign`] does.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Default)]
pub enum SignedOne {
    /// +1.
    #[default]
    PlusOne = 1,
    /// -1.
    MinusOne = -1,
}

impl num_traits::One for SignedOne {
    #[inline]
    fn one() -> Self {
        Self::PlusOne
    }
}

impl Mul<SignedOne> for SignedOne {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: SignedOne) -> Self::Output {
        match (self, rhs) {
            (Self::PlusOne, Self::PlusOne) => Self::PlusOne,
            (Self::PlusOne, Self::MinusOne) => Self::MinusOne,
            (Self::MinusOne, Self::PlusOne) => Self::MinusOne,
            (Self::MinusOne, Self::MinusOne) => Self::PlusOne,
        }
    }
}

/// This type is positive or negative; it is never zero.
impl Signed for SignedOne {
    #[inline]
    fn signum(&self) -> Sign {
        match self {
            SignedOne::PlusOne => Sign::Positive,
            SignedOne::MinusOne => Sign::Negative,
        }
    }
}

/// Both negations are representable: `PlusOne` and `MinusOne` are each other's additive inverse.
impl Negateable for SignedOne {
    #[inline]
    fn negate(&mut self) {
        *self = match self {
            SignedOne::PlusOne => SignedOne::MinusOne,
            SignedOne::MinusOne => SignedOne::PlusOne,
        };
    }
}

impl Neg for SignedOne {
    type Output = Self;

    #[inline]
    fn neg(mut self) -> Self::Output {
        Negateable::negate(&mut self);
        self
    }
}

impl NonZero for SignedOne {
    #[inline]
    fn is_not_zero(&self) -> bool {
        true
    }
}

/// The variants are declared with `PlusOne` first, so a derived `Ord` would order `PlusOne` before
/// `MinusOne`. Compare the discriminants instead, which gives `MinusOne < PlusOne`.
impl Ord for SignedOne {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        (*self as i8).cmp(&(*other as i8))
    }
}

impl PartialOrd for SignedOne {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Debug forwards to `Display`, because `1` and `-1` read better in test output than the variant
/// names.
impl fmt::Debug for SignedOne {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self, f)
    }
}

impl fmt::Display for SignedOne {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SignedOne::PlusOne => f.write_str("1"),
            SignedOne::MinusOne => f.write_str("-1"),
        }
    }
}

macro_rules! define_signed_ops {
    ($primitive:ident) => {
        impl From<SignedOne> for $primitive {
            fn from(rhs: SignedOne) -> Self {
                match rhs {
                    SignedOne::PlusOne => 1,
                    SignedOne::MinusOne => -1,
                }
            }
        }

        impl From<&SignedOne> for $primitive {
            fn from(rhs: &SignedOne) -> Self {
                match rhs {
                    SignedOne::PlusOne => 1,
                    SignedOne::MinusOne => -1,
                }
            }
        }

        impl Mul<SignedOne> for $primitive {
            type Output = Self;

            fn mul(mut self, rhs: SignedOne) -> Self::Output {
                MulAssign::mul_assign(&mut self, rhs);
                self
            }
        }

        impl Mul<&SignedOne> for $primitive {
            type Output = Self;

            fn mul(mut self, rhs: &SignedOne) -> Self::Output {
                MulAssign::mul_assign(&mut self, rhs);
                self
            }
        }

        impl Mul<&SignedOne> for &$primitive {
            type Output = $primitive;

            fn mul(self, rhs: &SignedOne) -> Self::Output {
                match rhs {
                    SignedOne::PlusOne => *self,
                    SignedOne::MinusOne => -self,
                }
            }
        }

        impl MulAssign<&SignedOne> for $primitive {
            fn mul_assign(&mut self, rhs: &SignedOne) {
                MulAssign::mul_assign(self, *rhs);
            }
        }

        impl MulAssign<SignedOne> for $primitive {
            fn mul_assign(&mut self, rhs: SignedOne) {
                match rhs {
                    SignedOne::PlusOne => {},
                    SignedOne::MinusOne => *self = -*self,
                }
            }
        }

        impl Div<SignedOne> for $primitive {
            type Output = Self;

            fn div(mut self, rhs: SignedOne) -> Self::Output {
                MulAssign::mul_assign(&mut self, rhs);
                self
            }
        }

        impl Div<&SignedOne> for $primitive {
            type Output = Self;

            fn div(mut self, rhs: &SignedOne) -> Self::Output {
                MulAssign::mul_assign(&mut self, rhs);
                self
            }
        }

        impl DivAssign<&SignedOne> for $primitive {
            fn div_assign(&mut self, rhs: &SignedOne) {
                DivAssign::div_assign(self, *rhs);
            }
        }

        impl DivAssign<SignedOne> for $primitive {
            fn div_assign(&mut self, rhs: SignedOne) {
                MulAssign::mul_assign(self, rhs);
            }
        }
    }
}

macro_rules! define_unsigned_ops {
    ($primitive:ident) => {
        impl Add<SignedOne> for $primitive {
            type Output = Self;

            fn add(mut self, rhs: SignedOne) -> Self::Output {
                AddAssign::add_assign(&mut self, rhs);
                self
            }
        }

        impl Add<&SignedOne> for $primitive {
            type Output = Self;

            fn add(mut self, rhs: &SignedOne) -> Self::Output {
                AddAssign::add_assign(&mut self, rhs);
                self
            }
        }

        impl AddAssign<&SignedOne> for $primitive {
            fn add_assign(&mut self, rhs: &SignedOne) {
                AddAssign::add_assign(self, *rhs);
            }
        }

        impl AddAssign<SignedOne> for $primitive {
            fn add_assign(&mut self, rhs: SignedOne) {
                match rhs {
                    SignedOne::PlusOne => *self += 1,
                    SignedOne::MinusOne => *self -= 1,
                }
            }
        }

        impl Sub<SignedOne> for $primitive {
            type Output = Self;

            fn sub(mut self, rhs: SignedOne) -> Self::Output {
                SubAssign::sub_assign(&mut self, rhs);
                self
            }
        }

        impl Sub<&SignedOne> for $primitive {
            type Output = Self;

            fn sub(mut self, rhs: &SignedOne) -> Self::Output {
                SubAssign::sub_assign(&mut self, rhs);
                self
            }
        }

        impl SubAssign<&SignedOne> for $primitive {
            fn sub_assign(&mut self, rhs: &SignedOne) {
                SubAssign::sub_assign(self, *rhs);
            }
        }

        impl SubAssign<SignedOne> for $primitive {
            fn sub_assign(&mut self, rhs: SignedOne) {
                match rhs {
                    SignedOne::PlusOne => *self -= 1,
                    SignedOne::MinusOne => *self += 1,
                }
            }
        }
    }
}

define_signed_ops!(i8);
define_signed_ops!(i16);
define_signed_ops!(i32);
define_signed_ops!(i64);
define_signed_ops!(i128);
define_unsigned_ops!(i8);
define_unsigned_ops!(i16);
define_unsigned_ops!(i32);
define_unsigned_ops!(i64);
define_unsigned_ops!(i128);

define_unsigned_ops!(u8);
define_unsigned_ops!(u16);
define_unsigned_ops!(u32);
define_unsigned_ops!(u64);
define_unsigned_ops!(u128);

#[cfg(test)]
mod test {
    use std::cmp::Ordering;

    use crate::{Negateable, NonZero, Sign, Signed};
    use crate::fixed::SignedOne;

    #[test]
    fn test_signed_one() {
        assert_eq!(<SignedOne as num_traits::One>::one(), SignedOne::PlusOne);
        assert_eq!(SignedOne::PlusOne * SignedOne::PlusOne, SignedOne::PlusOne);
        assert_eq!(SignedOne::PlusOne * SignedOne::MinusOne, SignedOne::MinusOne);
        assert_eq!(SignedOne::MinusOne * SignedOne::MinusOne, SignedOne::PlusOne);
    }

    #[test]
    fn test_default() {
        assert_eq!(SignedOne::default(), SignedOne::PlusOne);
    }

    #[test]
    fn test_signum() {
        assert_eq!(SignedOne::PlusOne.signum(), Sign::Positive);
        assert_eq!(SignedOne::MinusOne.signum(), Sign::Negative);
        assert!(SignedOne::PlusOne.is_positive());
        assert!(!SignedOne::MinusOne.is_positive());
        assert!(SignedOne::MinusOne.is_negative());
        assert!(!SignedOne::PlusOne.is_negative());
    }

    #[test]
    fn test_non_zero() {
        assert!(SignedOne::PlusOne.is_not_zero());
        assert!(SignedOne::MinusOne.is_not_zero());
    }

    #[test]
    fn test_negate() {
        assert_eq!(-SignedOne::PlusOne, SignedOne::MinusOne);
        assert_eq!(-SignedOne::MinusOne, SignedOne::PlusOne);

        let mut value = SignedOne::PlusOne;
        value.negate();
        assert_eq!(value, SignedOne::MinusOne);
        value.negate();
        assert_eq!(value, SignedOne::PlusOne);
    }

    /// A derived `Ord` would get this backwards, because `PlusOne` is declared first.
    #[test]
    fn test_ord() {
        assert_eq!(SignedOne::MinusOne.cmp(&SignedOne::PlusOne), Ordering::Less);
        assert_eq!(SignedOne::PlusOne.cmp(&SignedOne::MinusOne), Ordering::Greater);
        assert!(SignedOne::MinusOne < SignedOne::PlusOne);

        for a in [SignedOne::MinusOne, SignedOne::PlusOne] {
            assert_eq!(a.cmp(&a), Ordering::Equal);
            for b in [SignedOne::MinusOne, SignedOne::PlusOne] {
                assert_eq!(a.partial_cmp(&b), Some(a.cmp(&b)));
                assert_eq!(a.cmp(&b), b.cmp(&a).reverse());
                assert_eq!(a == b, a.cmp(&b) == Ordering::Equal);
            }
        }
    }

    #[test]
    fn test_display() {
        assert_eq!(SignedOne::PlusOne.to_string(), "1");
        assert_eq!(SignedOne::MinusOne.to_string(), "-1");
        assert_eq!(format!("{:?}", SignedOne::PlusOne), "1");
        assert_eq!(format!("{:?}", SignedOne::MinusOne), "-1");
    }

    #[test]
    fn test_integer() {
        assert_eq!(1 + SignedOne::PlusOne, 2);
        assert_eq!(-1 + SignedOne::PlusOne, 0);
        assert_eq!(1 + SignedOne::PlusOne, 2);
        assert_eq!(-1 + SignedOne::PlusOne, 0);
        assert_eq!(33 / SignedOne::PlusOne, 33);
        assert_eq!(-33 / &SignedOne::PlusOne, -33);
        assert_eq!(894 * SignedOne::PlusOne, 894);
        assert_eq!(-894 * &SignedOne::PlusOne, -894);

        assert_eq!(1 + SignedOne::MinusOne, 0);
        assert_eq!(-1 + SignedOne::MinusOne, -2);
        assert_eq!(1 - SignedOne::MinusOne, 2);
        assert_eq!(-1 - SignedOne::MinusOne, 0);
        assert_eq!(33 / SignedOne::MinusOne, -33);
        assert_eq!(-33 / &SignedOne::MinusOne, 33);
        assert_eq!(894 * SignedOne::MinusOne, -894);
        assert_eq!(-894 * &SignedOne::MinusOne, 894);
    }
}
