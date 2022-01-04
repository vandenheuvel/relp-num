//! # Signed One
use std::fmt;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

use crate::NonZero;

/// A type representing the value `1` or `-1`.
///
/// Can be used when a type from the `MatrixProvider` can only have the value `1` or `-1`, such as
/// with some network problems, where an arc is either incoming or outgoing.
#[derive(Eq, PartialEq, Copy, Clone)]
pub enum SignedOne {
    /// +1.
    PlusOne,
    /// -1.
    MinusOne,
}

impl num_traits::One for SignedOne {
    #[inline]
    #[must_use]
    fn one() -> Self {
        Self::PlusOne
    }
}

impl Default for SignedOne {
    fn default() -> Self {
        SignedOne::PlusOne
    }
}

impl Mul<SignedOne> for SignedOne {
    type Output = Self;

    #[inline]
    #[must_use]
    fn mul(self, rhs: SignedOne) -> Self::Output {
        match (self, rhs) {
            (Self::PlusOne, Self::PlusOne) => Self::PlusOne,
            (Self::PlusOne, Self::MinusOne) => Self::MinusOne,
            (Self::MinusOne, Self::PlusOne) => Self::MinusOne,
            (Self::MinusOne, Self::MinusOne) => Self::PlusOne,
        }
    }
}

impl NonZero for SignedOne {
    #[inline]
    #[must_use]
    fn is_not_zero(&self) -> bool {
        true
    }
}

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
    use crate::SignedOne;

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
