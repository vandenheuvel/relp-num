//! # One
//!
//! A type that is always one.
use std::fmt;
use std::ops::{Add, AddAssign, Div, };
use std::ops::Mul;

use crate::{NonZero, Sign, Signed};

/// # One
///
/// A ZST who's value is always `1`.
///
/// Can be used when a type from the `MatrixProvider` can only have the value `1`, such as with some
/// certain network problems, where the cost of a path might always equal `1`. Storing a rational
/// number in such a matrix would waste both space and time; this type stores the coefficient in no
/// space at all, and [`Absorb`](crate::Absorb) applies it to a wide accumulator without ever
/// materialising a `1`: multiplying by it is a clone, adding it is a single increment.
///
/// This type is zero-sized.
///
/// # Absent traits
///
/// There is deliberately no [`Neg`](std::ops::Neg) and no [`Negateable`](crate::Negateable) impl:
/// `-1` is not a value this type can represent, so negation would have to lie about its result.
/// Use [`SignedOne`](crate::fixed::SignedOne) when the coefficient can have either sign.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct One;

impl num_traits::One for One {
    #[inline]
    fn one() -> Self {
        Self
    }
}

impl Mul<One> for One {
    type Output = Self;

    #[inline]
    fn mul(self, _rhs: One) -> Self::Output {
        Self
    }
}

/// The only value of this type is `1`, which is positive.
impl Signed for One {
    #[inline]
    fn signum(&self) -> Sign {
        Sign::Positive
    }
}

impl NonZero for One {
    #[inline]
    fn is_not_zero(&self) -> bool {
        true
    }
}

/// Debug forwards to `Display`, because `1` reads better in test output than `One`.
impl fmt::Debug for One {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self, f)
    }
}

impl fmt::Display for One {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("1")
    }
}

macro_rules! define_ops {
    ($primitive:ident) => {
        impl From<One> for $primitive {
            fn from(_: One) -> Self {
                1
            }
        }

        impl From<&One> for $primitive {
            fn from(_: &One) -> Self {
                1
            }
        }

        impl Add<One> for $primitive {
            type Output = Self;

            fn add(self, _: One) -> Self::Output {
                self + 1
            }
        }

        impl Add<&One> for $primitive {
            type Output = Self;

            fn add(self, _: &One) -> Self::Output {
                self + 1
            }
        }

        impl AddAssign<&One> for $primitive {
            fn add_assign(&mut self, _: &One) {
                *self += 1;
            }
        }

        impl Mul<One> for $primitive {
            type Output = Self;

            fn mul(self, _: One) -> Self::Output {
                self
            }
        }

        impl Mul<&One> for $primitive {
            type Output = Self;

            fn mul(self, _: &One) -> Self::Output {
                self
            }
        }

        impl Mul<&One> for &$primitive {
            type Output = $primitive;

            fn mul(self, _: &One) -> Self::Output {
                *self
            }
        }

        impl Div<One> for $primitive {
            type Output = Self;

            fn div(self, _: One) -> Self::Output {
                self
            }
        }

        impl Div<&One> for $primitive {
            type Output = Self;

            fn div(self, _: &One) -> Self::Output {
                self
            }
        }
    }
}

define_ops!(i8);
define_ops!(i16);
define_ops!(i32);
define_ops!(i64);
define_ops!(i128);
define_ops!(u8);
define_ops!(u16);
define_ops!(u32);
define_ops!(u64);
define_ops!(u128);

#[cfg(test)]
mod test {
    use std::cmp::Ordering;

    use crate::{NonZero, Sign, Signed};
    use crate::fixed::One;

    #[test]
    fn test_one() {
        assert_eq!(<One as num_traits::One>::one(), One);
        assert_eq!(One * One, One);
    }

    /// Constructing a unit struct through `Default` is exactly what is under test here.
    #[test]
    #[allow(clippy::default_constructed_unit_structs)]
    fn test_default() {
        assert_eq!(One::default(), One);
    }

    #[test]
    fn test_signum() {
        assert_eq!(One.signum(), Sign::Positive);
        assert!(One.is_positive());
        assert!(!One.is_negative());
    }

    #[test]
    fn test_non_zero() {
        assert!(One.is_not_zero());
    }

    #[test]
    fn test_ord() {
        assert_eq!(One.cmp(&One), Ordering::Equal);
        assert_eq!(One.partial_cmp(&One), Some(Ordering::Equal));
        assert_eq!(One, One);
    }

    #[test]
    fn test_display() {
        assert_eq!(One.to_string(), "1");
        assert_eq!(format!("{One:?}"), "1");
    }

    #[test]
    fn test_integer() {
        assert_eq!(1 + One, 2);
        assert_eq!(-1 + One, 0);
        assert_eq!(33 / One, 33);
        assert_eq!(-33 / &One, -33);
        assert_eq!(894 * One, 894);
        assert_eq!(-894 * &One, -894);
        assert_eq!(0_u8 * &One, 0);
    }
}
