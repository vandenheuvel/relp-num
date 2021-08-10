//! # One
use std::fmt;
use std::ops::{Add, AddAssign, Div, };
use std::ops::Mul;

use crate::NonZero;

/// A type representing the value `1`.
///
/// Can be used when a type from the `MatrixProvider` can only have the value `1`, such as with some
/// certain network problems, where the cost of a path might always equal `1`.
///
/// This type is zero-sized.
#[derive(Ord, PartialOrd, Eq, PartialEq, Clone)]
pub struct One;

impl num_traits::One for One {
    #[inline]
    #[must_use]
    fn one() -> Self {
        Self
    }
}

impl Default for One {
    fn default() -> Self {
        One
    }
}

impl Mul<One> for One {
    type Output = Self;

    #[inline]
    #[must_use]
    fn mul(self, _rhs: One) -> Self::Output {
        Self
    }
}

impl NonZero for One {
    #[inline]
    #[must_use]
    fn is_not_zero(&self) -> bool {
        true
    }
}

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
                self.clone()
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
    use crate::One;

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
