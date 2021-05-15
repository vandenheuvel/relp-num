//! # One
use std::fmt;
use std::fmt::Display;
use std::ops::{Add, AddAssign, Div, };
use std::ops::Mul;

/// A type representing the value `1`.
///
/// Can be used when a type from the `MatrixProvider` can only have the value `1`, such as with some
/// certain network problems, where the cost of a path might always equal `1`.
///
/// This type is zero-sized.
#[derive(Ord, PartialOrd, Eq, PartialEq, Clone, Debug)]
pub struct One;

impl num_traits::One for One {
    fn one() -> Self {
        Self
    }
}

impl Mul<One> for One {
    type Output = Self;

    fn mul(self, _rhs: One) -> Self::Output {
        Self
    }
}

impl Display for One {
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

        impl Div<&One> for $primitive {
            type Output = Self;

            fn div(self, _: &One) -> Self::Output {
                self
            }
        }
    }
}

define_ops!(i32);
define_ops!(i64);
define_ops!(i128);
define_ops!(u32);
define_ops!(u64);
define_ops!(u128);
