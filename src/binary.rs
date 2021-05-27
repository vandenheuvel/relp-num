//! # Binary data
//!
//! A number type that is either zero or one.
use std::fmt;
use std::ops::{Add, AddAssign, Mul};

use crate::NonZero;

/// # Binary
///
/// A zero-one data type used primarily for the cost in the artificial tableau.
///
/// Note that addition works like addition in the group GF(2).
///
/// See also the documentation in relp::algorithm::two_phase::tableau::kind::artificial::Cost.
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
#[allow(missing_docs)]
pub enum Binary {
    Zero,
    One,
}

impl NonZero for Binary {
    fn is_not_zero(&self) -> bool {
        match self {
            Binary::Zero => false,
            Binary::One => true,
        }
    }
}

impl num_traits::Zero for Binary {
    fn zero() -> Self {
        Self::Zero
    }

    fn is_zero(&self) -> bool {
        self == &Binary::Zero
    }
}

impl num_traits::One for Binary {
    fn one() -> Self {
        Self::One
    }
}

impl fmt::Display for Binary {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
            Binary::Zero => "0",
            Binary::One => "1",
        })
    }
}

impl Add<Binary> for Binary {
    type Output = Self;

    fn add(self, rhs: Binary) -> Self::Output {
        match (self, rhs) {
            (Binary::Zero, Binary::Zero) => Binary::Zero,
            (Binary::Zero, Binary::One) => Binary::One,
            (Binary::One, Binary::Zero) => Binary::One,
            (Binary::One, Binary::One) => Binary::Zero,
        }
    }
}

impl Mul<Binary> for Binary {
    type Output = Self;

    fn mul(self, rhs: Binary) -> Self::Output {
        match (self, rhs) {
            (Binary::One, Binary::One) => Binary::One,
            _ => Binary::Zero,
        }
    }
}

macro_rules! define_ops {
    ($primitive:ident) => {
        impl From<Binary> for $primitive {
            fn from(other: Binary) -> Self {
                From::from(&other)
            }
        }

        impl From<&Binary> for $primitive {
            fn from(other: &Binary) -> Self {
                match other {
                    Binary::Zero => 0,
                    Binary::One => 1,
                }
            }
        }

        impl Add<Binary> for $primitive {
            type Output = Self;

            fn add(self, rhs: Binary) -> Self::Output {
                Add::add(self, &rhs)
            }
        }

        impl Add<&Binary> for $primitive {
            type Output = Self;

            fn add(self, rhs: &Binary) -> Self::Output {
                match rhs {
                    Binary::Zero => self,
                    Binary::One => self + 1,
                }
            }
        }

        impl AddAssign<&Binary> for $primitive {
            fn add_assign(&mut self, rhs: &Binary) {
                match rhs {
                    Binary::Zero => {},
                    Binary::One => *self += 1,
                }
            }
        }

        impl Mul<Binary> for $primitive {
            type Output = Self;

            fn mul(self, rhs: Binary) -> Self::Output {
                Mul::mul(self, &rhs)
            }
        }

        impl Mul<&Binary> for $primitive {
            type Output = Self;

            fn mul(self, rhs: &Binary) -> Self::Output {
                match rhs {
                    Binary::Zero => 0,
                    Binary::One => self,
                }
            }
        }

        impl Mul<&Binary> for &$primitive {
            type Output = $primitive;

            fn mul(self, rhs: &Binary) -> Self::Output {
                match rhs {
                    Binary::Zero => 0,
                    Binary::One => *self,
                }
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
    use crate::Binary;

    #[test]
    fn test_integer() {
        assert_eq!(1 + Binary::One, 2);
        assert_eq!(-1 + Binary::One, 0);
        assert_eq!(894 * Binary::One, 894);
        assert_eq!(-894 * &Binary::One, -894);
        assert_eq!(0_u8 * &Binary::One, 0);

        assert_eq!(1 + Binary::Zero, 1);
        assert_eq!(-1 + Binary::Zero, -1);
        assert_eq!(894 * Binary::Zero, 0);
        assert_eq!(-894 * &Binary::Zero, 0);
        assert_eq!(0_u8 * &Binary::Zero, 0);
    }
}
