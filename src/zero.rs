//! # Zero
//!
//! A type that is always zero.
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, AddAssign, Mul, Neg};

use crate::{Sign, Signed};

/// # Zero
///
/// A ZST who's value is always zero.
///
/// Can be used in specific situations where one knows that, for example, the right-hand side `b` is
/// always zero. Operations related to `b` should then be compiled away because the operations on
/// its elements are no-ops.
#[derive(Copy, Clone)]
pub struct Zero;

impl num_traits::Zero for Zero {
    fn zero() -> Self {
        Self
    }

    fn is_zero(&self) -> bool {
        true
    }
}

impl Add for Zero {
    type Output = Self;

    fn add(self, _: Self) -> Self::Output {
        Self
    }
}

impl Mul for Zero {
    type Output = Self;

    fn mul(self, _: Self) -> Self::Output {
        Self
    }
}

impl Eq for Zero {}

impl PartialEq for Zero {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl PartialOrd for Zero {
    fn partial_cmp(&self, _: &Self) -> Option<Ordering> {
        Some(Ordering::Equal)
    }
}

impl Ord for Zero {
    fn cmp(&self, _: &Self) -> Ordering {
        Ordering::Equal
    }
}

impl Signed for Zero {
    fn signum(&self) -> Sign {
        Sign::Zero
    }
}

impl Neg for Zero {
    type Output = Self;

    fn neg(self) -> Self::Output {
        self
    }
}

impl fmt::Debug for Zero {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl fmt::Display for Zero {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("0")
    }
}

macro_rules! define_ops {
    ($primitive:ident) => {
        impl From<Zero> for $primitive {
            fn from(_: Zero) -> Self {
                0
            }
        }

        impl From<&Zero> for $primitive {
            fn from(_: &Zero) -> Self {
                0
            }
        }

        impl Add<Zero> for $primitive {
            type Output = Self;

            fn add(self, _: Zero) -> Self::Output {
                self
            }
        }

        impl Add<&Zero> for $primitive {
            type Output = Self;

            fn add(self, _: &Zero) -> Self::Output {
                self
            }
        }

        impl AddAssign<&Zero> for $primitive {
            fn add_assign(&mut self, _: &Zero) {
            }
        }

        impl Mul<Zero> for $primitive {
            type Output = Self;

            fn mul(self, _: Zero) -> Self::Output {
                0
            }
        }

        impl Mul<&Zero> for $primitive {
            type Output = Self;

            fn mul(self, _: &Zero) -> Self::Output {
                0
            }
        }

        impl Mul<&Zero> for &$primitive {
            type Output = $primitive;

            fn mul(self, _: &Zero) -> Self::Output {
                0
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
    use crate::{Abs, Sign, Signed, Zero};

    #[test]
    fn test() {
        assert_eq!(Zero, num_traits::Zero::zero());
        assert!(num_traits::Zero::is_zero(&Zero));
        assert_eq!(Zero + Zero, Zero);
        assert_eq!(Zero * Zero, Zero);
        assert_eq!(Zero.abs(), Zero);
        assert_eq!(Zero.signum(), Sign::Zero);
    }
    
    #[test]
    fn test_integer() {
        assert_eq!(1 + Zero, 1);
        assert_eq!(-1 + Zero, -1);
        assert_eq!(894 * Zero, 0);
        assert_eq!(-894 * &Zero, 0);
        assert_eq!(0_u8 * &Zero, 0);
    }
}
