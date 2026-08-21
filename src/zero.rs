//! # Zero
//!
//! A type that is always zero.
use std::fmt;
use std::ops::{Add, AddAssign, Mul, Neg};

use crate::{Sign, Signed, Negateable};

/// # Zero
///
/// A ZST who's value is always zero.
///
/// Can be used in specific situations where one knows that, for example, the right-hand side `b` is
/// always zero. Operations related to `b` should then be compiled away because the operations on
/// its elements are no-ops.
///
/// The same applies to a matrix provider whose coefficients are structurally absent: the incidence
/// matrix of a network is mostly zero, and storing a rational number for each of those entries
/// wastes both space and time. This type stores the coefficient in no space at all, and
/// [`Widen`](crate::Widen) applies it to a wide accumulator without ever materialising a `0`:
/// adding it is nothing at all, multiplying by it clears the accumulator.
///
/// # Absent traits
///
/// There is deliberately no [`NonZero`](crate::NonZero) impl: this type *is* zero, and the whole
/// point of that trait is to assert the opposite.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
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

/// The only value of this type is `0`, which is neither positive nor negative.
impl Signed for Zero {
    #[inline]
    fn signum(&self) -> Sign {
        Sign::Zero
    }
}

/// Negating zero is a no-op, and the result is representable, so this type is negateable.
impl Negateable for Zero {
    #[inline]
    fn negate(&mut self) {
    }
}

impl Neg for Zero {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        self
    }
}

/// Debug forwards to `Display`, because `0` reads better in test output than `Zero`.
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
    use std::cmp::Ordering;

    use crate::{Abs, Negateable, Sign, Signed};
    use crate::fixed::Zero;

    #[test]
    fn test() {
        assert_eq!(Zero, num_traits::Zero::zero());
        assert!(num_traits::Zero::is_zero(&Zero));
        assert_eq!(Zero + Zero, Zero);
        assert_eq!(Zero * Zero, Zero);
        assert_eq!(Zero.abs(), Zero);
    }

    /// Constructing a unit struct through `Default` is exactly what is under test here.
    #[test]
    #[allow(clippy::default_constructed_unit_structs)]
    fn test_default() {
        assert_eq!(Zero::default(), Zero);
    }

    #[test]
    fn test_signum() {
        assert_eq!(Zero.signum(), Sign::Zero);
        assert!(!Zero.is_positive());
        assert!(!Zero.is_negative());
    }

    /// This type is the one of the four fixed types that must *not* implement
    /// [`NonZero`](crate::NonZero); all it can do is report that it is zero.
    #[test]
    fn test_non_zero() {
        assert!(num_traits::Zero::is_zero(&Zero));
    }

    #[test]
    fn test_negate() {
        let mut value = Zero;
        value.negate();
        assert_eq!(value, Zero);
        assert_eq!(-Zero, Zero);
    }

    #[test]
    fn test_ord() {
        assert_eq!(Zero.cmp(&Zero), Ordering::Equal);
        assert_eq!(Zero.partial_cmp(&Zero), Some(Ordering::Equal));
        assert_eq!(Zero, Zero);
    }

    #[test]
    fn test_display() {
        assert_eq!(Zero.to_string(), "0");
        assert_eq!(format!("{Zero:?}"), "0");
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
