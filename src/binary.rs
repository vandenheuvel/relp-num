//! # Binary data
//!
//! A number type that is either zero or one.
use std::fmt;
use std::ops::{Add, AddAssign, Mul};

use crate::{NonZero, Sign, Signed};

/// # Binary
///
/// A number that is either `0` or `1`, stored in a single byte.
///
/// Used primarily for the cost in the artificial tableau, where a variable is either minimised out
/// of the basis or ignored. The same shape appears in a matrix provider whose coefficients can only
/// be `0` or `1`: an incidence matrix, or a set cover. Storing a rational number for such a
/// coefficient wastes both space and time, so this type stores it in a byte and lets
/// [`Absorb`](crate::Absorb) apply it to a wide accumulator directly — adding a `Zero` is nothing at
/// all, multiplying by a `One` is a clone.
///
/// The variants are declared in increasing numeric order, so the derived [`Ord`] is the order of
/// the integers they stand for. Do not reorder them.
///
/// See also the documentation in relp::algorithm::two_phase::tableau::kind::artificial::Cost.
///
/// # Absent traits
///
/// There is deliberately no [`Neg`](std::ops::Neg) and no [`Negateable`](crate::Negateable) impl:
/// `-1` is not a value this type can represent, so negating `One` would have to lie about its
/// result. Use [`SignedOne`](crate::fixed::SignedOne) when the coefficient can have either sign.
///
/// There is also no `Add<Binary> for Binary`, and hence no [`num_traits::Zero`] or
/// [`num_traits::One`]: `One + One` is `2`, which this type cannot represent. The only addition
/// that makes sense is into a type that can hold the result, which is what [`Absorb`](crate::Absorb)
/// and the `Add<Binary> for i32`-style impls below do.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum Binary {
    /// `0`.
    #[default]
    Zero,
    /// `1`.
    One,
}

/// Unlike the other fixed types, this one can be zero, so the answer depends on the value.
impl NonZero for Binary {
    #[inline]
    fn is_not_zero(&self) -> bool {
        match self {
            Binary::Zero => false,
            Binary::One => true,
        }
    }
}

/// This type is zero or positive; it is never negative.
impl Signed for Binary {
    #[inline]
    fn signum(&self) -> Sign {
        match self {
            Binary::Zero => Sign::Zero,
            Binary::One => Sign::Positive,
        }
    }
}

/// Debug forwards to `Display`, because `0` and `1` read better in test output than the variant
/// names.
impl fmt::Debug for Binary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self, f)
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

/// Multiplication is closed on `{0, 1}` and agrees with multiplication of the integers `0` and `1`,
/// unlike addition, which is why this impl exists and `Add<Binary> for Binary` does not.
impl Mul<Binary> for Binary {
    type Output = Self;

    #[inline]
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
    use std::cmp::Ordering;

    use crate::{NonZero, Sign, Signed};
    use crate::fixed::Binary;

    #[test]
    fn test_binary() {
        assert_eq!(Binary::One * Binary::One, Binary::One);
        assert_eq!(Binary::One * Binary::Zero, Binary::Zero);
        assert_eq!(Binary::Zero * Binary::Zero, Binary::Zero);
    }

    #[test]
    fn test_default() {
        assert_eq!(Binary::default(), Binary::Zero);
    }

    #[test]
    fn test_signum() {
        assert_eq!(Binary::Zero.signum(), Sign::Zero);
        assert_eq!(Binary::One.signum(), Sign::Positive);
        assert!(!Binary::Zero.is_positive());
        assert!(Binary::One.is_positive());
        assert!(!Binary::Zero.is_negative());
        assert!(!Binary::One.is_negative());
    }

    /// This is the only one of the four fixed types whose answer depends on the value.
    #[test]
    fn test_non_zero() {
        assert!(!Binary::Zero.is_not_zero());
        assert!(Binary::One.is_not_zero());
    }

    /// `0 < 1`, and the ordering must be a total order.
    #[test]
    fn test_ord() {
        assert_eq!(Binary::Zero.cmp(&Binary::One), Ordering::Less);
        assert_eq!(Binary::One.cmp(&Binary::Zero), Ordering::Greater);
        assert!(Binary::Zero < Binary::One);

        for a in [Binary::Zero, Binary::One] {
            assert_eq!(a.cmp(&a), Ordering::Equal);
            for b in [Binary::Zero, Binary::One] {
                assert_eq!(a.partial_cmp(&b), Some(a.cmp(&b)));
                assert_eq!(a.cmp(&b), b.cmp(&a).reverse());
                assert_eq!(a == b, a.cmp(&b) == Ordering::Equal);
            }
        }
    }

    #[test]
    fn test_display() {
        assert_eq!(Binary::Zero.to_string(), "0");
        assert_eq!(Binary::One.to_string(), "1");
        assert_eq!(format!("{:?}", Binary::Zero), "0");
        assert_eq!(format!("{:?}", Binary::One), "1");
    }

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
