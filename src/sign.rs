/// # Signs
///
/// Existing sign traits often use the values `1`, `0` and `-1` to represent the sign of a number.
/// This is limiting because some types should never be zero is certain code sections, and having
/// to match on the `0` value is then unidiomatic. Moreover, such a sign is bulky for ratios, which
/// have a separate sign field anyway.
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Mul, MulAssign, Neg, Not};

use crate::non_zero::NonZeroSign;
use crate::NonZero;

/// # Signed numbers
///
/// A number that is positive, negative or zero.
pub trait Signed {
    /// Returns the sign of the number.
    fn signum(&self) -> Sign;
    /// Whether the number is (strictly) greater than zero.
    #[inline]
    fn is_positive(&self) -> bool {
        self.signum() == Sign::Positive
    }
    /// Whether the number is (strictly) smaller than zero.
    #[inline]
    fn is_negative(&self) -> bool {
        self.signum() == Sign::Negative
    }
}

/// A number that can be negated, that is, who's sign can be flipped.
pub trait Negateable: Signed {
    /// Negate the number, e.g. go from 1 to -1.
    fn negate(&mut self);
}

/// Sign with a zero variant.
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum Sign {
    /// x > 0
    Positive = 1,
    /// x == 0
    Zero = 0,
    /// x < 0
    Negative = -1,
}

impl Signed for Sign {
    #[inline]
    fn signum(&self) -> Sign {
        *self
    }

    #[inline]
    fn is_positive(&self) -> bool {
        *self == Sign::Positive
    }

    #[inline]
    fn is_negative(&self) -> bool {
        *self == Sign::Negative
    }
}

impl Negateable for Sign {
    #[inline]
    fn negate(&mut self) {
        match self {
            Sign::Positive => *self = Sign::Negative,
            Sign::Zero => {}
            Sign::Negative => *self = Sign::Positive,
        }
    }
}

impl Neg for Sign {
    type Output = Self;

    #[must_use]
    #[inline]
    fn neg(self) -> Self::Output {
        match self {
            Sign::Positive => Sign::Negative,
            Sign::Zero => Sign::Zero,
            Sign::Negative => Sign::Positive,
        }
    }
}

impl Not for Sign {
    type Output = Self;

    #[must_use]
    #[inline]
    fn not(self) -> Self::Output {
        match self {
            Sign::Positive => Sign::Negative,
            Sign::Zero => Sign::Zero,
            Sign::Negative => Sign::Positive,
        }
    }
}

impl NonZero for Sign {
    #[must_use]
    #[inline]
    fn is_not_zero(&self) -> bool {
        *self != Sign::Zero
    }
}

impl MulAssign for Sign {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = match (&self, rhs) {
            (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => Sign::Positive,
            (Sign::Zero, _) | (_, Sign::Zero) => Sign::Zero,
            (Sign::Positive, Sign::Negative) | (Sign::Negative, Sign::Positive) => Sign::Negative,
        };
    }
}

impl Mul for Sign {
    type Output = Self;

    #[must_use]
    #[inline]
    fn mul(mut self, rhs: Self) -> Self::Output {
        self *= rhs;
        self
    }
}

impl PartialOrd for Sign {
    #[must_use]
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Sign::Negative, Sign::Zero | Sign::Positive) | (Sign::Zero, Sign::Positive) => Some(Ordering::Less),
            (Sign::Zero, Sign::Zero) => Some(Ordering::Equal),
            (Sign::Positive, Sign::Zero | Sign::Negative) | (Sign::Zero, Sign::Negative) => Some(Ordering::Greater),
            (Sign::Negative, Sign::Negative) | (Sign::Positive, Sign::Positive) => None,
        }
    }
}

impl From<NonZeroSign> for Sign {
    #[must_use]
    #[inline]
    fn from(sign: NonZeroSign) -> Self {
        match sign {
            NonZeroSign::Positive => Sign::Positive,
            NonZeroSign::Negative => Sign::Negative,
        }
    }
}

impl fmt::Display for Sign {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Sign::Negative => "-",
            Sign::Zero => "0",
            Sign::Positive => "+",
        })
    }
}

#[cfg(test)]
mod test {
    use crate::{Sign, Signed};
    use crate::RB;

    #[test]
    fn test_integer() {
        assert_eq!(Signed::signum(&0_i32), Sign::Zero);
        assert_eq!(Signed::signum(&-1), Sign::Negative);
        assert_eq!(Signed::signum(&1_i128), Sign::Positive);
        assert_eq!(Signed::signum(&0_u32), Sign::Zero);
        assert_eq!(Signed::signum(&1_u64), Sign::Positive);
    }

    #[test]
    fn test_sign_boolean() {
        assert!(6.is_positive());
        assert!((-5).is_negative());
        assert!(!0.is_positive());
        assert!(!0.is_negative());
        assert!(!6.is_negative());
        assert!(!(-5).is_positive());
    }

    #[test]
    fn test_sign() {
        assert_eq!(!Sign::Zero, Sign::Zero);
        assert_eq!(!Sign::Positive, Sign::Negative);
        assert_eq!(!Sign::Negative, Sign::Positive);
        assert_eq!(Sign::Positive, -Sign::Negative);
        assert_eq!(Sign::Positive * Sign::Positive, Sign::Positive);
        assert_eq!(Sign::Negative * Sign::Negative, Sign::Positive);
        assert_eq!(Sign::Negative * Sign::Zero, -Sign::Zero);
    }

    #[test]
    fn test_sign_ord() {
        assert_eq!(Sign::Zero < Sign::Positive, true);
        assert_eq!(Sign::Positive < Sign::Positive, false);
        assert_eq!(Sign::Positive == Sign::Positive, true);
        assert_eq!(Sign::Zero == Sign::Zero, true);
        assert_eq!(Sign::Negative < Sign::Positive, true);
        assert_eq!(Sign::Negative < Sign::Zero, true);
        assert_eq!(Sign::Negative < Sign::Negative, false);
    }

    #[test]
    fn test_sign_conversion() {
        assert_eq!(Sign::Positive, crate::NonZeroSign::Positive.into());
    }

    #[test]
    fn test_numbers() {
        assert_eq!(Signed::signum(&1), Sign::Positive);
        assert_eq!(Signed::signum(&0), Sign::Zero);
        assert_eq!(Signed::signum(&(-1)), Sign::Negative);

        assert_eq!(RB!(0).signum(), Sign::Zero);
        assert_eq!(RB!(1).signum(), Sign::Positive);
        assert_eq!(RB!(-1).signum(), Sign::Negative);

        assert_eq!(RB!(-1).signum() * RB!(-1).signum(), Sign::Positive);
        assert_eq!(RB!(1).signum() * RB!(1).signum(), Sign::Positive);
        assert_eq!(RB!(-1).signum() * RB!(1).signum(), Sign::Negative);
    }
}
