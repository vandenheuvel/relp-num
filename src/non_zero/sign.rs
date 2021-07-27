//! # Signs of nonzero values
//!
//! Usual sign implementations have a sign for zero, the implementation in this module does not.
use std::cmp::Ordering;
use std::ops::{Mul, MulAssign, Not};

use crate::non_zero::NonZero;
use crate::sign::Sign;

/// A signed number that can have a nonzero value.
pub trait NonZeroSigned: NonZero + Clone {
    /// Whether the value is positive or negative.
    fn signum(&self) -> NonZeroSign;
    /// Whether `x > 0`.
    #[inline]
    fn is_positive(&self) -> bool {
        self.signum() == NonZeroSign::Positive
    }
    /// Whether `x < 0`.
    #[inline]
    fn is_negative(&self) -> bool {
        self.signum() == NonZeroSign::Negative
    }
}

/// Sign of a nonzero value.
///
/// Existing `Sign` traits, such in `num`, typically have a third value for the sign of 0. Working
/// with that trait creates many branches or match cases that should never be possible.
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum NonZeroSign {
    /// `x > 0`
    Positive = 1,
    /// `x < 0`
    Negative = -1,
}

impl NonZero for NonZeroSign {
    fn is_not_zero(&self) -> bool {
        true
    }
}

impl Not for NonZeroSign {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            NonZeroSign::Positive => NonZeroSign::Negative,
            NonZeroSign::Negative => NonZeroSign::Positive,
        }
    }
}

impl From<Sign> for NonZeroSign {
    fn from(other: Sign) -> Self {
        debug_assert!(other.is_not_zero());

        match other {
            Sign::Positive => NonZeroSign::Positive,
            Sign::Zero => panic!("attempt to convert a zero sign into a non zero sign"),
            Sign::Negative => NonZeroSign::Negative,
        }
    }
}

impl PartialOrd for NonZeroSign {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (NonZeroSign::Positive, NonZeroSign::Positive) => None,
            (NonZeroSign::Positive, NonZeroSign::Negative) => Some(Ordering::Greater),
            (NonZeroSign::Negative, NonZeroSign::Positive) => Some(Ordering::Less),
            (NonZeroSign::Negative, NonZeroSign::Negative) => None,
        }
    }
}

impl Mul for NonZeroSign {
    type Output = Self;

    fn mul(mut self, rhs: Self) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl MulAssign for NonZeroSign {
    fn mul_assign(&mut self, rhs: Self) {
        *self = match (*self, rhs) {
            (NonZeroSign::Positive, NonZeroSign::Positive) => NonZeroSign::Positive,
            (NonZeroSign::Positive, NonZeroSign::Negative) => NonZeroSign::Negative,
            (NonZeroSign::Negative, NonZeroSign::Positive) => NonZeroSign::Negative,
            (NonZeroSign::Negative, NonZeroSign::Negative) => NonZeroSign::Positive,
        }
    }
}

#[cfg(test)]
mod test {
    use std::cmp::Ordering;

    use crate::{NonZeroSign, NonZeroSigned, Sign};
    use crate::{R64, RB};

    #[test]
    fn test_cmp() {
        assert!(NonZeroSign::Positive > NonZeroSign::Negative);
        assert_eq!(NonZeroSign::Positive.partial_cmp(&NonZeroSign::Positive), None);
        assert_eq!(NonZeroSign::Negative.partial_cmp(&NonZeroSign::Negative), None);
        assert_eq!(NonZeroSign::Negative.partial_cmp(&NonZeroSign::Positive), Some(Ordering::Less));
    }

    #[test]
    fn test_numbers() {
        use crate::Signed;
        assert_eq!(Signed::signum(&RB!(1)), Sign::Positive);
        assert_eq!(Signed::signum(&RB!(-1)), Sign::Negative);
        assert!(NonZeroSigned::is_positive(&RB!(1)));
        assert!(NonZeroSigned::is_negative(&RB!(-1)));
    }

    #[test]
    fn test_numbers_non_zero() {
        assert_eq!(NonZeroSigned::signum(&1), NonZeroSign::Positive);
        assert_eq!(NonZeroSigned::signum(&(-1)), NonZeroSign::Negative);

        assert_eq!(NonZeroSigned::signum(&RB!(-1)) * NonZeroSigned::signum(&RB!(-1)), NonZeroSign::Positive);
        assert_eq!(NonZeroSigned::signum(&RB!(1)) * NonZeroSigned::signum(&RB!(1)), NonZeroSign::Positive);

        assert_eq!(RB!(-1).signum() * RB!(1).signum(), NonZeroSign::Negative);

        assert_eq!(R64!(1).signum(), NonZeroSign::Positive);
        assert_eq!(R64!(-1).signum(), NonZeroSign::Negative);

        assert_eq!(R64!(-1).signum() * R64!(-1).signum(), NonZeroSign::Positive);
        assert_eq!(R64!(1).signum() * R64!(1).signum(), NonZeroSign::Positive);
        assert_eq!(R64!(-1).signum() * R64!(1).signum(), NonZeroSign::Negative);
    }

    #[test]
    #[should_panic]
    fn test_zero() {
        NonZeroSigned::signum(&RB!(0));
    }
}
