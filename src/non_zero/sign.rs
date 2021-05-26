//! # Signs of nonzero values
//!
//! Usual sign implementations have a sign for zero, the implementation in this module does not.
use std::cmp::Ordering;
use std::ops::Mul;

use num_traits;

use crate::non_zero::NonZero;
use crate::sign::Sign;

/// A signed number that can have a nonzero value.
pub trait NonZeroSigned: NonZero + Clone {
    /// Whether the value is positive or negative.
    fn signum(&self) -> NonZeroSign;
    /// Whether `x > 0`.
    fn is_positive(&self) -> bool {
        self.signum() == NonZeroSign::Positive
    }
    /// Whether `x < 0`.
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
    Positive,
    /// `x < 0`
    Negative,
}

impl From<Sign> for NonZeroSign {
    fn from(value: Sign) -> Self {
        match value {
            Sign::Positive => Self::Positive,
            Sign::Zero => panic!("This method should only be called in a context where the value is not zero"),
            Sign::Negative => Self::Negative,
        }
    }
}

impl<T: num_traits::Zero + NonZero + PartialOrd<Self> + Clone> NonZeroSigned for T {
    default fn signum(&self) -> NonZeroSign {
        debug_assert!(self.is_not_zero());

        match self.partial_cmp(&Self::zero()) {
            Some(Ordering::Less) => NonZeroSign::Negative,
            Some(Ordering::Greater) => NonZeroSign::Positive,
            Some(Ordering::Equal) | None => unreachable!("\
                Should only be used on nonzero values, and those should always be comparable with \
                the zero value of the type.\
            "),
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

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (NonZeroSign::Positive, NonZeroSign::Positive) => NonZeroSign::Positive,
            (NonZeroSign::Positive, NonZeroSign::Negative) => NonZeroSign::Negative,
            (NonZeroSign::Negative, NonZeroSign::Positive) => NonZeroSign::Negative,
            (NonZeroSign::Negative, NonZeroSign::Negative) => NonZeroSign::Positive,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::NonZeroSign;

    #[test]
    fn test_cmp() {
        assert!(NonZeroSign::Positive > NonZeroSign::Negative);
        assert_eq!(NonZeroSign::Positive.partial_cmp(&NonZeroSign::Positive), None);
    }
}
