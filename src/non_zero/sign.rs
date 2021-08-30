//! # Signs of nonzero values
//!
//! Usual sign implementations have a sign for zero, the implementation in this module does not.
use std::cmp::Ordering;
use std::ops::{Mul, MulAssign, Neg, Not};

use crate::{Negateable, Signed};
use crate::non_zero::NonZero;
use crate::sign::Sign;

/// A signed number that can have a nonzero value.
pub trait NonZeroSigned: NonZero + Signed {
    /// Whether the value is positive or negative.
    fn non_zero_signum(&self) -> NonZeroSign;
    /// Whether `x > 0`.
    #[inline]
    fn non_zero_is_positive(&self) -> bool {
        self.non_zero_signum() == NonZeroSign::Positive
    }
    /// Whether `x < 0`.
    #[inline]
    fn non_zero_is_negative(&self) -> bool {
        self.non_zero_signum() == NonZeroSign::Negative
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

impl<T: NonZero + Signed> NonZeroSigned for T {
    #[inline]
    fn non_zero_signum(&self) -> NonZeroSign {
        match self.signum() {
            Sign::Positive => NonZeroSign::Positive,
            Sign::Zero => panic!("attempt to convert a zero sign into a non zero sign"),
            Sign::Negative => NonZeroSign::Negative,
        }
    }
}

impl Signed for NonZeroSign {
    fn signum(&self) -> Sign {
        match self {
            NonZeroSign::Positive => Sign::Positive,
            NonZeroSign::Negative => Sign::Negative,
        }
    }
}

impl NonZero for NonZeroSign {
    fn is_not_zero(&self) -> bool {
        true
    }
}

impl Negateable for NonZeroSign {
    fn negate(&mut self) {
        *self = match self {
            NonZeroSign::Positive => NonZeroSign::Negative,
            NonZeroSign::Negative => NonZeroSign::Positive,
        }
    }
}

impl Not for NonZeroSign {
    type Output = Self;

    fn not(mut self) -> Self::Output {
        Negateable::negate(&mut self);
        self
    }
}

impl Neg for NonZeroSign {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        Negateable::negate(&mut self);
        self
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
        assert!(RB!(1).is_positive());
        assert!(RB!(-1).is_negative());
    }

    #[test]
    fn test_numbers_non_zero() {
        assert_eq!(1.non_zero_signum(), NonZeroSign::Positive);
        assert_eq!((-1).non_zero_signum(), NonZeroSign::Negative);

        assert_eq!(RB!(-1).non_zero_signum() * RB!(-1).non_zero_signum(), NonZeroSign::Positive);
        assert_eq!(RB!(1).non_zero_signum() * RB!(1).non_zero_signum(), NonZeroSign::Positive);

        assert_eq!(RB!(-1).non_zero_signum() * RB!(1).non_zero_signum(), NonZeroSign::Negative);

        assert_eq!(R64!(1).non_zero_signum(), NonZeroSign::Positive);
        assert_eq!(R64!(-1).non_zero_signum(), NonZeroSign::Negative);

        assert_eq!(R64!(-1).non_zero_signum() * R64!(-1).non_zero_signum(), NonZeroSign::Positive);
        assert_eq!(R64!(1).non_zero_signum() * R64!(1).non_zero_signum(), NonZeroSign::Positive);
        assert_eq!(R64!(-1).non_zero_signum() * R64!(1).non_zero_signum(), NonZeroSign::Negative);
    }

    #[test]
    #[should_panic]
    fn test_zero() {
        RB!(0).non_zero_signum();
    }
}
