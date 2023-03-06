use std::cmp::Ordering;
use std::fmt;
use std::ops::{Mul, MulAssign};
use crate::NonZero;
use crate::sign::NonNegativeSign;

impl NonZero for NonNegativeSign {
    #[must_use]
    #[inline]
    fn is_not_zero(&self) -> bool {
        match self {
            Self::Zero => false,
            Self::Positive => true,
        }
    }
}

impl MulAssign for NonNegativeSign {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = match (&self, rhs) {
            (Self::Zero, _) | (Self::Positive, Self::Zero) => Self::Zero,
            (Self::Positive, Self::Positive) => Self::Positive,
        };
    }
}

impl Mul for NonNegativeSign {
    type Output = Self;

    #[must_use]
    #[inline]
    fn mul(mut self, rhs: Self) -> Self::Output {
        self *= rhs;
        self
    }
}

impl PartialOrd for NonNegativeSign {
    #[must_use]
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Self::Zero, Self::Positive) => Some(Ordering::Less),
            (Self::Zero, Self::Zero) => Some(Ordering::Equal),
            (Self::Positive, Self::Positive) => None,
            (Self::Positive, Self::Zero) => Some(Ordering::Greater),
        }
    }
}

impl fmt::Display for NonNegativeSign {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Zero => "0",
            Self::Positive => "+",
        })
    }
}
