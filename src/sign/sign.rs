use std::cmp::Ordering;
use std::fmt::Write;
use std::fmt;
use std::ops::{Mul, MulAssign, Neg, Not};
use crate::NonZero;
use crate::sign::Sign;

impl Neg for Sign {
    type Output = Self;

    #[must_use]
    #[inline]
    fn neg(self) -> Self::Output {
        match self {
            Self::Positive => Self::Negative,
            Self::Zero => Self::Zero,
            Self::Negative => Self::Positive,
        }
    }
}

impl Not for Sign {
    type Output = Self;

    #[must_use]
    #[inline]
    fn not(self) -> Self::Output {
        match self {
            Self::Positive => Self::Negative,
            Self::Zero => Self::Zero,
            Self::Negative => Self::Positive,
        }
    }
}

impl NonZero for Sign {
    #[must_use]
    #[inline]
    fn is_not_zero(&self) -> bool {
        *self != Self::Zero
    }
}

impl MulAssign for Sign {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = match (&self, rhs) {
            (Self::Positive, Self::Positive) | (Self::Negative, Self::Negative) => Self::Positive,
            (Self::Zero, _) | (_, Self::Zero) => Self::Zero,
            (Self::Positive, Self::Negative) | (Self::Negative, Self::Positive) => Self::Negative,
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
            (Self::Negative, Self::Zero | Self::Positive) | (Self::Zero, Self::Positive) => Some(Ordering::Less),
            (Self::Zero, Self::Zero) => Some(Ordering::Equal),
            (Self::Positive, Self::Zero | Self::Negative) | (Self::Zero, Self::Negative) => Some(Ordering::Greater),
            (Self::Negative, Self::Negative) | (Self::Positive, Self::Positive) => None,
        }
    }
}

impl fmt::Display for Sign {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Negative => "-",
            Self::Zero => "0",
            Self::Positive => "+",
        })
    }
}
