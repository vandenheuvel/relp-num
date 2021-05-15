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

/// # Signed number
///
/// A number that is positive, negative or zero.
pub trait Signed {
    fn signum(&self) -> Sign;
}

macro_rules! unsigned {
    ($type:ty) => {
        impl Signed for $type {
            fn signum(&self) -> Sign {
                if *self == 0 {
                    Sign::Zero
                } else {
                    Sign::Positive
                }
            }
        }
    }
}

unsigned!(u8);
unsigned!(u16);
unsigned!(u32);
unsigned!(u64);
unsigned!(u128);
unsigned!(usize);

macro_rules! signed {
    ($type:ty) => {
        impl Signed for $type {
            fn signum(&self) -> Sign {
                match self.cmp(&0) {
                    Ordering::Less => Sign::Negative,
                    Ordering::Equal => Sign::Zero,
                    Ordering::Greater => Sign::Positive,
                }
            }
        }
    }
}

signed!(i8);
signed!(i16);
signed!(i32);
signed!(i64);
signed!(i128);
signed!(isize);

/// Sign with a zero variant.
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum Sign {
    Positive,
    Zero,
    Negative,
}

impl Neg for Sign {
    type Output = Self;

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

    fn not(self) -> Self::Output {
        match self {
            Sign::Positive => Sign::Negative,
            Sign::Zero => Sign::Zero,
            Sign::Negative => Sign::Positive,
        }
    }
}

impl MulAssign for Sign {
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

    fn mul(mut self, rhs: Self) -> Self::Output {
        self *= rhs;
        self
    }
}

impl PartialOrd for Sign {
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
