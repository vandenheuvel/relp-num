//! # Rational numbers
//!
//! A combination of a numerator, denominator and a sign.
//!
//! Using rational numbers with large numerator and denominator is the way arbitrary precision
//! computation is done.
pub use big::Big8 as RationalBig;
pub use big::io::{f32_kind, f64_kind};
pub use big::NonZeroBig8 as NonZeroRationalBig;
pub use small::NonZeroRational128 as NonZeroRational128;
pub use small::NonZeroRational16 as NonZeroRational16;
pub use small::NonZeroRational32 as NonZeroRational32;
pub use small::NonZeroRational64 as NonZeroRational64;
pub use small::NonZeroRational8 as NonZeroRational8;
pub use small::NonZeroRationalUsize as NonZeroRationalUsize;
pub use small::Rational128 as Rational128;
pub use small::Rational16 as Rational16;
pub use small::Rational32 as Rational32;
pub use small::Rational64 as Rational64;
pub use small::Rational8 as Rational8;
pub use small::RationalUsize as RationalUsize;

use std::fmt::{Debug, Display};
use std::iter::Sum;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::{Abs, Field};
use crate::Negateable;
use crate::non_zero::{NonZero, NonZeroSign, NonZeroSigned};
use crate::sign::Sign;
use crate::Signed;

mod small;
pub(crate) mod big;
mod factorization;
mod macros;

/// Ratio between two numbers.
#[derive(Copy, Clone)]
pub struct Ratio<S, N, D: NonZero> {
    sign: S,
    numerator: N,
    denominator: D,
}

impl<S: Signed, N, D: NonZero> Signed for Ratio<S, N, D> {
    fn signum(&self) -> Sign {
        self.sign.signum()
    }
}

impl<S: Negateable, N, D: NonZero> Negateable for Ratio<S, N, D> {
    fn negate(&mut self) {
        self.sign.negate();
    }
}

/// Every ratio of exact integers is an exact field: division never rounds.
///
/// This is the reason [`Field`](crate::Field) is not blanket-implemented — see the note there.
impl<N, D: NonZero> Field for Ratio<Sign, N, D>
where
    Self: Eq
        + PartialOrd
        + num_traits::Zero
        + Neg<Output=Self>
        + num_traits::One
        + Add<Self, Output=Self>
        + for<'r> Add<&'r Self, Output=Self>
        + AddAssign<Self>
        + for<'r> AddAssign<&'r Self>
        + Sum
        + Sub<Self, Output=Self>
        + for<'r> Sub<&'r Self, Output=Self>
        + SubAssign<Self>
        + for<'r> SubAssign<&'r Self>
        + Mul<Self, Output=Self>
        + for<'r> Mul<&'r Self, Output=Self>
        + MulAssign<Self>
        + for<'r> MulAssign<&'r Self>
        + Div<Self, Output=Self>
        + for<'r> Div<&'r Self, Output=Self>
        + DivAssign<Self>
        + for<'r> DivAssign<&'r Self>
        + Clone
        + Display
        + Debug,
{}

/// A ratio that can represent zero has to be checked, and panics when it is.
impl<N, D: NonZero> NonZeroSigned for Ratio<Sign, N, D>
where
    Self: NonZero,
{
    #[inline]
    #[track_caller]
    fn non_zero_signum(&self) -> NonZeroSign {
        match self.sign {
            Sign::Positive => NonZeroSign::Positive,
            Sign::Negative => NonZeroSign::Negative,
            Sign::Zero => panic!("attempt to take the non zero sign of a zero ratio"),
        }
    }
}

/// A ratio that cannot represent zero reads its sign directly; there is no failure case.
impl<N, D: NonZero> NonZeroSigned for Ratio<NonZeroSign, N, D>
where
    Self: NonZero,
{
    #[inline]
    fn non_zero_signum(&self) -> NonZeroSign {
        self.sign
    }
}

/// The magnitude is untouched; only the sign field is written.
impl<N, D: NonZero> Abs for Ratio<Sign, N, D>
where
    Self: Neg<Output=Self> + Ord + num_traits::Zero,
{
    #[inline]
    fn abs(mut self) -> Self {
        if self.sign == Sign::Negative {
            self.sign = Sign::Positive;
        }
        self
    }
}

impl<S: NonZero, N: NonZero, D: NonZero> NonZero for Ratio<S, N, D> {
    fn is_not_zero(&self) -> bool {
        debug_assert_eq!(self.sign.is_not_zero(), self.numerator.is_not_zero());

        self.sign.is_not_zero()
    }
}

#[cfg(test)]
mod test;
