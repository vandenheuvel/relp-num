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
pub use small::Rational128 as Rational128;
pub use small::Rational16 as Rational16;
pub use small::Rational32 as Rational32;
pub use small::Rational64 as Rational64;
pub use small::Rational8 as Rational8;

use crate::non_zero::NonZero;
use crate::NonZeroSign;
use crate::sign::Sign;

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

impl<N: NonZero, D: NonZero> NonZero for Ratio<Sign, N, D> {
    #[must_use]
    #[inline]
    default fn is_not_zero(&self) -> bool {
        debug_assert!(self.denominator.is_not_zero());

        self.sign.is_not_zero()
    }
}

impl<N: NonZero, D: NonZero> NonZero for Ratio<NonZeroSign, N, D> {
    #[must_use]
    #[inline]
    default fn is_not_zero(&self) -> bool {
        debug_assert!(self.denominator.is_not_zero());

        self.sign.is_not_zero()
    }
}

#[cfg(test)]
mod test;
