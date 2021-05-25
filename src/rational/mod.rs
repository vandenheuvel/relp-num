//! # Rational numbers
//!
//! A combination of a numerator, denominator and a sign.
//!
//! Using rational numbers with large numerator and denominator is the way arbitrary precision
//! computation is done.
pub use big::Big8 as RationalBig;
pub use small::Rational128 as Rational128;
pub use small::Rational16 as Rational16;
pub use small::Rational32 as Rational32;
pub use small::Rational64 as Rational64;
pub use small::Rational8 as Rational8;

use crate::non_zero::NonZero;
use crate::sign::Sign;

mod small;
mod big;
mod factorization;
mod macros;

mod utilities;

/// # Rational number
///
/// Currently not used.
///
/// TODO(ARCHITECTURE): Is it interesting to implement this for integers?
trait Rational {
    type Sign;
    type Numerator;
    type Denominator;

    fn sign(&self) -> Self::Sign;
    fn numerator(&self) -> &Self::Numerator;
    fn numerator_mut(&mut self) -> &mut Self::Numerator;
    fn denominator(&self) -> &Self::Denominator;
    fn denominator_mut(&mut self) -> &mut Self::Denominator;
}

/// Ratio between two numbers.
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub struct Ratio<N, D: NonZero> {
    sign: Sign,
    numerator: N,
    denominator: D,
}

impl<N: NonZero, D: NonZero> NonZero for Ratio<N, D> {
    #[must_use]
    #[inline]
    default fn is_not_zero(&self) -> bool {
        debug_assert!(self.denominator.is_not_zero());

        self.numerator.is_not_zero()
    }
}

#[cfg(test)]
mod test;
