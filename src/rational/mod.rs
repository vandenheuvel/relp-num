//! # Rational numbers
//!
//! A combination of a numerator, denominator and a sign.
//!
//! Using rational numbers with large numerator and denominator is the way arbitrary precision
//! computation is done.
pub use crate::io::{f32_kind, f64_kind};

pub use big::Big8 as RationalBig;
pub use big::NonZeroBig8 as NonZeroRationalBig;

pub use small::Rational128 as Rational128;
pub use small::Rational16 as Rational16;
pub use small::Rational32 as Rational32;
pub use small::Rational64 as Rational64;
pub use small::Rational8 as Rational8;
pub use small::RationalSize as RationalSize;

pub use small::NonZeroRational128 as NonZeroRational128;
pub use small::NonZeroRational16 as NonZeroRational16;
pub use small::NonZeroRational32 as NonZeroRational32;
pub use small::NonZeroRational64 as NonZeroRational64;
pub use small::NonZeroRational8 as NonZeroRational8;
pub use small::NonZeroRationalSize as NonZeroRationalSize;

pub use small::NonNegativeRational128 as NonNegativeRational128;
pub use small::NonNegativeRational16 as NonNegativeRational16;
pub use small::NonNegativeRational32 as NonNegativeRational32;
pub use small::NonNegativeRational64 as NonNegativeRational64;
pub use small::NonNegativeRational8 as NonNegativeRational8;
pub use small::NonNegativeRationalSize as NonNegativeRationalSize;

pub use small::PositiveRational128 as PositiveRational128;
pub use small::PositiveRational16 as PositiveRational16;
pub use small::PositiveRational32 as PositiveRational32;
pub use small::PositiveRational64 as PositiveRational64;
pub use small::PositiveRational8 as PositiveRational8;
pub use small::PositiveRationalSize as PositiveRationalSize;

use crate::{Negateable, NonZeroSigned};
use crate::non_zero::NonZero;
use crate::sign::Sign;
use crate::Signed;

pub trait Rational: Clone {
    type Sign;
    type Numerator;
    type Denominator;
}

mod small;
mod big;
mod factorization;
mod macros;

#[cfg(test)]
mod test;
