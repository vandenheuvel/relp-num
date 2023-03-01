//! # An arbitrary precision rational type
//!
//! At the moment, this is just wrapping the `num::BigRational` type, following the newtype pattern.
//! This is needed because some of the impl's in this module are not provided by `num`. Methods on
//! this type can be modified and specialized as needed.
use crate::{NonZero, NonZeroSign, Sign, Ubig};
use crate::integer::big::NonZeroUbig;

pub (crate) mod io;
pub(crate) mod properties;
pub mod ops;

mod with_small_rational;
mod with_integer;
mod with_binary;
mod with_zero;
mod with_one;
mod with_option;

/// Ratio between two numbers.
#[derive(Copy, Clone)]
struct Ratio<S, N, D: NonZero> {
    sign: S,
    numerator: N,
    denominator: D,
}

pub type Big<const S: usize> = Ratio<Sign, Ubig<S>, NonZeroUbig<S>>;
pub type NonZeroBig<const S: usize> = Ratio<NonZeroSign, NonZeroUbig<S>, NonZeroUbig<S>>;

/// An arbitrary precision type.
pub type Big8 = Big<8>;
/// A non zero arbitrary precision type.
pub type NonZeroBig8 = NonZeroBig<8>;

#[cfg(test)]
mod test;
