//! # An arbitrary precision rational type
//!
//! At the moment, this is just wrapping the `num::BigRational` type, following the newtype pattern.
//! This is needed because some of the impl's in this module are not provided by `num`. Methods on
//! this type can be modified and specialized as needed.
use std::fmt;

use smallvec::SmallVec;

use crate::non_zero::NonZero;
use crate::rational::Ratio;
use crate::Sign;
use crate::rational::big::creation::to_str;

mod with_small;
mod creation;
pub mod ops;
mod with_binary;
mod special;
#[cfg(test)]
mod test;

pub type Big<const S: usize> = Ratio<SmallVec<[usize; S]>, SmallVec<[usize; S]>>;

pub type Big8 = Big<8>;

impl<const S: usize> NonZero for SmallVec<[usize; S]> {
    #[must_use]
    #[inline]
    fn is_not_zero(&self) -> bool {
        debug_assert!(self.last().map(NonZero::is_not_zero).unwrap_or(true));

        !self.is_empty()
    }
}

impl<const S: usize> fmt::Display for Big<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.sign {
            Sign::Positive => {}
            Sign::Zero => return f.write_str("0"),
            Sign::Negative => f.write_str("-")?,
        }

        f.write_str(&to_str(&self.numerator, 10))?;

        if self.denominator.len() > 1 || self.denominator[0] != 1 {
            f.write_str("/")?;
            f.write_str(&to_str(&self.denominator, 10))?;
        }

        fmt::Result::Ok(())
    }
}
