//! # An arbitrary precision rational type
//!
//! At the moment, this is just wrapping the `num::BigRational` type, following the newtype pattern.
//! This is needed because some of the impl's in this module are not provided by `num`. Methods on
//! this type can be modified and specialized as needed.
use std::fmt;

use smallvec::SmallVec;

use crate::non_zero::NonZero;
use crate::rational::Ratio;
use crate::sign::Sign;

mod with_small;
mod creation;
pub mod ops;
mod with_binary;
mod special;
#[cfg(test)]
mod test;

pub type Big<const S: usize> = Ratio<SmallVec<[usize; S]>, SmallVec<[usize; S]>>;

pub type Big8 = Big<8>;

impl<const S: usize> NonZero for Big<S> {
    fn is_not_zero(&self) -> bool {
        self.sign != Sign::Zero
    }
}

impl<const S: usize> fmt::Display for Big<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.sign, f)?;
        if self.numerator.len() == 1 {
            write!(f, "{}", self.numerator[0])?;
        } else {
            write!(f, "{:?}", self.numerator)?;
        }
        f.write_str("/")?;
        if self.denominator.len() == 1 {
            write!(f, "{}", self.denominator[0])
        } else {
            write!(f, "{:?}", self.denominator)
        }
    }
}
