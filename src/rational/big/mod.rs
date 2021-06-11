//! # An arbitrary precision rational type
//!
//! At the moment, this is just wrapping the `num::BigRational` type, following the newtype pattern.
//! This is needed because some of the impl's in this module are not provided by `num`. Methods on
//! this type can be modified and specialized as needed.
use std::fmt;

use smallvec::SmallVec;

use crate::{Sign, Signed};
use crate::non_zero::NonZero;
use crate::rational::big::creation::to_str;
use crate::rational::big::ops::is_well_formed;
use crate::rational::big::ops::normalize::simplify_fraction_without_info;
use crate::rational::Ratio;

mod with_small;
mod creation;
pub mod ops;
mod with_binary;
mod special;
#[cfg(test)]
mod test;

pub type Big<const S: usize> = Ratio<SmallVec<[usize; S]>, SmallVec<[usize; S]>>;

/// An arbitrary precision type.
///
/// Represents any rational number with a sign, numerator and denominator.
pub type Big8 = Big<8>;

impl<const S: usize> Big<S> {
    fn is_consistent(&self) -> bool {
        if !is_well_formed(&self.numerator) {
            return false;
        }
        if !is_well_formed(&self.denominator) {
            return false;
        }

        match self.sign {
            Sign::Zero => {
                self.numerator.is_empty() && self.denominator.len() == 1 && self.denominator[0] == 1
            }
            Sign::Positive | Sign::Negative => {
                if self.numerator.is_empty() {
                    return false;
                }
                if self.denominator.is_empty() {
                    return false;
                }

                let mut n_clone = self.numerator.clone();
                let mut d_clone = self.denominator.clone();
                simplify_fraction_without_info(&mut n_clone, &mut d_clone);

                n_clone == self.numerator && d_clone == self.denominator
            }
        }
    }
}

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

impl<const S: usize> Signed for Big<S> {
    fn signum(&self) -> Sign {
        self.sign
    }
}
