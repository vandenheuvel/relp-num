//! # Binary data
//!
//! A number type that is either zero or one.
use std::fmt;
use std::ops::{Add, Mul};

/// # Binary
///
/// A zero-one data type used primarily for the cost in the artificial tableau.
///
/// Note that addition works like addition in the group GF(2).
///
/// See also the documentation in relp::algorithm::two_phase::tableau::kind::artificial::Cost.
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
#[allow(missing_docs)]
pub enum Binary {
    Zero,
    One,
}

impl num_traits::Zero for Binary {
    fn zero() -> Self {
        Self::Zero
    }

    fn is_zero(&self) -> bool {
        self == &Binary::Zero
    }
}

impl num_traits::One for Binary {
    fn one() -> Self {
        Self::One
    }
}

impl fmt::Display for Binary {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
            Binary::Zero => "0",
            Binary::One => "1",
        })
    }
}

impl Add<Binary> for Binary {
    type Output = Self;

    fn add(self, rhs: Binary) -> Self::Output {
        match (self, rhs) {
            (Binary::Zero, Binary::Zero) => Binary::Zero,
            (Binary::Zero, Binary::One) => Binary::One,
            (Binary::One, Binary::Zero) => Binary::One,
            (Binary::One, Binary::One) => Binary::Zero,
        }
    }
}

impl Mul<Binary> for Binary {
    type Output = Self;

    fn mul(self, rhs: Binary) -> Self::Output {
        match (self, rhs) {
            (Binary::One, Binary::One) => Binary::One,
            _ => Binary::Zero,
        }
    }
}
