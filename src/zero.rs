//! # Zero
//!
//! A type that is always zero.
use std::ops::{Add, Mul};

use num_traits;

/// # Zero
///
/// A ZST who's value is always zero.
///
/// Can be used in specific situations where one knows that, for example, the right-hand side `b` is
/// always zero. Operations related to `b` should then be compiled away because the operations on
/// its elements are no-ops.
pub struct Zero;

impl num_traits::Zero for Zero {
    fn zero() -> Self {
        Self
    }

    fn is_zero(&self) -> bool {
        true
    }
}

impl Add for Zero {
    type Output = Self;

    fn add(self, _: Self) -> Self::Output {
        Self
    }
}

impl Mul for Zero {
    type Output = Self;

    fn mul(self, _: Self) -> Self::Output {
        Self
    }
}
