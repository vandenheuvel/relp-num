//! # Number factorization
//!
//! Factorize integers and rational numbers into numbers that are often primes.
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::{Add, AddAssign, Sub, SubAssign};

use num_traits::One;

use crate::non_zero::{NonZero, NonZeroSign};
use crate::Signed;

/// Creating a factorization of an integer or rational number.
///
/// This factorization does not necessarily consist of primes, as this can be computationally
/// expensive.
pub trait NonZeroFactorizable: NonZero + Clone {
    /// Some number greater than 1, probably a prime but not necessarily.
    type Factor: NonZero + Eq + PartialEq + Ord + PartialOrd + Hash + Clone + Debug;
    /// How often the factor appears in the number.
    ///
    /// This is marked Copy, because a 64-bit power already allows for values up to 2^(2^64), which
    /// has about 5.6 * 10^18 decimal digits. Finding primes that are larger than that is too
    /// expensive.
    type Power: Add<Output=Self::Power> + AddAssign + Sub<Output=Self::Power> + SubAssign + One + Signed + Eq + Copy + Clone + Debug;

    /// Decompose into factors.
    ///
    /// Note that these factors will often be, but are not guaranteed to be, primes.
    fn factorize(&self) -> NonZeroFactorization<Self::Factor, Self::Power>;
}

/// Prime factorization representation of a nonzero rational number.
///
/// Includes a sign.
#[derive(Eq, PartialEq, Clone, Debug)]
pub struct NonZeroFactorization<Factor, Power> {
    /// Whether the number is negative.
    pub sign: NonZeroSign,
    /// `(prime factor, power)` tuples.
    ///
    /// The factors should all be smaller than 64 bits and can have negative powers; that is, appear
    /// in the denominator. The powers can't be zero, as this is a sparse representation.
    ///
    /// When this field is empty, the value `1` or `-1` is represented, depending on `sign`.
    pub factors: Vec<(Factor, Power)>,
}
