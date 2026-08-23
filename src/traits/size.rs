//! # How much room a number takes
//!
//! Exact arithmetic has no rounding to wash a value away, so a number's cost is the size of its
//! encoding rather than its magnitude. `1 / 3` is small in value and small to store;
//! `10^30 / (10^30 + 1)` is a hair under one and expensive at both ends. Anything that wants to
//! reason about what a problem costs to hold has to be able to ask.
//!
//! What to do with the answer is [`Narrow`](crate::Narrow): once the sizes are known, the values
//! can be moved into a type that is only as wide as they need.

/// The size of a number's representation, in bits.
///
/// Counted over the magnitude: the sign is not part of it, because it costs the same however large
/// the value is.
///
/// # What implements it
///
/// The rational types of this crate. The primitive integers and the markers of
/// [`fixed`](crate::fixed) answer the same question trivially and are not implemented yet, so code
/// that wants to measure a mixed set of coefficients cannot do so through this trait alone.
pub trait EncodingSize {
    /// Bits in the numerator.
    ///
    /// Zero for the value zero, and the bit length of the magnitude otherwise.
    #[must_use]
    fn numerator_bits(&self) -> u32;

    /// Bits in the denominator.
    ///
    /// One for a value that is an integer, whose denominator is one.
    #[must_use]
    fn denominator_bits(&self) -> u32;

    /// What it costs to store this value.
    #[must_use]
    fn encoding_bits(&self) -> u64 {
        u64::from(self.numerator_bits()) + u64::from(self.denominator_bits())
    }
}
