//! # Storing a wide value in a narrow type
//!
//! The direction [`Absorb`](crate::Absorb) does not go. That one reads a narrow value into a wide
//! accumulator; this one writes a wide value back out into a narrow one. Both are written with the
//! wide type as `Self`, for the reason set out there: an implementation names both types and can be
//! written against what exists for the pair.
//!
//! Sizes come first. [`EncodingSize`](crate::EncodingSize) says how much room a value needs, and
//! this says whether the type that was picked has it.

/// Storing a value in a narrower type, exactly or not at all.
///
/// # Contract
///
/// [`narrow`](Narrow::narrow) returns `Some(n)` only when `n` is the same number, and `None`
/// exactly when no value of the narrow type is. It never rounds and never wraps. Widening the
/// result has to give back what was narrowed.
///
/// # What implements it
///
/// The rational types of this crate, into each of the fixed width rational types.
///
/// The table is deliberately smaller than [`Absorb`](crate::Absorb)'s, and not because the rest is
/// unwanted. Narrowing into the markers of [`fixed`](crate::fixed) and into the primitive integers
/// is the other half of what makes those types worth storing, and it is simply not written yet.
/// The asymmetry is a gap, not a statement that those conversions do not make sense.
pub trait Narrow<N> {
    /// This value in the narrow type, if it fits.
    #[must_use]
    fn narrow(&self) -> Option<N>;
}
