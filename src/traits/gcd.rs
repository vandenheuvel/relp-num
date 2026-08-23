//! # The greatest common divisor of two numbers
//!
//! For a field the usual notion is empty: every non-zero element divides every other one, so any
//! two values have every value as a common divisor. What is meant here is the divisor in the
//! *integer* sense, which a field of fractions still has: the largest `g >= 0` for which both
//! values are integer multiples of `g`. For two integers that is the ordinary greatest common
//! divisor, and for two fractions in lowest terms it is
//!
//! ```text
//! gcd(p1 / q1, p2 / q2) = gcd(p1, p2) / lcm(q1, q2)
//! ```
//!
//! which is again in lowest terms: a prime dividing both `gcd(p1, p2)` and `lcm(q1, q2)` would
//! divide one of the `p` and the `q` beside it, and those are coprime.
//!
//! # What it is for
//!
//! Dividing a set of fractions by their greatest common divisor leaves integers with no common
//! factor. That is the canonical form of a linear constraint, and it is what an exact solver wants
//! from scaling: a floating point solver scales a row for conditioning, which exact arithmetic
//! gives for free, but the encoding of the numbers is a cost that does not go away, and clearing
//! the denominators of a row is what removes it.

/// The greatest common divisor of two numbers, in the integer sense.
///
/// The result is the largest `g >= 0` for which both values are integer multiples of `g`. It is
/// zero exactly when both values are, and it is never negative: the sign of the operands says
/// nothing about what divides them.
///
/// # What implements it
///
/// The rational types of this crate, and only those.
///
/// A row whose coefficients are integers wants the same operation, and the routines for it are
/// already in the crate: a binary gcd per machine word, and one over the words of an arbitrary
/// precision integer. Implementing this for the primitive integers and for
/// [`Ubig`](crate::Ubig) is left for when a caller needs it, so a bound of `T: Gcd` means a
/// rational today.
pub trait Gcd: Sized {
    /// The greatest common divisor of two numbers.
    ///
    /// `None` when the result is not representable in this type, which a fixed width type can
    /// run into: the denominator of the result is the least common multiple of the two
    /// denominators, and that is larger than either of them.
    #[must_use]
    fn gcd(&self, other: &Self) -> Option<Self>;
}
