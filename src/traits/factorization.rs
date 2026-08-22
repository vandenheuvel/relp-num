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
/// This factorization does not necessarily consist of primes, and it is not necessarily complete:
/// finding all prime factors of a large number is expensive, so the routines give up at some point
/// and report whatever they did not decompose in
/// [`NonZeroFactorization::residual`](NonZeroFactorization#structfield.residual).
///
/// # Invariant
///
/// Whatever the parameters the implementation was tuned with, the factorization always describes
/// the entire value:
///
/// ```text
/// value == sign * residual * product(factor ^ power)
/// ```
///
/// So a factorization never silently loses part of the value; when a cofactor could not be split,
/// it ends up in `residual` and
/// [`NonZeroFactorization::is_complete`](NonZeroFactorization::is_complete) is `false`.
pub trait NonZeroFactorizable: NonZero + Clone {
    /// Some number greater than 1, probably a prime but not necessarily.
    type Factor: NonZero + Eq + PartialEq + Ord + PartialOrd + Hash + Clone + Debug;
    /// How often the factor appears in the number.
    ///
    /// This is marked Copy, because a 64-bit power already allows for values up to 2^(2^64), which
    /// has about 5.6 * 10^18 decimal digits. Finding primes that are larger than that is too
    /// expensive.
    type Power: Add<Output=Self::Power> + AddAssign + Sub<Output=Self::Power> + SubAssign + One + Signed + Eq + Copy + Clone + Debug;
    /// The part of the value that was not decomposed.
    ///
    /// This is one exactly when the factorization is complete. It is a separate type because it is
    /// not necessarily representable as a [`Factor`](NonZeroFactorizable::Factor): a cofactor of a
    /// big integer can be larger than a machine word, and a rational number leaves a residual on
    /// both sides of the fraction.
    type Residual: FactorizationResidual;

    /// Decompose into factors.
    ///
    /// Note that these factors will often be, but are not guaranteed to be, primes.
    ///
    /// The value is always described completely: see the invariant on
    /// [`NonZeroFactorizable`] and on [`NonZeroFactorization`].
    fn factorize(&self) -> NonZeroFactorization<Self::Factor, Self::Power, Self::Residual>;
}

/// The part of a value that a factorization did not decompose.
///
/// A residual of one means that nothing was left over, so the factors describe the value exactly.
///
/// This trait is deliberately weaker than [`num_traits::One`]: it demands no multiplication,
/// because the residual of a rational factorization is a `(numerator, denominator)` pair, which has
/// no meaningful product.
pub trait FactorizationResidual: Eq + Clone + Debug {
    /// The residual of a factorization that decomposed the entire value.
    fn one() -> Self;
    /// Whether nothing was left undecomposed.
    fn is_one(&self) -> bool;
}

macro_rules! residual_from_num_traits_one {
    ($($ty:ty)*) => {
        $(
            impl FactorizationResidual for $ty {
                #[inline]
                fn one() -> Self {
                    <$ty as One>::one()
                }

                #[inline]
                fn is_one(&self) -> bool {
                    <$ty as One>::is_one(self)
                }
            }
        )*
    }
}
residual_from_num_traits_one!(u8 u16 u32 u64 u128 usize);

/// A rational number leaves a residual on both sides of the fraction.
///
/// The two halves are `(numerator residual, denominator residual)`; they can't be merged into a
/// single value, as that value would generally not be an integer.
impl<Numerator, Denominator> FactorizationResidual for (Numerator, Denominator)
where
    Numerator: FactorizationResidual,
    Denominator: FactorizationResidual,
{
    #[inline]
    fn one() -> Self {
        (Numerator::one(), Denominator::one())
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0.is_one() && self.1.is_one()
    }
}

/// Factorization of a nonzero integer or rational number.
///
/// Includes a sign.
///
/// # Invariant
///
/// The three fields together always describe the entire value:
///
/// ```text
/// value == sign * residual * product(factor ^ power)
/// ```
///
/// The factorization routines are deliberately incomplete, because splitting a large cofactor is
/// expensive. Whatever they did not decompose is in `residual` rather than dropped, so the identity
/// above holds regardless of how they were tuned. Use [`Self::is_complete`] to find out whether the
/// value was decomposed entirely.
#[derive(Eq, PartialEq, Clone, Debug)]
pub struct NonZeroFactorization<Factor, Power, Residual> {
    /// Whether the number is negative.
    pub sign: NonZeroSign,
    /// `(factor, power)` tuples.
    ///
    /// These factors are often, but not necessarily, primes; they are all larger than 1. The
    /// factors should all be smaller than 64 bits and can have negative powers; that is, appear in
    /// the denominator. The powers can't be zero, as this is a sparse representation.
    ///
    /// When this field is empty, nothing was decomposed and the value is `sign * residual`. In
    /// particular, an empty list does **not** mean that the value is `1` or `-1`; that is the case
    /// only when the `residual` is one as well.
    pub factors: Vec<(Factor, Power)>,
    /// The part of the value that was not decomposed.
    ///
    /// One exactly when the factors describe the entire value, see [`Self::is_complete`]. It is
    /// always positive; the sign of the value is in `sign`.
    pub residual: Residual,
}

impl<Factor, Power, Residual: FactorizationResidual> NonZeroFactorization<Factor, Power, Residual> {
    /// Whether the value was decomposed entirely, that is, whether the residual is one.
    ///
    /// When this is `false`, the `factors` describe only the part of the value that could be split
    /// off cheaply, and multiplying them together does not reproduce the value: the `residual` is
    /// the missing factor.
    #[must_use]
    #[inline]
    pub fn is_complete(&self) -> bool {
        self.residual.is_one()
    }
}
