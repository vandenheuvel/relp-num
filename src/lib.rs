//! # relp-num
//!
//! Number types for the [RELP](https://crates.io/crates/relp) crate.
#![warn(missing_docs)]
// The tests deliberately exercise the operator impls in ways clippy reads as mistakes: calling the
// by-reference impls (`op_ref`), asserting the exact boolean a comparison yields on `Sign`, which
// is a genuinely partial order (`bool_assert_comparison`), using `x = x + y` to test `Add` rather
// than `AddAssign` (`assign_op_pattern`), and multiplying by zero (`erasing_op`).
#![cfg_attr(test, allow(
    clippy::op_ref,
    clippy::bool_assert_comparison,
    clippy::assign_op_pattern,
    clippy::erasing_op,
))]

mod binary;
mod zero;
mod one;
mod signed_one;

/// Number types whose value is fixed at compile time.
///
/// A matrix provider often stores coefficients that can only take one or two values: the incidence
/// matrix of a network is nothing but `1`, `-1` and `0`. Storing such a coefficient in a rational
/// number wastes both space and time, so these types store it in no space at all and let
/// [`Absorb`] apply it to a wide accumulator directly.
///
/// They live in their own module because [`One`](one::One) and [`Zero`](zero::Zero) would otherwise shadow the
/// `num_traits` traits of the same name, which are in scope in most code that uses this crate.
pub mod fixed {
    pub use crate::binary::Binary;
    pub use crate::one::One;
    pub use crate::signed_one::SignedOne;
    pub use crate::zero::Zero;
}

mod integer;
pub use integer::factorization::prime::Prime;
pub use integer::big::Ubig;
pub use integer::big::NonZeroUbig;

mod non_zero;
pub use non_zero::NonZero;
pub use non_zero::sign::NonZeroSign;
pub use non_zero::sign::NonZeroSigned;

mod rational;
// The inline capacity is part of the type, and a crate that implements `Absorb` for its own narrow
// type has to name the wide type it implements it for. Exporting only the alias for capacity eight
// would limit such an implementation to that one capacity.
pub use rational::big::Big;
pub use rational::big::NonZeroBig;
pub use rational::RationalBig;
pub use rational::RationalUsize;
pub use rational::Rational128;
pub use rational::Rational64;
pub use rational::Rational32;
pub use rational::Rational16;
pub use rational::Rational8;
pub use rational::NonZeroRationalBig;
pub use rational::NonZeroRationalUsize;
pub use rational::NonZeroRational128;
pub use rational::NonZeroRational64;
pub use rational::NonZeroRational32;
pub use rational::NonZeroRational16;
pub use rational::NonZeroRational8;

mod sign;
pub use sign::Sign;
pub use sign::Signed;
pub use sign::Negateable;

mod traits;
pub use traits::Abs;
pub use traits::Absorb;
pub use traits::AbsorbAll;
pub use traits::factorization::NonZeroFactorizable;
pub use traits::factorization::NonZeroFactorization;
pub use traits::factorization::FactorizationResidual;
pub use traits::Field;
pub use traits::FieldRef;
pub use traits::OrderedField;
pub use traits::OrderedFieldRef;

// This re-export is used in macros used to construct rationals in tests.
pub use num_traits::FromPrimitive;
