//! # relp-num
//!
//! Number types for the [RELP](https://crates.io/crates/relp) crate.
#![warn(missing_docs)]

#![feature(min_specialization)]
#![feature(trait_alias)]
#![feature(result_flattening)]
#![feature(unchecked_math)]
#![feature(core_intrinsics)]
#![feature(nonzero_ops)]
#![feature(bigint_helper_methods)]
#![feature(nonzero_negation_ops)]
#![feature(associated_type_bounds)]

mod binary;
pub use binary::Binary;

mod zero;
pub use zero::Zero;

mod one;
pub use one::One;

mod signed_one;
pub use signed_one::SignedOne;

mod integer;
pub use integer::factorization::prime::Prime;
pub use integer::big::Ubig;
pub use integer::big::NonZeroUbig;

mod non_zero;
pub use non_zero::NonZero;
pub use non_zero::sign::NonZeroSign;
pub use non_zero::sign::NonZeroSigned;

mod rational;
pub use rational::RationalBig;
pub use rational::RationalSize;
pub use rational::Rational128;
pub use rational::Rational64;
pub use rational::Rational32;
pub use rational::Rational16;
pub use rational::Rational8;
pub use rational::NonZeroRationalBig;
pub use rational::NonZeroRationalSize;
pub use rational::NonZeroRational128;
pub use rational::NonZeroRational64;
pub use rational::NonZeroRational32;
pub use rational::NonZeroRational16;
pub use rational::NonZeroRational8;
pub use rational::NonNegativeRationalSize;
pub use rational::NonNegativeRational128;
pub use rational::NonNegativeRational64;
pub use rational::NonNegativeRational32;
pub use rational::NonNegativeRational16;
pub use rational::NonNegativeRational8;
pub use rational::PositiveRationalSize;
pub use rational::PositiveRational128;
pub use rational::PositiveRational64;
pub use rational::PositiveRational32;
pub use rational::PositiveRational16;
pub use rational::PositiveRational8;

mod sign;
pub use sign::Sign;
pub use sign::Signed;
pub use sign::Negateable;

mod traits;
pub use traits::Abs;
pub use traits::factorization::NonZeroFactorizable;
pub use traits::factorization::NonZeroFactorization;
pub use traits::Field;
pub use traits::FieldRef;
pub use traits::OrderedField;
pub use traits::OrderedFieldRef;
pub use traits::Round;

// This re-export is used in macros used to construct rationals in tests.
pub use num_traits::FromPrimitive;

mod io;
