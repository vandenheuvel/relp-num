//! # relp-num
//!
//! Number types for the [RELP](https://crates.io/crates/relp) crate.
#![feature(asm)]
#![feature(min_specialization)]
#![feature(label_break_value)]
#![feature(trait_alias)]
#![feature(result_flattening)]
#![feature(unchecked_math)]

mod binary;
pub use binary::Binary;

mod zero;
pub use zero::Zero;

mod one;
pub use one::One;

mod integer;
pub use integer::factorization::prime::Prime;

mod non_zero;
pub use non_zero::NonZero;
pub use non_zero::sign::NonZeroSign;
pub use non_zero::sign::NonZeroSigned;

mod rational;
pub use rational::RationalBig;
pub use rational::Rational128;
pub use rational::Rational64;
pub use rational::Rational32;
pub use rational::Rational16;
pub use rational::Rational8;

mod sign;
pub use sign::Sign;
pub use sign::Signed;

mod traits;
pub use traits::Abs;
pub use traits::factorization::NonZeroFactorizable;
pub use traits::factorization::NonZeroFactorization;
pub use traits::Field;
pub use traits::FieldRef;
pub use traits::OrderedField;
pub use traits::OrderedFieldRef;

pub use num_traits::FromPrimitive;
