use crate::rational::small::{Rational128, Rational16, Rational32, Rational64, Rational8, RationalSize};
use crate::rational::small::{PositiveRational128, PositiveRational16, PositiveRational32, PositiveRational64, PositiveRational8, PositiveRationalSize};
use crate::rational::small::{NonZeroRational128, NonZeroRational16, NonZeroRational32, NonZeroRational64, NonZeroRational8, NonZeroRationalSize};
use crate::rational::small::{NonNegativeRational128, NonNegativeRational16, NonNegativeRational32, NonNegativeRational64, NonNegativeRational8, NonNegativeRationalSize};

use std::num::{NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroIsize};
use std::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize};

use crate::rational::big::Big;
use num_traits::ToPrimitive;
use paste::paste;

macro_rules! from_rational {
    [$($size:expr,)*] => {
        $(
            paste! {
                impl num_traits::FromPrimitive for [<Rational $size>] {
                    #[must_use]
                    #[inline]
                    fn from_i64(n: i64) -> Option<Self> {
                        [<i $size>]::try_from(n).ok()
                        .map(|numerator| {
                            Self {
                                numerator,
                                denominator: [<NonZeroI $size>]::new(1).unwrap(),
                            }
                        })
                    }

                    #[must_use]
                    #[inline]
                    fn from_u64(n: u64) -> Option<Self> {
                        [<i $size>]::try_from(n).ok().map(|numerator| {
                            Self {
                                numerator,
                                denominator: [<NonZeroI $size>]::new(1).unwrap(),
                            }
                        })
                    }

                    #[must_use]
                    #[inline]
                    fn from_f32(n: f32) -> Option<Self> {
                        Big::<8>::from_f32(n).map(Self::try_from).map(Result::ok).flatten()
                    }

                    #[must_use]
                    #[inline]
                    fn from_f64(n: f64) -> Option<Self> {
                        Big::<16>::from_f64(n).map(Self::try_from).map(Result::ok).flatten()
                    }
                }
                impl num_traits::FromPrimitive for [<NonZeroRational $size>] {
                    #[must_use]
                    #[inline]
                    fn from_i64(n: i64) -> Option<Self> {
                        [<i $size>]::try_from(n).ok()
                        .map([<NonZeroI $size>]::new)
                        .map(|numerator| {
                            Self {
                                numerator,
                                denominator: [<NonZeroI $size>]::new(1).unwrap(),
                            }
                        })
                    }

                    #[must_use]
                    #[inline]
                    fn from_u64(n: u64) -> Option<Self> {
                        [<i $size>]::try_from(n).ok()
                        .map([<NonZeroI $size>]::new)
                        .map(|numerator| {
                            Self {
                                numerator,
                                denominator: [<NonZeroI $size>]::new(1).unwrap(),
                            }
                        })
                    }

                    #[must_use]
                    #[inline]
                    fn from_f32(n: f32) -> Option<Self> {
                        Big::<8>::from_f32(n).map(Self::try_from).map(Result::ok).flatten()
                    }

                    #[must_use]
                    #[inline]
                    fn from_f64(n: f64) -> Option<Self> {
                        Big::<16>::from_f64(n).map(Self::try_from).map(Result::ok).flatten()
                    }
                }
                impl num_traits::FromPrimitive for [<NonNegativeRational $size>] {
                    #[must_use]
                    #[inline]
                    fn from_i64(n: i64) -> Option<Self> {
                        [<u $size>]::try_from(n).ok()
                        .map(|numerator| {
                            Self {
                                numerator,
                                denominator: [<NonZeroU $size>]::new(1).unwrap(),
                            }
                        })
                    }

                    #[must_use]
                    #[inline]
                    fn from_u64(n: u64) -> Option<Self> {
                        [<u $size>]::try_from(n).ok()
                        .map(|numerator| {
                            Self {
                                numerator,
                                denominator: [<NonZeroU $size>]::new(1).unwrap(),
                            }
                        })
                    }

                    #[must_use]
                    #[inline]
                    fn from_f32(n: f32) -> Option<Self> {
                        Big::<8>::from_f32(n).map(Self::try_from).map(Result::ok).flatten()
                    }

                    #[must_use]
                    #[inline]
                    fn from_f64(n: f64) -> Option<Self> {
                        Big::<16>::from_f64(n).map(Self::try_from).map(Result::ok).flatten()
                    }
                }
                impl num_traits::FromPrimitive for [<PositiveRational $size>] {
                    #[must_use]
                    #[inline]
                    fn from_i64(n: i64) -> Option<Self> {
                        [<u $size>]::try_from(n).ok()
                        .map([<NonZeroU $size>]::new)
                        .map(|numerator| {
                            Self {
                                numerator,
                                denominator: [<NonZeroU $size>]::new(1).unwrap(),
                            }
                        })
                    }

                    #[must_use]
                    #[inline]
                    fn from_u64(n: u64) -> Option<Self> {
                        [<u $size>]::try_from(n).ok()
                        .map([<NonZeroU $size>]::new)
                        .map(|numerator| {
                            Self {
                                numerator,
                                denominator: [<NonZeroU $size>]::new(1).unwrap(),
                            }
                        })
                    }

                    #[must_use]
                    #[inline]
                    fn from_f32(n: f32) -> Option<Self> {
                        Big::<8>::from_f32(n).map(Self::try_from).map(Result::ok).flatten()
                    }

                    #[must_use]
                    #[inline]
                    fn from_f64(n: f64) -> Option<Self> {
                        Big::<16>::from_f64(n).map(Self::try_from).map(Result::ok).flatten()
                    }
                }
            }
        )*
    }
}
from_rational![8, 16, 32, 64, 128,];

macro_rules! to_zero_numerator {
    ($ty:expr, [$($size:expr,)*]) => {
        $(
            paste! {
                impl ToPrimitive for [<$ty $size:camel>] {
                    fn to_isize(&self) -> Option<isize> {
                        (self.numerator / self.denominator.get()).try_into().ok()
                    }

                    fn to_i8(&self) -> Option<i8> {
                        (self.numerator / self.denominator.get()).try_into().ok()
                    }

                    fn to_i16(&self) -> Option<i16> {
                        (self.numerator / self.denominator.get()).try_into().ok()
                    }

                    fn to_i32(&self) -> Option<i32> {
                        (self.numerator / self.denominator.get()).try_into().ok()
                    }

                    fn to_i64(&self) -> Option<i64> {
                        (self.numerator / self.denominator.get()).try_into().ok()
                    }

                    fn to_i128(&self) -> Option<i128> {
                        (self.numerator / self.denominator.get()).try_into().ok()
                    }

                    fn to_usize(&self) -> Option<usize> {
                        (self.numerator / self.denominator.get()).try_into().ok()
                    }

                    fn to_u8(&self) -> Option<u8> {
                        (self.numerator / self.denominator.get()).try_into().ok()
                    }

                    fn to_u16(&self) -> Option<u16> {
                        (self.numerator / self.denominator.get()).try_into().ok()
                    }

                    fn to_u32(&self) -> Option<u32> {
                        (self.numerator / self.denominator.get()).try_into().ok()
                    }

                    fn to_u64(&self) -> Option<u64> {
                        (self.numerator / self.denominator.get()).try_into().ok()
                    }

                    fn to_u128(&self) -> Option<u128> {
                        (self.numerator / self.denominator.get()).try_into().ok()
                    }

                    fn to_f32(&self) -> Option<f32> {
                        Some(self.numerator as f32 / self.denominator.get() as f32)
                    }

                    fn to_f64(&self) -> Option<f64> {
                        Some(self.numerator as f64 / self.denominator.get() as f64)
                    }
                }
            }
        )*
    }
}
to_zero_numerator!("Rational", [8, 16, 32, 64, 128, "size",]);
to_zero_numerator!("NonNegativeRational", [8, 16, 32, 64, 128, "size",]);

macro_rules! to_non_zero_numerator {
    ($ty:expr, [$($size:expr,)*]) => {
        $(
            paste! {
                impl ToPrimitive for [<$ty $size:camel>] {
                    fn to_isize(&self) -> Option<isize> {
                        (self.numerator.get() / self.denominator.get()).try_into().ok()
                    }

                    fn to_i8(&self) -> Option<i8> {
                        (self.numerator.get() / self.denominator.get()).try_into().ok()
                    }

                    fn to_i16(&self) -> Option<i16> {
                        (self.numerator.get() / self.denominator.get()).try_into().ok()
                    }

                    fn to_i32(&self) -> Option<i32> {
                        (self.numerator.get() / self.denominator.get()).try_into().ok()
                    }

                    fn to_i64(&self) -> Option<i64> {
                        (self.numerator.get() / self.denominator.get()).try_into().ok()
                    }

                    fn to_i128(&self) -> Option<i128> {
                        (self.numerator.get() / self.denominator.get()).try_into().ok()
                    }

                    fn to_usize(&self) -> Option<usize> {
                        (self.numerator.get() / self.denominator.get()).try_into().ok()
                    }

                    fn to_u8(&self) -> Option<u8> {
                        (self.numerator.get() / self.denominator.get()).try_into().ok()
                    }

                    fn to_u16(&self) -> Option<u16> {
                        (self.numerator.get() / self.denominator.get()).try_into().ok()
                    }

                    fn to_u32(&self) -> Option<u32> {
                        (self.numerator.get() / self.denominator.get()).try_into().ok()
                    }

                    fn to_u64(&self) -> Option<u64> {
                        (self.numerator.get() / self.denominator.get()).try_into().ok()
                    }

                    fn to_u128(&self) -> Option<u128> {
                        (self.numerator.get() / self.denominator.get()).try_into().ok()
                    }

                    fn to_f32(&self) -> Option<f32> {
                        Some(self.numerator.get() as f32 / self.denominator.get() as f32)
                    }

                    fn to_f64(&self) -> Option<f64> {
                        Some(self.numerator.get() as f64 / self.denominator.get() as f64)
                    }
                }
            }
        )*
    }
}
to_non_zero_numerator!("NonZeroRational", [8, 16, 32, 64, 128, "size",]);
to_non_zero_numerator!("PositiveRational", [8, 16, 32, 64, 128, "size",]);
