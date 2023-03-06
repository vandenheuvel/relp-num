use num_traits;
use std::ops::Mul;
use std::ops::Add;
use paste::paste;

// Trait can't be used because One isn't implemented for NonZero types
// use crate::NonZero;
// use crate::rational::small::Ratio;
// impl<N: num_traits::One, D: num_traits::One + NonZero> num_traits::One for Ratio<N, D>
//     where
//         Self: Mul<Output=Self>,
// {
//     #[must_use]
//     #[inline]
//     fn one() -> Self {
//         Self {
//             numerator: N::one(),
//             denominator: D::one(),
//         }
//     }
//
//     #[inline]
//     fn set_one(&mut self) {
//         self.numerator.set_one();
//         self.denominator.set_one();
//     }
//
//     #[must_use]
//     #[inline]
//     fn is_one(&self) -> bool {
//         self.numerator.is_one() && self.denominator.is_one()
//     }
// }
// impl<N: num_traits::Zero, D: num_traits::One + NonZero> num_traits::Zero for Ratio<N, D>
//     where
//         Self: Add<Output=Self>,
// {
//     #[must_use]
//     #[inline]
//     fn zero() -> Self {
//         Self {
//             numerator: N::zero(),
//             denominator: D::one(),
//         }
//     }
//
//     #[inline]
//     fn set_zero(&mut self) {
//         self.numerator.set_zero();
//         self.denominator.set_one();
//     }
//
//     #[must_use]
//     #[inline]
//     fn is_zero(&self) -> bool {
//         self.numerator.is_zero()
//     }
// }

use std::num::{NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroIsize};
use std::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize};

use crate::rational::small::{Rational128, Rational16, Rational32, Rational64, Rational8, RationalSize};
use crate::rational::small::{PositiveRational128, PositiveRational16, PositiveRational32, PositiveRational64, PositiveRational8, PositiveRationalSize};
use crate::rational::small::{NonZeroRational128, NonZeroRational16, NonZeroRational32, NonZeroRational64, NonZeroRational8, NonZeroRationalSize};
use crate::rational::small::{NonNegativeRational128, NonNegativeRational16, NonNegativeRational32, NonNegativeRational64, NonNegativeRational8, NonNegativeRationalSize};

macro_rules! zero_one {
    ($ty:ident, $inner_ty:ident, [$($size:expr,)*]) => {
        $(
            paste! {
                impl num_traits::One for [<$ty $size>]
                where
                    Self: Mul<Output=Self>,
                {
                    #[must_use]
                    #[inline]
                    fn one() -> Self {
                        Self {
                            numerator: 1,
                            denominator: [<NonZero $inner_ty:upper $size:lower>]::new(1).unwrap(),
                        }
                    }

                    #[inline]
                    fn set_one(&mut self) {
                        self.numerator.set_one();
                        self.denominator = [<NonZero $inner_ty:upper $size:lower>]::new(1).unwrap();
                    }

                    #[must_use]
                    #[inline]
                    fn is_one(&self) -> bool {
                        self.numerator.is_one() && self.denominator.get().is_one()
                    }
                }

                impl num_traits::Zero for [<$ty $size>]
                where
                    Self: Add<Output=Self>,
                {
                    #[must_use]
                    #[inline]
                    fn zero() -> Self {
                        Self {
                            numerator: 0,
                            denominator: [<NonZero $inner_ty:upper $size:lower>]::new(1).unwrap(),
                        }
                    }

                    #[inline]
                    fn set_zero(&mut self) {
                        self.numerator.set_zero();
                        self.denominator = [<NonZero $inner_ty:upper $size:lower>]::new(1).unwrap();
                    }

                    #[must_use]
                    #[inline]
                    fn is_zero(&self) -> bool {
                        self.numerator.is_zero()
                    }
                }
            }
        )*
    }
}
zero_one!(Rational, i, [8, 16, 32, 64, 128, "Size",]);
zero_one!(NonNegativeRational, u, [8, 16, 32, 64, 128, "Size",]);

macro_rules! zero_one_non_zero {
    ($ty:ident, $inner_ty:ident, [$($size:expr,)*]) => {
        $(
            paste! {
                impl num_traits::One for [<$ty $size>]
                where
                    Self: Mul<Output=Self>,
                {
                    #[must_use]
                    #[inline]
                    fn one() -> Self {
                        Self {
                            numerator: [<$inner_ty $size:lower>]::new(1).unwrap(),
                            denominator: [<$inner_ty $size:lower>]::new(1).unwrap(),
                        }
                    }

                    #[inline]
                    fn set_one(&mut self) {
                        self.numerator = [<$inner_ty $size:lower>]::new(1).unwrap();
                        self.denominator = [<$inner_ty $size:lower>]::new(1).unwrap();
                    }

                    #[must_use]
                    #[inline]
                    fn is_one(&self) -> bool {
                        self.numerator.get().is_one() && self.denominator.get().is_one()
                    }
                }
            }
        )*
    }
}
zero_one_non_zero!(NonZeroRational, NonZeroI, [8, 16, 32, 64, 128, "Size",]);
zero_one_non_zero!(PositiveRational, NonZeroU, [8, 16, 32, 64, 128, "Size",]);
