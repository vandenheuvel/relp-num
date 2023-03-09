use std::cmp::Ordering;
use std::iter::Sum;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};
use std::ops::Neg;
use paste::paste;

use std::num::{NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroIsize};
use std::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize};

use crate::non_zero::NonZero;
use crate::sign::{Sign, NonZeroSign, NonNegativeSign};
use crate::rational::small::{Ratio, Rational128, Rational16, Rational32, Rational64, Rational8, RationalSize};
use crate::rational::small::{NonZeroRational128, NonZeroRational16, NonZeroRational32, NonZeroRational64, NonZeroRational8, NonZeroRationalSize};
use crate::rational::small::{NonNegativeRational128, NonNegativeRational16, NonNegativeRational32, NonNegativeRational64, NonNegativeRational8, NonNegativeRationalSize};

mod forwards;
mod building_block;


macro_rules! rational {
    [$($size:expr,)*] => {
        $(
            paste! {
                impl AddAssign<&Self> for [<Rational $size:camel>] {
                    #[inline]
                    fn add_assign(&mut self, rhs: &Self) {
                        building_block::[<add_sub_ $size>](
                            &mut self.numerator,
                            &mut self.denominator,
                            &rhs.numerator,
                            &rhs.denominator,
                            AddAssign::add_assign,
                        )
                    }
                }

                impl SubAssign<&Self> for [<Rational $size:camel>] {
                    #[inline]
                    fn sub_assign(&mut self, rhs: &Self) {
                        building_block::[<add_sub_ $size>](
                            &mut self.numerator,
                            &mut self.denominator,
                            &rhs.numerator,
                            &rhs.denominator,
                            SubAssign::sub_assign,
                        )
                    }
                }

                impl Sum for [<Rational $size:camel>] {
                    fn sum<I: Iterator<Item=Self>>(mut iter: I) -> Self {
                        let first_value = iter.next();
                        match first_value {
                            None => <Self as num_traits::Zero>::zero(),
                            Some(mut total) => {
                                while let Some(next_value) = iter.next() {
                                    total += next_value;
                                }

                                total
                            }
                        }
                    }
                }

                impl MulAssign<&Self> for [<Rational $size:camel>] {
                    #[inline]
                    fn mul_assign(&mut self, rhs: &Self) {
                        building_block::[<mul_ $size>](
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.numerator,
                            rhs.denominator,
                        )
                    }
                }

                impl Div<[<Rational $size:camel>]> for &[<Rational $size:camel>] {
                    type Output = [<Rational $size:camel>];

                    #[must_use]
                    #[inline]
                    fn div(self, mut rhs: [<Rational $size:camel>]) -> Self::Output {
                        building_block::[<mul_ $size>](
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.denominator,
                            [<NonZeroU $size>]::new(rhs.numerator).expect("attempt to divide by zero"),
                        )
                    }
                }

                impl DivAssign<&Self> for [<Rational $size:camel>] {
                    #[inline]
                    fn div_assign(&mut self, rhs: &Self) {
                        building_block::[<mul_ $size>](
                            &mut self.numerator,
                            &mut self.denominator,
                            rhs.denominator,
                            [<NonZeroU $size>]::new(rhs.numerator).expect("attempt to divide by zero"),
                        )
                    }
                }
            }
        )*
    }
}
rational![8, 16, 32, 64, 128, "size",];

// macro_rules! rational_non_zero {
//     [$($size:expr,)*] => {
//         $(
//             paste! {
//                 impl AddAssign<&Self> for [<NonZeroRational $size>] {
//                     #[inline]
//                     fn add_assign(&mut self, rhs: &Self) {
//                         match (self.sign, rhs.sign) {
//                             (NonZeroSign::Positive, NonZeroSign::Positive) | (NonZeroSign::Negative, NonZeroSign::Negative) => {
//                                 [<add_ $size>](
//                                     &mut self.numerator,
//                                     &mut self.denominator,
//                                     rhs.numerator,
//                                     rhs.denominator,
//                                 )
//                             }
//                             (NonZeroSign::Positive, NonZeroSign::Negative) | (NonZeroSign::Negative, NonZeroSign::Positive) => {
//                                 let sign_change = [<sub_ $size>](
//                                     &mut self.numerator,
//                                     &mut self.denominator,
//                                     rhs.numerator,
//                                     rhs.denominator,
//                                 );
//                                 match sign_change {
//                                     SignChange::None => {}
//                                     SignChange::Flip => self.sign.negate(),
//                                     SignChange::Zero => panic!("attempt to add with overflow"),
//                                 }
//                             }
//                         }
//                     }
//                 }
//                 impl SubAssign<&Self> for [<NonZeroRational $size>] {
//                     #[inline]
//                     fn sub_assign(&mut self, rhs: &Self) {
//                         match (self.sign, rhs.sign) {
//                             (NonZeroSign::Positive, NonZeroSign::Positive) | (NonZeroSign::Negative, NonZeroSign::Negative) => {
//                                 let sign_change = [<sub_ $size>](
//                                     &mut self.numerator,
//                                     &mut self.denominator,
//                                     rhs.numerator,
//                                     rhs.denominator,
//                                 );
//                                 match sign_change {
//                                     SignChange::None => {}
//                                     SignChange::Flip => self.sign.negate(),
//                                     SignChange::Zero => panic!("attempt to subtract with overflow"),
//                                 }
//                             }
//                             (NonZeroSign::Positive, NonZeroSign::Negative) | (NonZeroSign::Negative, NonZeroSign::Positive) => {
//                                 [<add_ $size>](
//                                     &mut self.numerator,
//                                     &mut self.denominator,
//                                     rhs.numerator,
//                                     rhs.denominator,
//                                 )
//                             }
//                         }
//                     }
//                 }
//                 impl MulAssign<&Self> for [<NonZeroRational $size>] {
//                     #[inline]
//                     fn mul_assign(&mut self, rhs: &Self) {
//                         self.sign *= rhs.sign;
//                         [<mul_ $size>](&mut self.numerator, &mut self.denominator, rhs.numerator, rhs.denominator);
//                     }
//                 }
//                 impl Div<[<NonZeroRational $size>]> for &[<NonZeroRational $size>] {
//                     type Output = [<NonZeroRational $size>];
//
//                     #[must_use]
//                     #[inline]
//                     fn div(self, mut rhs: [<NonZeroRational $size>]) -> Self::Output {
//                         let sign = self.sign * rhs.sign;
//                         [<mul_ $size>](&mut rhs.numerator, &mut rhs.denominator, self.denominator, self.numerator);
//                         Self::Output {
//                             sign,
//                             numerator: rhs.denominator,
//                             denominator: rhs.numerator,
//                         }
//                     }
//                 }
//                 impl DivAssign<&Self> for [<NonZeroRational $size>] {
//                     #[inline]
//                     fn div_assign(&mut self, rhs: &Self) {
//                         self.sign *= rhs.sign;
//                         [<mul_ $size>](&mut self.numerator, &mut self.denominator, rhs.denominator, rhs.numerator);
//                     }
//                 }
//             }
//         )*
//     }
// }
// rational_non_zero![8, 16, 32, 64, 128, "Size",];

// macro_rules! rational_non_negative {
//     [$($size:expr,)*] => {
//         $(
//             paste! {
//                 impl AddAssign<&Self> for [<NonNegativeRational $size>] {
//                     #[inline]
//                     fn add_assign(&mut self, rhs: &Self) {
//                         [<add_ $size>](
//                             &mut self.numerator,
//                             &mut self.denominator,
//                             rhs.numerator,
//                             rhs.denominator,
//                         )
//                     }
//                 }
//                 impl SubAssign<&Self> for [<NonNegativeRational $size>] {
//                     #[inline]
//                     fn sub_assign(&mut self, rhs: &Self) {
//                         let sign_change = [<sub_ $size>](
//                             &mut self.numerator,
//                             &mut self.denominator,
//                             rhs.numerator,
//                             rhs.denominator,
//                         );
//                         if sign_change == SignChange::Flip {
//                             panic!("attempt to subtract with overflow");
//                         }
//                     }
//                 }
//                 impl MulAssign<&Self> for [<NonNegativeRational $size>] {
//                     #[inline]
//                     fn mul_assign(&mut self, rhs: &Self) {
//                         [<mul_ $size>](&mut self.numerator, &mut self.denominator, rhs.numerator, rhs.denominator);
//                     }
//                 }
//                 impl Div<[<NonNegativeRational $size>]> for &[<NonNegativeRational $size>] {
//                     type Output = [<NonNegativeRational $size>];
//
//                     #[must_use]
//                     #[inline]
//                     fn div(self, mut rhs: [<NonNegativeRational $size>]) -> Self::Output {
//                         if rhs.is_zero() {
//                             panic!("attempt to divide by zero");
//                         }
//
//                         [<mul_ $size>](&mut rhs.numerator, &mut rhs.denominator, self.denominator, self.numerator);
//                         Self::Output {
//                             numerator: rhs.denominator,
//                             denominator: rhs.numerator,
//                         }
//                     }
//                 }
//                 impl DivAssign<&Self> for [<NonNegativeRational $size>] {
//                     #[inline]
//                     fn div_assign(&mut self, rhs: &Self) {
//                         [<mul_ $size>](&mut self.numerator, &mut self.denominator, rhs.denominator, rhs.numerator);
//                     }
//                 }
//             }
//         )*
//     }
// }
// rational_non_negative![8, 16, 32, 64, 128, "Size",];

macro_rules! rational_requiring_wide {
    ($name:ident, $uty:ty, $BITS:literal, $wide:ty, $sign:ident) => {
        impl Ord for $name {
            #[must_use]
            #[inline]
            fn cmp(&self, other: &Self) -> Ordering {
                self.partial_cmp(other).unwrap()
            }
        }

        impl PartialOrd for $name {
            #[must_use]
            #[inline]
            #[allow(unreachable_patterns)]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                self.sign.partial_cmp(&other.sign).or_else(|| {
                    debug_assert_eq!(self.sign, other.sign);
                    debug_assert!(self.is_not_zero());

                    let widening_mul = |left, right| {
                        let wide = unsafe { (left as $wide).unchecked_mul(right as $wide) };
                        ((wide >> $BITS) as $uty, wide as $uty)
                    };

                    let ad = widening_mul(self.numerator, other.denominator);
                    let bc = widening_mul(self.denominator, other.numerator);

                    Some(match (ad.cmp(&bc), self.sign) {
                        (Ordering::Less, $sign::Positive) | (Ordering::Greater, $sign::Negative) => Ordering::Less,
                        (Ordering::Equal, _) => Ordering::Equal,
                        (Ordering::Greater, $sign::Positive) | (Ordering::Less, $sign::Negative) => Ordering::Greater,
                        _ => panic!("Zero case would have been equal or nonzero type"),
                    })
                })
            }
        }
    }
}
rational_requiring_wide!(Rational8, u8, 8, u16, Sign);
rational_requiring_wide!(Rational16, u16, 16, u32, Sign);
rational_requiring_wide!(Rational32, u32, 32, u64, Sign);
rational_requiring_wide!(Rational64, u64, 64, u128, Sign);
rational_requiring_wide!(NonZeroRational8, u8, 8, u16, NonZeroSign);
rational_requiring_wide!(NonZeroRational16, u16, 16, u32, NonZeroSign);
rational_requiring_wide!(NonZeroRational32, u32, 32, u64, NonZeroSign);
rational_requiring_wide!(NonZeroRational64, u64, 64, u128, NonZeroSign);
rational_requiring_wide!(NonNegativeRational8, u8, 8, u16, NonNegativeSign);
rational_requiring_wide!(NonNegativeRational16, u16, 16, u32, NonNegativeSign);
rational_requiring_wide!(NonNegativeRational32, u32, 32, u64, NonNegativeSign);
rational_requiring_wide!(NonNegativeRational64, u64, 64, u128, NonNegativeSign);
