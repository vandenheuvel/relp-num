use std::convert::TryInto;
use std::fmt;
use std::str::FromStr;

use num_traits::Zero;
use num_traits::ToPrimitive;

use crate::non_zero::NonZeroSign;
use crate::rational::big::Big;
use crate::rational::small::{Rational128, Rational16, Rational32, Rational64, Rational8, RationalUsize};
use crate::rational::small::{NonZeroRational128, NonZeroRational16, NonZeroRational32, NonZeroRational64, NonZeroRational8, NonZeroRationalUsize};
use crate::rational::small::ops::building_blocks::{gcd128, gcd16, gcd32, gcd64, gcd8, gcd_usize};
use crate::rational::small::ops::building_blocks::{simplify128, simplify16, simplify32, simplify64, simplify8, simplify_usize};
use crate::sign::{Sign, Signed};

macro_rules! signed_floor {
    ($value:expr, $target:ty, $unsigned_target:ty) => {
        {
            let floor = $value.numerator / $value.denominator;
            // The magnitude is converted to the *unsigned* target, because the most negative value
            // of the target has a magnitude one larger than its largest positive value. Converting
            // to the signed target and negating afterwards would reject exactly that value.
            let magnitude: Option<$unsigned_target> = floor.try_into().ok();

            magnitude.and_then(|magnitude| match $value.sign {
                Sign::Zero | Sign::Positive => <$target>::try_from(magnitude).ok(),
                Sign::Negative => {
                    if magnitude <= <$target>::MIN.unsigned_abs() {
                        // Negation in the unsigned domain, where the magnitude of the most
                        // negative value is representable; the bit pattern is the same.
                        Some(magnitude.wrapping_neg() as $target)
                    } else {
                        None
                    }
                }
            })
        }
    }
}

macro_rules! unsigned_floor {
    ($value:expr) => {
        {
            match $value.sign {
                Sign::Zero | Sign::Positive => {
                    let floor = $value.numerator / $value.denominator;
                    floor.try_into().ok()
                }
                Sign::Negative => None,
            }
        }
    }
}

macro_rules! float {
    ($value:expr, $target:ty) => {
        {
            let ratio = $value.numerator as $target / $value.denominator as $target;
            let signed_ratio = match $value.sign {
                Sign::Zero | Sign::Positive => ratio,
                Sign::Negative => -ratio,
            };

            Some(signed_ratio)
        }
    }
}

macro_rules! creation {
    ($name:ident, $ity:ty, $uty:ty, $gcd_name:ident, $simplify_name:ident) => {
        impl $name {
            /// A ratio in lowest terms, or `None` when the denominator is zero.
            ///
            /// # Range
            ///
            /// The magnitude of this type is stored unsigned, while this constructor takes a
            /// signed numerator of the same width. A `Rational8` therefore represents every value
            /// from `-255` to `255`, but this constructor only reaches `-128` to `127`; the values
            /// in between are reached by [`FromStr`](std::str::FromStr), by
            /// [`FromPrimitive`](num_traits::FromPrimitive) from a wider primitive, and by
            /// arithmetic. They are representable but not convertible back:
            /// [`to_i8`](num_traits::ToPrimitive::to_i8) returns `None` for them, because an `i8`
            /// is what doesn't fit, not the ratio.
            #[must_use]
            pub fn new(numerator: $ity, mut denominator: $uty) -> Option<Self> {
                if denominator.is_zero() {
                    None
                } else {
                    Some({
                        let mut numerator_abs = numerator.unsigned_abs();
                        if numerator == 0 {
                            <Self as num_traits::Zero>::zero()
                        } else if numerator_abs == denominator {
                            Self {
                                sign: Signed::signum(&numerator),
                                numerator: 1,
                                denominator: 1,
                            }
                        } else {
                            if numerator_abs != 1 && denominator != 1 {
                                // Note that this gcd is computed at the width of this type; casting
                                // to `usize` first would discard the high bits of a `u128`.
                                let gcd = $gcd_name(numerator_abs, denominator);

                                numerator_abs /= gcd;
                                denominator /= gcd;
                            }

                            Self {
                                sign: Signed::signum(&numerator),
                                numerator: numerator_abs,
                                denominator,
                            }
                        }
                    })
                }
            }
            /// A ratio in lowest terms from a sign and a magnitude.
            ///
            /// # Return value
            ///
            /// `None` when the arguments describe no number: the denominator has to be nonzero,
            /// and the sign has to be [`Sign::Zero`] exactly when the numerator is zero. These
            /// invariants used to be checked with `debug_assert!` only, which let a release build
            /// construct a ratio with a zero denominator; `Big::new_signed` returns an `Option`
            /// for the same reason.
            #[must_use]
            pub fn new_signed<T: Into<Sign>>(sign: T, numerator: $uty, denominator: $uty) -> Option<Self> {
                if denominator == 0 {
                    return None;
                }

                match (sign.into(), numerator) {
                    (Sign::Zero, 0) => Some(<Self as num_traits::Zero>::zero()),
                    // `$simplify_name` doesn't terminate on a zero numerator.
                    (sign @ (Sign::Positive | Sign::Negative), numerator) if numerator != 0 => {
                        let (numerator, denominator) = $simplify_name(numerator, denominator);

                        Some(Self {
                            sign,
                            numerator,
                            denominator,
                        })
                    }
                    _ => None,
                }
            }
        }

        impl Default for $name {
            fn default() -> Self {
                Self::zero()
            }
        }

        /// Renders exactly like [`Display`](fmt::Display), so the output parses back.
        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(self, f)
            }
        }

        impl num_traits::FromPrimitive for $name {
            #[inline]
            fn from_i64(n: i64) -> Option<Self> {
                if n.unsigned_abs() <= <$uty>::MAX as u64 {
                    Some(Self {
                        sign: Signed::signum(&n),
                        numerator: n.unsigned_abs() as $uty,
                        denominator: 1,
                    })
                } else {
                    None
                }
            }

            #[inline]
            fn from_u64(n: u64) -> Option<Self> {
                if n <= <$uty>::MAX as u64 {
                    Some(Self {
                        sign: Signed::signum(&n),
                        numerator: n as $uty,
                        denominator: 1,
                    })
                } else {
                    None
                }
            }

            /// The default implementation goes through [`from_i64`](num_traits::FromPrimitive::from_i64),
            /// which discards every value that only a wider magnitude type can hold.
            #[inline]
            fn from_i128(n: i128) -> Option<Self> {
                let numerator = n.unsigned_abs().try_into().ok()?;

                Some(Self {
                    sign: Signed::signum(&n),
                    numerator,
                    denominator: 1,
                })
            }

            /// The default implementation goes through [`from_u64`](num_traits::FromPrimitive::from_u64),
            /// which discards every value that only a wider magnitude type can hold.
            #[inline]
            fn from_u128(n: u128) -> Option<Self> {
                let numerator = n.try_into().ok()?;

                Some(Self {
                    sign: Signed::signum(&n),
                    numerator,
                    denominator: 1,
                })
            }

            #[inline]
            fn from_f32(n: f32) -> Option<Self> {
                Big::<8>::from_f32(n).map(Self::from_big_if_it_fits).flatten()
            }

            #[inline]
            fn from_f64(n: f64) -> Option<Self> {
                Big::<16>::from_f64(n).map(Self::from_big_if_it_fits).flatten()
            }
        }

        impl ToPrimitive for $name {
            fn to_isize(&self) -> Option<isize> {
                signed_floor!(self, isize, usize)
            }

            fn to_i8(&self) -> Option<i8> {
                signed_floor!(self, i8, u8)
            }

            fn to_i16(&self) -> Option<i16> {
                signed_floor!(self, i16, u16)
            }

            fn to_i32(&self) -> Option<i32> {
                signed_floor!(self, i32, u32)
            }

            fn to_i64(&self) -> Option<i64> {
                signed_floor!(self, i64, u64)
            }

            fn to_i128(&self) -> Option<i128> {
                signed_floor!(self, i128, u128)
            }

            fn to_usize(&self) -> Option<usize> {
                unsigned_floor!(self)
            }

            fn to_u8(&self) -> Option<u8> {
                unsigned_floor!(self)
            }

            fn to_u16(&self) -> Option<u16> {
                unsigned_floor!(self)
            }

            fn to_u32(&self) -> Option<u32> {
                unsigned_floor!(self)
            }

            fn to_u64(&self) -> Option<u64> {
                unsigned_floor!(self)
            }

            fn to_u128(&self) -> Option<u128> {
                unsigned_floor!(self)
            }

            fn to_f32(&self) -> Option<f32> {
                float!(self, f32)
            }

            fn to_f64(&self) -> Option<f64> {
                float!(self, f64)
            }
        }

        impl FromStr for $name {
            type Err = &'static str;

            fn from_str(from: &str) -> Result<Self, Self::Err> {
                Big::<8>::from_str(from)
                    .map(|big| match Self::from_big_if_it_fits(big) {
                        Some(value) => Ok(value),
                        None => Err("value was too large for this type"),
                    })
                    .flatten()
            }
        }

        impl $name {
            fn from_big_if_it_fits<const S: usize>(big: Big<S>) -> Option<Self> {
                if num_traits::Zero::is_zero(&big) {
                    return Some(<Self as num_traits::Zero>::zero());
                }

                /// The number of `usize` words of a `Big` that this magnitude type can hold.
                ///
                /// At least one, also when a `usize` is not narrower than the magnitude type; a
                /// single word that is too large is rejected by the conversion below instead.
                const WORDS: usize = {
                    let words = std::mem::size_of::<$uty>() / std::mem::size_of::<usize>();
                    if words > 0 { words } else { 1 }
                };

                /// Reassemble the little endian `usize` words of a `Big` magnitude.
                fn scalar(words: &[usize]) -> Option<$uty> {
                    if words.len() > WORDS {
                        // More words than the magnitude type has room for, whatever they contain.
                        return None;
                    }

                    // `WORDS` words of a `usize` are never more than the 128 bits of the
                    // accumulator, so no shift below reaches its width.
                    let mut value = 0_u128;
                    for (index, &word) in words.iter().enumerate() {
                        value |= (word as u128) << (index as u32 * usize::BITS);
                    }

                    // A single word can still be too large, when the magnitude type is narrower
                    // than a `usize`.
                    value.try_into().ok()
                }

                Some(Self {
                    sign: big.sign,
                    numerator: scalar(&big.numerator)?,
                    denominator: scalar(&big.denominator)?,
                })
            }
        }

        impl From<&$name> for $name {
            #[inline]
            fn from(other: &$name) -> Self {
                *other
            }
        }

        impl num_traits::Zero for $name {
            #[inline]
            fn zero() -> Self {
                Self {
                    sign: Sign::Zero,
                    numerator: 0,
                    denominator: 1,
                }
            }

            #[inline]
            fn set_zero(&mut self) {
                self.sign = Sign::Zero;
                self.numerator = 0;
                self.denominator = 1;
            }

            #[inline]
            fn is_zero(&self) -> bool {
                self.sign == Sign::Zero
            }
        }
    }
}

creation!(Rational8, i8, u8, gcd8, simplify8);
creation!(Rational16, i16, u16, gcd16, simplify16);
creation!(Rational32, i32, u32, gcd32, simplify32);
creation!(Rational64, i64, u64, gcd64, simplify64);
creation!(Rational128, i128, u128, gcd128, simplify128);
creation!(RationalUsize, isize, usize, gcd_usize, simplify_usize);

macro_rules! impl_one {
    ($name:ident, $sign:ident) => {
        impl num_traits::One for $name {
            #[inline]
            fn one() -> Self {
                Self {
                    sign: $sign::Positive,
                    numerator: 1,
                    denominator: 1,
                }
            }

            #[inline]
            fn set_one(&mut self) {
                self.sign = $sign::Positive;
                self.numerator = 1;
                self.denominator = 1;
            }

            #[inline]
            fn is_one(&self) -> bool {
                self.numerator == 1 && self.denominator == 1 && self.sign == $sign::Positive
            }
        }
    }
}
impl_one!(Rational8, Sign);
impl_one!(Rational16, Sign);
impl_one!(Rational32, Sign);
impl_one!(Rational64, Sign);
impl_one!(Rational128, Sign);
impl_one!(RationalUsize, Sign);
impl_one!(NonZeroRational8, NonZeroSign);
impl_one!(NonZeroRational16, NonZeroSign);
impl_one!(NonZeroRational32, NonZeroSign);
impl_one!(NonZeroRational64, NonZeroSign);
impl_one!(NonZeroRational128, NonZeroSign);
impl_one!(NonZeroRationalUsize, NonZeroSign);

macro_rules! size_dependent_unsigned {
    ($name:ty, $uty:ty, $other:ty, $simplify:ident) => {
        impl From<$other> for $name {
            #[inline]
            fn from(other: $other) -> Self {
                Self {
                    sign: Signed::signum(&other),
                    numerator: other as $uty,
                    denominator: 1,
                }
            }
        }
        impl From<&$other> for $name {
            #[inline]
            fn from(other: &$other) -> Self {
                Self {
                    sign: Signed::signum(other),
                    numerator: *other as $uty,
                    denominator: 1,
                }
            }
        }
        impl From<($other, $other)> for $name {
            #[inline]
            fn from(other: ($other, $other)) -> Self {
                assert_ne!(other.1, 0, "attempt to divide by zero");

                // `$simplify` doesn't terminate on a zero numerator.
                if other.0 == 0 {
                    return <Self as num_traits::Zero>::zero();
                }

                let (numerator, denominator) = $simplify(other.0, other.1);

                Self {
                    sign: Signed::signum(&other.0) * Signed::signum(&other.1),
                    numerator: numerator as $uty,
                    denominator: denominator as $uty,
                }
            }
        }
    }
}

size_dependent_unsigned!(Rational8, u8, u8, simplify8);
size_dependent_unsigned!(Rational16, u16, u8, simplify8);
size_dependent_unsigned!(Rational16, u16, u16, simplify16);
size_dependent_unsigned!(Rational32, u32, u8, simplify8);
size_dependent_unsigned!(Rational32, u32, u16, simplify16);
size_dependent_unsigned!(Rational32, u32, u32, simplify32);
size_dependent_unsigned!(Rational64, u64, u8, simplify8);
size_dependent_unsigned!(Rational64, u64, u16, simplify16);
size_dependent_unsigned!(Rational64, u64, u32, simplify32);
size_dependent_unsigned!(Rational64, u64, u64, simplify64);
size_dependent_unsigned!(Rational128, u128, u8, simplify8);
size_dependent_unsigned!(Rational128, u128, u16, simplify16);
size_dependent_unsigned!(Rational128, u128, u32, simplify32);
size_dependent_unsigned!(Rational128, u128, u64, simplify64);
size_dependent_unsigned!(Rational128, u128, u128, simplify128);

macro_rules! size_dependent_signed {
    ($name:ty, $uty:ty, $other_signed:ty, $simplify:ident) => {
        impl From<$other_signed> for $name {
            #[inline]
            fn from(other: $other_signed) -> Self {
                Self {
                    sign: Signed::signum(&other),
                    numerator: other.unsigned_abs() as $uty,
                    denominator: 1,
                }
            }
        }
        impl From<&$other_signed> for $name {
            #[inline]
            fn from(other: &$other_signed) -> Self {
                Self {
                    sign: Signed::signum(other),
                    numerator: other.unsigned_abs() as $uty,
                    denominator: 1,
                }
            }
        }
        impl From<($other_signed, $other_signed)> for $name {
            #[inline]
            fn from(other: ($other_signed, $other_signed)) -> Self {
                assert_ne!(other.1, 0, "attempt to divide by zero");

                // `$simplify` doesn't terminate on a zero numerator.
                if other.0 == 0 {
                    return <Self as num_traits::Zero>::zero();
                }

                let (numerator, denominator) = $simplify(other.0.unsigned_abs(), other.1.unsigned_abs());

                Self {
                    sign: Signed::signum(&other.0) * Signed::signum(&other.1),
                    numerator: numerator as $uty,
                    denominator: denominator as $uty,
                }
            }
        }
    }
}

size_dependent_signed!(Rational8, u8, i8, simplify8);
size_dependent_signed!(Rational16, u16, i8, simplify8);
size_dependent_signed!(Rational16, u16, i16, simplify16);
size_dependent_signed!(Rational32, u32, i8, simplify8);
size_dependent_signed!(Rational32, u32, i16, simplify16);
size_dependent_signed!(Rational32, u32, i32, simplify32);
size_dependent_signed!(Rational64, u64, i8, simplify8);
size_dependent_signed!(Rational64, u64, i16, simplify16);
size_dependent_signed!(Rational64, u64, i32, simplify32);
size_dependent_signed!(Rational64, u64, i64, simplify64);
size_dependent_signed!(Rational128, u128, i8, simplify8);
size_dependent_signed!(Rational128, u128, i16, simplify16);
size_dependent_signed!(Rational128, u128, i32, simplify32);
size_dependent_signed!(Rational128, u128, i64, simplify64);
size_dependent_signed!(Rational128, u128, i128, simplify128);

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use num_traits::{FromPrimitive, ToPrimitive};

    use crate::{R16, R32, R64, R8, Rational128, Rational16, Rational32, Rational64, Rational8, RationalUsize};
    use crate::rational::Ratio;
    use crate::sign::Sign;

    #[test]
    fn test_debug() {
        assert_eq!(format!("{:?}", R8!(2, 3)), "2/3");
        assert_eq!(format!("{:?}", R8!(0)), "0");
        assert_eq!(format!("{:?}", R8!(-1)), "-1");
        assert_eq!(format!("{:?}", R8!(-0)), "0");
        assert_eq!(format!("{:?}", -R8!(2, 3)), "-2/3");
    }

    /// `Debug` output has to parse back, which means rendering it exactly like `Display`.
    #[test]
    fn test_debug_round_trips() {
        for value in [R8!(2, 3), R8!(0), R8!(-1), R8!(1), R8!(-2, 3), R8!(127, 2)] {
            let rendered = format!("{value:?}");
            assert_eq!(rendered, format!("{value}"));
            assert_eq!(Rational8::from_str(&rendered), Ok(value), "{rendered}");
        }
    }

    #[test]
    fn test_from() {
        assert_eq!(Rational8::from(4_u8), R8!(4));
        assert_eq!(Rational16::from(-4_i8), R16!(-4));
        assert_eq!(Rational8::from(&4_u8), R8!(4));
        assert_eq!(Rational16::from(&-4_i8), R16!(-4));
        assert_eq!(Rational16::from((-4_i8, 2_i8)), R16!(-2));
        assert_eq!(Rational16::from((4_u8, 2_u8)), R16!(2));
    }

    #[test]
    fn test_to_primitive() {
        assert_eq!(R8!(0).to_u8(), Some(0));
        assert_eq!(R8!(1, 2).to_u8(), Some(0));
        assert_eq!(R8!(3, 4).to_i8(), Some(0));
        assert_eq!(R8!(3, 2).to_i8(), Some(1));
        assert_eq!(R8!(-0).to_i8(), Some(0));
        assert_eq!(R8!(-1, 2).to_i8(), Some(0));
        assert_eq!(R8!(-3, 4).to_i8(), Some(0));
        assert_eq!(R8!(-3, 2).to_i8(), Some(-1));

        assert_eq!(Rational8::new(1, 1).unwrap().to_i32(), Some(1));
        assert_eq!(R8!(-10).to_i32(), Some(-10));
        assert_eq!(R8!(-11).to_u16(), None);
        assert_eq!(R64!(2_u64.pow(63) + 2_u64.pow(20)).to_i64(), None);
        assert_eq!(R8!(0).to_i64(), Some(0));
        assert_eq!(R8!(0).to_u64(), Some(0));
        assert_eq!(R8!(1, 2).to_u64(), Some(0));
        assert_eq!(R8!(8).to_u64(), Some(8));

        assert_eq!(R8!(0).to_f64(), Some(0_f64));
        assert_eq!(R32!(-156, 99).to_f64(), Some(-156_f64 / 99_f64));
        assert_eq!(R8!(3, 2).to_f64(), Some(1.5_f64));
        assert_eq!(R8!(-0).to_f64(), Some(0_f64));
        assert_eq!(R8!(-3, 2).to_f64(), Some(-1.5_f64));
    }

    /// The invariants used to be checked with `debug_assert!`, so a release build accepted them.
    #[test]
    fn test_new_signed_invalid() {
        // A zero denominator used to build a ratio that divides by zero.
        assert_eq!(Rational8::new_signed(Sign::Positive, 1, 0), None);
        assert_eq!(Rational8::new_signed(Sign::Zero, 0, 0), None);
        assert_eq!(Rational128::new_signed(Sign::Negative, u128::MAX, 0), None);

        // A sign that disagrees with the numerator.
        assert_eq!(Rational64::new_signed(Sign::Zero, 1, 1), None);
        assert_eq!(Rational64::new_signed(Sign::Positive, 0, 1), None);
        assert_eq!(Rational64::new_signed(Sign::Negative, 0, 1), None);

        // Valid arguments are unchanged.
        assert_eq!(Rational64::new_signed(Sign::Positive, 6, 18), Rational64::new(1, 3));
        assert_eq!(Rational64::new_signed(Sign::Zero, 0, 6), Some(R64!(0)));
        assert_eq!(Rational64::new_signed(Sign::Negative, 9, 18), Some(-R64!(1, 2)));
        assert_eq!(Rational128::new_signed(Sign::Negative, u128::MAX, 1).unwrap().numerator, u128::MAX);
    }

    /// The magnitude of the most negative value of a target doesn't fit its positive range.
    #[test]
    fn test_to_primitive_most_negative() {
        assert_eq!(Rational8::from_str("-128").unwrap().to_i8(), Some(i8::MIN));
        assert_eq!(Rational8::from_str("-129").unwrap().to_i8(), None);
        assert_eq!(Rational8::from_str("128").unwrap().to_i8(), None);
        assert_eq!(Rational8::from_str("-255/2").unwrap().to_i8(), Some(-127));
        assert_eq!(Rational16::from_str("-257/2").unwrap().to_i8(), Some(i8::MIN));

        assert_eq!(Rational16::from_str("-32768").unwrap().to_i16(), Some(i16::MIN));
        assert_eq!(Rational16::from_str("-32769").unwrap().to_i16(), None);

        assert_eq!(Rational64::from_i64(i64::MIN).unwrap().to_i64(), Some(i64::MIN));
        assert_eq!(Rational64::from_i64(i64::MIN).unwrap().to_i32(), None);
        assert_eq!(Rational128::from_i128(i128::MIN).unwrap().to_i128(), Some(i128::MIN));
        assert_eq!(Rational128::from_i128(i128::MIN).unwrap().to_i64(), None);
        assert_eq!(Rational128::from_i64(i64::MIN).unwrap().to_i64(), Some(i64::MIN));

        // The most negative `isize`, whose magnitude a `RationalUsize` can hold.
        let value: RationalUsize = Ratio {
            sign: Sign::Negative,
            numerator: 1 << (usize::BITS - 1),
            denominator: 1,
        };
        assert_eq!(value.to_isize(), Some(isize::MIN));
        let value: RationalUsize = Ratio { sign: Sign::Negative, numerator: usize::MAX, denominator: 1 };
        assert_eq!(value.to_isize(), None);

        // Truncation towards zero and the unsigned conversions are unchanged.
        assert_eq!(R8!(-3, 2).to_i8(), Some(-1));
        assert_eq!(R8!(-0).to_i8(), Some(0));
        assert_eq!(R8!(-1).to_u8(), None);
        assert_eq!(R8!(127).to_i8(), Some(127));
    }

    /// Values that need more than a single `usize` word of the `Big` they are parsed into.
    #[test]
    fn test_from_str_above_64_bits() {
        let value = Rational128::from_str("18446744073709551616").unwrap();
        assert_eq!(value.sign, Sign::Positive);
        assert_eq!(value.numerator, 1 << 64);
        assert_eq!(value.denominator, 1);

        let value = Rational128::from_str(&i128::MAX.to_string()).unwrap();
        assert_eq!(value.numerator, i128::MAX as u128);
        assert_eq!(value.denominator, 1);

        let value = Rational128::from_str(&u128::MAX.to_string()).unwrap();
        assert_eq!(value.numerator, u128::MAX);
        assert_eq!(value.denominator, 1);

        let value = Rational128::from_str(&format!("-{}", u128::MAX)).unwrap();
        assert_eq!(value.sign, Sign::Negative);
        assert_eq!(value.numerator, u128::MAX);

        // A denominator of more than one word.
        let value = Rational128::from_str("1/18446744073709551616").unwrap();
        assert_eq!(value.numerator, 1);
        assert_eq!(value.denominator, 1 << 64);

        // One word too many is still rejected, at every width; this is `2 ^ 128`.
        assert_eq!(
            Rational128::from_str("340282366920938463463374607431768211456"),
            Err("value was too large for this type"),
        );
        assert_eq!(Rational64::from_str("18446744073709551616"), Err("value was too large for this type"));
        assert_eq!(Rational32::from_str("4294967296"), Err("value was too large for this type"));
        assert_eq!(Rational8::from_str("256"), Err("value was too large for this type"));
        assert_eq!(Rational8::from_str("1/256"), Err("value was too large for this type"));
        assert_eq!(RationalUsize::from_str(&usize::MAX.to_string()).unwrap().numerator, usize::MAX);
        assert_eq!(
            RationalUsize::from_str(&(usize::MAX as u128 + 1).to_string()),
            Err("value was too large for this type"),
        );
    }

    /// Floats larger than a `u64`, which are parsed into a multi word `Big` as well.
    #[test]
    fn test_from_f64_above_64_bits() {
        // `1e30` is exactly representable in an `f64`, as this many.
        let value = Rational128::from_f64(1e30).unwrap();
        assert_eq!(value.numerator, 1_000_000_000_000_000_019_884_624_838_656);
        assert_eq!(value.denominator, 1);

        let value = Rational128::from_f64(-(2_f64.powi(100))).unwrap();
        assert_eq!(value.sign, Sign::Negative);
        assert_eq!(value.numerator, 1 << 100);
        assert_eq!(value.denominator, 1);

        let value = Rational128::from_f32(2_f32.powi(80)).unwrap();
        assert_eq!(value.numerator, 1 << 80);

        // `2 ^ 128` needs one word more than a `u128` has.
        assert_eq!(Rational128::from_f64(2_f64.powi(128)), None);
        assert_eq!(Rational128::from_f64(u128::MAX as f64), None);
        assert_eq!(Rational64::from_f64(1e30), None);
    }

    /// The default implementations of these two route through the 64 bit ones.
    #[test]
    fn test_from_128_bit_primitive() {
        assert_eq!(Rational128::from_i128(i128::MAX).unwrap().numerator, i128::MAX as u128);
        assert_eq!(Rational128::from_i128(i128::MIN).unwrap().numerator, 1 << 127);
        assert_eq!(Rational128::from_i128(i128::MIN).unwrap().sign, Sign::Negative);
        assert_eq!(Rational128::from_u128(u128::MAX).unwrap().numerator, u128::MAX);
        assert_eq!(Rational128::from_i128(0).unwrap(), <Rational128 as num_traits::Zero>::zero());

        assert_eq!(RationalUsize::from_u128(usize::MAX as u128).unwrap().numerator, usize::MAX);
        assert_eq!(RationalUsize::from_u128(usize::MAX as u128 + 1), None);

        assert_eq!(Rational64::from_i128(i128::MAX), None);
        assert_eq!(Rational64::from_u128(u128::MAX), None);
        assert_eq!(Rational64::from_i128(i64::MIN as i128).unwrap().numerator, 1 << 63);
        assert_eq!(Rational8::from_i128(-128).unwrap().numerator, 128);
        assert_eq!(Rational8::from_i128(-256), None);
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn test_from_div_zero() {
        Rational32::from((4, 0));
    }

    #[test]
    fn test_from_tuple_zero_numerator() {
        // A zero numerator used to be handed to `simplify`, which doesn't terminate on it.
        macro_rules! assert_canonical_zero {
            ($value:expr) => {{
                let value = $value;
                assert_eq!(value.sign, Sign::Zero);
                assert_eq!(value.numerator, 0);
                assert_eq!(value.denominator, 1);
            }}
        }

        // Signed tuples
        assert_canonical_zero!(Rational8::from((0_i8, 5_i8)));
        assert_canonical_zero!(Rational32::from((0_i32, 5_i32)));
        assert_canonical_zero!(Rational32::from((0_i16, -3_i16)));
        assert_canonical_zero!(Rational128::from((0_i128, -7_i128)));

        // Unsigned tuples
        assert_canonical_zero!(Rational8::from((0_u8, 5_u8)));
        assert_canonical_zero!(Rational32::from((0_u32, 5_u32)));
        assert_canonical_zero!(Rational32::from((0_u16, 3_u16)));
        assert_canonical_zero!(Rational128::from((0_u128, 7_u128)));

        assert_eq!(Rational32::from((0_i32, 5_i32)), R32!(0));
        assert_eq!(Rational32::from((0_u32, 5_u32)), R32!(0));
    }

    #[test]
    fn test_new_128_bit_gcd() {
        // The gcd used to be computed after casting both arguments to `usize`, discarding the
        // high 64 bits on a 64-bit platform.
        let value = Rational128::new(3 << 64, 2_u128 << 64).unwrap();
        assert_eq!(value.sign, Sign::Positive);
        assert_eq!(value.numerator, 3);
        assert_eq!(value.denominator, 2);

        let value = Rational128::new(6, 1_u128 << 64).unwrap();
        assert_eq!(value.numerator, 3);
        assert_eq!(value.denominator, 1_u128 << 63);

        // Numerator and denominator both larger than 64 bits, result in lowest terms.
        let value = Rational128::new(6_i128 << 70, 4_u128 << 70).unwrap();
        assert_eq!(value.numerator, 3);
        assert_eq!(value.denominator, 2);

        // The low 64 bits of these are 3 and 2, coprime, while the actual gcd is 2 ^ 64 + 1.
        let large_factor = (1_i128 << 64) + 1;
        let value = Rational128::new(3 * large_factor, 2 * large_factor as u128).unwrap();
        assert_eq!(value.sign, Sign::Positive);
        assert_eq!(value.numerator, 3);
        assert_eq!(value.denominator, 2);

        let value = Rational128::new(-(5 << 100), 15_u128 << 100).unwrap();
        assert_eq!(value.sign, Sign::Negative);
        assert_eq!(value.numerator, 1);
        assert_eq!(value.denominator, 3);
    }
}
