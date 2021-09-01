use std::{fmt, mem};
use std::cmp::{min, Ordering};
use std::convert::TryFrom;
use std::convert::TryInto;
use std::iter::repeat;
use std::num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize};
use std::num::{NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize};
use std::str::FromStr;

use num_traits::{FromPrimitive, One, ToPrimitive, Zero};
use smallvec::{smallvec, SmallVec};

use crate::{NonZero, NonZeroSign, Ubig};
use crate::integer::big::{BITS_PER_WORD, NonZeroUbig};
use crate::integer::big::ops::div::div;
use crate::integer::big::ops::non_zero::is_one_non_zero;
use crate::integer::big::ops::normalize::{gcd_scalar, simplify_fraction_without_info};
use crate::integer::big::properties::cmp;
use crate::rational::big::{Big, NonZeroBig};
use crate::rational::Ratio;
use crate::rational::small::ops::building_blocks::{simplify128, simplify16, simplify32, simplify64, simplify8};
use crate::sign::Sign;
use crate::sign::Signed;

impl<const S: usize> Big<S> {
    pub fn new(numerator: i64, denominator: u64) -> Option<Self> {
        if 0 != denominator {
            Some({
                let mut numerator_abs = numerator.unsigned_abs() as usize;
                let mut denominator = denominator as usize;
                if numerator == 0 {
                    Self::zero()
                } else if numerator_abs == denominator {
                    Self {
                        sign: Signed::signum(&numerator),
                        numerator: Ubig::one(),
                        denominator: NonZeroUbig::one(),
                    }
                } else {
                    if numerator_abs != 1 && denominator != 1 {
                        let gcd = gcd_scalar(numerator_abs, denominator);

                        numerator_abs /= gcd;
                        denominator /= gcd;
                    }

                    Self {
                        sign: Signed::signum(&numerator),
                        numerator: Ubig::new(numerator_abs),
                        denominator: unsafe { NonZeroUbig::new_unchecked(denominator) },
                    }
                }
            })
        } else {
            None
        }
    }
}

impl<const S: usize> Default for Big<S> {
    fn default() -> Self {
        Self::zero()
    }
}

impl<const S: usize> fmt::Debug for Big<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.sign {
            Sign::Positive => {}
            Sign::Zero => return f.write_str("0"),
            Sign::Negative => f.write_str("-")?,
        }

        if self.numerator.len() == 1 {
            fmt::Debug::fmt(&self.numerator.first().unwrap(), f)?;
        } else {
            fmt::Debug::fmt(self.numerator.inner(), f)?;
        }

        if !self.denominator.is_one() {
            f.write_str(" / ")?;
            if self.denominator.len() == 1 {
                fmt::Debug::fmt(self.denominator.first(), f)?;
            } else {
                fmt::Debug::fmt(&self.denominator.inner(), f)?;
            }
        }

        Ok(())
    }
}

macro_rules! forwards {
    ($ty:ty) => {
        impl<const S: usize> From<&$ty> for Big<S> {
            fn from(other: &$ty) -> Self {
                From::from(*other)
            }
        }
    }
}

forwards!(u8);
forwards!(u16);
forwards!(u32);
forwards!(u64);
forwards!(NonZeroU8);
forwards!(NonZeroU16);
forwards!(NonZeroU32);
forwards!(NonZeroU64);
forwards!(i8);
forwards!(i16);
forwards!(i32);
forwards!(i64);
forwards!(NonZeroI8);
forwards!(NonZeroI16);
forwards!(NonZeroI32);
forwards!(NonZeroI64);

macro_rules! from_integer_unsigned {
    ($ty:ty) => {
        impl<const S: usize> From<$ty> for Big<S> {
            fn from(value: $ty) -> Self {
                Self {
                    sign: Signed::signum(&value),
                    numerator: Ubig::from(value as usize),
                    denominator: NonZeroUbig::one(),
                }
            }
        }
    }
}

from_integer_unsigned!(u8);
from_integer_unsigned!(u16);
from_integer_unsigned!(u32);
from_integer_unsigned!(u64);
from_integer_unsigned!(usize);

macro_rules! from_integer_unsigned_non_zero {
    ($ty:ty) => {
        impl<const S: usize> From<$ty> for Big<S> {
            fn from(value: $ty) -> Self {
                Self {
                    sign: Signed::signum(&value),
                    numerator: Ubig::from(value.get() as usize),
                    denominator: NonZeroUbig::one(),
                }
            }
        }
    }
}

from_integer_unsigned_non_zero!(NonZeroU8);
from_integer_unsigned_non_zero!(NonZeroU16);
from_integer_unsigned_non_zero!(NonZeroU32);
from_integer_unsigned_non_zero!(NonZeroU64);
from_integer_unsigned_non_zero!(NonZeroUsize);

macro_rules! from_integer_signed {
    ($ty:ty) => {
        impl<const S: usize> From<$ty> for Big<S> {
            fn from(value: $ty) -> Self {
                Self {
                    sign: Signed::signum(&value),
                    numerator: Ubig::new(value.unsigned_abs() as usize),
                    denominator: NonZeroUbig::one(),
                }
            }
        }
    }
}

from_integer_signed!(i8);
from_integer_signed!(i16);
from_integer_signed!(i32);
from_integer_signed!(i64);
from_integer_signed!(isize);

macro_rules! from_integer_signed_non_zero {
    ($ty:ty) => {
        impl<const S: usize> From<$ty> for Big<S> {
            fn from(value: $ty) -> Self {
                Self {
                    sign: Signed::signum(&value),
                    numerator: Ubig::from(value.get().unsigned_abs() as usize),
                    denominator: NonZeroUbig::one(),
                }
            }
        }
    }
}

from_integer_signed_non_zero!(NonZeroI8);
from_integer_signed_non_zero!(NonZeroI16);
from_integer_signed_non_zero!(NonZeroI32);
from_integer_signed_non_zero!(NonZeroI64);
from_integer_signed_non_zero!(NonZeroIsize);

macro_rules! impl_from_iu {
    ($numerator:ty, $denominator:ty, $simplify:ident) => {
        impl<const S: usize> From<($numerator, $denominator)> for Big<S> {
            #[must_use]
            #[inline]
            fn from((numerator, denominator): ($numerator, $denominator)) -> Self {
                // This is for tests only at the moment, do a run time assert
                assert!(denominator.is_not_zero());

                if mem::size_of::<$numerator>() > mem::size_of::<usize>() {
                    debug_assert!(numerator.abs() <= usize::MAX as $numerator);
                }
                if mem::size_of::<$denominator>() > mem::size_of::<usize>() {
                    debug_assert!(denominator <= usize::MAX as $denominator);
                }

                if numerator == 0 {
                    <Self as num_traits::Zero>::zero()
                } else {
                    let sign = <$numerator as Signed>::signum(&numerator);
                    let (numerator, denominator) = $simplify(numerator.unsigned_abs(), denominator);

                    Self {
                        sign,
                        numerator: Ubig::new(numerator as usize),
                        denominator: NonZeroUbig::new(denominator as usize).unwrap(),
                    }
                }
            }
        }
    }
}

impl_from_iu!(i8, u8, simplify8);
impl_from_iu!(i16, u16, simplify16);
impl_from_iu!(i32, u32, simplify32);
impl_from_iu!(i64, u64, simplify64);
impl_from_iu!(i128, u128, simplify128);

macro_rules! impl_from_ii {
    ($ty:ty) => {
        impl<const S: usize> From<($ty, $ty)> for Big<S> {
            #[must_use]
            #[inline]
            fn from((numerator, denominator): ($ty, $ty)) -> Self {
                // This is for tests only at the moment, do a run time assert
                assert!(denominator.is_not_zero());

                if mem::size_of::<$ty>() > mem::size_of::<usize>() {
                    debug_assert!(numerator.abs() <= usize::MAX as $ty);
                }
                if mem::size_of::<$ty>() > mem::size_of::<usize>() {
                    debug_assert!(denominator <= usize::MAX as $ty);
                }

                let sign = <$ty as Signed>::signum(&numerator) * <$ty as Signed>::signum(&denominator);
                debug_assert_eq!(sign == Sign::Zero, numerator == 0);

                Self {
                    sign,
                    numerator: Ubig::from(numerator.unsigned_abs() as usize),
                    denominator: NonZeroUbig::new(denominator.unsigned_abs() as usize).unwrap(),
                }
            }
        }
    }
}

impl_from_ii!(i8);
impl_from_ii!(i16);
impl_from_ii!(i32);
impl_from_ii!(i64);
impl_from_ii!(i128);
impl_from_ii!(isize);

macro_rules! impl_from_ratio {
    ($numerator:ty, $denominator:ty, $denominator_inner:ty) => {
        impl<const S: usize> From<Ratio<Sign, $numerator, $denominator>> for Big<S> {
            fn from(ratio: Ratio<Sign, $numerator, $denominator>) -> Self {
                if mem::size_of::<$numerator>() > mem::size_of::<usize>() {
                    debug_assert!(ratio.numerator.abs() <= usize::MAX as $numerator);
                }
                if mem::size_of::<$numerator>() > mem::size_of::<$denominator>() {
                    debug_assert!(ratio.denominator.get() <= usize::MAX as $denominator_inner);
                }

                if ratio.sign == Sign::Zero {
                    <Self as num_traits::Zero>::zero()
                } else {
                    Self {
                        sign: ratio.sign,
                        numerator: Ubig::new(ratio.numerator.unsigned_abs() as usize),
                        denominator: unsafe {
                            // SAFETY: The denominator type is NonZeroU*
                            NonZeroUbig::new_unchecked(ratio.denominator.get() as usize)
                        },
                    }
                }
            }
        }
    }
}

impl_from_ratio!(i8, NonZeroU8, u8);
impl_from_ratio!(i16, NonZeroU16, u16);
impl_from_ratio!(i32, NonZeroU32, u32);
impl_from_ratio!(i64, NonZeroU64, u64);
impl_from_ratio!(i128, NonZeroU128, u128);
impl_from_ratio!(isize, NonZeroUsize, usize);

const ONES_32: u32 = (1 << 8) - 1;
const ONES_64: u64 = (1 << 11) - 1;

impl<const S: usize> FromPrimitive for Big<S> {
    fn from_i64(n: i64) -> Option<Self> {
        Some(Self {
            sign: Signed::signum(&n),
            numerator: Ubig::new(n.unsigned_abs() as usize),
            denominator: NonZeroUbig::one(),
        })
    }

    fn from_u64(n: u64) -> Option<Self> {
        Some(Self {
            sign: if n != 0 { Sign::Positive } else { Sign::Zero },
            numerator: Ubig::new(n as usize),
            denominator: NonZeroUbig::one(),
        })
    }

    fn from_f32(n: f32) -> Option<Self> {
        Self::from_float_kind(f32_kind(n))
    }

    fn from_f64(n: f64) -> Option<Self> {
        Self::from_float_kind(f64_kind(n))
    }
}

pub enum FloatKind {
    Zero,
    Subnormal(FloatAsRatio),
    Infinity,
    NaN,
    Normal(FloatAsRatio),
}

pub struct FloatAsRatio {
    pub sign: u64,
    pub exponent: i32,
    pub fraction: NonZeroU64,
}

pub fn f32_kind(n: f32) -> FloatKind {
    let n = n.to_bits();
    let sign = (n & 0b1000_0000_0000_0000_0000_0000_0000_0000) >> (32 - 1);
    let exponent = (n & 0b0111_1111_1000_0000_0000_0000_0000_0000) >> (32 - 1 - 8);
    let fraction = n & 0b0000_0000_0111_1111_1111_1111_1111_1111;

    match (exponent, fraction) {
        (0, 0) => FloatKind::Zero,
        (0, _) => FloatKind::Subnormal(FloatAsRatio {
            sign: sign as u64,
            exponent: 1 - 127 - 23,
            fraction: unsafe {
                // SAFETY: Zero would have matched earlier branch
                NonZeroU64::new_unchecked(fraction as u64)
            },
        }),
        (ONES_32, 0) => FloatKind::Infinity,
        (ONES_32, _) => FloatKind::NaN,
        _ => FloatKind::Normal(FloatAsRatio {
            sign: sign as u64,
            exponent: exponent as i32 - 127 - 23,
            fraction: unsafe {
                // SAFETY: A constant is always added
                NonZeroU64::new_unchecked((fraction + (1 << 23)) as u64)
                // SAFETY: A constant is always added
            },
        }),
    }
}

pub fn f64_kind(n: f64) -> FloatKind {
    let n = n.to_bits();
    let sign = (n & 0b1000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000) >> (64 - 1);
    let exponent = (n & 0b0111_1111_1111_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000) >> (64 - 1 - 11);
    let fraction = n & 0b0000_0000_0000_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111;

    assert_eq!(mem::size_of::<usize>(), mem::size_of::<u64>());

    match (exponent, fraction) {
        (0, 0) => FloatKind::Zero,
        (0, _) => FloatKind::Subnormal(FloatAsRatio {
            sign,
            exponent: 1 - 1023 - 52,
            fraction: unsafe {
                // SAFETY: Zero would have matched earlier branch
                NonZeroU64::new_unchecked(fraction)
            },
        }),
        (ONES_64, 0) => FloatKind::Infinity,
        (ONES_64, _) => FloatKind::NaN,
        _ => FloatKind::Normal(FloatAsRatio {
            sign,
            exponent: exponent as i32 - 1023 - 52,
            fraction: unsafe {
                // SAFETY: A constant is always added
                NonZeroU64::new_unchecked(fraction + (1 << 52))
            },
        }),
    }
}

impl<const S: usize> Big<S> {
    fn from_float_kind(kind: FloatKind) -> Option<Self> {
        match kind {
            FloatKind::Subnormal(as_ratio) | FloatKind::Normal(as_ratio) => {
                let (numerator, denominator) = from_float_helper(as_ratio.exponent, as_ratio.fraction);

                Some(Self {
                    sign: if as_ratio.sign > 0 { Sign::Negative } else { Sign::Positive },
                    numerator,
                    denominator,
                })
            }
            FloatKind::Zero => Some(Self::zero()),
            _ => None,
        }
    }
}

pub fn from_float_helper<const S: usize>(power: i32, fraction: NonZeroU64) -> (Ubig<S>, NonZeroUbig<S>) {
    match power.cmp(&0) {
        Ordering::Less => {
            let numerator_zeros = fraction.trailing_zeros();
            let shift = power.unsigned_abs();

            let numerator_shift = min(numerator_zeros, shift);
            let denominator_shift = shift - numerator_shift;

            let words_shift = denominator_shift / BITS_PER_WORD;
            let bits_shift = denominator_shift % BITS_PER_WORD;
            let size = words_shift + 1;
            let mut denominator = SmallVec::with_capacity(size as usize);

            denominator.extend(repeat(0).take(words_shift as usize));
            denominator.push(1 << bits_shift);

            let numerator = unsafe {
                // SAFETY: Fraction is non zero
                Ubig::from_inner_unchecked(smallvec![fraction.get() as usize >> numerator_shift])
            };

            (numerator, unsafe { NonZeroUbig::from_inner_unchecked(denominator) })
        }
        Ordering::Equal => {
            (unsafe {
                // SAFETY: Fraction is non zero
                Ubig::from_inner_unchecked(smallvec![fraction.get() as usize])
            }, NonZeroUbig::one())
        }
        Ordering::Greater => {
            let shift = power.unsigned_abs();
            let words_shift = shift / BITS_PER_WORD;
            let bits_shift = shift % BITS_PER_WORD;

            let overflows = fraction.leading_zeros() < bits_shift;
            let size = 1 + words_shift + if overflows { 1 } else { 0 };
            let mut numerator = SmallVec::with_capacity(size as usize);

            numerator.extend(repeat(0).take(words_shift as usize));

            numerator.push((fraction.get() as usize) << bits_shift);
            if overflows {
                numerator.push(fraction.get() as usize >> (BITS_PER_WORD - bits_shift));
            }

            (
                unsafe {
                    // SAFETY: last value is not zero
                    Ubig::from_inner_unchecked(numerator)
                },
                NonZeroUbig::one(),
            )
        }
    }
}

impl<const S: usize, const I1: usize, const I2: usize> TryFrom<(Sign, [usize; I1], [usize; I2])> for Big<S> {
    // TODO
    type Error = ();

    fn try_from((sign, numerator, denominator): (Sign, [usize; I1], [usize; I2])) -> Result<Self, Self::Error> {
        match (sign, Ubig::try_from(numerator), NonZeroUbig::try_from(denominator)) {
            (Sign::Positive | Sign::Negative, Ok(numerator), Ok(denominator)) if !numerator.is_zero() => {
                Ok(Self { sign, numerator, denominator })
            }
            (Sign::Zero, Ok(numerator), Ok(_)) if numerator.is_zero() => Ok(Self::zero()),
            _ => Err(()),
        }
    }
}

impl<const S: usize> From<&Big<S>> for Big<S> {
    fn from(reference: &Big<S>) -> Self {
        reference.clone()
    }
}

impl<const S: usize> num_traits::Zero for Big<S> {
    fn zero() -> Self {
        Self {
            sign: Sign::Zero,
            numerator: Ubig::zero(),
            denominator: NonZeroUbig::one(),
        }
    }

    fn set_zero(&mut self) {
        self.sign = Sign::Zero;
        self.numerator.set_zero();
        self.denominator.set_one();
    }

    fn is_zero(&self) -> bool {
        self.sign == Sign::Zero
    }
}

impl<const S: usize> num_traits::One for Big<S> {
    fn one() -> Self {
        Self {
            sign: Sign::Positive,
            numerator: Ubig::one(),
            denominator: NonZeroUbig::one(),
        }
    }

    fn set_one(&mut self) {
        self.numerator.set_one();
        self.denominator.set_one();
    }

    fn is_one(&self) -> bool {
        self.denominator[0] == 1 && self.numerator.len() == 1 && self.numerator[0] == 1 && self.denominator.len() == 1
    }
}

impl<const S: usize> num_traits::One for NonZeroBig<S> {
    fn one() -> Self {
        Self {
            sign: NonZeroSign::Positive,
            numerator: NonZeroUbig::one(),
            denominator: NonZeroUbig::one(),
        }
    }

    fn set_one(&mut self) {
        self.numerator.set_one();
        self.denominator.set_one();
    }

    fn is_one(&self) -> bool {
        self.numerator[0] == 1 && self.denominator[0] == 1 && self.numerator.len() == 1 && self.denominator.len() == 1
    }
}

impl<const S: usize> Big<S> {
    pub fn new_signed<T: Into<Sign>>(sign: T, numerator: u64, denominator: u64) -> Option<Self> {
        if denominator != 0 {
            let sign = sign.into();

            match (sign, numerator) {
                (Sign::Positive | Sign::Negative, n) if n != 0 => {
                    let (numerator, denominator) = simplify64(numerator, denominator);

                    Some(Self {
                        sign,
                        numerator: Ubig::new(numerator as usize),
                        denominator: unsafe { NonZeroUbig::new_unchecked(denominator as usize) },
                    })
                }
                (Sign::Zero, 0) => Some(Self::zero()),
                _ => None,
            }
        } else {
            None
        }
    }
}

impl<const S: usize> FromStr for Big<S> {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let _radix = 10;

        if s.contains('.') || s.contains(',') {
            return Err("Decimal separators are not supported");
        }

        match s.len() {
            0 => Err("Empty string"),
            _ => {
                let (sign, s) = match &s[..1] {
                    "+" => (Sign::Positive, &s[1..]),
                    "-" => (Sign::Negative, &s[1..]),
                    _ => (Sign::Positive, &s[..]),
                };

                match s.find('/') {
                    None => {
                        let numerator = Ubig::from_str(s)?;

                        Ok(Big {
                            sign: if numerator.is_not_zero() { sign } else { Sign::Zero },
                            numerator,
                            denominator: NonZeroUbig::one(),
                        })
                    }
                    Some(index) => {
                        // The number is a ratio between two others
                        let (numerator_text, denominator_text) = (&s[..index], &s[(index + 1)..]);
                        let mut numerator = Ubig::from_str(numerator_text)?;
                        let mut denominator = NonZeroUbig::from_str(denominator_text)
                            .map_err(|value| {
                                match value {
                                    "Zero value" => "Zero division",
                                    other => other,
                                }
                            })?;

                        Ok(if numerator.is_not_zero() {
                            unsafe {
                                // SAFETY: Are well-formed and non zero
                                simplify_fraction_without_info(numerator.inner_mut(), denominator.inner_mut());
                            }

                            Big {
                                sign,
                                numerator,
                                denominator,
                            }
                        } else {
                            Zero::zero()
                        })
                    }
                }
            }
        }
    }
}

impl<const S: usize> fmt::Display for Big<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.sign {
            Sign::Positive => {}
            Sign::Zero => return f.write_str("0"),
            Sign::Negative => f.write_str("-")?,
        }

        fmt::Display::fmt(&self.numerator, f)?;

        if !self.denominator.is_one() {
            f.write_str("/")?;
            fmt::Display::fmt(&self.denominator, f)?;
        }

        fmt::Result::Ok(())
    }
}

macro_rules! signed_small {
    ($value:expr, $target:ident) => {
        if $value.sign == Sign::Zero {
            Some(0)
        } else {
            let result = if unsafe { !is_one_non_zero(&$value.denominator) } {
                match cmp(&$value.numerator, &$value.denominator) {
                    Ordering::Less => Some(0),
                    Ordering::Equal => Some(1),
                    Ordering::Greater => {
                        let maybe_large_result = unsafe {
                            // SAFETY: Denominator is not zero
                            div::<S>(&$value.numerator, &$value.denominator)
                        };
                        match maybe_large_result.len() {
                            0 => Some(0),
                            1 => maybe_large_result[0].try_into().ok(),
                            _ => None,
                        }
                    }
                }
            } else {
                $value.numerator.$target()
            };

            result.map(|value| if $value.sign == Sign::Negative {
                -value
            } else {
                value
            })
        }
    }
}

macro_rules! unsigned_small {
    ($value:expr, $target:ident) => {
        match $value.sign {
            Sign::Positive => {
                if unsafe { !is_one_non_zero(&$value.denominator) } {
                    match cmp(&$value.numerator, &$value.denominator) {
                        Ordering::Less => Some(0),
                        Ordering::Equal => Some(1),
                        Ordering::Greater => {
                            let result = unsafe {
                                // SAFETY: Denominator is not zero
                                div::<S>(&$value.numerator, &$value.denominator)
                            };
                            match result.len() {
                                0 => Some(0),
                                1 => result[0].try_into().ok(),
                                _ => None,
                            }}
                    }
                } else {
                    $value.numerator.$target()
                }
            }
            Sign::Zero => Some(0),
            Sign::Negative => None,
        }
    }
}
impl<const S: usize> ToPrimitive for Big<S> {
    fn to_isize(&self) -> Option<isize> {
        signed_small!(self, to_isize)
    }

    fn to_i8(&self) -> Option<i8> {
        signed_small!(self, to_i8)
    }

    fn to_i16(&self) -> Option<i16> {
        signed_small!(self, to_i16)
    }

    fn to_i32(&self) -> Option<i32> {
        signed_small!(self, to_i32)
    }

    fn to_i64(&self) -> Option<i64> {
        signed_small!(self, to_i64)
    }

    fn to_i128(&self) -> Option<i128> {
        todo!()
    }

    fn to_usize(&self) -> Option<usize> {
        unsigned_small!(self, to_usize)
    }

    fn to_u8(&self) -> Option<u8> {
        unsigned_small!(self, to_u8)
    }

    fn to_u16(&self) -> Option<u16> {
        unsigned_small!(self, to_u16)
    }

    fn to_u32(&self) -> Option<u32> {
        unsigned_small!(self, to_u32)
    }

    fn to_u64(&self) -> Option<u64> {
        unsigned_small!(self, to_u64)
    }

    fn to_u128(&self) -> Option<u128> {
        todo!()
    }

    fn to_f32(&self) -> Option<f32> {
        Some(match self.sign {
            Sign::Positive => self.numerator.to_f32().unwrap() / self.denominator.to_f32().unwrap(),
            Sign::Zero => 0_f32,
            Sign::Negative => -self.numerator.to_f32().unwrap() / self.denominator.to_f32().unwrap(),
        })
    }

    fn to_f64(&self) -> Option<f64> {
        Some(match self.sign {
            Sign::Positive => self.numerator.to_f64().unwrap() / self.denominator.to_f64().unwrap(),
            Sign::Zero => 0_f64,
            Sign::Negative => -self.numerator.to_f64().unwrap() / self.denominator.to_f64().unwrap(),
        })
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use num_traits::{One, ToPrimitive, Zero};
    use smallvec::{smallvec, SmallVec};

    use crate::{Abs, Rational64, RationalBig, Sign, Ubig};
    use crate::integer::big::{BITS_PER_WORD, NonZeroUbig};
    use crate::integer::big::io::from_str_radix;
    use crate::integer::big::ops::normalize::simplify_fraction_without_info;
    use crate::rational::big::{Big, Big8};
    use crate::RB;

    #[test]
    fn from() {
        let x = Rational64::new(4, 3).unwrap();
        let y = Big8::from(x);
        let z = RB!(4, 3);
        assert_eq!(y, z);

        let x = <Big8 as num_traits::FromPrimitive>::from_f32(0_f32).unwrap();
        assert_eq!(x, RB!(0, 1));

        let x = <Big8 as num_traits::FromPrimitive>::from_f32(1_f32).unwrap();
        assert_eq!(x, RB!(1, 1));

        let x = <Big8 as num_traits::FromPrimitive>::from_f32(0.5).unwrap();
        assert_eq!(x, RB!(1, 2));

        let x = <Big8 as num_traits::FromPrimitive>::from_f32(2_f32).unwrap();
        assert_eq!(x, RB!(2, 1));

        let x = <Big8 as num_traits::FromPrimitive>::from_f32(1.5_f32).unwrap();
        assert_eq!(x, RB!(3, 2));
        let x = <Big8 as num_traits::FromPrimitive>::from_f64(0_f64).unwrap();
        assert_eq!(x, RB!(0, 1));

        let x = <Big8 as num_traits::FromPrimitive>::from_f64(1_f64).unwrap();
        assert_eq!(x, RB!(1, 1));

        let x = <Big8 as num_traits::FromPrimitive>::from_f64(0.5).unwrap();
        assert_eq!(x, RB!(1, 2));

        let x = <Big8 as num_traits::FromPrimitive>::from_f64(2_f64).unwrap();
        assert_eq!(x, RB!(2, 1));

        let x = <Big8 as num_traits::FromPrimitive>::from_f64(1.5_f64).unwrap();
        assert_eq!(x, RB!(3, 2));

        let x = <Big8 as num_traits::FromPrimitive>::from_f64(f64::MIN_POSITIVE).unwrap();
        let (words, bits) = (1022 / BITS_PER_WORD, 1022 % BITS_PER_WORD);
        let mut denominator = smallvec![0; words as usize];
        denominator.push(1 << bits);
        let expected = Big8 {
            sign: Sign::Positive,
            numerator: Ubig::one(),
            denominator: unsafe { NonZeroUbig::from_inner_unchecked(denominator) },
        };
        assert_eq!(x, expected);

        let x = <Big8 as num_traits::FromPrimitive>::from_f64(f64::MAX).unwrap();
        let total_shift = (1 << (11 - 1)) - 1 - 52;
        let (words, bits) = (total_shift / BITS_PER_WORD, total_shift % BITS_PER_WORD);
        let mut numerator = smallvec![0; words as usize];
        numerator.push(((1 << (52 + 1)) - 1) << bits); // Doesn't overflow, fits exactly in this last word
        let expected = Big8 {
            sign: Sign::Positive,
            numerator: unsafe { Ubig::from_inner_unchecked(numerator) },
            denominator: NonZeroUbig::one(),
        };
        assert_eq!(x, expected);

        let y = <Big8 as num_traits::FromPrimitive>::from_f64(4f64 / 3f64).unwrap();
        let z = RB!(4, 3);
        assert!((y - z).abs() < Big8::new(1, 2 << 10).unwrap());

        // 2 ** 543
        assert_eq!(
            RB!(28793048285076456849987446449190283896766061557132266451844835664715760516297522370041860391064901485759493828054533728788532902755163518009654497157537048672862208_f64),
            RationalBig {
                sign: Sign::Positive,
                numerator: unsafe { Ubig::from_inner_unchecked(smallvec![0, 0, 0, 0, 0, 0, 0, 0, 1 << 31]) },
                denominator: NonZeroUbig::one(),
            }
        );

        assert_eq!(<Big8 as num_traits::FromPrimitive>::from_i64(0), Some(RB!(0)));
        assert_eq!(<Big8 as num_traits::FromPrimitive>::from_i64(1), Some(RB!(1)));
        assert_eq!(<Big8 as num_traits::FromPrimitive>::from_i64(-1), Some(-RB!(1)));
        assert_eq!(<Big8 as num_traits::FromPrimitive>::from_u64(0), Some(RB!(0)));
        assert_eq!(<Big8 as num_traits::FromPrimitive>::from_u64(1), Some(RB!(1)));
        assert_eq!(<Big8 as num_traits::FromPrimitive>::from_f32(f32::NAN), None);
        assert_eq!(<Big8 as num_traits::FromPrimitive>::from_f32(f32::INFINITY), None);
        assert_eq!(<Big8 as num_traits::FromPrimitive>::from_f32(f32::NEG_INFINITY), None);
        assert_eq!(<Big8 as num_traits::FromPrimitive>::from_f32(2_i64.pow(22) as f32), Some(RB!(2_i64.pow(22), 1)));
        assert_eq!(<Big8 as num_traits::FromPrimitive>::from_f32(2_i64.pow(23) as f32), Some(RB!(2_i64.pow(23), 1)));
        assert_eq!(<Big8 as num_traits::FromPrimitive>::from_f64(f64::NAN), None);
        assert_eq!(<Big8 as num_traits::FromPrimitive>::from_f64(f64::INFINITY), None);
        assert_eq!(<Big8 as num_traits::FromPrimitive>::from_f64(f64::NEG_INFINITY), None);
        assert_eq!(<Big8 as num_traits::FromPrimitive>::from_f64(2_i64.pow(52) as f64), Some(RB!(2_i64.pow(52), 1)));
        assert_eq!(<Big8 as num_traits::FromPrimitive>::from_f64(2_i64.pow(53) as f64), Some(RB!(2_i64.pow(53), 1)));
    }

    #[test]
    fn test_one() {
        let mut x = RB!(132);
        x.set_one();
        assert_eq!(x, RB!(1));
        assert_eq!(RB!(1), Big::one());
    }

    #[test]
    fn test_signed() {
        assert_eq!(Big::new_signed(Sign::Positive, 1, 2).unwrap(), RB!(1, 2));
        assert_eq!(Big::new_signed(Sign::Zero, 0, 1).unwrap(), RB!(0));
        assert_eq!(Big::new_signed(Sign::Negative, 1, 3).unwrap(), RB!(-1, 3));
    }

    #[test]
    fn test_new() {
        assert_eq!(RB!(3, 3), RB!(1));
    }

    #[test]
    fn from_int() {
        assert_eq!(Big::from(0_i32), RB!(0));
        assert_eq!(Big::from(0_u32), RB!(0));
        assert_eq!(Big::from(1_i64), RB!(1));
        assert_eq!(Big::from(19_u8), RB!(19));
        assert_eq!(Big::from(-1_i16), RB!(-1));
    }

    #[test]
    fn from_tuple() {
        assert_eq!(Big::from((0_i32, 1_u32)), RB!(0));
        assert_eq!(Big::from((0_i32, 5_u32)), RB!(0));
        assert_eq!(Big::from((1_i64, 2_u64)), RB!(1, 2));
        assert_eq!(Big::from((22_i8, 2_u8)), RB!(11));
        assert_eq!(Big::from((-1_i16, 2_u16)), RB!(-1, 2));
        assert_eq!(Big::from((-1_i32, 1_i32)), RB!(-1));
    }

    #[test]
    fn from_str() {
        assert_eq!(Big::from_str("0"), Ok(RB!(0)));
        assert_eq!(Big::from_str("0000000"), Ok(RB!(0)));
        assert_eq!(Big::from_str("0/2"), Ok(RB!(0)));
        assert_eq!(Big::from_str("-0/2"), Ok(RB!(0)));
        assert_eq!(Big::from_str("-2"), Ok(RB!(-2)));
        assert_eq!(Big8::from_str("-2a"), Err("Character is not a digit"));
        assert_eq!(Big8::from_str("-2.1"), Err("Decimal separators are not supported"));
        assert_eq!(Big8::from_str("-2.1/3"), Err("Decimal separators are not supported"));
        assert_eq!(Big::from_str("-0"), Ok(RB!(0)));
        assert_eq!(Big8::from_str("0/"), Err("Empty string"));
        assert_eq!(Big8::from_str("0/0"), Err("Zero division"));
        assert_eq!(Big8::from_str(""), Err("Empty string"));
        assert_eq!(Big::from_str("1/2"), Ok(RB!(1, 2)));
        assert_eq!(Big::from_str("-3/2"), Ok(RB!(-3, 2)));
        assert_eq!(
            Big8::from_str("27670116110564327425"),
            Ok(Big {
                sign: Sign::Positive,
                numerator: unsafe { Ubig::from_inner_unchecked(smallvec![(1 << 63) + (1 << 0), 1]) },
                denominator: NonZeroUbig::one(),
            }),
        );
        assert_eq!(
            Big8::from_str("27670116110564327425/2"),
            Ok(Big {
                sign: Sign::Positive,
                numerator: unsafe { Ubig::from_inner_unchecked(smallvec![(1 << 63) + (1 << 0), 1]) },
                denominator: NonZeroUbig::new(2).unwrap(),
            }),
        );
        assert_eq!(
            Big8::from_str("27670116110564327425/27670116110564327425"),
            Ok(Big {
                sign: Sign::Positive,
                numerator: Ubig::one(),
                denominator: NonZeroUbig::one(),
            }),
        );
        assert_eq!(
            Big8::from_str("18446744073709551616/2"),
            Ok(Big {
                sign: Sign::Positive,
                numerator: unsafe { Ubig::from_inner_unchecked(smallvec![1 << 63]) },
                denominator: NonZeroUbig::one(),
            }),
        );
        assert_eq!(
            Big8::from_str("-36893488147419103232"),
            Ok(Big {
                sign: Sign::Negative,
                numerator: unsafe { Ubig::from_inner_unchecked(smallvec![0, 2]) },
                denominator: NonZeroUbig::one(),
            }),
        );

        assert_eq!(from_str_radix::<10, 8>("407030945657418069975"), Ok(smallvec![1202576035807934423, 22]));
        assert_eq!(from_str_radix::<10, 8>("36893488147419103232"), Ok(smallvec![0, 1 << 1]));
        assert_eq!(from_str_radix::<10, 8>("18889465931478580854784"), Ok(smallvec![0, 1 << 10]));
        assert_eq!(from_str_radix::<10, 8>("19342813113834066795298816"), Ok(smallvec![0, 1 << 20]));
        assert_eq!(from_str_radix::<10, 8>("1208925819614629174706176"), Ok(smallvec![0, 1 << (80 - 64)]));

        assert_eq!(
            Big8::from_str("-1208925819614629174706176/10301051460877537453973547267843"),
            Ok(Big {
                sign: Sign::Negative,
                numerator: unsafe { Ubig::from_inner_unchecked(smallvec![0, 1 << (80 - 64)]) },
                denominator: unsafe { NonZeroUbig::from_inner_unchecked(smallvec![0x6b9676a56c7c3703, 0x82047e0eae]) },
            }),
        );

        type SV = SmallVec<[usize; 8]>;

        let mut x = from_str_radix::<10, 8>("676230147000402641135208532975102322580080121519024130").unwrap();
        let expected: SV = smallvec![7877410236203542530, 0xe30d7c46c1f853f7, 1987261794136745];
        assert_eq!(x, expected);
        let mut y = from_str_radix::<10, 8>("68468465468464168545346854646").unwrap();
        let expected: SV = smallvec![7062882560094707446, 3711682950];
        assert_eq!(y, expected);
        unsafe { simplify_fraction_without_info(&mut x, &mut y) };
        let expected: SV = smallvec![13162077154956547073, 17403806869180131835, 993630897068372];
        assert_eq!(x, expected);
        let expected: SV = smallvec![3531441280047353723, 1855841475];
        assert_eq!(y, expected);

        let z = Big8::from_str("676230147000402641135208532975102322580080121519024130/68468465468464168545346854646");
        assert_eq!(z, Ok(Big {
            sign: Sign::Positive,
            numerator: unsafe { Ubig::from_inner_unchecked(x) },
            denominator: unsafe { NonZeroUbig::from_inner_unchecked(y) },
        }));

        assert_eq!(
            Big8::from_str("1190934288550035983230200000000/1219533185348999122218328290051").unwrap(),
            Big8::from_str("23800000000/24371529219").unwrap(),
        );
    }

    #[test]
    fn test_to_str() {
        type SV = SmallVec<[usize; 8]>;

        assert_eq!(Ubig::<1>::zero().to_string(), "0");
        assert_eq!(Ubig::<1>::one().to_string(), "1");
        assert_eq!(Ubig::<1>::new(2).to_string(), "2");
        assert_eq!(Ubig::<1>::new(3).to_string(), "3");
        assert_eq!(Ubig::<1>::new(10).to_string(), "10");
        assert_eq!(Ubig::<1>::new(11).to_string(), "11");
        assert_eq!(Ubig::<1>::new(101).to_string(), "101");
        assert_eq!(Ubig::<1>::new(123).to_string(), "123");
        assert_eq!(Ubig::<1>::new(usize::MAX).to_string(), "18446744073709551615");
        assert_eq!(unsafe { Ubig::<1>::from_inner_unchecked(smallvec![0, 1]) }.to_string(), "18446744073709551616");
        assert_eq!(unsafe { Ubig::<1>::from_inner_unchecked(smallvec![1, 1]) }.to_string(), "18446744073709551617");

        for i in 1..100 {
            let expected = unsafe { Ubig::from_inner_unchecked(smallvec![i]) };
            assert_eq!(Ubig::<8>::from_str(&expected.to_string()), Ok(expected));
        }

        let x: SV = smallvec![13284626917187606528, 14353657804625640860, 11366567065457835548, 501247837944];
        assert_eq!(
            unsafe { Ubig::from_inner_unchecked(x) }.to_string(),
            "3146383673420971972032023490593198871229613539715389096610302560000000",
        );
        let y: SV = smallvec![10945929334190035713, 13004504757950498814, 9];
        assert_eq!(unsafe { Ubig::from_inner_unchecked(y) }.to_string(), "3302432073363697202172148890923583722241");
        let y: SV = smallvec![602229295517812052, 3];
        assert_eq!(unsafe { Ubig::from_inner_unchecked(y) }.to_string(), "55942461516646466900");
    }

    #[test]
    fn test_debug() {
        assert_eq!(format!("{:?}", RB!(2, 3)), "2 / 3");
        assert_eq!(
            format!("{:?}", RationalBig::from_str("676230147000402641135208532975102322580080121519024130").unwrap()),
            "[7877410236203542530, 16360869664650712055, 1987261794136745]",
        );
    }

    #[test]
    fn test_to_primitive() {
        assert_eq!(RB!(1, 2).to_u64(), Some(0));
        assert_eq!(RB!(1, 1).to_u64(), Some(1));
        assert_eq!(RB!(2, 1).to_u64(), Some(2));
        assert_eq!(RB!(-1, 2).to_u64(), None);
        assert_eq!(RB!(1, 2).to_i8(), Some(0));
        assert_eq!(RB!(1, 1).to_i8(), Some(1));
        assert_eq!(RB!(2, 1).to_i8(), Some(2));
        assert_eq!(RB!(-1, 2).to_i8(), Some(0));
        assert_eq!(RB!(-1, 1).to_i8(), Some(-1));

        assert_eq!(RB!(1, 2).to_f32(), Some(0.5_f32));
        assert_eq!(RB!(1, 2).to_f64(), Some(0.5_f64));
        assert_eq!(RB!(-1, 2).to_f64(), Some(-0.5_f64));
        assert_eq!(RB!(123456789, 1).to_f64(), Some(123456789_f64));
        assert_eq!(RB!(9_007_199_254_740_992, 1).to_f64(), Some(9_007_199_254_740_992_f64));
        assert_eq!(RB!(9_007_199_254_740_993, 1).to_f64(), Some(9_007_199_254_740_993_f64));
        assert_eq!(RB!(9_007_199_254_740_994, 1).to_f64(), Some(9_007_199_254_740_994_f64));
    }
}
