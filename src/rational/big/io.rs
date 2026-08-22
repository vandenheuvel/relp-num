use std::{fmt, mem};
use std::cmp::{min, Ordering};
use std::convert::TryFrom;
use std::num::{NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize};
use std::num::{NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize};
use std::str::FromStr;

use num_traits::{FromPrimitive, One, ToPrimitive, Zero};
use smallvec::{smallvec, SmallVec};

use crate::{NonZero, NonZeroSign, Ubig};
use crate::integer::big::{BITS_PER_WORD, NonZeroUbig};
use crate::integer::big::io::{highest_word, words_to_u128};
use crate::integer::big::ops::div::div;
use crate::integer::big::ops::non_zero::is_one_non_zero;
use crate::integer::big::ops::normalize::{gcd_scalar, simplify_fraction_without_info};
use crate::integer::big::properties::cmp;
use crate::rational::big::{Big, NonZeroBig};
use crate::rational::{Rational128, RationalUsize};
use crate::rational::small::ops::building_blocks::{simplify128, simplify16, simplify32, simplify64, simplify8, simplify_usize};
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
        // The same representation as `Display`, such that it round trips through `FromStr`
        fmt::Display::fmt(self, f)
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
    ($ty:ty, $simplify:ident) => {
        impl<const S: usize> From<($ty, $ty)> for Big<S> {
            #[inline]
            fn from((numerator, denominator): ($ty, $ty)) -> Self {
                // This is for tests only at the moment, do a run time assert
                assert!(denominator.is_not_zero());

                if mem::size_of::<$ty>() > mem::size_of::<usize>() {
                    debug_assert!(numerator.unsigned_abs() as u128 <= usize::MAX as u128);
                    debug_assert!(denominator.unsigned_abs() as u128 <= usize::MAX as u128);
                }

                if numerator == 0 {
                    <Self as num_traits::Zero>::zero()
                } else {
                    let sign = <$ty as Signed>::signum(&numerator) * <$ty as Signed>::signum(&denominator);
                    debug_assert_ne!(sign, Sign::Zero);

                    let (numerator, denominator) = $simplify(
                        numerator.unsigned_abs(), denominator.unsigned_abs(),
                    );

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

impl_from_ii!(i8, simplify8);
impl_from_ii!(i16, simplify16);
impl_from_ii!(i32, simplify32);
impl_from_ii!(i64, simplify64);
impl_from_ii!(i128, simplify128);
impl_from_ii!(isize, simplify_usize);

/// Conversion from a fixed size ratio that doesn't fit in a single word.
///
/// The equivalents for the smaller fixed size ratios are in the `with_small_rational` module; those
/// can cast their numerator and denominator into a single word, these can't.
macro_rules! from_small_rational {
    ($small:ident, $new_numerator:path, $new_denominator_unchecked:path) => {
        impl<const S: usize> From<$small> for Big<S> {
            #[inline]
            fn from(value: $small) -> Self {
                match value.sign {
                    Sign::Zero => {
                        debug_assert_eq!(value.numerator, 0);

                        <Self as num_traits::Zero>::zero()
                    }
                    Sign::Positive | Sign::Negative => Self {
                        sign: value.sign,
                        // The input is in lowest terms already, so no simplification is needed
                        numerator: $new_numerator(value.numerator),
                        denominator: unsafe {
                            // SAFETY: Input denominator is nonzero
                            $new_denominator_unchecked(value.denominator)
                        },
                    },
                }
            }
        }

        impl<const S: usize> From<&$small> for Big<S> {
            #[inline]
            fn from(value: &$small) -> Self {
                From::from(*value)
            }
        }
    }
}

from_small_rational!(Rational128, Ubig::new_u128, NonZeroUbig::new_u128_unchecked);
from_small_rational!(RationalUsize, Ubig::new, NonZeroUbig::new_unchecked);

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

/// See also the `std::num::FpCategory`.
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

            denominator.extend(std::iter::repeat_n(0, words_shift as usize));
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

            numerator.extend(std::iter::repeat_n(0, words_shift as usize));

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

impl<const S: usize> Big<S> {
    /// Build a ratio from raw limbs, without reducing it.
    ///
    /// Only for tests that need a value which is deliberately not in lowest terms, such as the
    /// input to a reduction routine or a `Display` of the stored components. Every other way in is
    /// expected to reduce, because a stored ratio has to be coprime for `PartialEq` and `Ord` to
    /// agree and for the arithmetic kernels to hold their precondition.
    #[cfg(test)]
    pub(crate) fn from_raw_limbs<const I1: usize, const I2: usize>(
        sign: Sign,
        numerator: [usize; I1],
        denominator: [usize; I2],
    ) -> Self {
        let numerator = Ubig::try_from(numerator).expect("well formed numerator");
        let denominator = NonZeroUbig::try_from(denominator).expect("well formed denominator");
        debug_assert_eq!(sign == Sign::Zero, numerator.is_zero());

        Self { sign, numerator, denominator }
    }
}

impl<const S: usize, const I1: usize, const I2: usize> TryFrom<(Sign, [usize; I1], [usize; I2])> for Big<S> {
    // TODO
    type Error = ();

    fn try_from((sign, numerator, denominator): (Sign, [usize; I1], [usize; I2])) -> Result<Self, Self::Error> {
        match (sign, Ubig::try_from(numerator), NonZeroUbig::try_from(denominator)) {
            (Sign::Positive | Sign::Negative, Ok(numerator), Ok(denominator)) if !numerator.is_zero() => {
                // The limbs are taken as given, so they need not be coprime. Storing them that
                // way would break the type's invariant: `PartialEq` compares the components while
                // `Ord` cross multiplies, so the two would disagree, and the arithmetic kernels
                // are written against the coprimality precondition. `Self::new` reduces its
                // arguments for the same reason, so this does too.
                let mut numerator = numerator;
                let mut denominator = denominator;

                // SAFETY: `Ubig::try_from` and `NonZeroUbig::try_from` only accept well formed
                // arrays, the numerator was just tested to be non zero and the denominator cannot
                // be zero by its type.
                unsafe {
                    simplify_fraction_without_info(numerator.inner_mut(), denominator.inner_mut());
                }

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
        self.sign = Sign::Positive;
        self.numerator.set_one();
        self.denominator.set_one();
    }

    fn is_one(&self) -> bool {
        self.sign == Sign::Positive &&
            self.denominator[0] == 1 && self.numerator.len() == 1 &&
            self.numerator[0] == 1 && self.denominator.len() == 1
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
        self.sign = NonZeroSign::Positive;
        self.numerator.set_one();
        self.denominator.set_one();
    }

    fn is_one(&self) -> bool {
        self.sign == NonZeroSign::Positive &&
            self.numerator[0] == 1 && self.denominator[0] == 1 &&
            self.numerator.len() == 1 && self.denominator.len() == 1
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
                // Match on the first byte; the string doesn't have to start on an ASCII character,
                // so slicing at index one is not necessarily on a character boundary
                let (sign, s) = match s.as_bytes().first() {
                    Some(b'+') => (Sign::Positive, &s[1..]),
                    Some(b'-') => (Sign::Negative, &s[1..]),
                    _ => (Sign::Positive, s),
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

/// The magnitude of the integer part of a ratio, truncated towards zero.
///
/// # Return value
///
/// `None` if the magnitude doesn't fit a `u128`, the magnitude otherwise.
macro_rules! integer_magnitude {
    ($value:expr) => {
        {
            if unsafe { !is_one_non_zero(&$value.denominator) } {
                match cmp(&$value.numerator, &$value.denominator) {
                    Ordering::Less => Some(0_u128),
                    Ordering::Equal => Some(1_u128),
                    Ordering::Greater => {
                        let result = unsafe {
                            // SAFETY: Denominator is not zero
                            div::<S>(&$value.numerator, &$value.denominator)
                        };

                        words_to_u128(&result)
                    }
                }
            } else {
                words_to_u128(&$value.numerator)
            }
        }
    }
}

macro_rules! signed_small {
    ($value:expr, $target:ty, $unsigned:ty) => {
        match $value.sign {
            Sign::Zero => Some(0),
            Sign::Positive => integer_magnitude!($value)
                .and_then(|magnitude| <$target>::try_from(magnitude).ok()),
            Sign::Negative => integer_magnitude!($value)
                .and_then(|magnitude| {
                    // Negating the magnitude in the target type would overflow for the most
                    // negative value, so the negation is done in the unsigned domain
                    if magnitude <= <$target>::MIN.unsigned_abs() as u128 {
                        Some((magnitude as $unsigned).wrapping_neg() as $target)
                    } else {
                        None
                    }
                }),
        }
    }
}

macro_rules! unsigned_small {
    ($value:expr, $target:ty) => {
        match $value.sign {
            Sign::Zero => Some(0),
            Sign::Negative => None,
            Sign::Positive => integer_magnitude!($value)
                .and_then(|magnitude| <$target>::try_from(magnitude).ok()),
        }
    }
}

/// The ratio between the numerator and the denominator, as a float.
///
/// The value should not be zero.
macro_rules! ratio_to_float {
    ($value:expr, $target:ty, $to_float:ident) => {
        {
            let numerator = $value.numerator.$to_float().unwrap();
            let denominator = $value.denominator.$to_float().unwrap();

            if numerator.is_finite() && denominator.is_finite() {
                numerator / denominator
            } else {
                // At least one of the two doesn't fit the target on its own, while their ratio
                // might very well do so. Divide the highest words and account for the bits that
                // were dropped below them with the exponent.
                //
                // Note that this keeps only a single word of each side, so the result can be off
                // by an ulp; it is the best that can be done without a full length division.
                let (numerator, numerator_shift) = highest_word(&$value.numerator);
                let (denominator, denominator_shift) = highest_word(&$value.denominator);

                let exponent = numerator_shift as i32 - denominator_shift as i32;
                // Applying the exponent in two steps, because a single step can overflow the
                // target while the result doesn't
                let half = exponent / 2;

                (numerator as $target / denominator as $target)
                    * (2 as $target).powi(half)
                    * (2 as $target).powi(exponent - half)
            }
        }
    }
}

impl<const S: usize> ToPrimitive for Big<S> {
    fn to_isize(&self) -> Option<isize> {
        signed_small!(self, isize, usize)
    }

    fn to_i8(&self) -> Option<i8> {
        signed_small!(self, i8, u8)
    }

    fn to_i16(&self) -> Option<i16> {
        signed_small!(self, i16, u16)
    }

    fn to_i32(&self) -> Option<i32> {
        signed_small!(self, i32, u32)
    }

    fn to_i64(&self) -> Option<i64> {
        signed_small!(self, i64, u64)
    }

    fn to_i128(&self) -> Option<i128> {
        signed_small!(self, i128, u128)
    }

    fn to_usize(&self) -> Option<usize> {
        unsigned_small!(self, usize)
    }

    fn to_u8(&self) -> Option<u8> {
        unsigned_small!(self, u8)
    }

    fn to_u16(&self) -> Option<u16> {
        unsigned_small!(self, u16)
    }

    fn to_u32(&self) -> Option<u32> {
        unsigned_small!(self, u32)
    }

    fn to_u64(&self) -> Option<u64> {
        unsigned_small!(self, u64)
    }

    fn to_u128(&self) -> Option<u128> {
        unsigned_small!(self, u128)
    }

    fn to_f32(&self) -> Option<f32> {
        Some(match self.sign {
            Sign::Zero => 0_f32,
            Sign::Positive => ratio_to_float!(self, f32, to_f32),
            Sign::Negative => -ratio_to_float!(self, f32, to_f32),
        })
    }

    fn to_f64(&self) -> Option<f64> {
        Some(match self.sign {
            Sign::Zero => 0_f64,
            Sign::Positive => ratio_to_float!(self, f64, to_f64),
            Sign::Negative => -ratio_to_float!(self, f64, to_f64),
        })
    }
}

#[cfg(test)]
mod test {
    use std::cmp::Ordering;
    use std::str::FromStr;

    use num_traits::{One, ToPrimitive, Zero};
    use smallvec::{smallvec, SmallVec};

    use crate::{Abs, NonZeroSign, Rational128, Rational64, RationalBig, RationalUsize, Sign, Ubig};
    use crate::integer::big::{BITS_PER_WORD, NonZeroUbig};
    use crate::integer::big::io::from_str_radix;
    use crate::integer::big::ops::normalize::simplify_fraction_without_info;
    use crate::rational::big::{Big, Big8, NonZeroBig8};
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
    fn test_one_respects_sign() {
        assert!(RB!(1).is_one());
        assert!(!RB!(-1).is_one());
        assert!(!RB!(0).is_one());
        assert!(!RB!(2).is_one());
        assert!(!RB!(1, 2).is_one());

        // Setting a negative value to one makes it positive
        let mut negative = RB!(-5, 6);
        negative.set_one();
        assert_eq!(negative.sign, Sign::Positive);
        assert!(negative.is_one());
        assert_eq!(negative, RB!(1));

        // Setting the zero value to one doesn't leave the sign at zero
        let mut zero = RB!(0);
        zero.set_one();
        assert_eq!(zero.sign, Sign::Positive);
        assert!(zero.is_one());
        assert_eq!(zero, RB!(1));

        // The same holds for the non zero variant
        let mut non_zero = NonZeroBig8 {
            sign: NonZeroSign::Negative,
            numerator: NonZeroUbig::one(),
            denominator: NonZeroUbig::one(),
        };
        assert!(!non_zero.is_one());
        non_zero.set_one();
        assert_eq!(non_zero.sign, NonZeroSign::Positive);
        assert!(non_zero.is_one());
        // `NonZeroBig` doesn't implement `Debug`, so this can't be an `assert_eq`
        assert!(non_zero == NonZeroBig8::one());
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
    fn from_large_small_rational() {
        // The zero value is the canonical zero
        let zero = Big8::from(Rational128::zero());
        assert_eq!(zero.sign, Sign::Zero);
        assert!(zero.numerator.is_zero());
        assert!(zero.denominator.is_one());
        assert_eq!(zero, RB!(0));
        assert_eq!(Big8::from(RationalUsize::zero()), RB!(0));

        assert_eq!(Big8::from(Rational128::one()), RB!(1));
        assert_eq!(Big8::from(RationalUsize::one()), RB!(1));

        assert_eq!(Big8::from(Rational128::new(-1, 1).unwrap()), RB!(-1));
        assert_eq!(Big8::from(Rational128::new(-3, 2).unwrap()), RB!(-3, 2));
        assert_eq!(Big8::from(RationalUsize::new(-1, 1).unwrap()), RB!(-1));
        assert_eq!(Big8::from(RationalUsize::new(-3, 2).unwrap()), RB!(-3, 2));

        // The input is in lowest terms, and stays that way
        assert_eq!(Big8::from(Rational128::new(4, 6).unwrap()), RB!(2, 3));
        assert_eq!(Big8::from(RationalUsize::new(-4, 6).unwrap()), RB!(-2, 3));

        // References convert to the same value
        for value in [Rational128::zero(), Rational128::one(), Rational128::new(-3, 2).unwrap()] {
            assert_eq!(Big8::from(&value), Big8::from(value));
        }
        for value in [RationalUsize::zero(), RationalUsize::one(), RationalUsize::new(-3, 2).unwrap()] {
            assert_eq!(Big8::from(&value), Big8::from(value));
        }

        assert_eq!(
            Big8::from(RationalUsize::new_signed(Sign::Negative, usize::MAX, 1).unwrap()),
            Big8::from_str(&format!("-{}", usize::MAX)).unwrap(),
        );
    }

    #[test]
    fn from_rational_128_multiple_words() {
        // A `u128` doesn't fit in a single word on a 64 bit platform
        let words_needed = 128 / BITS_PER_WORD as usize;

        let large_numerator = Rational128::new_signed(Sign::Positive, u128::MAX, 1).unwrap();
        assert_eq!(
            Big8::from(large_numerator),
            Big8::from_str("340282366920938463463374607431768211455").unwrap(),
        );
        assert_eq!(Big8::from(large_numerator).to_string(), u128::MAX.to_string());
        assert_eq!(Big8::from(large_numerator).numerator.len(), words_needed);

        let large_denominator = Rational128::new_signed(Sign::Negative, 1, u128::MAX).unwrap();
        assert_eq!(
            Big8::from(large_denominator),
            Big8::from_str("-1/340282366920938463463374607431768211455").unwrap(),
        );
        assert_eq!(Big8::from(large_denominator).denominator.len(), words_needed);

        let both_large = Rational128::new_signed(Sign::Negative, u128::MAX - 2, u128::MAX).unwrap();
        assert_eq!(
            Big8::from(both_large),
            Big8::from_str(
                "-340282366920938463463374607431768211453/340282366920938463463374607431768211455",
            ).unwrap(),
        );

        // A value divided by itself is one
        assert_eq!(Big8::from(Rational128::new_signed(Sign::Positive, u128::MAX, u128::MAX).unwrap()), RB!(1));
        assert_eq!(Big8::from(Rational128::new_signed(Sign::Negative, u128::MAX, u128::MAX).unwrap()), -RB!(1));
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
    fn from_tuple_signed_is_normalized() {
        // The fraction is reduced to lowest terms, whatever the signs are
        assert_eq!(Big8::from((2_i32, 4_i32)), RB!(1, 2));
        assert_eq!(Big8::from((-2_i32, 4_i32)), RB!(-1, 2));
        assert_eq!(Big8::from((2_i32, -4_i32)), RB!(-1, 2));
        assert_eq!(Big8::from((-2_i32, -4_i32)), RB!(1, 2));
        assert_eq!(Big8::from((6_i8, 4_i8)), RB!(3, 2));
        assert_eq!(Big8::from((100_i64, 10_i64)), RB!(10));
        assert_eq!(Big8::from((4_i128, 6_i128)), RB!(2, 3));
        assert_eq!(Big8::from((4_isize, 6_isize)), RB!(2, 3));

        // Equality and ordering agree with each other
        assert_eq!(Big8::from((2_i32, 4_i32)).cmp(&RB!(1, 2)), Ordering::Equal);
        assert_eq!(Big8::from((-2_i32, 4_i32)).cmp(&RB!(-1, 2)), Ordering::Equal);

        // A zero numerator gives the canonical zero, whatever the denominator is
        for value in [(0_i32, 5_i32), (0_i32, -5_i32), (0_i32, 1_i32)] {
            let zero = Big8::from(value);

            assert_eq!(zero.sign, Sign::Zero);
            assert!(zero.numerator.is_zero());
            assert!(zero.denominator.is_one());
            assert_eq!(zero, RB!(0));
            assert_eq!(zero.cmp(&RB!(0)), Ordering::Equal);
        }
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
        // The debug representation is the same as the display representation, so it round trips
        for text in [
            "0",
            "1",
            "-1",
            "2/3",
            "-2/3",
            "18446744073709551616",
            "-18446744073709551616",
            "676230147000402641135208532975102322580080121519024130",
            "676230147000402641135208532975102322580080121519024130/68468465468464168545346854646",
        ] {
            let value = RationalBig::from_str(text).unwrap();

            assert_eq!(format!("{:?}", value), format!("{}", value));
            assert_eq!(RationalBig::from_str(&format!("{:?}", value)), Ok(value));
        }

        assert_eq!(format!("{:?}", RB!(2, 3)), "2/3");
        assert_eq!(format!("{:?}", RB!(0)), "0");
        assert_eq!(format!("{:?}", RB!(-1)), "-1");
    }

    /// Both the numerator and the denominator can be too large for the target on their own.
    #[test]
    fn test_to_float_large_ratio() {
        let (words, bits) = (1200 / BITS_PER_WORD, 1200 % BITS_PER_WORD);
        let mut numerator: SmallVec<[usize; 8]> = smallvec![0; words as usize];
        numerator.push(1 << bits);
        let mut denominator = numerator.clone();
        denominator[0] |= 1;

        // 2 ** 1200 / (2 ** 1200 + 1), which is just below one and in lowest terms
        let value = Big8 {
            sign: Sign::Positive,
            numerator: unsafe { Ubig::from_inner_unchecked(numerator) },
            denominator: unsafe { NonZeroUbig::from_inner_unchecked(denominator) },
        };

        assert_eq!(value.to_f64(), Some(1_f64));
        assert_eq!(value.to_f32(), Some(1_f32));
        assert_eq!((-value.clone()).to_f64(), Some(-1_f64));
    }

    /// The magnitude of the most negative value doesn't fit the target type.
    #[test]
    fn test_to_primitive_most_negative() {
        assert_eq!(Big8::from_str("-128").unwrap().to_i8(), Some(i8::MIN));
        assert_eq!(Big8::from_str("-32768").unwrap().to_i16(), Some(i16::MIN));
        assert_eq!(Big8::from_str("-2147483648").unwrap().to_i32(), Some(i32::MIN));
        assert_eq!(Big8::from_str("-9223372036854775808").unwrap().to_i64(), Some(i64::MIN));
        assert_eq!(
            Big8::from_str("-170141183460469231731687303715884105728").unwrap().to_i128(),
            Some(i128::MIN),
        );
        assert_eq!(
            Big8::from_str(&isize::MIN.to_string()).unwrap().to_isize(),
            Some(isize::MIN),
        );

        // One below the most negative value still doesn't fit
        assert_eq!(Big8::from_str("-129").unwrap().to_i8(), None);
        assert_eq!(Big8::from_str("-9223372036854775809").unwrap().to_i64(), None);

        // The positive counterpart doesn't fit either
        assert_eq!(Big8::from_str("128").unwrap().to_i8(), None);
        assert_eq!(Big8::from_str("9223372036854775808").unwrap().to_i64(), None);
    }

    #[test]
    fn test_to_primitive_128() {
        assert_eq!(RB!(0).to_u128(), Some(0));
        assert_eq!(RB!(0).to_i128(), Some(0));
        assert_eq!(RB!(1).to_u128(), Some(1));
        assert_eq!(RB!(-1).to_i128(), Some(-1));
        assert_eq!(RB!(-1).to_u128(), None);
        assert_eq!(RB!(1, 2).to_u128(), Some(0));
        assert_eq!(RB!(-3, 2).to_i128(), Some(-1));

        // Round trip through the `Rational128` conversion
        let large = Rational128::new_signed(Sign::Positive, u128::MAX, 1).unwrap();
        assert_eq!(Big8::from(large).to_u128(), Some(u128::MAX));
        assert_eq!(Big8::from(large).to_i128(), None);

        let large = Rational128::new_signed(Sign::Positive, i128::MAX as u128, 1).unwrap();
        assert_eq!(Big8::from(large).to_i128(), Some(i128::MAX));

        // A value that needs more than a `u128`
        let too_large = Big8::from_str("340282366920938463463374607431768211456").unwrap();
        assert_eq!(too_large.to_u128(), None);
        assert_eq!(too_large.to_i128(), None);
    }

    /// The first byte of the string is not necessarily a character boundary.
    #[test]
    fn test_from_str_not_ascii() {
        assert_eq!(Big8::from_str("\u{e9}"), Err("Character is not a digit"));
        assert_eq!(Big8::from_str("-\u{e9}"), Err("Character is not a digit"));
        assert_eq!(Big8::from_str("\u{e9}/2"), Err("Character is not a digit"));
        assert_eq!(Big8::from_str("1/\u{e9}"), Err("Character is not a digit"));
        assert_eq!(Big8::from_str("\u{1f600}"), Err("Character is not a digit"));
    }

    /// A string that is empty, or that only contains whitespace, is not a number.
    #[test]
    fn test_from_str_no_digits() {
        for text in ["", " ", "\t\n", "-", "+", "/", "-/", " 1", "1 ", "1 / 2", "- 1"] {
            assert!(Big8::from_str(text).is_err(), "parsed {:?}", text);
        }

        // A string of zeros is still zero
        assert_eq!(Big8::from_str("0"), Ok(RB!(0)));
        assert_eq!(Big8::from_str("0000"), Ok(RB!(0)));
        assert_eq!(Big8::from_str("-0000"), Ok(RB!(0)));
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
