#![allow(unused_unsafe)]

use core::mem;
use std::cmp::Ordering;
use std::convert::TryFrom;
use std::convert::TryInto;
use std::fmt;
use std::num::{NonZeroU128, NonZeroUsize};
use std::str::FromStr;

use num_traits::{FromPrimitive, One, ToPrimitive, Zero};
use smallvec::SmallVec;
use smallvec::smallvec;

use crate::integer::big::{BITS_PER_WORD, NonZeroUbig, Ubig};
use crate::integer::big::ops::building_blocks::is_well_formed;
use crate::integer::big::ops::non_zero::{add_assign_single_non_zero, mul_assign_single_non_zero, shl_mut, shr_mut};
use crate::rational::{f32_kind, f64_kind};
use crate::rational::big::io::FloatKind;

impl<const S: usize> Ubig<S> {
    /// Creates a new unsigned integer with the small specified value.
    #[must_use]
    #[inline]
    pub fn new(value: usize) -> Self {
        Ubig(if value > 0 { smallvec![value] } else { smallvec![] })
    }
    /// Creates a new unsigned integer with the specified value.
    ///
    /// The value might not fit in a single word.
    #[must_use]
    #[inline]
    pub fn new_u128(value: u128) -> Self {
        Ubig(u128_words(value))
    }
    #[must_use]
    #[inline]
    pub(crate) unsafe fn from_inner_unchecked(values: SmallVec<[usize; S]>) -> Self {
        debug_assert!(is_well_formed(&values));

        Self(values)
    }
}

impl<const S: usize> NonZeroUbig<S> {
    /// Creates a new unsigned integer with the small specified value.
    ///
    /// If the specified value is non zero, this succeeds, otherwise, returns `None`.
    #[must_use]
    pub fn new(n: usize) -> Option<Self> {
        if n != 0 {
            Some(unsafe { Self(smallvec![n]) })
        } else {
            None
        }
    }
    /// Creates a new unsigned integer with the specified value.
    ///
    /// The value might not fit in a single word; if the specified value is non zero, this succeeds,
    /// otherwise, returns `None`.
    #[must_use]
    pub fn new_u128(n: u128) -> Option<Self> {
        if n != 0 {
            Some(Self(u128_words(n)))
        } else {
            None
        }
    }
    #[must_use]
    #[inline]
    pub(crate) unsafe fn new_unchecked(value: usize) -> Self {
        NonZeroUbig(smallvec![value])
    }
    /// # Safety
    ///
    /// The value should not be zero.
    #[must_use]
    #[inline]
    pub(crate) unsafe fn new_u128_unchecked(value: u128) -> Self {
        debug_assert_ne!(value, 0);

        NonZeroUbig(u128_words(value))
    }
    #[must_use]
    #[inline]
    pub(crate) unsafe fn from_inner_unchecked(values: SmallVec<[usize; S]>) -> Self {
        debug_assert!(is_well_formed(&values));

        Self(values)
    }
}

impl<const S: usize> Default for Ubig<S> {
    fn default() -> Self {
        Self::zero()
    }
}

impl<const S: usize> From<NonZeroUsize> for Ubig<S> {
    fn from(value: NonZeroUsize) -> Self {
        Self(smallvec![value.get()])
    }
}

impl<const S: usize> From<NonZeroUsize> for NonZeroUbig<S> {
    fn from(value: NonZeroUsize) -> Self {
        Self(smallvec![value.get()])
    }
}

impl<const S: usize> From<NonZeroU128> for Ubig<S> {
    fn from(value: NonZeroU128) -> Self {
        Self(u128_words(value.get()))
    }
}

impl<const S: usize> From<NonZeroU128> for NonZeroUbig<S> {
    fn from(value: NonZeroU128) -> Self {
        Self(u128_words(value.get()))
    }
}

impl<const S: usize, const I: usize> TryFrom<[usize; I]> for Ubig<S> {
    // TODO
    type Error = ();

    fn try_from(value: [usize; I]) -> Result<Self, Self::Error> {
        if is_well_formed(&value) {
            Ok(Self(SmallVec::from_slice(&value)))
        } else {
            Err(())
        }
    }
}

impl<const S: usize, const I: usize> TryFrom<[usize; I]> for NonZeroUbig<S> {
    // TODO
    type Error = ();

    fn try_from(value: [usize; I]) -> Result<Self, Self::Error> {
        if is_well_formed(&value) && !value.is_empty() {
            Ok(Self(SmallVec::from_slice(&value)))
        } else {
            Err(())
        }
    }
}

impl<const S: usize> Zero for Ubig<S> {
    #[inline]
    fn zero() -> Self {
        Self(smallvec![])
    }

    #[inline]
    fn set_zero(&mut self) {
        self.0.clear();
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
}

impl<const S: usize> One for Ubig<S> {
    #[inline]
    fn one() -> Self {
        Self(smallvec![1])
    }

    #[inline]
    fn set_one(&mut self) {
        self.0.clear();
        self.0.push(1);
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0.len() == 1 && self.0[0] == 1
    }
}

impl<const S: usize> One for NonZeroUbig<S> {
    #[inline]
    fn one() -> Self {
        Self(smallvec![1])
    }

    #[inline]
    fn set_one(&mut self) {
        self.0.truncate(1);
        *unsafe { self.0.get_unchecked_mut(0) } = 1;
    }

    #[inline]
    fn is_one(&self) -> bool {
        *unsafe { self.0.get_unchecked(0) } == 1 && self.0.len() == 1
    }
}


impl<const S: usize> From<usize> for Ubig<S> {
    fn from(value: usize) -> Self {
        Self(if value > 0 { smallvec![value] } else { smallvec![] })
    }
}

impl<const S: usize> From<u128> for Ubig<S> {
    fn from(value: u128) -> Self {
        Self::new_u128(value)
    }
}

/// Splits a `u128` into little endian words of the size of a `usize`.
///
/// The number of words that is needed depends on the platform: two on a 64 bit platform, four on a
/// 32 bit platform.
///
/// # Return value
///
/// A well formed value: trailing zero words are removed, such that the result is empty if and only
/// if the value is zero.
#[must_use]
#[inline]
fn u128_words<const S: usize>(value: u128) -> SmallVec<[usize; S]> {
    // At least one word, also when a `usize` would not be smaller than a `u128`
    let word_count = (mem::size_of::<u128>() / mem::size_of::<usize>()).max(1) as u32;

    let mut words = (0..word_count)
        .map(|index| (value >> (index * BITS_PER_WORD)) as usize)
        .collect::<SmallVec<[usize; S]>>();

    while let Some(&0) = words.last() {
        words.pop();
    }

    debug_assert!(is_well_formed(&words));

    words
}

impl<const S: usize> FromStr for Ubig<S> {
    // TODO(ARCHITECTURE): Better error handling
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        from_str_radix::<10, S>(s).map(Self)
    }
}

impl<const S: usize> FromStr for NonZeroUbig<S> {
    // TODO(ARCHITECTURE): Better error handling
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        from_str_radix::<10, S>(s)
            .and_then(|inner| {
                if !inner.is_empty() {
                    Ok(unsafe { Self(inner) })
                } else {
                    Err("Zero value")
                }
            })
    }
}

impl<const S: usize> fmt::Display for Ubig<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&to_str_radix::<10>(self))
    }
}

impl<const S: usize> fmt::Display for NonZeroUbig<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // TODO(PERFORMANCE): Skip zero case
        f.write_str(&to_str_radix::<10>(self))
    }
}

#[inline]
pub fn from_str_radix<const RADIX: u32, const S: usize>(s: &str) -> Result<SmallVec<[usize; S]>, &'static str> {
    debug_assert!(RADIX <= 36);

    match s.len() {
        0 => Err("Empty string"),
        _ => {
            // Note that the input is not trimmed: whitespace is not a digit, so a string that is
            // empty after trimming would otherwise be read as zero
            let mut char_iterator = s
                .chars()
                .skip_while(|&c| c == '0');
            match char_iterator.next() {
                None => Ok(smallvec![]),
                Some(value) => {
                    match value.to_digit(RADIX) {
                        None => Err("Character is not a digit"),
                        Some(value) => {
                            let mut non_zero_total = unsafe { smallvec![value as usize] };

                            for character in char_iterator {
                                match character.to_digit(RADIX) {
                                    None => return Err("Character is not a digit"),
                                    Some(value) => {
                                        mul_assign_single_non_zero(&mut non_zero_total, RADIX as usize);
                                        add_assign_single_non_zero(&mut non_zero_total, value as usize);
                                    }
                                }
                            }

                            Ok(non_zero_total)
                        }
                    }
                }
            }
        }
    }
}

fn to_str_radix<const RADIX: u32>(value: &[usize]) -> String {
    assert!(RADIX > 1 && RADIX <= 36);

    match value.len() {
        0 => "0".to_string(),
        _ => {
            let mut digits = vec![0];

            // Set highest word to the lowest index, and reverse the bits
            let mut leading_zero_words = 0;
            while value[leading_zero_words] == 0 {
                // At least the last value is not allowed to be zero, so we don't have to check bounds
                leading_zero_words += 1;
            }
            let leading_zero_bits = value.last().unwrap().leading_zeros();

            // Set highest word to the lowest index, and reverse the bits
            let mut value = value.iter()
                .skip(leading_zero_words)
                .map(|word| word.reverse_bits())
                .rev()
                .collect::<SmallVec<[usize; 8]>>();
            let len_before_shift = value.len() as u32;
            shr_mut(&mut value, 0, leading_zero_bits);

            let bit_count = len_before_shift * BITS_PER_WORD - leading_zero_bits;
            debug_assert_eq!(value[0] % 2, 1);
            for bit_index in 0..bit_count {
                update_digits::<RADIX>(&mut digits, value[0] % 2 == 1);
                shr_mut(&mut value, 0, 1);

                if value.is_empty() {
                    // Had this many bits remaining
                    for _ in (bit_index + 1)..(leading_zero_words as u32 * BITS_PER_WORD + bit_count) {
                        update_digits::<RADIX>(&mut digits, false);
                    }
                    break;
                }
            }

            digits.into_iter()
                .rev()
                .map(|digit| {
                    if digit < 10 {
                        digit.to_string()
                    } else {
                        ASCII_LOWER[(digit - 10) as usize].to_string()
                    }
                })
                .collect()
        }
    }
}

static ASCII_LOWER: [char; 26] = [
    'a', 'b', 'c', 'd', 'e',
    'f', 'g', 'h', 'i', 'j',
    'k', 'l', 'm', 'n', 'o',
    'p', 'q', 'r', 's', 't',
    'u', 'v', 'w', 'x', 'y',
    'z',
];

fn update_digits<const RADIX: u32>(digits: &mut Vec<u32>, mut carry: bool) {
    for digit in digits.iter_mut() {
        *digit *= 2; // binary, each bit multiplies by 2
        if carry {
            *digit += 1;
            carry = false;
        }
        if *digit >= RADIX {
            *digit %= RADIX;
            carry = true;
        }
    }
    if carry {
        digits.push(1);
    }
}

impl<const S: usize> FromPrimitive for Ubig<S> {
    fn from_isize(n: isize) -> Option<Self> {
        if n >= 0 {
            Some(Self::new(n.unsigned_abs()))
        } else {
            None
        }
    }

    fn from_i8(n: i8) -> Option<Self> {
        if n >= 0 {
            Some(Self::new(n.unsigned_abs() as usize))
        } else {
            None
        }
    }

    fn from_i16(n: i16) -> Option<Self> {
        if n >= 0 {
            Some(Self::new(n.unsigned_abs() as usize))
        } else {
            None
        }
    }

    fn from_i32(n: i32) -> Option<Self> {
        if n >= 0 {
            Some(Self::new(n.unsigned_abs() as usize))
        } else {
            None
        }
    }

    fn from_i64(n: i64) -> Option<Self> {
        if n >= 0 {
            Some(Self::new(n.unsigned_abs() as usize))
        } else {
            None
        }
    }

    fn from_i128(n: i128) -> Option<Self> {
        if n >= 0 {
            Self::from_u128(n.unsigned_abs())
        } else {
            None
        }
    }

    fn from_usize(n: usize) -> Option<Self> {
        Some(Self::new(n))
    }

    fn from_u8(n: u8) -> Option<Self> {
        Some(Self::new(n as usize))
    }

    fn from_u16(n: u16) -> Option<Self> {
        Some(Self::new(n as usize))
    }

    fn from_u32(n: u32) -> Option<Self> {
        Some(Self::new(n as usize))
    }

    fn from_u64(n: u64) -> Option<Self> {
        Some(Self::new(n as usize))
    }

    fn from_u128(n: u128) -> Option<Self> {
        Some(Self::new_u128(n))
    }

    fn from_f32(n: f32) -> Option<Self> {
        Self::from_float_kind(f32_kind(n))
    }

    fn from_f64(n: f64) -> Option<Self> {
        Self::from_float_kind(f64_kind(n))
    }
}

impl<const S: usize> Ubig<S> {
    fn from_float_kind(kind: FloatKind) -> Option<Self> {
        match kind  {
            FloatKind::Subnormal(as_ratio) | FloatKind::Normal(as_ratio) => {
                if as_ratio.sign == 0 {
                    let result = match as_ratio.exponent.cmp(&0) {
                        Ordering::Less => {
                            // The value is `fraction * 2 ** exponent`, so it is shifted to the
                            // right; the fractional part is truncated towards zero. The shift can
                            // be larger than the number of bits in the fraction, a subnormal `f64`
                            // has an exponent of -1074.
                            let shift = as_ratio.exponent.unsigned_abs();
                            let result = as_ratio.fraction.get()
                                .checked_shr(shift)
                                .unwrap_or(0);

                            Self::new_u128(result as u128)
                        }
                        Ordering::Equal => Self::new_u128(as_ratio.fraction.get() as u128),
                        Ordering::Greater => {
                            // The value is shifted to the left
                            let shift = as_ratio.exponent.unsigned_abs();
                            let (words, bits) = (shift / BITS_PER_WORD, shift % BITS_PER_WORD);

                            // The fraction is not zero, so this is well formed and not empty
                            let mut values = u128_words::<S>(as_ratio.fraction.get() as u128);
                            shl_mut(&mut values, words as usize, bits);

                            unsafe {
                                // SAFETY: Shifting a non zero value to the left keeps it well
                                // formed and non zero
                                Self::from_inner_unchecked(values)
                            }
                        }
                    };

                    Some(result)
                } else {
                    None
                }
            },
            FloatKind::Zero => Some(Self::zero()),
            _ => None,
        }
    }
}


macro_rules! small {
    ($value:expr) => {
        {
            match $value.len() {
                0 => Some(0),
                1 => $value[0].try_into().ok(),
                _ => None,
            }
        }
    }
}

/// The number of significant bits of the value.
#[must_use]
#[inline]
pub(crate) fn bit_length(words: &[usize]) -> u32 {
    debug_assert!(is_well_formed(words));

    match words.last() {
        None => 0,
        Some(&last) => (words.len() as u32 - 1) * BITS_PER_WORD + (BITS_PER_WORD - last.leading_zeros()),
    }
}

/// The highest word of the value, together with the number of bits that were dropped below it.
///
/// This is the value shifted to the right as far as is needed to fit a single word; it keeps the
/// most significant bits, which is what a float needs.
///
/// The value should not be zero.
#[must_use]
pub(crate) fn highest_word(words: &[usize]) -> (usize, u32) {
    debug_assert!(!words.is_empty());

    let shift = bit_length(words).saturating_sub(BITS_PER_WORD);
    let (word_shift, bit_shift) = ((shift / BITS_PER_WORD) as usize, shift % BITS_PER_WORD);
    debug_assert!(word_shift < words.len());

    let low = words[word_shift] >> bit_shift;
    let high = if bit_shift > 0 && word_shift + 1 < words.len() {
        words[word_shift + 1] << (BITS_PER_WORD - bit_shift)
    } else {
        0
    };

    (low | high, shift)
}

/// The value of the words as a `u128`.
///
/// # Return value
///
/// `None` if the value doesn't fit a `u128`, the value otherwise.
#[must_use]
#[inline]
pub(crate) fn words_to_u128(words: &[usize]) -> Option<u128> {
    // At least one word, also when a `usize` would not be smaller than a `u128`
    let word_count = (mem::size_of::<u128>() / mem::size_of::<usize>()).max(1);

    if words.len() > word_count {
        return None;
    }

    let mut total = 0_u128;
    for (index, &word) in words.iter().enumerate() {
        total |= (word as u128) << (index as u32 * BITS_PER_WORD);
    }

    Some(total)
}

macro_rules! to_primitive_impl {
    ($name:ty) => {
        impl<const S: usize> ToPrimitive for $name {
            fn to_isize(&self) -> Option<isize> {
                small!(self)
            }

            fn to_i8(&self) -> Option<i8> {
                small!(self)
            }

            fn to_i16(&self) -> Option<i16> {
                small!(self)
            }

            fn to_i32(&self) -> Option<i32> {
                small!(self)
            }

            fn to_i64(&self) -> Option<i64> {
                small!(self)
            }

            fn to_i128(&self) -> Option<i128> {
                words_to_u128(self).and_then(|value| i128::try_from(value).ok())
            }

            fn to_usize(&self) -> Option<usize> {
                small!(self)
            }

            fn to_u8(&self) -> Option<u8> {
                small!(self)
            }

            fn to_u16(&self) -> Option<u16> {
                small!(self)
            }

            fn to_u32(&self) -> Option<u32> {
                small!(self)
            }

            fn to_u64(&self) -> Option<u64> {
                small!(self)
            }

            fn to_u128(&self) -> Option<u128> {
                words_to_u128(self)
            }

            fn to_f32(&self) -> Option<f32> {
                Some(make_float_32::<S>(self))
            }

            fn to_f64(&self) -> Option<f64> {
                Some(make_float_64::<S>(self))
            }
        }
    }
}

to_primitive_impl!(Ubig<S>);
to_primitive_impl!(NonZeroUbig<S>);

macro_rules! define_float_maker {
    ($name:ident, $target:ty, $bit_array:ty, $bits_in_exponent:expr, $bits_in_fraction:expr) => {
        fn $name<const S: usize>(values: &[usize]) -> $target {
            let sign = 0;

            match values.last() {
                None => <$target>::zero(),
                Some(last_value) => {
                    debug_assert_ne!(*last_value, 0);
                    let bits_in_highest = BITS_PER_WORD - last_value.leading_zeros();
                    debug_assert!(bits_in_highest > 0);
                    let bits = (values.len() - 1) as u32 * BITS_PER_WORD + bits_in_highest;
                    debug_assert!(bits > 0);

                    let biased_exponent = bits as $bit_array + ((2 as $bit_array).pow($bits_in_exponent - 1) - 1 - 1);
                    if biased_exponent >= ((1 as $bit_array) << $bits_in_exponent) - 1 {
                        // The value doesn't fit the target; an exponent field of all ones is
                        // infinity, anything larger would overflow into the sign bit
                        return <$target>::INFINITY;
                    }
                    let exponent = biased_exponent << $bits_in_fraction;

                    let mut copy = SmallVec::<[usize; S]>::from_slice(values);
                    *copy.last_mut().unwrap() -= 1 << (bits_in_highest - 1);

                    let remaining_bits = bits - 1;
                    let fraction = match remaining_bits.cmp(&$bits_in_fraction) {
                        Ordering::Less => copy[0] << ($bits_in_fraction - remaining_bits),
                        Ordering::Equal => copy[0],
                        Ordering::Greater => {
                            let to_shift = remaining_bits - $bits_in_fraction;
                            let (highest_bit_lost_set, any_other_set) = {
                                let index = to_shift - 1;

                                let (words, bits) = ((index / BITS_PER_WORD) as usize, index % BITS_PER_WORD);
                                let highest_bit_lost = copy[words] & (1 << bits) > 0;

                                let any_other = copy[..words].iter().any(|&w| w != 0)
                                    || {
                                        if bits == 0 {
                                            false
                                        } else {
                                            let mask = !0 >> (BITS_PER_WORD - bits);
                                            mask & copy[words] > 0
                                        }
                                    };

                                (highest_bit_lost, any_other)
                            };

                            let (words, bits) = (to_shift / BITS_PER_WORD, to_shift % BITS_PER_WORD);

                            let unrounded = 'scope: {
                                // Subtracting the implicit leading bit can have zeroed the highest
                                // words; drop them to satisfy the assumptions of `shr_mut`. Note
                                // that `words` counts the lowest words that are shifted away, so
                                // it is unaffected by this.
                                while let Some(&0) = copy.last() {
                                    copy.pop();
                                }

                                if words as usize >= copy.len() {
                                    // Everything that is left is shifted away; this includes the
                                    // case where the value is a power of two and nothing is left
                                    break 'scope 0;
                                }

                                shr_mut(&mut copy, words as usize, bits);

                                match copy.last() {
                                    Some(&value) => value,
                                    None => 0,
                                }
                            };

                            if highest_bit_lost_set {
                                if any_other_set {
                                    unrounded + 1
                                } else {
                                    // Tie to even
                                    if unrounded % 2 == 1 {
                                        unrounded + 1
                                    } else {
                                        unrounded
                                    }
                                }
                            } else {
                                unrounded
                            }
                        },
                    };

                    // The fraction is added rather than or-ed in: rounding can carry out of
                    // the mantissa, leaving `fraction == 1 << $bits_in_fraction`, and that carry
                    // has to increment the exponent. Or-ing loses it whenever the biased exponent
                    // is odd, which halves the result. The exponent is bounded above, so the carry
                    // at worst produces an all ones exponent with a zero mantissa, which is the
                    // correct encoding of infinity.
                    <$target>::from_bits(sign | (exponent + fraction as $bit_array))
                }
            }
        }
    }
}

define_float_maker!(make_float_32, f32, u32, 8, 23);
define_float_maker!(make_float_64, f64, u64, 11, 52);

#[cfg(test)]
mod test {
    use std::num::NonZeroU128;
    use std::str::FromStr;

    use num_traits::FromPrimitive;
    use num_traits::One;
    use num_traits::ToPrimitive;
    use num_traits::Zero;
    use smallvec::{smallvec, SmallVec};

    use crate::integer::big::{BITS_PER_WORD, NonZeroUbig};
    use crate::Ubig;

    /// Two to the power of the argument, as an arbitrary precision integer.
    fn power_of_two<const S: usize>(power: u32) -> Ubig<S> {
        let (words, bits) = (power / BITS_PER_WORD, power % BITS_PER_WORD);

        let mut values: SmallVec<[usize; S]> = smallvec![0; words as usize];
        values.push(1 << bits);

        unsafe {
            // SAFETY: The last word is not zero
            Ubig::from_inner_unchecked(values)
        }
    }

    /// Two to the power of the argument, plus one.
    fn power_of_two_plus_one<const S: usize>(power: u32) -> Ubig<S> {
        debug_assert!(power >= BITS_PER_WORD);

        let mut value = power_of_two::<S>(power);
        unsafe {
            // SAFETY: The power is at least a word, so the lowest word is zero and the value stays
            // well formed
            value.inner_mut()[0] |= 1;
        }

        value
    }

    /// The values that are interesting when a `u128` is split into words.
    const U128_CASES: [u128; 8] = [
        0,
        1,
        19,
        usize::MAX as u128,
        usize::MAX as u128 + 1,
        (usize::MAX as u128 + 1) * 3,
        i128::MAX as u128,
        u128::MAX,
    ];

    #[test]
    fn test_from_u128() {
        assert_eq!(Ubig::<8>::new_u128(0), Ubig::zero());
        assert_eq!(Ubig::<8>::new_u128(1), Ubig::one());
        assert_eq!(Ubig::<8>::new_u128(19), Ubig::new(19));
        assert_eq!(Ubig::<8>::new_u128(usize::MAX as u128), Ubig::new(usize::MAX));

        // Nothing is truncated when more than a single word is needed
        for value in U128_CASES {
            assert_eq!(Ubig::<8>::new_u128(value).to_string(), value.to_string());
            assert_eq!(Ubig::<8>::from_str(&value.to_string()), Ok(Ubig::new_u128(value)));

            // The `From` implementation is the same conversion
            assert_eq!(Ubig::<8>::from(value), Ubig::new_u128(value));
        }
    }

    #[test]
    fn test_from_u128_is_normalized() {
        // The zero value is empty, all others don't have a trailing zero word
        assert!(Ubig::<8>::new_u128(0).inner().is_empty());
        for value in U128_CASES {
            assert!(unsafe { Ubig::<8>::new_u128(value).is_well_formed() });
            assert_eq!(Ubig::<8>::new_u128(value).is_zero(), value == 0);
        }
    }

    #[test]
    fn test_non_zero_from_u128() {
        assert_eq!(NonZeroUbig::<8>::new_u128(0), None);
        assert_eq!(NonZeroUbig::<8>::new_u128(1), Some(NonZeroUbig::one()));

        for value in U128_CASES.into_iter().filter(|&value| value != 0) {
            let expected = NonZeroUbig::<8>::from_str(&value.to_string()).unwrap();

            assert_eq!(NonZeroUbig::<8>::new_u128(value), Some(expected.clone()));
            assert_eq!(unsafe { NonZeroUbig::<8>::new_u128_unchecked(value) }, expected);
            assert!(unsafe { expected.is_well_formed() });

            let non_zero = NonZeroU128::new(value).unwrap();
            assert_eq!(NonZeroUbig::<8>::from(non_zero), expected);
            assert_eq!(Ubig::<8>::from(non_zero), Ubig::new_u128(value));
        }
    }

    #[test]
    fn test_from_primitive() {
        assert_eq!(Ubig::<1>::from_i16(-4), None);
        assert_eq!(Ubig::<1>::from_u16(4), Some(Ubig::from(4_usize)));
        assert_eq!(Ubig::<1>::from_i128(0), Some(Ubig::from(0_usize)));
        assert_eq!(Ubig::<1>::from_i128(1), Some(Ubig::from(1_usize)));
        assert_eq!(Ubig::<1>::from_i128(-1), None);

        assert_eq!(Ubig::<1>::from_f32(1.5_f32), Some(Ubig::from(1_usize)));
        assert_eq!(Ubig::<1>::from_f32(1_f32), Some(Ubig::from(1_usize)));
        assert_eq!(Ubig::<1>::from_f32(0.5_f32), Some(Ubig::from(0_usize)));
        assert_eq!(Ubig::<1>::from_f32(0.75_f32), Some(Ubig::from(0_usize)));
        assert_eq!(Ubig::<1>::from_f32(0_f32), Some(Ubig::from(0_usize)));

        assert_eq!(Ubig::<1>::from_f32(-1.5_f32), None);
        assert_eq!(Ubig::<1>::from_f32(-0_f32), Some(Ubig::from(0_usize)));
    }

    #[test]
    fn test_from_primitive_large() {
        for value in U128_CASES {
            assert_eq!(Ubig::<8>::from_u128(value), Some(Ubig::new_u128(value)));
        }

        assert_eq!(Ubig::<8>::from_i128(i128::MAX), Some(Ubig::new_u128(i128::MAX as u128)));
        assert_eq!(Ubig::<8>::from_i128(i128::MIN), None);
        assert_eq!(Ubig::<8>::from_u128(u128::MAX).unwrap().to_string(), u128::MAX.to_string());
    }

    /// A positive binary exponent means the fraction is shifted to the left, not to the right.
    #[test]
    fn test_from_float_with_positive_exponent() {
        // The formatting with a zero precision is the exact value of the float, which is an integer
        for value in [
            1e16_f64,
            9007199254740992_f64,
            1.8446744073709552e19,
            2_f64.powi(64),
            2_f64.powi(100),
            2_f64.powi(1000),
            1e300,
        ] {
            let expected = Ubig::<8>::from_str(&format!("{:.0}", value)).unwrap();
            assert_eq!(Ubig::<8>::from_f64(value), Some(expected), "value {}", value);
        }

        for value in [1e30_f32, 2_f32.powi(64), 2_f32.powi(100), f32::MAX] {
            let expected = Ubig::<8>::from_str(&format!("{:.0}", value)).unwrap();
            assert_eq!(Ubig::<8>::from_f32(value), Some(expected), "value {}", value);
        }
    }

    /// A negative binary exponent can shift away more bits than a `u64` has.
    #[test]
    fn test_from_float_with_large_negative_exponent() {
        // Truncation towards zero, so all of these are zero
        assert_eq!(Ubig::<8>::from_f64(f64::MIN_POSITIVE), Some(Ubig::zero()));
        assert_eq!(Ubig::<8>::from_f64(f64::from_bits(1)), Some(Ubig::zero()));
        assert_eq!(Ubig::<8>::from_f64(1e-300), Some(Ubig::zero()));
        assert_eq!(Ubig::<8>::from_f32(1e-30_f32), Some(Ubig::zero()));
        assert_eq!(Ubig::<8>::from_f32(f32::MIN_POSITIVE), Some(Ubig::zero()));
        assert_eq!(Ubig::<8>::from_f32(f32::from_bits(1)), Some(Ubig::zero()));
    }

    /// Subtracting the implicit leading bit can zero the highest word, which used to underflow the
    /// bookkeeping of the words that are shifted away.
    #[test]
    fn test_to_float_powers_of_two() {
        for power in [0_u32, 1, 52, 53, 62, 63, 64, 65, 66, 100, 127, 128, 200, 1000] {
            let value = power_of_two::<8>(power);
            assert_eq!(value.to_f64(), Some(2_f64.powi(power as i32)), "2 ** {}", power);
        }

        for power in [0_u32, 1, 22, 23, 30, 31, 32, 33, 63, 64, 65, 100, 127] {
            let value = power_of_two::<8>(power);
            assert_eq!(value.to_f32(), Some(2_f32.powi(power as i32)), "2 ** {}", power);
        }
    }

    #[test]
    fn test_to_float_one_above_power_of_two() {
        for power in [64_u32, 65, 66, 100, 127, 128, 200] {
            let value = power_of_two_plus_one::<8>(power);
            assert_eq!(value.to_f64(), Some(2_f64.powi(power as i32)), "2 ** {} + 1", power);
        }

        for power in [64_u32, 65, 100, 127] {
            let value = power_of_two_plus_one::<8>(power);
            assert_eq!(value.to_f32(), Some(2_f32.powi(power as i32)), "2 ** {} + 1", power);
        }
    }

    /// A value that is too large for the target overflowed the exponent field into the sign bit.
    #[test]
    fn test_to_float_overflow_is_infinite() {
        // Larger than the largest finite `f32`
        for power in [128_u32, 129, 140, 300, 1000] {
            for value in [power_of_two::<8>(power), power_of_two_plus_one::<8>(power)] {
                let result = value.to_f32().unwrap();

                assert_eq!(result, f32::INFINITY, "2 ** {}", power);
                assert!(result.is_sign_positive(), "2 ** {}", power);
            }
        }

        // Larger than the largest finite `f64`
        for power in [1024_u32, 1025, 2000] {
            for value in [power_of_two::<8>(power), power_of_two_plus_one::<8>(power)] {
                let result = value.to_f64().unwrap();

                assert_eq!(result, f64::INFINITY, "2 ** {}", power);
                assert!(result.is_sign_positive(), "2 ** {}", power);
            }
        }

        // Just below the threshold the values are still finite
        assert_eq!(power_of_two::<8>(127).to_f32(), Some(2_f32.powi(127)));
        assert_eq!(power_of_two::<8>(1023).to_f64(), Some(2_f64.powi(1023)));
    }

    /// Rounding can carry out of the mantissa, which has to increment the exponent.
    ///
    /// The parts used to be or-ed together, which drops that carry whenever the biased exponent is
    /// odd, that is, whenever the value has an odd number of bits. The result is then exactly half
    /// of the true value. `2 ** p - d` for a small `d` rounds up to `2 ** p` and so is the shape
    /// that triggers it.
    #[test]
    fn test_to_float_mantissa_carry() {
        assert_eq!(Ubig::<8>::from((1_u128 << 55) - 1).to_f64(), Some(2_f64.powi(55)));
        assert_eq!(Ubig::<8>::from((1_u128 << 25) - 1).to_f32(), Some(2_f32.powi(25)));

        for power in 2_u32..=127 {
            // Do not underflow at the small powers
            for difference in 1..=64_u128.min((1_u128 << power) - 1) {
                let value = (1_u128 << power) - difference;
                let big = Ubig::<8>::from(value);

                assert_eq!(big.to_f64(), Some(value as f64), "2 ** {power} - {difference}");
                assert_eq!(big.to_f32(), Some(value as f32), "2 ** {power} - {difference}");
            }
        }
    }

    #[test]
    fn test_to_primitive_128() {
        for value in U128_CASES {
            assert_eq!(Ubig::<8>::new_u128(value).to_u128(), Some(value));
        }

        assert_eq!(Ubig::<8>::zero().to_i128(), Some(0));
        assert_eq!(Ubig::<8>::new_u128(i128::MAX as u128).to_i128(), Some(i128::MAX));
        assert_eq!(Ubig::<8>::new_u128(i128::MAX as u128 + 1).to_i128(), None);
        assert_eq!(Ubig::<8>::new_u128(u128::MAX).to_i128(), None);

        assert_eq!(NonZeroUbig::<8>::new_u128(u128::MAX).unwrap().to_u128(), Some(u128::MAX));
        assert_eq!(NonZeroUbig::<8>::one().to_i128(), Some(1));

        // Larger than a `u128`
        let too_large = Ubig::<8>::from_str("340282366920938463463374607431768211456").unwrap();
        assert_eq!(too_large.to_u128(), None);
        assert_eq!(too_large.to_i128(), None);
    }

    #[test]
    fn test_to_primitive() {
        assert_eq!(Ubig::<1>::from(4_usize).to_i16(), Some(4));

        assert_eq!(Ubig::<1>::from(0_usize).to_f32(), Some(0_f32));
        assert_eq!(Ubig::<1>::from(1_usize).to_f32(), Some(1_f32));
        assert_eq!(Ubig::<1>::from(2_usize).to_f32(), Some(2_f32));
        assert_eq!(Ubig::<1>::from(3_usize).to_f32(), Some(3_f32));
        assert_eq!(Ubig::<1>::from(4_usize).to_f32(), Some(4_f32));
        assert_eq!(Ubig::<1>::from(5_usize).to_f32(), Some(5_f32));
        assert_eq!(Ubig::<1>::from(6_usize).to_f32(), Some(6_f32));
        assert_eq!(Ubig::<1>::from(7_usize).to_f32(), Some(7_f32));

        assert_eq!(Ubig::<1>::from(0_usize).to_f64(), Some(0_f64));
        assert_eq!(Ubig::<1>::from(1_usize).to_f64(), Some(1_f64));
        assert_eq!(Ubig::<1>::from(2_usize).to_f64(), Some(2_f64));
        assert_eq!(Ubig::<1>::from(3_usize).to_f64(), Some(3_f64));
        assert_eq!(Ubig::<1>::from(4_usize).to_f64(), Some(4_f64));
        assert_eq!(Ubig::<1>::from(5_usize).to_f64(), Some(5_f64));
        assert_eq!(Ubig::<1>::from(6_usize).to_f64(), Some(6_f64));
        assert_eq!(Ubig::<1>::from(7_usize).to_f64(), Some(7_f64));
        assert_eq!(Ubig::<1>::from(123456789_usize).to_f64(), Some(123456789_f64));
    }

    #[test]
    fn test_to_primitive_rounding() {
        assert_eq!(Ubig::<1>::from(16777216_usize).to_f32(), Some(16777216_f32));
        assert_eq!(Ubig::<1>::from(16777217_usize).to_f32(), Some(16777217_f32));
        assert_eq!(Ubig::<1>::from(16777218_usize).to_f32(), Some(16777218_f32));
        assert_eq!(Ubig::<1>::from(16777219_usize).to_f32(), Some(16777219_f32));

        assert_eq!(Ubig::<1>::from(123_456_789_usize).to_f32(), Some(123456790_f32));

        for i in 0..100 {
            let x = 2_usize.pow(25) + i;
            assert_eq!(Ubig::<1>::from(x).to_f32(), Some(x as f32));
        }

        assert_eq!(Ubig::<1>::from(9_007_199_254_740_992_usize).to_f32(), Some(9007199000000000_f32));
        assert_eq!(Ubig::<1>::from(9_007_199_254_740_993_usize).to_f32(), Some(9007199000000000_f32));
        assert_eq!(Ubig::<1>::from(9_007_199_254_740_994_usize).to_f32(), Some(9007199000000000_f32));

        assert_eq!(Ubig::<1>::from(9_007_199_254_740_992_usize).to_f64(), Some(9_007_199_254_740_992_f64));
        assert_eq!(Ubig::<1>::from(9_007_199_254_740_993_usize).to_f64(), Some(9_007_199_254_740_992_f64));
        assert_eq!(Ubig::<1>::from(9_007_199_254_740_994_usize).to_f64(), Some(9_007_199_254_740_994_f64));

        for i in 0..100 {
            let x = 2_usize.pow(54) + i;
            assert_eq!(Ubig::<1>::from(x).to_f64(), Some(x as f64));
        }
    }
}
