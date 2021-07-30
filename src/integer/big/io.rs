#![allow(unused_unsafe)]

use core::mem;
use std::cmp::Ordering;
use std::convert::TryFrom;
use std::convert::TryInto;
use std::fmt;
use std::num::NonZeroUsize;
use std::str::FromStr;

use num_traits::{FromPrimitive, One, ToPrimitive, Zero};
use smallvec::SmallVec;
use smallvec::smallvec;

use crate::integer::big::{BITS_PER_WORD, NonZeroUbig, Ubig};
use crate::integer::big::ops::building_blocks::is_well_formed;
use crate::integer::big::ops::non_zero::{add_assign_single_non_zero, mul_assign_single_non_zero, shr, shr_mut};
use crate::rational::{f32_kind, f64_kind};
use crate::rational::big::io::FloatKind;

impl<const S: usize> Ubig<S> {
    /// Creates a new unsigned integer with the small specified value.
    #[must_use]
    #[inline]
    pub fn new(value: usize) -> Self {
        Ubig(if value > 0 { smallvec![value] } else { smallvec![] })
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
    #[must_use]
    #[inline]
    pub(crate) unsafe fn new_unchecked(value: usize) -> Self {
        NonZeroUbig(smallvec![value])
    }
    #[must_use]
    #[inline]
    pub(crate) unsafe fn from_inner_unchecked(values: SmallVec<[usize; S]>) -> Self {
        debug_assert!(is_well_formed(&values));

        Self(values)
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
    #[must_use]
    #[inline]
    fn zero() -> Self {
        Self(smallvec![])
    }

    #[inline]
    fn set_zero(&mut self) {
        self.0.clear();
    }

    #[must_use]
    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
}

impl<const S: usize> One for Ubig<S> {
    #[must_use]
    #[inline]
    fn one() -> Self {
        Self(smallvec![1])
    }

    #[inline]
    fn set_one(&mut self) {
        self.0.clear();
        self.0.push(1);
    }

    #[must_use]
    #[inline]
    fn is_one(&self) -> bool {
        self.0.len() == 1 && self.0[0] == 1
    }
}

impl<const S: usize> One for NonZeroUbig<S> {
    #[must_use]
    #[inline]
    fn one() -> Self {
        Self(smallvec![1])
    }

    #[inline]
    fn set_one(&mut self) {
        self.0.truncate(1);
        *unsafe { self.0.get_unchecked_mut(0) } = 1;
    }

    #[must_use]
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
            .map(|inner| {
                if !inner.is_empty() {
                    Ok(unsafe { Self(inner) })
                } else {
                    Err("Zero value")
                }
            })
            .flatten()
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
            let mut char_iterator = s
                .trim()
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
        let bits = mem::size_of::<u32>() * 8;
        let groups = 128 / bits;

        let mut data = (0..groups)
            .map(|i| (n >> (i * bits)) as usize)
            .collect::<SmallVec<_>>();
        while let Some(0) = data.last() {
            data.pop();
        }

        debug_assert!(is_well_formed(&data));

        Some(unsafe {
            // SAFETY: data does not end in a zero value.
            Self::from_inner_unchecked(data)
        })
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
                            let result = as_ratio.fraction.get() >> as_ratio.exponent.unsigned_abs();
                            Self::from(result as usize)
                        }
                        Ordering::Equal => Self::from(as_ratio.fraction.get() as usize),
                        Ordering::Greater => {
                            let exponent = as_ratio.exponent.unsigned_abs();
                            let (words, bits) = (exponent / BITS_PER_WORD, exponent % BITS_PER_WORD);
                            let values = [as_ratio.fraction.get() as usize];
                            let result = shr(&values, words as usize, bits);

                            unsafe {
                                Self::from_inner_unchecked(result)
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
                todo!()
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
                todo!()
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

                    let exponent = (bits as $bit_array + ((2 as $bit_array).pow($bits_in_exponent - 1) - 1 - 1)) << $bits_in_fraction;

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

                            let (mut words, bits) = (to_shift / BITS_PER_WORD, to_shift % BITS_PER_WORD);

                            let unrounded = 'scope: {
                                // Satisfy the assumptions of `shr_mut`
                                while let Some(0) = copy.last() {
                                    if copy.len() == 1 {
                                        // This is the last value. We must be dealing with a power of 2.
                                        break 'scope 0;
                                    }
                                    copy.pop();
                                    words -= 1;
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

                    <$target>::from_bits(sign | exponent | fraction as $bit_array)
                }
            }
        }
    }
}

define_float_maker!(make_float_32, f32, u32, 8, 23);
define_float_maker!(make_float_64, f64, u64, 11, 52);

#[cfg(test)]
mod test {
    use num_traits::FromPrimitive;
    use num_traits::ToPrimitive;

    use crate::Ubig;

    #[test]
    fn test_from_primitive() {
        assert_eq!(Ubig::<1>::from_i16(-4), None);
        assert_eq!(Ubig::<1>::from_u16(4), Some(Ubig::from(4)));
        assert_eq!(Ubig::<1>::from_i128(0), Some(Ubig::from(0)));
        assert_eq!(Ubig::<1>::from_i128(1), Some(Ubig::from(1)));
        assert_eq!(Ubig::<1>::from_i128(-1), None);

        assert_eq!(Ubig::<1>::from_f32(1.5_f32), Some(Ubig::from(1)));
        assert_eq!(Ubig::<1>::from_f32(1_f32), Some(Ubig::from(1)));
        assert_eq!(Ubig::<1>::from_f32(0.5_f32), Some(Ubig::from(0)));
        assert_eq!(Ubig::<1>::from_f32(0.75_f32), Some(Ubig::from(0)));
        assert_eq!(Ubig::<1>::from_f32(0_f32), Some(Ubig::from(0)));

        assert_eq!(Ubig::<1>::from_f32(-1.5_f32), None);
        assert_eq!(Ubig::<1>::from_f32(-0_f32), Some(Ubig::from(0)));
    }

    #[test]
    fn test_to_primitive() {
        assert_eq!(Ubig::<1>::from(4).to_i16(), Some(4));

        assert_eq!(Ubig::<1>::from(0).to_f32(), Some(0_f32));
        assert_eq!(Ubig::<1>::from(1).to_f32(), Some(1_f32));
        assert_eq!(Ubig::<1>::from(2).to_f32(), Some(2_f32));
        assert_eq!(Ubig::<1>::from(3).to_f32(), Some(3_f32));
        assert_eq!(Ubig::<1>::from(4).to_f32(), Some(4_f32));
        assert_eq!(Ubig::<1>::from(5).to_f32(), Some(5_f32));
        assert_eq!(Ubig::<1>::from(6).to_f32(), Some(6_f32));
        assert_eq!(Ubig::<1>::from(7).to_f32(), Some(7_f32));

        assert_eq!(Ubig::<1>::from(0).to_f64(), Some(0_f64));
        assert_eq!(Ubig::<1>::from(1).to_f64(), Some(1_f64));
        assert_eq!(Ubig::<1>::from(2).to_f64(), Some(2_f64));
        assert_eq!(Ubig::<1>::from(3).to_f64(), Some(3_f64));
        assert_eq!(Ubig::<1>::from(4).to_f64(), Some(4_f64));
        assert_eq!(Ubig::<1>::from(5).to_f64(), Some(5_f64));
        assert_eq!(Ubig::<1>::from(6).to_f64(), Some(6_f64));
        assert_eq!(Ubig::<1>::from(7).to_f64(), Some(7_f64));
        assert_eq!(Ubig::<1>::from(123456789).to_f64(), Some(123456789_f64));
    }

    #[test]
    fn test_to_primitive_rounding() {
        assert_eq!(Ubig::<1>::from(16777216).to_f32(), Some(16777216_f32));
        assert_eq!(Ubig::<1>::from(16777217).to_f32(), Some(16777217_f32));
        assert_eq!(Ubig::<1>::from(16777218).to_f32(), Some(16777218_f32));
        assert_eq!(Ubig::<1>::from(16777219).to_f32(), Some(16777219_f32));

        assert_eq!(Ubig::<1>::from(123_456_789).to_f32(), Some(123456790_f32));

        for i in 0..100 {
            let x = 2_usize.pow(25) + i;
            assert_eq!(Ubig::<1>::from(x).to_f32(), Some(x as f32));
        }

        assert_eq!(Ubig::<1>::from(9_007_199_254_740_992).to_f32(), Some(9007199000000000_f32));
        assert_eq!(Ubig::<1>::from(9_007_199_254_740_993).to_f32(), Some(9007199000000000_f32));
        assert_eq!(Ubig::<1>::from(9_007_199_254_740_994).to_f32(), Some(9007199000000000_f32));

        assert_eq!(Ubig::<1>::from(9_007_199_254_740_992).to_f64(), Some(9_007_199_254_740_992_f64));
        assert_eq!(Ubig::<1>::from(9_007_199_254_740_993).to_f64(), Some(9_007_199_254_740_992_f64));
        assert_eq!(Ubig::<1>::from(9_007_199_254_740_994).to_f64(), Some(9_007_199_254_740_994_f64));

        for i in 0..100 {
            let x = 2_usize.pow(54) + i;
            assert_eq!(Ubig::<1>::from(x).to_f64(), Some(x as f64));
        }
    }
}
