#![allow(unused_unsafe)]

use std::convert::TryFrom;
use std::fmt;
use std::num::NonZeroUsize;
use std::str::FromStr;

use num_traits::{One, Zero};
use smallvec::SmallVec;
use smallvec::smallvec;

use crate::integer::big::{BITS_PER_WORD, NonZeroUbig, Ubig};
use crate::integer::big::ops::building_blocks::is_well_formed;
use crate::integer::big::ops::non_zero::{add_assign_single_non_zero, mul_assign_single_non_zero, shr_mut};

impl<const S: usize> Ubig<S> {
    #[must_use]
    #[inline]
    pub fn new(value: usize) -> Self {
        Ubig(if value > 0 { smallvec![value] } else { smallvec![] })
    }
    #[must_use]
    #[inline]
    pub fn from_inner(values: SmallVec<[usize; S]>) -> Option<Self> {
        if is_well_formed(&values) {
            Some(Self(values))
        } else {
            None
        }
    }
    #[must_use]
    #[inline]
    pub unsafe fn from_inner_unchecked(values: SmallVec<[usize; S]>) -> Self {
        debug_assert!(is_well_formed(&values));

        Self(values)
    }
}

impl<const S: usize> NonZeroUbig<S> {
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
    pub unsafe fn new_unchecked(value: usize) -> Self {
        NonZeroUbig(smallvec![value])
    }
    #[must_use]
    #[inline]
    pub fn from_inner(values: SmallVec<[usize; S]>) -> Option<Self> {
        if is_well_formed(&values) && !values.is_empty() {
            Some(Self(values))
        } else {
            None
        }
    }
    #[must_use]
    #[inline]
    pub unsafe fn from_inner_unchecked(values: SmallVec<[usize; S]>) -> Self {
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
        f.write_str(&to_str_radix::<10>(&self))
    }
}

impl<const S: usize> fmt::Display for NonZeroUbig<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // TODO(PERFORMANCE): Skip zero case
        f.write_str(&to_str_radix::<10>(&self))
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
