use std::cmp::{min, Ordering};
use std::iter::repeat;
use std::mem;
use std::num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize};
use std::str::FromStr;

use num_traits;
use smallvec::{smallvec, SmallVec};

use crate::rational::big::Big;
use crate::rational::big::ops::{add_assign_single, BITS_PER_WORD, mul_assign_single};
use crate::rational::big::ops::building_blocks::shr_mut;
use crate::rational::big::ops::is_well_formed;
use crate::rational::big::ops::normalize::{gcd_scalar, simplify_fraction_without_info};
use crate::rational::Ratio;
use crate::rational::small::{simplify128, simplify16, simplify32, simplify64, simplify8};
use crate::sign::Sign;
use crate::sign::Signed;

impl<const S: usize> Big<S> {
    pub fn new(numerator: i64, denominator: u64) -> Self {
        debug_assert_ne!(denominator, 0);

        let mut numerator_abs = numerator.unsigned_abs() as usize;
        let mut denominator = denominator as usize;
        if numerator == 0 {
            <Self as num_traits::Zero>::zero()
        } else if numerator_abs == denominator {
            Self {
                sign: Signed::signum(&numerator),
                numerator: smallvec![1],
                denominator: smallvec![1],
            }
        } else {
            if numerator_abs != 1 && denominator != 1 {
                let gcd = gcd_scalar(numerator_abs, denominator);

                numerator_abs /= gcd;
                denominator /= gcd;
            }

            Self {
                sign: Signed::signum(&numerator),
                numerator: smallvec![numerator_abs],
                denominator: smallvec![denominator],
            }
        }
    }
}

macro_rules! from_integer_unsigned {
    ($ty:ty) => {
        impl<const S: usize> From<$ty> for Big<S> {
            fn from(value: $ty) -> Self {
                Self {
                    sign: Signed::signum(&value),
                    numerator: if value > 0 { smallvec![value as usize] } else { smallvec![] },
                    denominator: smallvec![1],
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

macro_rules! from_integer_signed {
    ($ty:ty) => {
        impl<const S: usize> From<$ty> for Big<S> {
            fn from(value: $ty) -> Self {
                Self {
                    sign: Signed::signum(&value),
                    numerator: if value != 0 { smallvec![value.unsigned_abs() as usize] } else { smallvec![] },
                    denominator: smallvec![1],
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

macro_rules! impl_from_iu {
    ($numerator:ty, $denominator:ty, $simplify:ident) => {
        impl<const S: usize> From<($numerator, $denominator)> for Big<S> {
            #[must_use]
            #[inline]
            fn from((numerator, denominator): ($numerator, $denominator)) -> Self {
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
                        numerator: smallvec![numerator as usize],
                        denominator: smallvec![denominator as usize],
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
                    numerator: smallvec![numerator.unsigned_abs() as usize],
                    denominator: smallvec![denominator.unsigned_abs() as usize],
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
        impl<const S: usize> From<Ratio<$numerator, $denominator>> for Big<S> {
            fn from(ratio: Ratio<$numerator, $denominator>) -> Self {
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
                        numerator: smallvec![ratio.numerator.unsigned_abs() as usize],
                        denominator: smallvec![ratio.denominator.get() as usize],
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

impl<const S: usize> num_traits::FromPrimitive for Big<S> {
    fn from_i64(n: i64) -> Option<Self> {
        Some(Self::new(n, 1))
    }

    fn from_u64(n: u64) -> Option<Self> {
        Some(Self {
            sign: Signed::signum(&n),
            numerator: if n > 0 { smallvec![n as usize] } else { smallvec![] },
            denominator: smallvec![1],
        })
    }

    fn from_f32(n: f32) -> Option<Self> {
        let n = n.to_bits();
        let sign     = (n & 0b10000000_00000000_00000000_00000000) >> (32 - 1);
        let exponent = (n & 0b01111111_10000000_00000000_00000000) >> (32 - 1 - 8);
        let fraction =  n & 0b00000000_01111111_11111111_11111111;

        match (exponent, fraction) {
            (0, 0) => Some(<Self as num_traits::Zero>::zero()),
            (0, _) => Some(Self::from_float(sign as u64, 1 - 127 - 23, fraction as u64)), // subnormals
            (ONES_32, 0) => None, // infinity
            (ONES_32, _) => None, // NaN
            _ => Some(Self::from_float(sign as u64, exponent as i32 - 127 - 23, (fraction + (1 << 23))  as u64)),
        }
    }

    fn from_f64(n: f64) -> Option<Self> {
        let n = n.to_bits();
        let sign     = (n & 0b10000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000) >> (64 - 1);
        let exponent = (n & 0b01111111_11110000_00000000_00000000_00000000_00000000_00000000_00000000) >> (64 - 1 - 11);
        let fraction =  n & 0b00000000_00001111_11111111_11111111_11111111_11111111_11111111_11111111;

        assert_eq!(mem::size_of::<usize>(), mem::size_of::<u64>());

        match (exponent, fraction) {
            (0, 0) => Some(<Self as num_traits::Zero>::zero()),
            (0, _) => Some(Self::from_float(sign, 1 - 1023 - 52, fraction)), // subnormals
            (ONES_64, 0) => None, // infinity
            (ONES_64, _) => None, // NaN
            _ => Some(Self::from_float(sign, exponent as i32 - 1023 - 52, fraction + (1 << 52))),
        }
    }
}

impl<const S: usize> Big<S> {
    fn from_float(sign: u64, power: i32, fraction: u64) -> Self {
        let (numerator, denominator) = match power.cmp(&0) {
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

                (smallvec![fraction as usize >> numerator_shift], denominator)
            }
            Ordering::Equal => {
                debug_assert_ne!(fraction, 0);
                (smallvec![fraction as usize], smallvec![1])
            },
            Ordering::Greater => {
                let shift = power.unsigned_abs();
                let words_shift = shift / BITS_PER_WORD;
                let bits_shift = shift % BITS_PER_WORD;

                let overflows = fraction.leading_zeros() < bits_shift;
                let size = 1 + words_shift + if overflows { 1 } else { 0 };
                let mut numerator = SmallVec::with_capacity(size as usize);

                numerator.extend(repeat(0).take(words_shift as usize));

                numerator.push((fraction as usize) << bits_shift);
                if overflows {
                    numerator.push(fraction as usize >> (BITS_PER_WORD - bits_shift));
                }

                (numerator, smallvec![1])
            }
        };

        Self {
            sign: if sign > 0 { Sign::Negative } else { Sign::Positive },
            numerator,
            denominator,
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
            numerator: SmallVec::with_capacity(0),
            denominator: smallvec![1],
        }
    }

    fn set_zero(&mut self) {
        self.sign = Sign::Zero;
        self.numerator.clear();
        debug_assert!(self.denominator.len() >= 1);
        self.denominator[0] = 1;
        self.denominator.truncate(1);
    }

    fn is_zero(&self) -> bool {
        self.sign == Sign::Zero
    }
}

impl<const S: usize> num_traits::One for Big<S> {
    fn one() -> Self {
        Self {
            sign: Sign::Positive,
            numerator: smallvec![1],
            denominator: smallvec![1],
        }
    }

    fn set_one(&mut self) {
        self.numerator.clear();
        self.numerator.push(1);
        debug_assert!(self.denominator.len() >= 1);
        self.denominator[0] = 1;
        self.denominator.truncate(1);
    }

    fn is_one(&self) -> bool {
        self.denominator[0] == 1 && self.numerator.len() == 1 && self.numerator[0] == 1 && self.denominator.len() == 1
    }
}

impl<const S: usize> Big<S> {
    pub fn new_signed<T: Into<Sign>>(sign: T, numerator: u64, denominator: u64) -> Self {
        debug_assert_ne!(denominator, 0);

        let sign = sign.into();

        match sign {
            Sign::Positive => debug_assert_ne!(numerator, 0),
            Sign::Zero => {
                debug_assert_eq!(numerator, 0);

                return Self {
                    sign: Sign::Zero,
                    numerator: smallvec![],
                    denominator: smallvec![1],
                };
            },
            Sign::Negative => {}
        }

        let (numerator, denominator) = simplify64(numerator, denominator);

        Self {
            sign,
            numerator: smallvec![numerator as usize],
            denominator: smallvec![denominator as usize],
        }
    }
}

impl<const S: usize> FromStr for Big<S> {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let radix = 10;

        if s.contains(".") || s.contains(",") {
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

                match s.find("/") {
                    None => {
                        let numerator = int_from_str(s, radix)?;

                        if numerator.is_empty() {
                            Ok(<Self as num_traits::Zero>::zero())
                        } else {
                            Ok(Big {
                                sign,
                                numerator,
                                denominator: smallvec![1],
                            })
                        }
                    }
                    Some(index) => {
                        // The number is a ratio between two others
                        let (numerator_text, denominator_text) = (&s[..index], &s[(index + 1)..]);
                        let mut numerator = int_from_str(numerator_text, radix)?;
                        let mut denominator = int_from_str(denominator_text, radix)?;
                        if denominator.is_empty() {
                            return Err("Zero division");
                        }

                        if numerator.is_empty() {
                            Ok(<Self as num_traits::Zero>::zero())
                        } else {
                            simplify_fraction_without_info(&mut numerator, &mut denominator);

                            Ok(Big {
                                sign,
                                numerator,
                                denominator,
                            })
                        }
                    }
                }
            }
        }
    }
}

pub fn int_from_str<const S: usize>(s: &str, radix: u32) -> Result<SmallVec<[usize; S]>, &'static str> {
    debug_assert!(radix <= 36);

    match s.len() {
        0 => Err("Empty string"),
        _ => {
            let mut char_iterator = s.chars().skip_while(|&c| c == '0');
            match char_iterator.next() {
                None => Ok(smallvec![]),
                Some(value) => {
                    match value.to_digit(radix) {
                        None => Err("Character is not a digit"),
                        Some(value) => {
                            let mut total = smallvec![value as usize];

                            for character in char_iterator {
                                match character.to_digit(radix) {
                                    None => return Err("Character is not a digit"),
                                    Some(value) => {
                                        mul_assign_single(&mut total, radix as usize);
                                        add_assign_single(&mut total, value as usize);
                                    }
                                }
                            }

                            Ok(total)
                        }
                    }
                }
            }
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

pub fn to_str<const S: usize>(value: &SmallVec<[usize; S]>, radix: u32) -> String {
    debug_assert!(is_well_formed(value));
    debug_assert!(radix > 1 && radix <= 36);

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
            let mut value: SmallVec<[usize; S]> = value.iter()
                .skip(leading_zero_words)
                .map(|word| word.reverse_bits())
                .rev()
                .collect();
            shr_mut(&mut value, 0, leading_zero_bits);

            let bit_count = value.len() as u32 * BITS_PER_WORD - leading_zero_bits;
            debug_assert_eq!(value[0] % 2, 1);
            for bit_index in 0..bit_count {
                update_digits(&mut digits, value[0] % 2 == 1, radix);
                shr_mut(&mut value, 0, 1);

                if value.is_empty() {
                    // Had this many bits remaining
                    for _ in (bit_index + 1)..(leading_zero_words as u32 * BITS_PER_WORD + bit_count) {
                        update_digits(&mut digits, false, radix);
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

fn update_digits(digits: &mut Vec<u32>, mut carry: bool, radix: u32) {
    for digit in digits.iter_mut() {
        *digit *= 2; // binary, each bit multiplies by 2
        if carry {
            *digit += 1;
            carry = false;
        }
        if *digit >= radix {
            *digit %= radix;
            carry = true;
        }
    }
    if carry {
        digits.push(1);
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use num_traits::One;
    use smallvec::{smallvec, SmallVec};

    use crate::{Abs, Rational64, RationalBig, Sign};
    use crate::rational::big::{Big, Big8};
    use crate::rational::big::creation::{int_from_str, to_str};
    use crate::rational::big::ops::BITS_PER_WORD;
    use crate::rational::big::ops::normalize::simplify_fraction_without_info;
    use crate::RB;

    #[test]
    fn from() {
        let x = Rational64::new(4, 3);
        let y = Big8::from(x);
        let z = Big8::new(4, 3);
        assert_eq!(y, z);

        let x = <Big8 as num_traits::FromPrimitive>::from_f32(0_f32).unwrap();
        assert_eq!(x, Big8::new(0, 1));

        let x = <Big8 as num_traits::FromPrimitive>::from_f32(1_f32).unwrap();
        assert_eq!(x, Big8::new(1, 1));

        let x = <Big8 as num_traits::FromPrimitive>::from_f32(0.5).unwrap();
        assert_eq!(x, Big8::new(1, 2));

        let x = <Big8 as num_traits::FromPrimitive>::from_f32(2_f32).unwrap();
        assert_eq!(x, Big8::new(2, 1));

        let x = <Big8 as num_traits::FromPrimitive>::from_f32(1.5_f32).unwrap();
        assert_eq!(x, Big8::new(3, 2));
        let x = <Big8 as num_traits::FromPrimitive>::from_f64(0_f64).unwrap();
        assert_eq!(x, Big8::new(0, 1));

        let x = <Big8 as num_traits::FromPrimitive>::from_f64(1_f64).unwrap();
        assert_eq!(x, Big8::new(1, 1));

        let x = <Big8 as num_traits::FromPrimitive>::from_f64(0.5).unwrap();
        assert_eq!(x, Big8::new(1, 2));

        let x = <Big8 as num_traits::FromPrimitive>::from_f64(2_f64).unwrap();
        assert_eq!(x, Big8::new(2, 1));

        let x = <Big8 as num_traits::FromPrimitive>::from_f64(1.5_f64).unwrap();
        assert_eq!(x, Big8::new(3, 2));

        let x = <Big8 as num_traits::FromPrimitive>::from_f64(f64::MIN_POSITIVE).unwrap();
        let (words, bits) = (1022 / BITS_PER_WORD, 1022 % BITS_PER_WORD);
        let mut denominator = smallvec![0; words as usize];
        denominator.push(1 << bits);
        let expected = Big8 {
            sign: Sign::Positive,
            numerator: smallvec![1],
            denominator,
        };
        assert_eq!(x, expected);

        let x = <Big8 as num_traits::FromPrimitive>::from_f64(f64::MAX).unwrap();
        let total_shift = (1 << (11 - 1)) - 1 - 52;
        let (words, bits) = (total_shift / BITS_PER_WORD, total_shift % BITS_PER_WORD);
        let mut numerator= smallvec![0; words as usize];
        numerator.push(((1 << (52 + 1)) - 1) << bits); // Doesn't overflow, fits exactly in this last word
        let expected = Big8 {
            sign: Sign::Positive,
            numerator,
            denominator: smallvec![1],
        };
        assert_eq!(x, expected);

        let y = <Big8 as num_traits::FromPrimitive>::from_f64(4f64 / 3f64).unwrap();
        let z = Big8::new(4, 3);
        assert!((y - z).abs() < Big8::new(1, 2 << 10));

        // 2 ** 543
        assert_eq!(
            RB!(28793048285076456849987446449190283896766061557132266451844835664715760516297522370041860391064901485759493828054533728788532902755163518009654497157537048672862208_f64),
            RationalBig {
                sign: Sign::Positive,
                numerator: smallvec![0, 0, 0, 0, 0, 0, 0, 0, 1 << 31],
                denominator: smallvec![1],
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
        assert_eq!(Big::new_signed(Sign::Positive, 1, 2), RB!(1, 2));
        assert_eq!(Big::new_signed(Sign::Zero, 0, 1), RB!(0));
        assert_eq!(Big::new_signed(Sign::Negative, 1, 3), RB!(-1, 3));
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
                numerator: smallvec![(1 << 63) + (1 << 0), 1],
                denominator: smallvec![1],
            }),
        );
        assert_eq!(
            Big8::from_str("27670116110564327425/2"),
            Ok(Big {
                sign: Sign::Positive,
                numerator: smallvec![(1 << 63) + (1 << 0), 1],
                denominator: smallvec![2],
            }),
        );
        assert_eq!(
            Big8::from_str("27670116110564327425/27670116110564327425"),
            Ok(Big {
                sign: Sign::Positive,
                numerator: smallvec![1],
                denominator: smallvec![1],
            }),
        );
        assert_eq!(
            Big8::from_str("18446744073709551616/2"),
            Ok(Big {
                sign: Sign::Positive,
                numerator: smallvec![1 << 63],
                denominator: smallvec![1],
            }),
        );
        assert_eq!(
            Big8::from_str("-36893488147419103232"),
            Ok(Big {
                sign: Sign::Negative,
                numerator: smallvec![0, 2],
                denominator: smallvec![1],
            }),
        );

        assert_eq!(int_from_str::<8>("36893488147419103232", 10), Ok(smallvec![0, 1 << 1]));
        assert_eq!(int_from_str::<8>("18889465931478580854784", 10), Ok(smallvec![0, 1 << 10]));
        assert_eq!(int_from_str::<8>("19342813113834066795298816", 10), Ok(smallvec![0, 1 << 20]));
        assert_eq!(int_from_str::<8>("1208925819614629174706176", 10), Ok(smallvec![0, 1 << (80 - 64)]));

        assert_eq!(
            Big8::from_str("-1208925819614629174706176/10301051460877537453973547267843"),
            Ok(Big {
                sign: Sign::Negative,
                numerator: smallvec![0, 1 << (80 - 64)],
                denominator: smallvec![0x6b9676a56c7c3703, 0x82047e0eae],
            }),
        );

        type SV = SmallVec<[usize; 8]>;

        let mut x = int_from_str::<8>("676230147000402641135208532975102322580080121519024130", 10).unwrap();
        let expected: SV = smallvec![7877410236203542530, 0xe30d7c46c1f853f7, 1987261794136745];
        assert_eq!(x, expected);
        let mut y = int_from_str::<8>("68468465468464168545346854646", 10).unwrap();
        let expected: SV = smallvec![7062882560094707446, 3711682950];
        assert_eq!(y, expected);
        simplify_fraction_without_info(&mut x, &mut y);
        let expected: SV = smallvec![13162077154956547073, 17403806869180131835, 993630897068372];
        assert_eq!(x, expected);
        let expected: SV = smallvec![3531441280047353723, 1855841475];
        assert_eq!(y, expected);

        let z = Big8::from_str("676230147000402641135208532975102322580080121519024130/68468465468464168545346854646");
        assert_eq!(z, Ok(Big {
            sign: Sign::Positive,
            numerator: x,
            denominator: y,
        }));

        assert_eq!(
            Big8::from_str("1190934288550035983230200000000/1219533185348999122218328290051").unwrap(),
            Big8::from_str("23800000000/24371529219").unwrap(),
        );
    }

    #[test]
    fn test_to_str() {
        type SV = SmallVec<[usize; 8]>;

        let x: SV = smallvec![];
        assert_eq!(to_str(&x, 10), "0");
        let x: SV = smallvec![1];
        assert_eq!(to_str(&x, 10), "1");
        let x: SV = smallvec![2];
        assert_eq!(to_str(&x, 10), "2");
        let x: SV = smallvec![3];
        assert_eq!(to_str(&x, 10), "3");
        let x: SV = smallvec![10];
        assert_eq!(to_str(&x, 10), "10");
        let x: SV = smallvec![11];
        assert_eq!(to_str(&x, 10), "11");
        let x: SV = smallvec![101];
        assert_eq!(to_str(&x, 10), "101");
        let x: SV = smallvec![123];
        assert_eq!(to_str(&x, 10), "123");
        let x: SV = smallvec![usize::MAX];
        assert_eq!(to_str(&x, 10), "18446744073709551615");
        let x: SV = smallvec![0, 1];
        assert_eq!(to_str(&x, 10), "18446744073709551616");
        let x: SV = smallvec![1, 1];
        assert_eq!(to_str(&x, 10), "18446744073709551617");

        assert_eq!(to_str(&int_from_str::<1>("123", 10).unwrap(), 10), "123");

        for i in 1..100 {
            let expected: SV = smallvec![i];
            assert_eq!(int_from_str::<8>(&to_str(&expected, 10), 10), Ok(expected));
        }

        let x: SV = smallvec![13284626917187606528, 14353657804625640860, 11366567065457835548, 501247837944];
        assert_eq!(to_str(&x, 10), "3146383673420971972032023490593198871229613539715389096610302560000000");
        let y: SV = smallvec![10945929334190035713, 13004504757950498814, 9];
        assert_eq!(to_str(&y, 10), "3302432073363697202172148890923583722241");
    }
}
