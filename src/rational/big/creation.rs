use std::cmp::{min, Ordering};
use std::iter::repeat;
use std::mem;
use std::num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize};

use num_traits;
use smallvec::{smallvec, SmallVec};

use crate::rational::big::Big;
use crate::rational::big::ops::BITS_PER_WORD;
use crate::rational::big::ops::normalize::gcd_scalar;
use crate::rational::Ratio;
use crate::rational::small::simplify64;
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

macro_rules! impl_from {
    ($numerator:ty, $denominator:ty) => {
        impl<const S: usize> From<($numerator, $denominator)> for Big<S> {
            fn from((numerator, denominator): ($numerator, $denominator)) -> Self {
                if mem::size_of::<$numerator>() > mem::size_of::<usize>() {
                    debug_assert!(numerator.abs() <= usize::MAX as $numerator);
                }
                if mem::size_of::<$denominator>() > mem::size_of::<usize>() {
                    debug_assert!(denominator <= usize::MAX as $denominator);
                }

                Self {
                    sign: <$numerator as Signed>::signum(&numerator),
                    numerator: smallvec![numerator.unsigned_abs() as usize],
                    denominator: smallvec![denominator as usize],
                }
            }
        }
    }
}

impl_from!(i8, u8);
impl_from!(i16, u16);
impl_from!(i32, u32);
impl_from!(i64, u64);
impl_from!(i128, u128);
impl_from!(isize, usize);

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

                Self {
                    sign: <$numerator as Signed>::signum(&ratio.numerator),
                    numerator: smallvec![ratio.numerator.abs() as usize],
                    denominator: smallvec![ratio.denominator.get() as usize],
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

const ONES: usize = (1 << 11) - 1;

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

    fn from_f64(n: f64) -> Option<Self> {
        let n = n.to_bits() as usize;
        let sign     = (n & 0b10000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000) >> (64 - 1);
        let exponent = (n & 0b01111111_11110000_00000000_00000000_00000000_00000000_00000000_00000000) >> (64 - 1 - 11);
        let fraction =  n & 0b00000000_00001111_11111111_11111111_11111111_11111111_11111111_11111111;

        match (exponent, fraction) {
            (0, 0) => Some(<Self as num_traits::Zero>::zero()),
            (0, _) => Some(Self::from_float(sign, 1 - 1023 - 52, fraction)), // subnormals
            (ONES, 0) => None, // infinity
            (ONES, _) => None, // NaN
            _ => Some(Self::from_float(sign, exponent as isize - 1023 - 52, fraction + (1 << 52))),
        }
    }
}

impl<const S: usize> Big<S> {
    fn from_float(sign: usize, power: isize, fraction: usize) -> Self {
        let (numerator, denominator) = match power.cmp(&0) {
            Ordering::Less => {
                let numerator_zeros = fraction.trailing_zeros() as usize;
                let shift = power.unsigned_abs() as usize;

                let numerator_shift = min(numerator_zeros, shift);
                let denominator_shift = shift - numerator_shift;

                let words_shift = denominator_shift / BITS_PER_WORD;
                let bits_shift = denominator_shift % BITS_PER_WORD;
                let size = words_shift + 1;
                let mut denominator = SmallVec::with_capacity(size);

                denominator.extend(repeat(0).take(words_shift));
                denominator.push(1 << bits_shift);

                (smallvec![fraction >> numerator_shift], denominator)
            }
            Ordering::Equal => (smallvec![fraction], smallvec![1]),
            Ordering::Greater => {
                let shift = power.unsigned_abs() as usize;
                let words_shift = shift / BITS_PER_WORD;
                let bits_shift = shift % BITS_PER_WORD;

                let overflows = (fraction.leading_zeros() as usize) < bits_shift;
                let size = 1 + words_shift + if overflows { 1 } else { 0 };
                let mut numerator = SmallVec::with_capacity(size);

                numerator.extend(repeat(0).take(words_shift));

                let fraction = fraction;
                numerator.push(fraction << bits_shift);
                if overflows {
                    numerator.push(fraction >> (BITS_PER_WORD - bits_shift));
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
        // Numerator always has at least one element
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
        // Numerator always has at least one element
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

#[cfg(test)]
mod test {
    use crate::{Rational64, Sign, Abs, RationalBig};
    use crate::rational::big::{Big8, Big};
    use num_traits::{One};
    use crate::rational::big::ops::BITS_PER_WORD;
    use smallvec::smallvec;
    use crate::RB;

    #[test]
    fn from() {
        let x = Rational64::new(4, 3);
        let y = Big8::from(x);
        let z = Big8::new(4, 3);
        assert_eq!(y, z);

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
        let mut denominator = smallvec![0; words];
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
        let mut numerator= smallvec![0; words];
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
}
