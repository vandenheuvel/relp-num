//! # NonZero signs of integers
use std::cmp::Ordering;
use std::num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize};
use std::num::{NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize};

use crate::Sign;
use crate::Signed;

macro_rules! unsigned {
    ($ty:ty) => {
        impl Signed for $ty {
            #[must_use]
            #[inline]
            fn signum(&self) -> Sign {
                if *self == 0 {
                    Sign::Zero
                } else {
                    Sign::Positive
                }
            }
        }
    }
}

unsigned!(u8);
unsigned!(u16);
unsigned!(u32);
unsigned!(u64);
unsigned!(u128);
unsigned!(usize);

macro_rules! signed {
    ($ty:ty) => {
        impl Signed for $ty {
            #[must_use]
            #[inline]
            fn signum(&self) -> Sign {
                match self.cmp(&0) {
                    Ordering::Less => Sign::Negative,
                    Ordering::Equal => Sign::Zero,
                    Ordering::Greater => Sign::Positive,
                }
            }
        }
    }
}

signed!(i8);
signed!(i16);
signed!(i32);
signed!(i64);
signed!(i128);
signed!(isize);

macro_rules! non_zero_unsigned {
    ($ty:ty) => {
        impl Signed for $ty {
            #[must_use]
            #[inline]
            fn signum(&self) -> Sign {
                Sign::Positive
            }
        }
    }
}

non_zero_unsigned!(NonZeroU8);
non_zero_unsigned!(NonZeroU16);
non_zero_unsigned!(NonZeroU32);
non_zero_unsigned!(NonZeroU64);
non_zero_unsigned!(NonZeroU128);
non_zero_unsigned!(NonZeroUsize);

macro_rules! non_zero_signed {
    ($ty:ty) => {
        impl Signed for $ty {
            #[must_use]
            #[inline]
            fn signum(&self) -> Sign {
                if self.get() > 0 {
                    Sign::Positive
                } else {
                    Sign::Negative
                }
            }
        }
    }
}

non_zero_signed!(NonZeroI8);
non_zero_signed!(NonZeroI16);
non_zero_signed!(NonZeroI32);
non_zero_signed!(NonZeroI64);
non_zero_signed!(NonZeroI128);
non_zero_signed!(NonZeroIsize);

#[cfg(test)]
mod test {
    use std::num::{NonZeroI8, NonZeroU8};

    use crate::{NonZeroSign, NonZeroSigned};

    #[test]
    fn test_zero_sign() {
        assert_eq!(NonZeroU8::new(1).unwrap().signum(), NonZeroSign::Positive);
        assert_eq!(NonZeroI8::new(1).unwrap().signum(), NonZeroSign::Positive);
        assert_eq!(NonZeroI8::new(-1).unwrap().signum(), NonZeroSign::Negative);
    }
}
