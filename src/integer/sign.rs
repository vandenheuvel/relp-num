//! # NonZero signs of integers
use std::cmp::Ordering;
use std::num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8};
use std::num::{NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8};

use crate::non_zero::NonZeroSign;
use crate::non_zero::NonZeroSigned;

macro_rules! define_u {
    ($ty:ty) => {
        impl NonZeroSigned for $ty {
            #[must_use]
            #[inline]
            fn signum(&self) -> NonZeroSign {
                if *self > 0 {
                    NonZeroSign::Positive
                } else {
                    panic!("attempt to take a non zero sign of a zero value")
                }
            }
        }
    }
}

define_u!(u8);
define_u!(u16);
define_u!(u32);
define_u!(u64);
define_u!(u128);

macro_rules! define {
    ($ty:ty) => {
        impl NonZeroSigned for $ty {
            #[must_use]
            #[inline]
            fn signum(&self) -> NonZeroSign {
                match self.cmp(&0) {
                    Ordering::Less => NonZeroSign::Negative,
                    Ordering::Equal => panic!("attempt to take a non zero sign of a zero value"),
                    Ordering::Greater => NonZeroSign::Positive,
                }
            }
        }
    }
}

define!(i8);
define!(i16);
define!(i32);
define!(i64);
define!(i128);

macro_rules! define_non_zero_u {
    ($ty:ty) => {
        impl NonZeroSigned for $ty {
            #[must_use]
            #[inline]
            fn signum(&self) -> NonZeroSign {
                NonZeroSign::Positive
            }
        }
    }
}

define_non_zero_u!(NonZeroU8);
define_non_zero_u!(NonZeroU16);
define_non_zero_u!(NonZeroU32);
define_non_zero_u!(NonZeroU64);
define_non_zero_u!(NonZeroU128);

macro_rules! define_non_zero {
    ($ty:ty) => {
        impl NonZeroSigned for $ty {
            #[must_use]
            #[inline]
            fn signum(&self) -> NonZeroSign {
                if self.get() > 0 {
                    NonZeroSign::Positive
                } else {
                    NonZeroSign::Negative
                }
            }
        }
    }
}

define_non_zero!(NonZeroI8);
define_non_zero!(NonZeroI16);
define_non_zero!(NonZeroI32);
define_non_zero!(NonZeroI64);
define_non_zero!(NonZeroI128);

#[cfg(test)]
mod test {
    use std::num::{NonZeroI8, NonZeroU8};

    use crate::{NonZeroSign, NonZeroSigned};

    #[test]
    fn test_zero_sign() {
        assert_eq!(NonZeroSigned::signum(&1_u32), NonZeroSign::Positive);
        assert_eq!(NonZeroSigned::signum(&-1_i32), NonZeroSign::Negative);

        assert_eq!(NonZeroSigned::signum(&NonZeroU8::new(1).unwrap()), NonZeroSign::Positive);
        assert_eq!(NonZeroSigned::signum(&NonZeroI8::new(1).unwrap()), NonZeroSign::Positive);
        assert_eq!(NonZeroSigned::signum(&NonZeroI8::new(-1).unwrap()), NonZeroSign::Negative);
    }

    #[test]
    #[should_panic]
    fn test_non_zero_on_zero() {
        NonZeroSigned::signum(&0_u32);
    }

    #[test]
    #[should_panic]
    fn test_non_zero_on_zero_signed() {
        NonZeroSigned::signum(&0_i8);
    }
}
