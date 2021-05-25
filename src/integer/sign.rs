//! # NonZero signs of integers
use std::cmp::Ordering;

use crate::non_zero::NonZeroSign;
use crate::non_zero::NonZeroSigned;

macro_rules! define {
    ($ty:ty) => {
        impl NonZeroSigned for $ty {
            #[must_use]
            #[inline]
            fn signum(&self) -> NonZeroSign {
                match self.cmp(&0) {
                    Ordering::Less => NonZeroSign::Negative,
                    Ordering::Equal => panic!(),
                    Ordering::Greater => NonZeroSign::Positive,
                }
            }
        }
    }
}

define!(u8);
define!(u16);
define!(u32);
define!(u64);
define!(u128);
define!(i8);
define!(i16);
define!(i32);
define!(i64);
define!(i128);
