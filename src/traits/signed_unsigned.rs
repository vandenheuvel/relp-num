use std::num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize};
use std::num::{NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize};
use crate::{Rational8, Rational16, Rational32, Rational64, Rational128, RationalSize};
use crate::{PositiveRational8, PositiveRational16, PositiveRational32, PositiveRational64, PositiveRational128, PositiveRationalSize};
use crate::{NonZeroRational8, NonZeroRational16, NonZeroRational32, NonZeroRational64, NonZeroRational128, NonZeroRationalSize};

use crate::{NonNegativeRational8, NonNegativeRational16, NonNegativeRational32, NonNegativeRational64, NonNegativeRational128, NonNegativeRationalSize};

trait Signed {
    type Unsigned: Unsigned;
}

trait Unsigned {
    type Signed: Signed;
}

macro_rules! pair {
    ($uty:ty, $ity:ty) => {
        impl Unsigned for $uty {
            type Signed = $ity;
        }

        impl Signed for $ity {
            type Unsigned = $uty;
        }
    }
}

pair!(u8, i8);
pair!(u16, i16);
pair!(u32, i32);
pair!(u64, i64);
pair!(u128, i128);
pair!(usize, isize);
pair!(NonZeroU8, NonZeroI8);
pair!(NonZeroU16, NonZeroI16);
pair!(NonZeroU32, NonZeroI32);
pair!(NonZeroU64, NonZeroI64);
pair!(NonZeroU128, NonZeroI128);
pair!(NonZeroUsize, NonZeroIsize);
pair!(Rational8, NonNegativeRational8);
pair!(Rational16, NonNegativeRational16);
pair!(Rational32, NonNegativeRational32);
pair!(Rational64, NonNegativeRational64);
pair!(Rational128, NonNegativeRational128);
pair!(RationalSize, NonNegativeRationalSize);
pair!(NonZeroRational8, PositiveRational8);
pair!(NonZeroRational16, PositiveRational16);
pair!(NonZeroRational32, PositiveRational32);
pair!(NonZeroRational64, PositiveRational64);
pair!(NonZeroRational128, PositiveRational128);
pair!(NonZeroRationalSize, PositiveRationalSize);
