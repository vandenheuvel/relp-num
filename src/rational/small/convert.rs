use crate::{Sign, Signed};
use crate::rational::small::{Ratio, Rational128, Rational16, Rational32, Rational64, Rational8, RationalSize};
use crate::rational::big::Big;
use num_traits::ToPrimitive;


macro_rules! signed_floor {
    ($value:expr, $target:ty) => {
        {
            let floor = $value.numerator / $value.denominator;
            floor.try_into().ok()
                .map(|value: $target| match $value.sign {
                    Sign::Zero | Sign::Positive => value,
                    // TODO: This is probably wrong
                    Sign::Negative => -value,
                })
        }
    }
}

macro_rules! unsigned_floor {
    ($value:expr) => {
        {
            match $value.sign {
                Sign::Zero | Sign::Positive => {
                    let floor = $value.numerator / $value.denominator;
                    floor.try_into().ok()
                }
                Sign::Negative => None,
            }
        }
    }
}

macro_rules! float {
    ($value:expr, $target:ty) => {
        {
            let ratio = $value.numerator as $target / $value.denominator as $target;
            let signed_ratio = match $value.sign {
                Sign::Zero | Sign::Positive => ratio,
                Sign::Negative => -ratio,
            };

            Some(signed_ratio)
        }
    }
}

macro_rules! conversion {
    ($name:ident, $ity:ty, $uty:ty, $gcd_name:ident, $simplify_name:ident) => {
        impl num_traits::FromPrimitive for $name {
            #[must_use]
            #[inline]
            fn from_i64(n: i64) -> Option<Self> {
                if n.unsigned_abs() <= <$uty>::MAX as u64 {
                    Some(Self {
                        sign: Signed::signum(&n),
                        numerator: n.unsigned_abs() as $uty,
                        denominator: 1,
                    })
                } else {
                    None
                }
            }

            #[must_use]
            #[inline]
            fn from_u64(n: u64) -> Option<Self> {
                if n <= <$uty>::MAX as u64 {
                    Some(Self {
                        sign: Signed::signum(&n),
                        numerator: n as $uty,
                        denominator: 1,
                    })
                } else {
                    None
                }
            }

            #[must_use]
            #[inline]
            fn from_f32(n: f32) -> Option<Self> {
                Big::<8>::from_f32(n).map(Self::from_big_if_it_fits).flatten()
            }

            #[must_use]
            #[inline]
            fn from_f64(n: f64) -> Option<Self> {
                Big::<16>::from_f64(n).map(Self::from_big_if_it_fits).flatten()
            }
        }

        impl ToPrimitive for $name {
            fn to_isize(&self) -> Option<isize> {
                signed_floor!(self, isize)
            }

            fn to_i8(&self) -> Option<i8> {
                signed_floor!(self, i8)
            }

            fn to_i16(&self) -> Option<i16> {
                signed_floor!(self, i16)
            }

            fn to_i32(&self) -> Option<i32> {
                signed_floor!(self, i32)
            }

            fn to_i64(&self) -> Option<i64> {
                signed_floor!(self, i64)
            }

            fn to_i128(&self) -> Option<i128> {
                signed_floor!(self, i128)
            }

            fn to_usize(&self) -> Option<usize> {
                unsigned_floor!(self)
            }

            fn to_u8(&self) -> Option<u8> {
                unsigned_floor!(self)
            }

            fn to_u16(&self) -> Option<u16> {
                unsigned_floor!(self)
            }

            fn to_u32(&self) -> Option<u32> {
                unsigned_floor!(self)
            }

            fn to_u64(&self) -> Option<u64> {
                unsigned_floor!(self)
            }

            fn to_u128(&self) -> Option<u128> {
                unsigned_floor!(self)
            }

            fn to_f32(&self) -> Option<f32> {
                float!(self, f32)
            }

            fn to_f64(&self) -> Option<f64> {
                float!(self, f64)
            }
        }
    }
}
conversion!(Rational8, i8, u8, gcd8, simplify8);
conversion!(Rational16, i16, u16, gcd16, simplify16);
conversion!(Rational32, i32, u32, gcd32, simplify32);
conversion!(Rational64, i64, u64, gcd64, simplify64);
conversion!(Rational128, i128, u128, gcd128, simplify128);
conversion!(RationalSize, isize, usize, gcd_usize, simplify_usize);
