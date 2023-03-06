use std::cmp::Ordering;
use std::ops::{Mul, MulAssign, Neg, Not};
use crate::{NonZero, NonZeroSign};
use crate::NonZeroSigned;
use paste::paste;
use std::num::{NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroIsize};
use std::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize};

macro_rules! non_zero_signed {
    [$($size:expr,)*] => {
        $(
            paste! {
                impl NonZeroSigned for [<NonZeroI $size>] {
                    fn signum(&self) -> NonZeroSign {
                        if self > 0 {
                            NonZeroSign::Positive
                        } else {
                            NonZeroSign::Negative
                        }
                    }
                }
            }
        )*
    }
}
non_zero_signed![8, 16, 32, 64, 128, "size",];

macro_rules! non_zero_unsigned {
    [$($size:expr,)*] => {
        $(
            paste! {
                impl NonZeroSigned for [<NonZeroU $size>] {
                    fn signum(&self) -> NonZeroSign {
                        NonZeroSign::Positive
                    }
                }
            }
        )*
    }
}
non_zero_unsigned![8, 16, 32, 64, 128, "size",];


impl NonZero for NonZeroSign {
    fn is_not_zero(&self) -> bool {
        true
    }
}

impl Not for NonZeroSign {
    type Output = Self;

    fn not(mut self) -> Self::Output {
        Negateable::negate(&mut self);
        self
    }
}

impl Neg for NonZeroSign {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        Negateable::negate(&mut self);
        self
    }
}

impl PartialOrd for NonZeroSign {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Self::Positive, Self::Positive) => None,
            (Self::Positive, Self::Negative) => Some(Ordering::Greater),
            (Self::Negative, Self::Positive) => Some(Ordering::Less),
            (Self::Negative, Self::Negative) => None,
        }
    }
}

impl Mul for NonZeroSign {
    type Output = Self;

    fn mul(mut self, rhs: Self) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl MulAssign for NonZeroSign {
    fn mul_assign(&mut self, rhs: Self) {
        *self = match (*self, rhs) {
            (Self::Positive, Self::Positive) => Self::Positive,
            (Self::Positive, Self::Negative) => Self::Negative,
            (Self::Negative, Self::Positive) => Self::Negative,
            (Self::Negative, Self::Negative) => Self::Positive,
        }
    }
}

#[cfg(test)]
mod test {
    use std::cmp::Ordering;

    use crate::{NonZeroSign, NonZeroSigned, Sign};
    use crate::{R64, RB};

    #[test]
    fn test_cmp() {
        assert!(NonZeroSign::Positive > NonZeroSign::Negative);
        assert_eq!(NonZeroSign::Positive.partial_cmp(&NonZeroSign::Positive), None);
        assert_eq!(NonZeroSign::Negative.partial_cmp(&NonZeroSign::Negative), None);
        assert_eq!(NonZeroSign::Negative.partial_cmp(&NonZeroSign::Positive), Some(Ordering::Less));
    }

    #[test]
    fn test_numbers() {
        use crate::Signed;
        assert_eq!(Signed::signum(&RB!(1)), Sign::Positive);
        assert_eq!(Signed::signum(&RB!(-1)), Sign::Negative);
        assert!(RB!(1).is_positive());
        assert!(RB!(-1).is_negative());
    }

    #[test]
    fn test_numbers_non_zero() {
        assert_eq!(1.non_zero_signum(), NonZeroSign::Positive);
        assert_eq!((-1).non_zero_signum(), NonZeroSign::Negative);

        assert_eq!(RB!(-1).non_zero_signum() * RB!(-1).non_zero_signum(), NonZeroSign::Positive);
        assert_eq!(RB!(1).non_zero_signum() * RB!(1).non_zero_signum(), NonZeroSign::Positive);

        assert_eq!(RB!(-1).non_zero_signum() * RB!(1).non_zero_signum(), NonZeroSign::Negative);

        assert_eq!(R64!(1).non_zero_signum(), NonZeroSign::Positive);
        assert_eq!(R64!(-1).non_zero_signum(), NonZeroSign::Negative);

        assert_eq!(R64!(-1).non_zero_signum() * R64!(-1).non_zero_signum(), NonZeroSign::Positive);
        assert_eq!(R64!(1).non_zero_signum() * R64!(1).non_zero_signum(), NonZeroSign::Positive);
        assert_eq!(R64!(-1).non_zero_signum() * R64!(1).non_zero_signum(), NonZeroSign::Negative);
    }

    #[test]
    #[should_panic]
    fn test_zero() {
        RB!(0).non_zero_signum();
    }
}
