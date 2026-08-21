//! # Signs of nonzero values
//!
//! Usual sign implementations have a sign for zero, the implementation in this module does not.
use std::cmp::Ordering;
use std::ops::{Mul, MulAssign, Neg, Not};

use crate::{Negateable, Signed};
use crate::non_zero::NonZero;
use crate::sign::Sign;

/// A signed number that can have a nonzero value.
pub trait NonZeroSigned: NonZero + Signed {
    /// Whether the value is positive or negative.
    fn non_zero_signum(&self) -> NonZeroSign;
    /// Whether `x > 0`.
    #[inline]
    fn non_zero_is_positive(&self) -> bool {
        self.non_zero_signum() == NonZeroSign::Positive
    }
    /// Whether `x < 0`.
    #[inline]
    fn non_zero_is_negative(&self) -> bool {
        self.non_zero_signum() == NonZeroSign::Negative
    }
}

/// Sign of a nonzero value.
///
/// Existing `Sign` traits, such in `num`, typically have a third value for the sign of 0. Working
/// with that trait creates many branches or match cases that should never be possible.
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum NonZeroSign {
    /// `x > 0`
    Positive = 1,
    /// `x < 0`
    Negative = -1,
}

/// Derive the non zero sign from the general sign, panicking on zero.
///
/// Used for the number types that can represent zero, where the guarantee is a contract the
/// caller has to keep rather than something the type enforces. Types that cannot be zero get a
/// total implementation instead, and never reach a panic.
macro_rules! non_zero_signed_by_panic {
    ($($t:ty),+ $(,)?) => {$(
        impl NonZeroSigned for $t {
            #[inline]
            #[track_caller]
            fn non_zero_signum(&self) -> NonZeroSign {
                match Signed::signum(self) {
                    Sign::Positive => NonZeroSign::Positive,
                    Sign::Negative => NonZeroSign::Negative,
                    Sign::Zero => panic!(
                        "attempt to take the non zero sign of a zero value of type {}",
                        std::any::type_name::<$t>(),
                    ),
                }
            }
        }
    )+}
}

non_zero_signed_by_panic!(i8, i16, i32, i64, i128, isize);
non_zero_signed_by_panic!(u8, u16, u32, u64, u128, usize);
non_zero_signed_by_panic!(Sign);

/// Derive the non zero sign from a type that cannot represent zero.
macro_rules! non_zero_signed_total {
    ($t:ty, $sign:expr) => {
        /// The type cannot represent zero, so there is no failure case.
        impl NonZeroSigned for $t {
            #[inline]
            fn non_zero_signum(&self) -> NonZeroSign {
                $sign(self)
            }
        }
    }
}

non_zero_signed_total!(crate::fixed::One, |_: &crate::fixed::One| NonZeroSign::Positive);
non_zero_signed_total!(crate::fixed::SignedOne, |value: &crate::fixed::SignedOne| match value {
    crate::fixed::SignedOne::PlusOne => NonZeroSign::Positive,
    crate::fixed::SignedOne::MinusOne => NonZeroSign::Negative,
});

impl Signed for NonZeroSign {
    fn signum(&self) -> Sign {
        match self {
            NonZeroSign::Positive => Sign::Positive,
            NonZeroSign::Negative => Sign::Negative,
        }
    }
}

impl NonZero for NonZeroSign {
    fn is_not_zero(&self) -> bool {
        true
    }
}

impl Negateable for NonZeroSign {
    fn negate(&mut self) {
        *self = match self {
            NonZeroSign::Positive => NonZeroSign::Negative,
            NonZeroSign::Negative => NonZeroSign::Positive,
        }
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

impl From<Sign> for NonZeroSign {
    fn from(other: Sign) -> Self {
        debug_assert!(other.is_not_zero());

        match other {
            Sign::Positive => NonZeroSign::Positive,
            Sign::Zero => panic!("attempt to convert a zero sign into a non zero sign"),
            Sign::Negative => NonZeroSign::Negative,
        }
    }
}

/// Signs are totally ordered as `Negative < Positive`, matching the discriminants.
impl Ord for NonZeroSign {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        (*self as i8).cmp(&(*other as i8))
    }
}

impl PartialOrd for NonZeroSign {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
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
            (NonZeroSign::Positive, NonZeroSign::Positive) => NonZeroSign::Positive,
            (NonZeroSign::Positive, NonZeroSign::Negative) => NonZeroSign::Negative,
            (NonZeroSign::Negative, NonZeroSign::Positive) => NonZeroSign::Negative,
            (NonZeroSign::Negative, NonZeroSign::Negative) => NonZeroSign::Positive,
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
        assert_eq!(NonZeroSign::Positive.partial_cmp(&NonZeroSign::Positive), Some(Ordering::Equal));
        assert_eq!(NonZeroSign::Negative.partial_cmp(&NonZeroSign::Negative), Some(Ordering::Equal));
        assert_eq!(NonZeroSign::Negative.partial_cmp(&NonZeroSign::Positive), Some(Ordering::Less));
    }

    /// `a == b` must imply `partial_cmp(a, b) == Some(Equal)`.
    #[test]
    fn test_cmp_contract() {
        for a in [NonZeroSign::Negative, NonZeroSign::Positive] {
            assert_eq!(a.partial_cmp(&a), Some(Ordering::Equal));
            assert!(a <= a);
            assert!(a >= a);
            for b in [NonZeroSign::Negative, NonZeroSign::Positive] {
                assert_eq!(a == b, a.partial_cmp(&b) == Some(Ordering::Equal));
                assert_eq!(a.partial_cmp(&b), Some(a.cmp(&b)));
                assert_eq!(a.cmp(&b), b.cmp(&a).reverse());
            }
        }
        assert!(NonZeroSign::Negative < NonZeroSign::Positive);
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
