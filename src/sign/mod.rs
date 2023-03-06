//! # Signs
//!
//! Existing sign traits often use the values `1`, `0` and `-1` to represent the sign of a number.
//! This is limiting because some types should never be zero is certain code sections, and having
//! to match on the `0` value is then unidiomatic. Moreover, such a sign is bulky for ratios, which
//! have a separate sign field anyway.


/// Sign with a zero variant.
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum Sign {
    /// x > 0
    Positive = 1,
    /// x == 0
    Zero = 0,
    /// x < 0
    Negative = -1,
}
/// # Signed numbers
///
/// A number that is positive, negative or zero.
pub trait Signed {
    /// Returns the sign of the number.
    fn signum(&self) -> Sign;
    /// Whether the number is (strictly) greater than zero.
    #[inline]
    fn is_positive(&self) -> bool {
        self.signum() == Sign::Positive
    }
    /// Whether the number is (strictly) smaller than zero.
    #[inline]
    fn is_negative(&self) -> bool {
        self.signum() == Sign::Negative
    }
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum NonZeroSign {
    Positive = 1,
    Negative = -1,
}
impl From<NonZeroSign> for Sign {
    default fn from(value: NonZeroSign) -> Self {
        match value {
            NonZeroSign::Positive => Sign::Positive,
            NonZeroSign::Negative => Sign::Negative,
        }
    }
}
pub trait NonZeroSigned {
    /// Returns the sign of the number.
    fn signum(&self) -> NonZeroSign;
    /// Whether the number is (strictly) greater than zero.
    #[inline]
    fn is_positive(&self) -> bool {
        self.signum() == NonZeroSign::Positive
    }
    /// Whether the number is (strictly) smaller than zero.
    #[inline]
    fn is_negative(&self) -> bool {
        self.signum() == NonZeroSign::Negative
    }
}
// TODO: Once specialization can handle intersections, enable the below:
// impl<T: NonZeroSigned> Signed for T {
//     default fn signum(&self) -> Sign {
//         NonZeroSigned::signum(&self).into()
//     }
// }

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum NonNegativeSign {
    Positive = 1,
    Zero = 0,
}
impl From<NonNegativeSign> for Sign {
    default fn from(value: NonNegativeSign) -> Self {
        match value {
            NonNegativeSign::Zero => Sign::Zero,
            NonNegativeSign::Positive => Sign::Positive,
        }
    }
}
pub trait NonNegativelySigned {
    /// Returns the sign of the number.
    fn signum(&self) -> NonNegativeSign;
    /// Whether the number is (strictly) greater than zero.
    #[inline]
    fn is_positive(&self) -> bool {
        self.signum() == NonNegativeSign::Positive
    }
    /// Whether the number is (strictly) smaller than zero.
    #[inline]
    fn is_negative(&self) -> bool {
        false
    }
}
// TODO: Once specialization can handle intersections, enable the below:
// impl<T: NonNegativelySigned> Signed for T {
//     default fn signum(&self) -> Sign {
//         NonNegativelySigned::signum(&self).into()
//     }
// }

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum PositiveSign {
    Positive,
}
impl From<PositiveSign> for NonNegativeSign {
    fn from(_value: PositiveSign) -> Self {
        NonNegativeSign::Positive
    }
}
impl From<PositiveSign> for NonZeroSign {
    fn from(_value: PositiveSign) -> Self {
        NonZeroSign::Positive
    }
}
impl From<PositiveSign> for Sign {
    fn from(_value: PositiveSign) -> Self {
        Sign::Positive
    }
}
pub trait PositivelySigned {
    /// Returns the sign of the number.
    fn signum(&self) -> PositiveSign;
    /// Whether the number is (strictly) greater than zero.
    #[inline]
    fn is_positive(&self) -> bool {
        true
    }
    /// Whether the number is (strictly) smaller than zero.
    #[inline]
    fn is_negative(&self) -> bool {
        false
    }
}
// TODO: Once specialization can handle intersections, enable the below:
// impl<T: PositivelySigned> NonNegativelySigned for T {
//     fn signum(&self) -> NonNegativeSign {
//         PositivelySigned::signum(&self).into()
//     }
// }

mod sign;
mod non_zero_sign;
mod non_negative_sign;
mod positive_sign;

#[cfg(test)]
mod test {
    use crate::{Sign, Signed};
    use crate::RB;

    #[test]
    fn test_integer() {
        assert_eq!(Signed::signum(&0_i32), Sign::Zero);
        assert_eq!(Signed::signum(&-1), Sign::Negative);
        assert_eq!(Signed::signum(&1_i128), Sign::Positive);
        assert_eq!(Signed::signum(&0_u32), Sign::Zero);
        assert_eq!(Signed::signum(&1_u64), Sign::Positive);
    }

    #[test]
    fn test_sign_boolean() {
        assert!(6.is_positive());
        assert!((-5).is_negative());
        assert!(!0.is_positive());
        assert!(!0.is_negative());
        assert!(!6.is_negative());
        assert!(!(-5).is_positive());
    }

    #[test]
    fn test_sign() {
        assert_eq!(!Sign::Zero, Sign::Zero);
        assert_eq!(!Sign::Positive, Sign::Negative);
        assert_eq!(!Sign::Negative, Sign::Positive);
        assert_eq!(Sign::Positive, -Sign::Negative);
        assert_eq!(Sign::Positive * Sign::Positive, Sign::Positive);
        assert_eq!(Sign::Negative * Sign::Negative, Sign::Positive);
        assert_eq!(Sign::Negative * Sign::Zero, -Sign::Zero);
    }

    #[test]
    fn test_sign_ord() {
        assert_eq!(Sign::Zero < Sign::Positive, true);
        assert_eq!(Sign::Positive < Sign::Positive, false);
        assert_eq!(Sign::Positive == Sign::Positive, true);
        assert_eq!(Sign::Zero == Sign::Zero, true);
        assert_eq!(Sign::Negative < Sign::Positive, true);
        assert_eq!(Sign::Negative < Sign::Zero, true);
        assert_eq!(Sign::Negative < Sign::Negative, false);
    }

    #[test]
    fn test_sign_conversion() {
        assert_eq!(Sign::Positive, crate::NonZeroSign::Positive.into());
    }

    #[test]
    fn test_numbers() {
        assert_eq!(Signed::signum(&1), Sign::Positive);
        assert_eq!(Signed::signum(&0), Sign::Zero);
        assert_eq!(Signed::signum(&(-1)), Sign::Negative);

        assert_eq!(RB!(0).signum(), Sign::Zero);
        assert_eq!(RB!(1).signum(), Sign::Positive);
        assert_eq!(RB!(-1).signum(), Sign::Negative);

        assert_eq!(RB!(-1).signum() * RB!(-1).signum(), Sign::Positive);
        assert_eq!(RB!(1).signum() * RB!(1).signum(), Sign::Positive);
        assert_eq!(RB!(-1).signum() * RB!(1).signum(), Sign::Negative);
    }
}
