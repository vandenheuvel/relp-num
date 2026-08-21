use std::cmp::Ordering;
use std::ops::Deref;

use crate::{NonZero, Sign, Ubig};
use crate::integer::big::NonZeroUbig;
use crate::integer::big::ops::building_blocks::is_well_formed;
use crate::Signed;

impl<const S: usize> NonZero for Ubig<S> {
    #[inline]
    fn is_not_zero(&self) -> bool {
        !self.0.is_empty()
    }
}

impl<const S: usize> NonZero for NonZeroUbig<S> {
    #[inline]
    fn is_not_zero(&self) -> bool {
        true
    }
}

impl<const S: usize> Deref for Ubig<S> {
    type Target = [usize];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const S: usize> Deref for NonZeroUbig<S> {
    type Target = [usize];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const S: usize> Signed for Ubig<S> {
    #[inline]
    fn signum(&self) -> Sign {
        // Unlike `NonZeroUbig`, this type represents zero, so it is not always positive.
        if self.is_not_zero() { Sign::Positive } else { Sign::Zero }
    }

    #[inline]
    fn is_positive(&self) -> bool {
        self.is_not_zero()
    }

    #[inline]
    fn is_negative(&self) -> bool {
        false
    }
}

impl<const S: usize> Signed for NonZeroUbig<S> {
    fn signum(&self) -> Sign {
        Sign::Positive
    }

    fn is_positive(&self) -> bool {
        true
    }

    fn is_negative(&self) -> bool {
        false
    }
}

impl<const S: usize> Ord for NonZeroUbig<S> {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp(&self.0, &other.0)
    }
}

impl<const S: usize> Ord for Ubig<S> {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp(&self.0, &other.0)
    }
}

impl<const S: usize> PartialOrd for NonZeroUbig<S> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const S: usize> PartialOrd for Ubig<S> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[must_use]
#[inline]
pub fn cmp(left: &[usize], right: &[usize]) -> Ordering {
    debug_assert!(is_well_formed(left));
    debug_assert!(is_well_formed(right));

    match left.len().cmp(&right.len()) {
        Ordering::Less => Ordering::Less,
        Ordering::Equal => {
            // TODO(PERFORMANCE): Check that bounds checks are not done twice.
            for (left_word, right_word) in left.iter().zip(right.iter()).rev() {
                match left_word.cmp(right_word) {
                    Ordering::Less => return Ordering::Less,
                    Ordering::Equal => {}
                    Ordering::Greater => return Ordering::Greater,
                }
            }

            Ordering::Equal
        }
        Ordering::Greater => Ordering::Greater,
    }
}

#[cfg(test)]
mod test {
    use crate::{NonZero, Sign, Signed, Ubig};
    use crate::integer::big::NonZeroUbig;

    /// `Ubig` represents zero, so it is not unconditionally positive.
    ///
    /// It used to report `Sign::Positive` for every value, including the zero that `NonZero` in
    /// this same file correctly recognises, which contradicts the documented meaning of
    /// `is_positive` as strictly greater than zero.
    #[test]
    fn test_signed_zero_is_not_positive() {
        let zero = Ubig::<8>::from(0_u128);
        assert!(!zero.is_not_zero());
        assert_eq!(zero.signum(), Sign::Zero);
        assert!(!zero.is_positive());
        assert!(!zero.is_negative());

        for value in [1_u128, 2, u64::MAX as u128, u128::MAX] {
            let big = Ubig::<8>::from(value);
            assert!(big.is_not_zero(), "{value}");
            assert_eq!(big.signum(), Sign::Positive, "{value}");
            assert!(big.is_positive(), "{value}");
            assert!(!big.is_negative(), "{value}");
        }
    }

    /// The non zero variant is positive by construction.
    #[test]
    fn test_non_zero_signed_is_positive() {
        for value in [1_u128, 2, u128::MAX] {
            let big = NonZeroUbig::<8>::new_u128(value).unwrap();
            assert_eq!(big.signum(), Sign::Positive, "{value}");
            assert!(big.is_positive(), "{value}");
        }
    }
}
