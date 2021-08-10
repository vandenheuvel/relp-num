use std::cmp::Ordering;
use std::ops::Deref;

use crate::{NonZero, Sign, Ubig};
use crate::integer::big::NonZeroUbig;
use crate::integer::big::ops::building_blocks::is_well_formed;
use crate::Signed;

impl<const S: usize> NonZero for Ubig<S> {
    #[must_use]
    #[inline]
    fn is_not_zero(&self) -> bool {
        !self.0.is_empty()
    }
}

impl<const S: usize> NonZero for NonZeroUbig<S> {
    #[must_use]
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
        self.partial_cmp(other).unwrap()
    }
}

impl<const S: usize> Ord for Ubig<S> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<const S: usize> PartialOrd for NonZeroUbig<S> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(cmp(&self.0, &other.0))
    }
}

impl<const S: usize> PartialOrd for Ubig<S> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(cmp(&self.0, &other.0))
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
