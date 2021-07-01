use std::intrinsics::assume;
use std::ops::{Add, AddAssign, Mul};

use num_traits::Zero;

use crate::integer::big::{NonZeroUbig, Ubig};
use crate::integer::big::ops::building_blocks::add_assign_slice;
use crate::integer::big::ops::non_zero::{add_assign, mul_non_zero};

pub(crate) mod building_blocks;
pub mod non_zero;
pub mod div;
pub mod normalize;


impl<const S: usize> Add for Ubig<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        let (mut left, right) = if rhs.0.len() > self.0.len() {
            (rhs, self)
        } else {
            (self, rhs)
        };

        if right.is_zero() {
            return left;
        }

        unsafe {
            // SAFETY: Last value can only become zero with overflow, which is accounted for
            let overflow = add_assign_slice(left.inner_mut(), &right);
            if overflow {
                left.inner_mut().push(1);
            }
        }

        left
    }
}


impl<const S: usize> Add for NonZeroUbig<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        let (mut left, right) = if rhs.0.len() > self.0.len() {
            (rhs, self)
        } else {
            (self, rhs)
        };

        left += &right;

        left
    }
}


impl<const S: usize> AddAssign<&Self> for Ubig<S> {
    #[inline]
    fn add_assign(&mut self, rhs: &Ubig<S>) {
        add_assign(&mut self.0, &rhs.0);
    }
}

impl<const S: usize> AddAssign<&Self> for NonZeroUbig<S> {
    #[inline]
    fn add_assign(&mut self, rhs: &Self) {
        unsafe {
            // SAFETY: Is non zero so not empty
            assume(!self.0.is_empty());
            assume(!rhs.0.is_empty());
        }
        add_assign(&mut self.0, &rhs.0);
    }
}

impl<const S: usize> Mul for Ubig<S> {
    type Output = Self;

    fn mul(mut self, rhs: Self) -> Self::Output {
        if !self.is_zero() && !rhs.is_zero() {
            unsafe {
                // SAFETY: Are not empty so not zero
                Self(mul_non_zero(&self.0, &rhs.0))
            }
        } else {
            self.set_zero();
            self
        }
    }
}

impl<const S: usize> Mul for NonZeroUbig<S> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        unsafe {
            // SAFETY: Are not empty so not zero
            Self(mul_non_zero(&self.0, &rhs.0))
        }
    }
}

#[cfg(test)]
mod test {
    use smallvec::smallvec;

    use crate::{Ubig, NonZeroUbig};
    use std::str::FromStr;
    use num_traits::One;

    #[test]
    fn test_add() {
        assert_eq!(Ubig::<8>::from(0) + Ubig::<8>::from(0), Ubig::<8>::from(0));
        assert_eq!(Ubig::<8>::from(0) + Ubig::<8>::from(1), Ubig::<8>::from(1));
        assert_eq!(Ubig::<8>::from(1) + Ubig::<8>::from(0), Ubig::<8>::from(1));
        assert_eq!(Ubig::<8>::from(8) + Ubig::<8>::from(9), Ubig::<8>::from(17));
        assert_eq!(
            Ubig::<8>::from(usize::MAX) + Ubig::<8>::from(1),
            unsafe { Ubig::<8>::from_inner_unchecked(smallvec![0, 1]) },
        );
    }

    #[test]
    fn test_add_non_zero() {
        assert_eq!(
            NonZeroUbig::<8>::from_str("8").unwrap() + NonZeroUbig::<8>::from_str("9").unwrap(),
            NonZeroUbig::<8>::from_str("17").unwrap(),
        );
        assert_eq!(
            NonZeroUbig::<8>::from_str("18446744073709551615").unwrap() + NonZeroUbig::<8>::one(),
            NonZeroUbig::<8>::from_str("18446744073709551616").unwrap(),
        );
    }

    #[test]
    fn test_mul() {
        assert_eq!(Ubig::<8>::from(0) * Ubig::<8>::from(0), Ubig::<8>::from(0));
        assert_eq!(Ubig::<8>::from(0) * Ubig::<8>::from(1), Ubig::<8>::from(0));
        assert_eq!(Ubig::<8>::from(1) * Ubig::<8>::from(0), Ubig::<8>::from(0));
        assert_eq!(Ubig::<8>::from(8) * Ubig::<8>::from(9), Ubig::<8>::from(72));
        assert_eq!(
            Ubig::<8>::from(usize::MAX) * Ubig::<8>::from(1),
            Ubig::<8>::from(usize::MAX),
        );
    }

    #[test]
    fn test_mul_non_zero() {
        assert_eq!(
            NonZeroUbig::<8>::from_str("8").unwrap() * NonZeroUbig::<8>::from_str("9").unwrap(),
            NonZeroUbig::<8>::from_str("72").unwrap(),
        );
        assert_eq!(
            NonZeroUbig::<8>::from_str("18446744073709551615").unwrap() * NonZeroUbig::<8>::one(),
            NonZeroUbig::<8>::from_str("18446744073709551615").unwrap(),
        );
    }
}
