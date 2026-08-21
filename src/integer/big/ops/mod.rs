use std::hint::assert_unchecked;
use std::ops::{Add, AddAssign, Mul};

use num_traits::Zero;

use crate::integer::big::{NonZeroUbig, Ubig};
use crate::integer::big::ops::non_zero::{add_assign, mul_non_zero};

pub(crate) mod building_blocks;
pub mod non_zero;
pub mod div;
pub mod normalize;


impl<const S: usize> Add for Ubig<S> {
    type Output = Self;

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

        left += &right;

        left
    }
}


impl<const S: usize> Add for NonZeroUbig<S> {
    type Output = Self;

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
            assert_unchecked(!self.0.is_empty());
            assert_unchecked(!rhs.0.is_empty());
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
    use std::str::FromStr;

    use num_traits::One;
    use smallvec::smallvec;

    use crate::{NonZeroUbig, Ubig};

    #[test]
    fn test_add() {
        assert_eq!(Ubig::<8>::from(0_usize) + Ubig::<8>::from(0_usize), Ubig::<8>::from(0_usize));
        assert_eq!(Ubig::<8>::from(0_usize) + Ubig::<8>::from(1_usize), Ubig::<8>::from(1_usize));
        assert_eq!(Ubig::<8>::from(1_usize) + Ubig::<8>::from(0_usize), Ubig::<8>::from(1_usize));
        assert_eq!(Ubig::<8>::from(8_usize) + Ubig::<8>::from(9_usize), Ubig::<8>::from(17_usize));
        assert_eq!(
            Ubig::<8>::from(usize::MAX) + Ubig::<8>::from(1_usize),
            unsafe { Ubig::<8>::from_inner_unchecked(smallvec![0, 1]) },
        );
    }

    #[test]
    fn test_add_unequal_lengths() {
        // A carry out of the shorter operand has to be propagated into the higher words of the
        // longer operand, not appended on top of it.

        let one = Ubig::<8>::from(1_usize);

        let large = Ubig::<8>::from_str("18446744073709551616").unwrap(); // 2 ** 64
        let expected = Ubig::<8>::from_str("18446744073709551617").unwrap();
        assert_eq!(one.clone() + large.clone(), expected);
        assert_eq!(large + one.clone(), expected);

        // [usize::MAX, 5] + [1] == [0, 6]
        let left = unsafe { Ubig::<8>::from_inner_unchecked(smallvec![usize::MAX, 5]) };
        let expected = unsafe { Ubig::<8>::from_inner_unchecked(smallvec![0, 6]) };
        assert_eq!(left.clone() + one.clone(), expected);
        assert_eq!(one.clone() + left, expected);

        // A carry that travels across several words.
        let left = unsafe {
            Ubig::<8>::from_inner_unchecked(smallvec![usize::MAX, usize::MAX, usize::MAX, 5])
        };
        let expected = unsafe { Ubig::<8>::from_inner_unchecked(smallvec![0, 0, 0, 6]) };
        assert_eq!(left.clone() + one.clone(), expected);
        assert_eq!(one.clone() + left, expected);

        // A carry that travels across several words and out of the top one.
        let left = unsafe {
            Ubig::<8>::from_inner_unchecked(smallvec![usize::MAX, usize::MAX, usize::MAX])
        };
        let expected = unsafe { Ubig::<8>::from_inner_unchecked(smallvec![0, 0, 0, 1]) };
        assert_eq!(left.clone() + one.clone(), expected);
        assert_eq!(one.clone() + left, expected);

        // Longer operand on the right, no carry at all.
        let left = unsafe { Ubig::<8>::from_inner_unchecked(smallvec![1, 2, 3]) };
        let right = unsafe { Ubig::<8>::from_inner_unchecked(smallvec![10, 20]) };
        let expected = unsafe { Ubig::<8>::from_inner_unchecked(smallvec![11, 22, 3]) };
        assert_eq!(left.clone() + right.clone(), expected);
        assert_eq!(right + left, expected);
    }

    #[test]
    fn test_add_non_zero_unequal_lengths() {
        let one = NonZeroUbig::<8>::one();

        let large = NonZeroUbig::<8>::from_str("18446744073709551616").unwrap(); // 2 ** 64
        let expected = NonZeroUbig::<8>::from_str("18446744073709551617").unwrap();
        assert_eq!(one.clone() + large.clone(), expected);
        assert_eq!(large + one.clone(), expected);

        // [usize::MAX, 5] + [1] == [0, 6]
        let left = unsafe { NonZeroUbig::<8>::from_inner_unchecked(smallvec![usize::MAX, 5]) };
        let expected = unsafe { NonZeroUbig::<8>::from_inner_unchecked(smallvec![0, 6]) };
        assert_eq!(left.clone() + one.clone(), expected);
        assert_eq!(one.clone() + left, expected);

        let left = unsafe {
            NonZeroUbig::<8>::from_inner_unchecked(smallvec![usize::MAX, usize::MAX, usize::MAX, 5])
        };
        let expected = unsafe { NonZeroUbig::<8>::from_inner_unchecked(smallvec![0, 0, 0, 6]) };
        assert_eq!(left.clone() + one.clone(), expected);
        assert_eq!(one + left, expected);
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
        assert_eq!(Ubig::<8>::from(0_usize) * Ubig::<8>::from(0_usize), Ubig::<8>::from(0_usize));
        assert_eq!(Ubig::<8>::from(0_usize) * Ubig::<8>::from(1_usize), Ubig::<8>::from(0_usize));
        assert_eq!(Ubig::<8>::from(1_usize) * Ubig::<8>::from(0_usize), Ubig::<8>::from(0_usize));
        assert_eq!(Ubig::<8>::from(8_usize) * Ubig::<8>::from(9_usize), Ubig::<8>::from(72_usize));
        assert_eq!(
            Ubig::<8>::from(usize::MAX) * Ubig::<8>::from(1_usize),
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
