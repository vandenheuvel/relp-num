use std::cmp::{min, Ordering};
use std::mem;

use smallvec::{SmallVec};

use crate::rational::big::ops::{cmp, is_well_formed, sub, sub_assign_result_positive, sub_assign_single_result_positive};
use crate::rational::big::ops::building_blocks::{shr, shr_mut, shl_mut};
use crate::rational::big::ops::div::{div_assign_double, div_assign_one_word, div_assign_by_odd};

#[inline]
pub fn gcd<const S: usize>(left: &SmallVec<[usize; S]>, right: &SmallVec<[usize; S]>) -> SmallVec<[usize; S]> {
    debug_assert!(is_well_formed(left));
    debug_assert!(is_well_formed(right));
    debug_assert!(!left.is_empty());
    debug_assert!(!right.is_empty());
    debug_assert!(left[0] != 1 || left.len() > 1);
    debug_assert!(right[0] != 1 || right.len() > 1);
    debug_assert_ne!(left, right);

    let (left_zero_words, left_zero_bits) = unsafe { trailing_zeros(left) };
    let (right_zero_words, right_zero_bits) = unsafe { trailing_zeros(right) };
    let left = shr(left, left_zero_words, left_zero_bits);
    let right = shr(right, right_zero_words, right_zero_bits);

    let (words, bits) = min((left_zero_words, left_zero_bits), (right_zero_words, right_zero_bits));

    let mut odd_gcd = binary_gcd(left, right);
    shl_mut(&mut odd_gcd, words, bits);

    odd_gcd
}

#[inline]
pub fn prepare_gcd_single<const S: usize>(
    left: &SmallVec<[usize; S]>, mut right: usize,
) -> (SmallVec<[usize; S]>, usize, u32) {
    let left_zero_bits = left[0].trailing_zeros();
    let right_zero_bits = right.trailing_zeros();

    let zero_bits = min(left_zero_bits, right_zero_bits);
    let large_shifted = shr(left,0, left_zero_bits);
    right >>= right_zero_bits;

    return (large_shifted, right, zero_bits)
}

#[inline]
pub fn prepare_gcd_single_mut<const S: usize>(
    left: &mut SmallVec<[usize; S]>, mut right: usize,
) -> (usize, u32, u32, u32) {
    let left_zero_bits = left[0].trailing_zeros();
    let right_zero_bits = right.trailing_zeros();

    let zero_bits = min(left_zero_bits, right_zero_bits);
    shr_mut(left,0, zero_bits);
    right >>= zero_bits;

    return (right, left_zero_bits - zero_bits, right_zero_bits - zero_bits, zero_bits)
}

#[inline]
pub fn gcd_single<const S: usize>(
    mut large: SmallVec<[usize; S]>, small: usize, bits: u32,
) -> usize {
    debug_assert_eq!(small % 2, 1);
    while large.len() > 1 {
        debug_assert_eq!(large[0] % 2, 1);

        sub_assign_single_result_positive(&mut large, small);
        let (zero_words, zero_bits) = unsafe { trailing_zeros(&large) };
        shr_mut(&mut large, zero_words, zero_bits);
    }

    let mut left = large[0];
    let mut right = small;

    loop {
        debug_assert_eq!(left % 2, 1);
        debug_assert_eq!(right % 2, 1);

        if right == left {
            break right << bits;
        }

        if left > right {
            mem::swap(&mut left, &mut right);
        }

        right -= left;

        right >>= right.trailing_zeros();
    }
}

#[inline]
pub fn gcd_scalar(mut left: usize, mut right: usize) -> usize {
    debug_assert_ne!(left, 0);
    debug_assert_ne!(right, 0);
    debug_assert_ne!(left, right);

    let left_zeros = left.trailing_zeros();
    let right_zeros = right.trailing_zeros();
    let zeros = min(left_zeros, right_zeros);

    left >>= left_zeros;
    right >>= right_zeros;

    loop {
        if left == right {
            break right << zeros;
        }

        if left > right {
            mem::swap(&mut left, &mut right);
        }

        right -= left;

        right >>= right.trailing_zeros();
    }
}

#[inline]
pub fn simplify_fraction_gcd_single<const S: usize>(left: &mut SmallVec<[usize; S]>, right: usize) -> usize {
    debug_assert!(is_well_formed(left));
    debug_assert!(!left.is_empty());
    debug_assert_ne!(right, 0);
    debug_assert_ne!(right, 1);
    debug_assert!(left[0] != 1 || left.len() > 1);

    let (mut right, left_to_shift, right_to_shift, zero_bits) = prepare_gcd_single_mut(left, right);
    let right_shifted = right >> right_to_shift;

    if right > 1 {
        let other = shr(left, 0, left_to_shift);
        // TODO(PERFORMANCE): If no left_to_shift, do the first allocation after subtraction?
        if other[0] != 1 || other.len() > 1 {
            let gcd = gcd_single(other, right_shifted, zero_bits);

            if gcd > 1 {
                right /= gcd;
                div_assign_one_word(left, gcd);
            }
        }
    }

    right
}

#[inline]
pub fn simplify_fraction_without_info<const S: usize>(numerator: &mut SmallVec<[usize; S]>, denominator: &mut SmallVec<[usize; S]>) {
    debug_assert!(is_well_formed(numerator));
    debug_assert!(is_well_formed(denominator));
    debug_assert!(!numerator.is_empty());
    debug_assert!(!denominator.is_empty());

    if numerator[0] == 1 && numerator.len() == 1 || denominator[0] == 1 && denominator.len() == 1 {
        return;
    }

    match cmp(numerator, denominator) {
        Ordering::Equal => {
            numerator.truncate(1); numerator[0] = 1;
            denominator.truncate(1); denominator[0] = 1;
        }
        Ordering::Less | Ordering::Greater => simplify_fraction_gcd(numerator, denominator),
    }
}

#[inline]
pub fn simplify_fraction_gcd<const S: usize>(left: &mut SmallVec<[usize; S]>, right: &mut SmallVec<[usize; S]>) {
    debug_assert!(is_well_formed(left));
    debug_assert!(is_well_formed(right));
    debug_assert!(!left.is_empty());
    debug_assert!(!right.is_empty());
    debug_assert!(left[0] != 1 || left.len() > 1);
    debug_assert!(right[0] != 1 || right.len() > 1);
    // This restriction could be relaxed, but it might cost an allocation if this is not checked
    // beforehand. So we leave it to the caller to ensure that they are not equal before entering
    // the method.
    debug_assert_ne!(right, left);

    let which_odd = remove_shared_two_factors_mut(left, right);
    let start_values = match which_odd {
        WhichOdd::Left(words_to_shift, bits_to_shift) => {
            prepare_side(left, right, words_to_shift, bits_to_shift)
        }
        WhichOdd::Right(words_to_shift, bits_to_shift) => {
            prepare_side(right, left, words_to_shift, bits_to_shift)
        }
        WhichOdd::Both => Some((left.clone(), right.clone())),
    };

    if let Some((start_left, start_right)) = start_values {
        if !(start_left[0] == 1 && start_left.len() == 1) && !(start_right[0] == 1 && start_right.len() == 1) {
            let gcd = binary_gcd(start_left, start_right);
            debug_assert!(is_well_formed(&gcd));
            debug_assert!(!gcd.is_empty());
            debug_assert_eq!(gcd[0] % 2, 1);

            match (cmp(&left, &gcd), cmp(&right, &gcd)) {
                (Ordering::Equal, _) => div_assign_by_odd(right, &gcd),
                (_, Ordering::Equal) => div_assign_by_odd(left, &gcd),
                (_, _) => if gcd[0] != 1 || gcd.len() > 1 {
                    div_assign_double(left, right, gcd);
                },
            }
        }
    }
}

#[inline]
pub fn remove_shared_two_factors_mut<const S: usize>(left: &mut SmallVec<[usize; S]>, right: &mut SmallVec<[usize; S]>) -> WhichOdd {
    let (left_zero_words, left_zero_bits) = unsafe { trailing_zeros(left) };
    let (right_zero_words, right_zero_bits) = unsafe { trailing_zeros(right) };

    let (zero_words, zero_bits) = min((left_zero_words, left_zero_bits), (right_zero_words, right_zero_bits));
    shr_mut(left, zero_words, zero_bits);
    shr_mut(right, zero_words, zero_bits);

    match (left_zero_words, left_zero_bits).cmp(&(right_zero_words, right_zero_bits)) {
        Ordering::Less => WhichOdd::Left(right_zero_words - left_zero_words, right_zero_bits - left_zero_bits),
        Ordering::Equal => WhichOdd::Both,
        Ordering::Greater => WhichOdd::Right(left_zero_words - right_zero_words, left_zero_bits - right_zero_bits),
    }
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum WhichOdd {
    Left(usize, u32),
    Right(usize, u32),
    Both,
}

#[inline]
fn prepare_side<const S: usize>(
    already_odd: &mut SmallVec<[usize; S]>,
    even: &mut SmallVec<[usize; S]>, words_to_shift: usize, bits_to_shift: u32,
) -> Option<(SmallVec<[usize; S]>, SmallVec<[usize; S]>)> {
    let oddified = shr(even, words_to_shift, bits_to_shift);
    let mut other = match cmp(already_odd, &oddified) {
        Ordering::Less => {
            // left is smallest, subtract it from even_right

            // second start value is known to be positive
            sub(&oddified, already_odd)
        }
        Ordering::Equal => {
            // even = already_odd * 2 ** k with k = words_to_shift * BITS_PER_WORD + bits_to_shift
            already_odd.truncate(1);
            already_odd[0] = 1;
            // TODO(PERFORMANCE): Reuse allocation?
            even.truncate(words_to_shift + 1);
            for i in 0..words_to_shift {
                even[i] = 0;
            }
            even[words_to_shift] = 1 << bits_to_shift;

            return None;
        }
        Ordering::Greater => {
            // even_right is smallest, subtract it from left

            // second start value is known to be positive
            sub(already_odd, &oddified)
        }
    };

    // other is now even:
    let (zero_words, zero_bits) = unsafe { trailing_zeros(&other) };
    shr_mut(&mut other, zero_words, zero_bits);

    // now both `other` and `oddified` are odd, it is unknown which one is larger
    Some((other, oddified))
}

#[inline]
fn binary_gcd<const S: usize>(mut left: SmallVec<[usize; S]>, mut right: SmallVec<[usize; S]>) -> SmallVec<[usize; S]> {
    debug_assert!(!left.is_empty() && is_well_formed(&left));
    debug_assert!(!right.is_empty() && is_well_formed(&right));

    loop {
        debug_assert_eq!(left[0] % 2, 1);
        debug_assert_eq!(right[0] % 2, 1);

        match cmp_and_remove(&mut left, &mut right) {
            Ordering::Less => {
                sub_assign_result_positive(&mut right, &left);
                let (zero_words, zero_bits) = unsafe { trailing_zeros(&right) };
                shr_mut(&mut right, zero_words, zero_bits);
            }
            Ordering::Equal => break left,
            Ordering::Greater => {
                sub_assign_result_positive(&mut left, &right);
                let (zero_words, zero_bits) = unsafe { trailing_zeros(&left) };
                shr_mut(&mut left, zero_words, zero_bits);
            }
        }
    }
}

#[inline]
fn cmp_and_remove<const S: usize>(left: &mut SmallVec<[usize; S]>, right: &mut SmallVec<[usize; S]>) -> Ordering {
    debug_assert!(is_well_formed(left));
    debug_assert!(is_well_formed(right));

    match left.len().cmp(&right.len()) {
        Ordering::Less => Ordering::Less,
        Ordering::Equal => {
            let length = left.len();
            debug_assert_eq!(right.len(), length);

            let mut nr_equal = 0;
            for (left_word, right_word) in left.iter().zip(right.iter()).rev() {
                match left_word.cmp(right_word) {
                    Ordering::Less => {
                        left.truncate(length - nr_equal);
                        right.truncate(length - nr_equal);
                        return Ordering::Less
                    },
                    Ordering::Equal => {
                        nr_equal += 1;
                    }
                    Ordering::Greater => {
                        left.truncate(length - nr_equal);
                        right.truncate(length - nr_equal);
                        return Ordering::Greater
                    },
                }
            }

            Ordering::Equal
        }
        Ordering::Greater => Ordering::Greater,
    }
}

/// Count the number of trailing zeros.
///
/// Alternatively phrased, what is the highest power of 2 that divides the input value?
///
/// This method should not be called on a zero value.
///
/// # Returns
///
/// A tuple where the first item indicates the number of (least significant) words that are zero and
/// the second item indicates the number of trailing bits that are zero in the first value that is
/// not zero.
#[inline]
pub unsafe fn trailing_zeros<const S: usize>(values: &SmallVec<[usize; S]>) -> (usize, u32) {
    debug_assert!(!values.is_empty() && is_well_formed(values));

    let mut zero_words = 0;
    while values.get_unchecked(zero_words) == &0 {
        // At least the last value is not allowed to be zero, so we don't have to check bounds
        zero_words += 1;
    }

    (zero_words, values.get_unchecked(zero_words).trailing_zeros())
}

#[cfg(test)]
mod test {
    use smallvec::smallvec;

    use crate::rational::big::ops::normalize::{binary_gcd, trailing_zeros, gcd_scalar, simplify_fraction_gcd_single, gcd_single, simplify_fraction_gcd, remove_shared_two_factors_mut, WhichOdd};
    use crate::rational::big::ops::test::SV;

    #[test]
    fn test_binary_gcd() {
        let x: SV = smallvec![7];
        let y: SV = smallvec![15];
        let expected: SV = smallvec![1];
        assert_eq!(binary_gcd(x, y), expected);

        let x: SV = smallvec![35];
        let y: SV = smallvec![125];
        let expected: SV = smallvec![5];
        assert_eq!(binary_gcd(x, y), expected);

        let x: SV = smallvec![6851533845];
        let y: SV = smallvec![6468684843];
        let expected: SV = smallvec![3];
        assert_eq!(binary_gcd(x, y), expected);

        let x: SV = smallvec![2_usize.pow(59) - 55]; // prime
        let y: SV = smallvec![964684684643];
        let expected: SV = smallvec![1];
        assert_eq!(binary_gcd(x, y), expected);

        let x: SV = smallvec![1, 1];
        let y: SV = smallvec![3, 0, 1];
        let expected: SV = smallvec![1];
        assert_eq!(binary_gcd(x, y), expected);

        let x: SV = smallvec![1, 1];
        let y: SV = smallvec![1, 1];
        let expected: SV = smallvec![1, 1];
        assert_eq!(binary_gcd(x, y), expected);
    }
    use crate::rational::big::ops::gcd;
    #[test]
    fn test_gcd() {
        let x: SV = smallvec![6];
        let y: SV = smallvec![12];
        assert_eq!(gcd(&x, &y), x);
    }

    #[test]
    fn test_zeros() {
        let x: SV = smallvec![1];
        assert_eq!(unsafe { trailing_zeros(&x) }, (0, 0));

        let x: SV = smallvec![0, 1];
        assert_eq!(unsafe { trailing_zeros(&x) }, (1, 0));

        let x: SV = smallvec![2];
        assert_eq!(unsafe { trailing_zeros(&x) }, (0, 1));

        let x: SV = smallvec![0, 2];
        assert_eq!(unsafe { trailing_zeros(&x) }, (1, 1));

        let x: SV = smallvec![0, 0, 0, 14, 6];
        assert_eq!(unsafe { trailing_zeros(&x) }, (3, 1));
    }

    #[test]
    fn test_simplify_fraction_gcd_single() {
        let mut x: SV = smallvec![990];
        assert_eq!(simplify_fraction_gcd_single(&mut x, 141), 47);
        let expected: SV = smallvec![330];
        assert_eq!(x, expected);
    }

    #[test]
    fn test_simplify_fraction_gcd() {
        let mut left: SV = smallvec![3];
        let mut right: SV = smallvec![6];
        simplify_fraction_gcd(&mut left, &mut right);
        let expected_left: SV = smallvec![1];
        let expected_right: SV = smallvec![2];
        assert_eq!(left, expected_left);
        assert_eq!(right, expected_right);

        let mut left: SV = smallvec![18];
        let mut right: SV = smallvec![9];
        simplify_fraction_gcd(&mut left, &mut right);
        let expected_left: SV = smallvec![2];
        let expected_right: SV = smallvec![1];
        assert_eq!(left, expected_left);
        assert_eq!(right, expected_right);

        let mut left: SV = smallvec![10];
        let mut right: SV = smallvec![44];
        simplify_fraction_gcd(&mut left, &mut right);
        let expected_left: SV = smallvec![5];
        let expected_right: SV = smallvec![22];
        assert_eq!(left, expected_left);
        assert_eq!(right, expected_right);
    }

    #[test]
    fn test_remove_shared_two_factors_mut() {
        let mut left: SV = smallvec![3];
        let mut right: SV = smallvec![6];
        let which_odd = remove_shared_two_factors_mut(&mut left, &mut right);
        assert_eq!(which_odd, WhichOdd::Left(0, 1));
        let expected_left: SV = smallvec![3];
        let expected_right: SV = smallvec![6];
        assert_eq!(left, expected_left);
        assert_eq!(right, expected_right);
    }

    #[test]
    fn test_gcd_scalar() {
        assert_eq!(gcd_scalar(2, 3), 1);
        assert_eq!(gcd_scalar(990, 141), 3);
        assert_eq!(gcd_scalar(4, 2), 2);
        assert_eq!(gcd_scalar(7, 11), 1);
        assert_eq!(gcd_scalar(9889, 11), 11);
        assert_eq!(gcd_scalar(3 * 129, 98540), 1);
        assert_eq!(gcd_scalar(3 * 127, 3 * 98987), 3);
        assert_eq!(gcd_scalar(789 * 987, 789 * 6188988), 2367);
    }

    #[test]
    fn test_gcd_single() {
        assert_eq!(gcd_single::<2>(smallvec![1, 1], 3, 0), 1);
        assert_eq!(gcd_single::<2>(smallvec![1, 2], 3, 0), 3);
        assert_eq!(gcd_single::<2>(smallvec![13835058055282163747, 1 << 3], (1 << 62) + 1, 0), (1 << 62) + 1);
        assert_eq!(gcd_single::<2>(
                smallvec![4611686018427388777, (1 << 7) + (1 << 6) + (1 << 4) + (1 << 3) + (1 << 1)],
                (1 << 62) + 1,
                0,
            ),
            (1 << 62) + 1,
        );
        assert_eq!(gcd_single::<2>(
                smallvec![4611686018427388777, (1 << 7) + (1 << 6) + (1 << 4) + (1 << 3) + (1 << 1)],
                873,
                0,
            ),
            873,
        );
    }
}
