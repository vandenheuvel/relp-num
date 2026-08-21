use std::cmp::{min, Ordering};
use std::mem;

use smallvec::SmallVec;

use crate::integer::big::BITS_PER_WORD;
use crate::integer::big::ops::building_blocks::{is_well_formed, is_well_formed_non_zero};
use crate::integer::big::ops::div::{div_assign_by_odd, div_assign_double, div_assign_one_word};
use crate::integer::big::ops::non_zero::{both_not_one_non_zero, is_one_non_zero, shl_mut, shr, shr_mut, sub, sub_assign_result_positive};
use crate::integer::big::ops::non_zero::sub_assign_single_result_positive;
use crate::integer::big::properties::cmp;

#[must_use]
pub unsafe fn is_coprime_non_zero(left: &[usize], right: &[usize]) -> bool {
    debug_assert!(is_well_formed_non_zero(left));
    debug_assert!(is_well_formed_non_zero(right));

    const S: usize = 8;

    let mut left_clone = SmallVec::<[usize; S]>::from_slice(left);
    let mut right_clone = SmallVec::<[usize; S]>::from_slice(right);
    // SAFETY: The clones are word for word copies of the two operands, which the caller guarantees
    // to be well formed and not empty.
    unsafe { simplify_fraction_without_info(&mut left_clone, &mut right_clone) };

    left_clone.as_slice() == left && right_clone.as_slice() == right
}

#[inline]
pub unsafe fn gcd<const S: usize>(left: &[usize], right: &[usize]) -> SmallVec<[usize; S]> {
    debug_assert!(is_well_formed(left));
    debug_assert!(is_well_formed(right));
    debug_assert!(!left.is_empty());
    debug_assert!(!right.is_empty());
    // SAFETY: The caller guarantees that neither operand is empty.
    debug_assert!(!unsafe { is_one_non_zero(left) });
    // SAFETY: The caller guarantees that neither operand is empty.
    debug_assert!(!unsafe { is_one_non_zero(right) });
    debug_assert_ne!(left, right);

    // SAFETY: The caller guarantees that both operands are well formed and not empty.
    let (left_zero_words, left_zero_bits) = unsafe { trailing_zeros(left) };
    // SAFETY: The caller guarantees that both operands are well formed and not empty.
    let (right_zero_words, right_zero_bits) = unsafe { trailing_zeros(right) };
    let left = shr(left, left_zero_words, left_zero_bits);
    let right = shr(right, right_zero_words, right_zero_bits);

    let (words, bits) = min((left_zero_words, left_zero_bits), (right_zero_words, right_zero_bits));

    // SAFETY: Exactly its own trailing zeros were shifted out of each operand, so both are now the
    // odd part of a non zero value: not empty, well formed, and with an odd first word.
    let mut odd_gcd = unsafe { binary_gcd(left, right) };
    shl_mut(&mut odd_gcd, words, bits);

    odd_gcd
}

/// Split off the powers of two of a large and a small value.
///
/// # Returns
///
/// A tuple with the odd part of `left`, the odd part of `right` and the number of factors two that
/// the two values share. That last number is always smaller than [`BITS_PER_WORD`], because `right`
/// is a single, nonzero word.
#[inline]
/// # Safety
///
/// `left` has to be well formed and not zero, and `right` has to be non zero.
pub unsafe fn prepare_gcd_single<const S: usize>(
    left: &[usize], mut right: usize,
) -> (SmallVec<[usize; S]>, usize, u32) {
    // `trailing_zeros` scans upward with unchecked indexing and stops only on a non-zero word, so
    // an operand that is not well formed reads past the end. Note the requirement is well
    // formedness, not just non-emptiness: an all zero vector is non-empty and still runs off.
    debug_assert!(is_well_formed_non_zero(left), "the operand has to be well formed and not zero");
    debug_assert_ne!(right, 0);

    // `left[0]` can be zero, in which case the number of trailing zero bits doesn't fit in a single
    // word: the number of whole zero words has to be shifted away separately.
    // SAFETY: `left` is well formed and not zero, which the assertion above establishes, so the
    // `debug_assert`s the second half of that, so a caller that hands it an all zero value makes it
    // scan past the end. Every caller in the crate passes the words of a non zero `NonZeroUbig` or
    // of a value it has just checked, so the requirement holds today; it is not enforced here.
    let (left_zero_words, left_zero_bits) = unsafe { trailing_zeros(left) };
    let right_zero_bits = right.trailing_zeros();

    let zero_bits = shared_zero_bits(left_zero_words, left_zero_bits, right_zero_bits);
    let large_shifted = shr(left, left_zero_words, left_zero_bits);
    right >>= right_zero_bits;

    (large_shifted, right, zero_bits)
}

/// Divide out the powers of two that a large and a small value share.
///
/// `left` is shifted right by the number of factors two the two values share.
///
/// # Returns
///
/// A tuple with the small value shifted right by the shared number of factors two, the number of
/// whole words and the number of bits that `left` still has to be shifted right by to become odd,
/// the number of bits the returned small value still has to be shifted right by to become odd, and
/// the number of shared factors two.
#[inline]
/// # Safety
///
/// `left` has to be well formed and not zero, and `right` has to be non zero.
pub unsafe fn prepare_gcd_single_mut<const S: usize>(
    left: &mut SmallVec<[usize; S]>, mut right: usize,
) -> (usize, usize, u32, u32, u32) {
    // `trailing_zeros` scans upward with unchecked indexing and stops only on a non-zero word, so
    // an operand that is not well formed reads past the end. Note the requirement is well
    // formedness, not just non-emptiness: an all zero vector is non-empty and still runs off.
    debug_assert!(is_well_formed_non_zero(left), "the operand has to be well formed and not zero");
    debug_assert_ne!(right, 0);

    // `left[0]` can be zero, in which case the number of trailing zero bits doesn't fit in a single
    // word: the number of whole zero words has to be shifted away separately.
    // SAFETY: `left` is well formed and not zero, which the assertion above establishes, so the
    // `debug_assert`s the second half of that, so a caller that hands it an all zero value makes it
    // scan past the end. Every caller in the crate passes the words of a non zero `NonZeroUbig` or
    // of a value it has just checked, so the requirement holds today; it is not enforced here.
    let (left_zero_words, left_zero_bits) = unsafe { trailing_zeros(left) };
    let right_zero_bits = right.trailing_zeros();

    let zero_bits = shared_zero_bits(left_zero_words, left_zero_bits, right_zero_bits);
    shr_mut(left, 0, zero_bits);
    right >>= zero_bits;

    let (left_words_to_shift, left_bits_to_shift) = shift_difference(
        left_zero_words, left_zero_bits, 0, zero_bits,
    );

    (right, left_words_to_shift, left_bits_to_shift, right_zero_bits - zero_bits, zero_bits)
}

/// How many factors two do a large and a small value share?
///
/// The result is always smaller than [`BITS_PER_WORD`], because the small value is a single,
/// nonzero word.
#[inline]
fn shared_zero_bits(left_zero_words: usize, left_zero_bits: u32, right_zero_bits: u32) -> u32 {
    debug_assert!(right_zero_bits < BITS_PER_WORD);

    if left_zero_words > 0 {
        // `left` has at least `BITS_PER_WORD` factors two, so `right` has the fewest
        right_zero_bits
    } else {
        min(left_zero_bits, right_zero_bits)
    }
}

#[inline]
/// # Safety
///
/// `large` has to be well formed and not zero. The loop then maintains that.
pub unsafe fn gcd_single<const S: usize>(
    mut large: SmallVec<[usize; S]>, small: usize, bits: u32,
) -> usize {
    // `trailing_zeros` scans upward with unchecked indexing and stops only on a non-zero word, so
    // an operand that is not well formed reads past the end. Note the requirement is well
    // formedness, not just non-emptiness: an all zero vector is non-empty and still runs off.
    debug_assert!(is_well_formed_non_zero(&large), "the operand has to be well formed and not zero");
    debug_assert_eq!(small % 2, 1);

    while large.len() > 1 {
        debug_assert_eq!(large[0] % 2, 1);

        sub_assign_single_result_positive(&mut large, small);
        // SAFETY: `large` is more than one word long at the top of the loop and `small` is a single
        // word, so the difference is positive and therefore not empty, and the subtraction leaves
        // it well formed.
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
pub unsafe fn simplify_fraction_gcd_single<const S: usize>(
    left: &mut SmallVec<[usize; S]>,
    right: usize,
) -> usize {
    debug_assert!(is_well_formed(left));
    debug_assert!(!left.is_empty());
    debug_assert!(left[0] != 1 || left.len() > 1);
    debug_assert_ne!(right, 0);
    debug_assert_ne!(right, 1);

    // SAFETY: `left` is well formed and not zero, and `right` is non zero, by this function's
    // contract.
    let (mut right, left_words_to_shift, left_bits_to_shift, right_to_shift, _) = unsafe {
        prepare_gcd_single_mut(left, right)
    };
    let right_shifted = right >> right_to_shift;

    if right_shifted > 1 {
        let other = shr::<S>(left, left_words_to_shift, left_bits_to_shift);
        // TODO(PERFORMANCE): If no left_to_shift, do the first allocation after subtraction?
        // SAFETY: `other` is `left` with exactly its remaining trailing zeros shifted out, so it is
        // the odd part of a non zero value and therefore not empty.
        if !unsafe { is_one_non_zero(&other) } {
            debug_assert_eq!(other[0] % 2, 1);
            debug_assert_eq!(right_shifted % 2, 1);
            // TODO(ARCHITECTURE): Don't pass that bit count through the function to cancel it again after
            // SAFETY: `other` came out of the shift above, which leaves it well formed, and it is
            // not zero because it is at least as large as the odd part of a non zero value.
            let gcd = unsafe { gcd_single(other, right_shifted, 0) };

            if gcd > 1 {
                right /= gcd;
                // SAFETY: `left` is still well formed and not empty; shifting right by its own
                // trailing zeros cannot empty a non zero value. `gcd` divides `other`, which is
                // the odd part of `left`, so it divides `left` exactly, and it is odd because
                // both of its own operands are.
                unsafe { div_assign_one_word(left, gcd) };
            }
        }
    }

    right
}

#[inline]
pub unsafe fn simplify_fraction_without_info<const S: usize>(
    left: &mut SmallVec<[usize; S]>,
    right: &mut SmallVec<[usize; S]>,
) {
    debug_assert!(is_well_formed_non_zero(left));
    debug_assert!(is_well_formed_non_zero(right));

    // SAFETY: The caller guarantees that neither operand is empty.
    if !unsafe { both_not_one_non_zero(left, right) } {
        return;
    }

    match cmp(left, right) {
        Ordering::Equal => {
            left.truncate(1); left[0] = 1;
            right.truncate(1); right[0] = 1;
        }
        // SAFETY: Both operands are well formed and not empty by the caller's guarantee, the check
        // above established that neither is one, and this arm is the one where they differ.
        Ordering::Less | Ordering::Greater => unsafe { simplify_fraction_gcd(left, right) },
    }
}

#[inline]
pub unsafe fn simplify_fraction_gcd<const S: usize>(
    left: &mut SmallVec<[usize; S]>,
    right: &mut SmallVec<[usize; S]>,
) {
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

    // SAFETY: Both operands are well formed and not zero by this function's contract.
    let which_odd = unsafe { remove_shared_two_factors_mut(left, right) };
    let (start_left, start_right) = match which_odd {
        WhichOdd::Left(words_to_shift, bits_to_shift) => {
            // SAFETY: Shifting a non zero value right by the factors two it shares with another
            // leaves it well formed and not empty, so both operands still are. This arm is the one
            // where `left` came out odd and `right` still has `(words_to_shift, bits_to_shift)`
            // factors two to give up.
            match unsafe { prepare_side(left, right, words_to_shift, bits_to_shift) } {
                PreparationResult::StartValues(values) => values,
                PreparationResult::EqualAfterShift => {
                    left.truncate(1);
                    left[0] = 1;
                    right.truncate(words_to_shift + 1);
                    for i in 0..words_to_shift {
                        right[i] = 0;
                    }
                    right[words_to_shift] = 1 << bits_to_shift;
                    return;
                }
            }
        }
        WhichOdd::Right(words_to_shift, bits_to_shift) => {
            // SAFETY: As above, with the roles reversed: `right` came out odd and `left` still has
            // `(words_to_shift, bits_to_shift)` factors two to give up.
            match unsafe { prepare_side(right, left, words_to_shift, bits_to_shift) } {
                PreparationResult::StartValues(values) => values,
                PreparationResult::EqualAfterShift => {
                    right.truncate(1);
                    right[0] = 1;
                    // TODO(PERFORMANCE): Reuse allocation?
                    left.truncate(words_to_shift + 1);
                    for i in 0..words_to_shift {
                        left[i] = 0;
                    }
                    left[words_to_shift] = 1 << bits_to_shift;
                    return;
                }
            }
        }
        WhichOdd::Both => (left.clone(), right.clone()),
    };

    // SAFETY: Neither start value is empty. `prepare_side` returns the odd part of a difference of
    // two unequal values and the odd part of the even operand, both non zero; the `Both` arm clones
    // the two operands, which the caller guarantees not to be empty.
    if unsafe { both_not_one_non_zero(&start_left, &start_right) } {
        // SAFETY: Both start values are well formed, not empty and odd. `prepare_side` shifts the
        // trailing zeros out of both of the values it returns, and in the `Both` arm the two
        // operands came out of `remove_shared_two_factors_mut` with the same number of factors two
        // removed, which leaves both of them odd.
        let gcd = unsafe { binary_gcd(start_left, start_right) };
        debug_assert!(is_well_formed(&gcd));
        debug_assert!(!gcd.is_empty());
        debug_assert_eq!(gcd[0] % 2, 1);

        if gcd[0] != 1 || gcd.len() > 1 {
            // `gcd` divides both operands: the odd one directly, and the even one because its odd
            // part is what went into the computation. The two operands are still unequal, because
            // `remove_shared_two_factors_mut` shifted both by the same, exact amount. So at most
            // one of the two comparisons below is `Equal`, and the other side is then strictly
            // greater than `gcd` rather than smaller, which is what the divisions require.
            match (cmp(left, &gcd), cmp(right, &gcd)) {
                (Ordering::Equal, _) => {
                    left[0] = 1; left.truncate(1);
                    // SAFETY: `gcd` is odd, larger than one and divides `right`. `right` cannot
                    // equal `gcd` here, because `left` does and the two differ, so it is larger.
                    unsafe { div_assign_by_odd(right, &gcd) };
                }
                (_, Ordering::Equal) => {
                    // SAFETY: As above, with the roles reversed.
                    unsafe { div_assign_by_odd(left, &gcd) };
                    right[0] = 1; right.truncate(1);
                }
                // SAFETY: Neither operand equals `gcd` in this arm, and `gcd` divides both, so
                // both are strictly larger. `gcd` is odd, larger than one, well formed and not
                // empty, and both operands are well formed and not empty.
                (_, _) => unsafe { div_assign_double(left, right, gcd) },
            }
        }
    }
}

/// Divide out the factors two that two values share, and report which of them came out odd.
///
/// # Safety
///
/// Both values have to be well formed and not zero. That is a memory safety requirement, not just
/// a correctness one.
#[inline]
pub unsafe fn remove_shared_two_factors_mut<const S: usize>(
    left: &mut SmallVec<[usize; S]>,
    right: &mut SmallVec<[usize; S]>,
) -> WhichOdd {
    debug_assert!(is_well_formed_non_zero(left), "the left operand has to be well formed and not zero");
    debug_assert!(is_well_formed_non_zero(right), "the right operand has to be well formed and not zero");

    // SAFETY: Both operands are well formed and not zero by this function's contract.
    let (left_zero_words, left_zero_bits) = unsafe { trailing_zeros(left) };
    // SAFETY: As above.
    let (right_zero_words, right_zero_bits) = unsafe { trailing_zeros(right) };

    let (zero_words, zero_bits) = min((left_zero_words, left_zero_bits), (right_zero_words, right_zero_bits));
    shr_mut(left, zero_words, zero_bits);
    shr_mut(right, zero_words, zero_bits);

    match (left_zero_words, left_zero_bits).cmp(&(right_zero_words, right_zero_bits)) {
        Ordering::Less => {
            let (words, bits) = shift_difference(right_zero_words, right_zero_bits, left_zero_words, left_zero_bits);
            WhichOdd::Left(words, bits)
        },
        Ordering::Equal => WhichOdd::Both,
        Ordering::Greater => {
            let (words, bits) = shift_difference(left_zero_words, left_zero_bits, right_zero_words, right_zero_bits);
            WhichOdd::Right(words, bits)
        },
    }
}

fn shift_difference(left_words: usize, left_bits: u32, right_words: usize, right_bits: u32) -> (usize, u32) {
    debug_assert!(left_words >= right_words);

    if left_bits >= right_bits {
        (left_words - right_words, left_bits - right_bits)
    } else {
        debug_assert!(left_words > right_words);
        (left_words - right_words - 1, BITS_PER_WORD + left_bits - right_bits)
    }
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum WhichOdd {
    Left(usize, u32),
    Right(usize, u32),
    Both,
}

/// Produce two odd start values for [`binary_gcd`] from an odd and an even operand.
///
/// # Safety
///
/// Both operands have to be well formed and not empty, `already_odd` has to be odd and `even` has
/// to have at least `words_to_shift` whole zero words and `bits_to_shift` further zero bits.
#[inline]
unsafe fn prepare_side<const S: usize>(
    already_odd: &SmallVec<[usize; S]>,
    even: &SmallVec<[usize; S]>, words_to_shift: usize, bits_to_shift: u32,
) -> PreparationResult<S> {
    let oddified = shr(even, words_to_shift, bits_to_shift);
    let mut other = match cmp(already_odd, &oddified) {
        Ordering::Less => {
            // left is smallest, subtract it from even_right

            // second start value is known to be positive
            // SAFETY: Both are well formed, and this arm is the one where `oddified` is the larger
            // of the two, which is what the subtraction requires.
            unsafe { sub(&oddified, already_odd) }
        }
        Ordering::Equal => {
            // even = already_odd * 2 ** k with k = words_to_shift * BITS_PER_WORD + bits_to_shift
            return PreparationResult::EqualAfterShift;
        }
        Ordering::Greater => {
            // even_right is smallest, subtract it from left

            // second start value is known to be positive
            // SAFETY: Both are well formed, and this arm is the one where `already_odd` is the
            // larger of the two.
            unsafe { sub(already_odd, &oddified) }
        }
    };

    // other is now even:
    // SAFETY: `other` is the difference of two values that the match above found to be unequal, so
    // it is non zero, and `sub` leaves its result well formed.
    let (zero_words, zero_bits) = unsafe { trailing_zeros(&other) };
    shr_mut(&mut other, zero_words, zero_bits);

    // now both `other` and `oddified` are odd, it is unknown which one is larger
    PreparationResult::StartValues((other, oddified))
}

enum PreparationResult<const S: usize> {
    StartValues((SmallVec<[usize; S]>, SmallVec<[usize; S]>)),
    EqualAfterShift,
}

#[inline]
unsafe fn binary_gcd<const S: usize>(mut left: SmallVec<[usize; S]>, mut right: SmallVec<[usize; S]>) -> SmallVec<[usize; S]> {
    debug_assert!(!left.is_empty() && is_well_formed(&left));
    debug_assert!(!right.is_empty() && is_well_formed(&right));

    loop {
        debug_assert_eq!(left[0] % 2, 1);
        debug_assert_eq!(right[0] % 2, 1);

        match cmp_and_remove(&mut left, &mut right) {
            Ordering::Less => {
                // SAFETY: `right` is the larger of the two, possibly with the most significant
                // words it shares with `left` already removed, which is exactly what this expects.
                unsafe { sub_assign_result_positive(&mut right, &left) };
                // SAFETY: The two were unequal, so their difference is non zero and therefore not
                // empty; `sub_assign_result_positive` pops the trailing zero words it leaves.
                let (zero_words, zero_bits) = unsafe { trailing_zeros(&right) };
                shr_mut(&mut right, zero_words, zero_bits);
            }
            Ordering::Equal => break left,
            Ordering::Greater => {
                // SAFETY: As above, with the roles reversed.
                unsafe { sub_assign_result_positive(&mut left, &right) };
                // SAFETY: As above, with the roles reversed.
                let (zero_words, zero_bits) = unsafe { trailing_zeros(&left) };
                shr_mut(&mut left, zero_words, zero_bits);
            }
        }
    }
}

/// Compare two values, stripping the most significant words they have in common off the larger.
///
/// The caller subtracts the smaller from the larger afterwards; those shared words cancel in that
/// subtraction, so removing them beforehand saves the work. Every access below is bounds checked,
/// so this needs nothing of its operands for memory safety.
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
                        right.truncate(length - nr_equal);
                        return Ordering::Less
                    },
                    Ordering::Equal => {
                        nr_equal += 1;
                    }
                    Ordering::Greater => {
                        left.truncate(length - nr_equal);
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
///
/// # Safety
///
/// `values` must be well formed and not empty. The scan below is what needs it: it walks up from
/// the least significant word without a bound of its own, and only the guarantee that the last
/// word is not zero stops it inside the slice.
#[inline]
pub unsafe fn trailing_zeros(values: &[usize]) -> (usize, u32) {
    debug_assert!(!values.is_empty() && is_well_formed(values));

    let mut zero_words = 0;
    // SAFETY: `values` is not empty, so index zero is in bounds, and every further step is only
    // taken after finding a zero word. The caller guarantees the last word is not zero, so the
    // loop stops at or before it and never reads past the end.
    while unsafe { values.get_unchecked(zero_words) } == &0 {
        // At least the last value is not allowed to be zero, so we don't have to check bounds
        zero_words += 1;
    }

    // SAFETY: The loop above only exits on an index that it found to be in bounds.
    (zero_words, unsafe { values.get_unchecked(zero_words) }.trailing_zeros())
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use smallvec::{smallvec, SmallVec};

    use crate::integer::big::io::from_str_radix;
    use crate::integer::big::ops::non_zero::shr;
    use crate::integer::big::ops::normalize::{binary_gcd, gcd_scalar, gcd_single, prepare_gcd_single, prepare_gcd_single_mut, remove_shared_two_factors_mut, simplify_fraction_gcd, simplify_fraction_gcd_single, simplify_fraction_without_info, trailing_zeros, WhichOdd};
    use crate::integer::big::ops::normalize::gcd;
    use crate::Ubig;

    pub type SV = SmallVec<[usize; 8]>;

    #[test]
    fn test_binary_gcd() {
        unsafe {
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

            // [17182455669393173089, 8195493687874724080, 2236847494119194494]
            // [17628647896610972437, 18063123016434192470, 1524534684235201587]
            let x = from_str_radix::<10, 8>("761159759740049482819703824192566027846076086339694209633").unwrap();
            let y = from_str_radix::<10, 8>("518772270804619926440708190306636065541232071485957284629").unwrap();
            let expected: SV = smallvec![3];
            assert_eq!(binary_gcd(x, y), expected);

            let x = from_str_radix::<10, 8>("13315363230513411010491282670607898860050786975267763235425").unwrap();
            let y = from_str_radix::<10, 8>("518772270804619926440708190306636065541232071485957284629").unwrap();
            let expected: SV = smallvec![1];
            assert_eq!(binary_gcd(x, y), expected);

            // [17182455669393173089, 8195493687874724080, 2236847494119194494, 2]
            // [15546263315196014731, 7428251573324005790, 5285916862589597670, 2]
            let x = from_str_radix::<10, 8>("13315363230513411010491282670607898860050786975267763235425").unwrap();
            let y = from_str_radix::<10, 8>("14352907772122650863372699051221170991133251118239677804683").unwrap();
            let expected: SV = smallvec![1];
            assert_eq!(binary_gcd(x, y), expected);

            let x = from_str_radix::<10, 8>("2537510112612432421162161736760954813703561240667558277280326395321829260829").unwrap();
            let y = from_str_radix::<10, 8>("28066955534242121399724313080842652291012276578744271510348498026737179911481").unwrap();
            let expected: SV = smallvec![1];
            assert_eq!(binary_gcd(x, y), expected);
        }
    }

    #[test]
    fn test_gcd() {
        unsafe {
            let x: SV = smallvec![6];
            let y: SV = smallvec![12];
            assert_eq!(gcd::<8>(&x, &y), x);

            let x: SV = smallvec![131522304505784511, 2433];
            let y: SV = smallvec![15588921427233345156];
            let expected: SV = smallvec![3];
            assert_eq!(gcd::<8>(&x, &y), expected);

            let x: SV = smallvec![15588921427233345156, 28952784];
            let y: SV = smallvec![81331626909];
            let expected: SV = smallvec![81331626909];
            assert_eq!(gcd::<8>(&x, &y), expected);

            let x: SV = smallvec![1202576035807934423, 22];
            let y: SV = smallvec![8031097105200];
            let expected: SV = smallvec![501943569075];
            assert_eq!(gcd::<8>(&x, &y), expected);

            let x: SV = smallvec![5427079275432240933];
            let y: SV = smallvec![8031097105200];
            let expected: SV = smallvec![6692580921];
            assert_eq!(gcd::<8>(&x, &y), expected);

            let x: SV = smallvec![16256560833088857922, 16549708957000594284, 7174888939365837514];
            let y: SV = smallvec![12764522021006322602, 13940785908623865679, 16353990074255549379, 2111485];
            let expected = from_str_radix::<10, 8>("2441488190682268924480702310120250331237912178039550781250").unwrap();
            assert_eq!(gcd::<8>(&x, &y), expected);

            let x: SV = smallvec![0, 16256560833088857922, 16549708957000594284, 7174888939365837514];
            let y: SV = smallvec![0, 12764522021006322602, 13940785908623865679, 16353990074255549379, 2111485];
            let expected = from_str_radix::<10, 8>("45037507812500000000000000000000000000000000000000000000000000000000000000000").unwrap();
            assert_eq!(gcd::<8>(&x, &y), expected);
        }
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
        assert_eq!(unsafe { simplify_fraction_gcd_single(&mut x, 141) }, 47);
        let expected: SV = smallvec![330];
        assert_eq!(x, expected);
    }

    /// The large value can be a multiple of `2 ** BITS_PER_WORD`, in which case its lowest word is
    /// zero and the number of trailing zero bits does not fit in a single word shift.
    #[test]
    fn test_prepare_gcd_single_word_multiple() {
        // 2 ** 64, odd right hand side: nothing is shared, so nothing may be shifted away
        let x: SV = smallvec![0, 1];
        let (large, small, bits) = unsafe { prepare_gcd_single::<8>(&x, 274177) };
        let expected: SV = smallvec![1];
        assert_eq!((large, small, bits), (expected, 274177, 0));

        // 3 * 2 ** 128 and 6 share exactly one factor two
        let x: SV = smallvec![0, 0, 3];
        let (large, small, bits) = unsafe { prepare_gcd_single::<8>(&x, 6) };
        let expected: SV = smallvec![3];
        assert_eq!((large, small, bits), (expected, 3, 1));

        // A value that is odd is unaffected
        let x: SV = smallvec![990];
        let (large, small, bits) = unsafe { prepare_gcd_single::<8>(&x, 141) };
        let expected: SV = smallvec![495];
        assert_eq!((large, small, bits), (expected, 141, 0));
    }

    #[test]
    fn test_prepare_gcd_single_mut_word_multiple() {
        let mut x: SV = smallvec![0, 1]; // 2 ** 64
        let (small, left_words, left_bits, right_bits, shared_bits) = unsafe { prepare_gcd_single_mut(&mut x, 274177) };
        assert_eq!((small, right_bits, shared_bits), (274177, 0, 0));
        let expected: SV = smallvec![0, 1];
        assert_eq!(x, expected);
        // shifting away the reported amount makes the value odd
        let odd: SV = smallvec![1];
        assert_eq!(shr::<8>(&x, left_words, left_bits), odd);

        let mut x: SV = smallvec![0, 0, 3]; // 3 * 2 ** 128
        let (small, left_words, left_bits, right_bits, shared_bits) = unsafe { prepare_gcd_single_mut(&mut x, 6) };
        assert_eq!((small, right_bits, shared_bits), (3, 0, 1));
        let expected: SV = smallvec![0, 1 << 63, 1]; // 3 * 2 ** 127
        assert_eq!(x, expected);
        let odd: SV = smallvec![3];
        assert_eq!(shr::<8>(&x, left_words, left_bits), odd);

        let mut x: SV = smallvec![990];
        let (small, left_words, left_bits, right_bits, shared_bits) = unsafe { prepare_gcd_single_mut(&mut x, 141) };
        assert_eq!((small, left_words, left_bits, right_bits, shared_bits), (141, 0, 1, 0, 0));
        let expected: SV = smallvec![990];
        assert_eq!(x, expected);
    }

    /// `2 ** 64 / 274177` is not an integer; the gcd of the two is one, so nothing may change.
    ///
    /// Note that `274177` divides `2 ** 64 + 1`, which is what a shift by a whole word used to
    /// erroneously produce.
    #[test]
    fn test_simplify_fraction_gcd_single_word_multiple() {
        let mut x: SV = smallvec![0, 1]; // 2 ** 64
        assert_eq!(unsafe { simplify_fraction_gcd_single(&mut x, 274177) }, 274177);
        let expected: SV = smallvec![0, 1];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 0, 1]; // 2 ** 128
        assert_eq!(unsafe { simplify_fraction_gcd_single(&mut x, 274177) }, 274177);
        let expected: SV = smallvec![0, 0, 1];
        assert_eq!(x, expected);

        // Only the shared factors two can be divided out
        let mut x: SV = smallvec![0, 1]; // 2 ** 64
        assert_eq!(unsafe { simplify_fraction_gcd_single(&mut x, 6) }, 3);
        let expected: SV = smallvec![1 << 63]; // 2 ** 63
        assert_eq!(x, expected);

        // 3 * 2 ** 128 and 12 share all of 12
        let mut x: SV = smallvec![0, 0, 3];
        assert_eq!(unsafe { simplify_fraction_gcd_single(&mut x, 12) }, 1);
        let expected: SV = smallvec![0, 1 << 62]; // 2 ** 126
        assert_eq!(x, expected);
    }

    /// Cross check `simplify_fraction_gcd_single` against `u128` arithmetic.
    #[test]
    fn test_simplify_fraction_gcd_single_against_u128() {
        fn gcd_reference(mut left: u128, mut right: u128) -> u128 {
            while right != 0 {
                let next = left % right;
                left = right;
                right = next;
            }
            left
        }

        let mut state = 0x2545f4914f6cdd1d_u64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state as usize
        };

        for _ in 0..(1 << 12) {
            // Cover both a single and a double word value, values with many factors two, and
            // values that are a multiple of 2 ** 64 and so have a zero lowest word
            let low = match next() % 4 {
                0 => 0,
                1 => next().checked_shl((next() % 128) as u32).unwrap_or(0),
                _ => next(),
            };
            let high = next().checked_shr((next() % 128) as u32).unwrap_or(0);
            let right = next() >> (next() % 64);

            let mut values: SV = smallvec![low];
            if high > 0 {
                values.push(high);
            } else if low == 0 {
                continue;
            }

            let value = ((high as u128) << 64) | low as u128;
            if value == 1 || right < 2 {
                continue;
            }

            let gcd = gcd_reference(value, right as u128);
            let quotient = value / gcd;

            let mut expected: SV = smallvec![quotient as usize];
            if quotient >> 64 > 0 {
                expected.push((quotient >> 64) as usize);
            }

            let result = unsafe { simplify_fraction_gcd_single(&mut values, right) };
            assert_eq!(result, right / gcd as usize, "gcd({value}, {right})");
            assert_eq!(values, expected, "gcd({value}, {right})");
        }
    }

    #[test]
    fn test_simplify_without_info() {
        let x = Ubig::<8>::from_str("1208925819614629174706176").unwrap();
        let y = Ubig::<8>::from_str("10301051460877537453973547267843").unwrap();

        let mut xx = x.clone();
        let mut yy = y.clone();
        unsafe { simplify_fraction_without_info(xx.inner_mut(), yy.inner_mut()) };
        assert_eq!(xx, x);
        assert_eq!(yy, y);


        let mut x: SV = smallvec![12384794773201432064, 64560677146];
        let mut y: SV = smallvec![12499693862731150083, 66111026448];
        unsafe { simplify_fraction_without_info(&mut x, &mut y) };
        let xx: SV = smallvec![23800000000];
        let yy: SV = smallvec![24371529219];
        assert_eq!(x, xx);
        assert_eq!(y, yy);
    }

    #[test]
    fn test_simplify_fraction_gcd() {
        unsafe {
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

            let mut left = Ubig::<8>::from_str("92599469589222131768757076514696607382155504523751371565834361998764652118557").unwrap();
            let mut right = Ubig::<8>::from_str("80627506337117343961599775375716501347124738605551411762759133617725727360716").unwrap();
            simplify_fraction_gcd(left.inner_mut(), right.inner_mut());
            let expected_left = Ubig::<8>::from_str("92599469589222131768757076514696607382155504523751371565834361998764652118557").unwrap();
            let expected_right = Ubig::<8>::from_str("80627506337117343961599775375716501347124738605551411762759133617725727360716").unwrap();
            assert_eq!(left, expected_left);
            assert_eq!(right, expected_right);

            let mut left = Ubig::<8>::from_str("56133911068484242799448626161685304582024553157488543020696996053474359822962").unwrap();
            let mut right = Ubig::<8>::from_str("38216995984691851084372960027886471545826521541414504619469803608024496954797").unwrap();
            let mut x = left.clone();
            let mut y = right.clone();
            remove_shared_two_factors_mut(x.inner_mut(), y.inner_mut());
            assert_eq!(x, left);
            assert_eq!(y, right);
            simplify_fraction_gcd(left.inner_mut(), right.inner_mut());
            let expected_left = Ubig::<8>::from_str("56133911068484242799448626161685304582024553157488543020696996053474359822962").unwrap();
            let expected_right = Ubig::<8>::from_str("38216995984691851084372960027886471545826521541414504619469803608024496954797").unwrap();
            assert_eq!(left, expected_left);
            assert_eq!(right, expected_right);

            let mut left = Ubig::<8>::from_str("96149135622564868513332764767713630331755573676701733681721499377985831780603").unwrap();
            let mut right = Ubig::<8>::from_str("99939187751827453177194542570098438266282603262618044779272964070464092694778").unwrap();
            simplify_fraction_gcd(left.inner_mut(), right.inner_mut());
            let expected_left = Ubig::<8>::from_str("32049711874188289504444254922571210110585191225567244560573833125995277260201").unwrap();
            let expected_right = Ubig::<8>::from_str("33313062583942484392398180856699479422094201087539348259757654690154697564926").unwrap();
            assert_eq!(left, expected_left);
            assert_eq!(right, expected_right);
        }
    }

    #[test]
    fn test_remove_shared_two_factors_mut() {
        let mut left: SV = smallvec![3];
        let mut right: SV = smallvec![6];
        let which_odd = unsafe { remove_shared_two_factors_mut(&mut left, &mut right) };
        assert_eq!(which_odd, WhichOdd::Left(0, 1));
        let expected_left: SV = smallvec![3];
        let expected_right: SV = smallvec![6];
        assert_eq!(left, expected_left);
        assert_eq!(right, expected_right);

        let mut left: SV = smallvec![0, 16256560833088857922, 16549708957000594284, 7174888939365837514];
        let mut right: SV = smallvec![0, 16549708957000594284, 16549708957000594284, 7174888939365837514];
        unsafe { remove_shared_two_factors_mut(&mut left, &mut right) };
        let expected_left = from_str_radix::<10, 8>("1220744095341134462240351155060125165618956089019775390625").unwrap();
        let expected_right = from_str_radix::<10, 8>("1220744095341134462240351155060125165619102663081731258806").unwrap();
        assert_eq!(left, expected_left);
        assert_eq!(right, expected_right);

        let mut left: SV = smallvec![0, 12511854210725346487, 1932217123071064976, 10302437120704275430, 18852552];
        let mut right: SV = smallvec![0, 6021696704607738643, 14862474386500622791, 14562584587638410510, 8871];
        unsafe { remove_shared_two_factors_mut(&mut left, &mut right) };
        let expected_left: SV = smallvec![12511854210725346487, 1932217123071064976, 10302437120704275430, 18852552];
        let expected_right: SV = smallvec![6021696704607738643, 14862474386500622791, 14562584587638410510, 8871];
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
        assert_eq!(unsafe { gcd_single::<2>(smallvec![1, 1], 3, 0) }, 1);
        assert_eq!(unsafe { gcd_single::<2>(smallvec![1, 2], 3, 0) }, 3);
        assert_eq!(unsafe { gcd_single::<2>(smallvec![13835058055282163747, 1 << 3], (1 << 62) + 1, 0) }, (1 << 62) + 1);
        assert_eq!(unsafe { gcd_single::<2>(
                smallvec![4611686018427388777, (1 << 7) + (1 << 6) + (1 << 4) + (1 << 3) + (1 << 1)],
                (1 << 62) + 1,
                0,
            ) },
            (1 << 62) + 1,
        );
        assert_eq!(unsafe { gcd_single::<2>(
                smallvec![4611686018427388777, (1 << 7) + (1 << 6) + (1 << 4) + (1 << 3) + (1 << 1)],
                873,
                0,
            ) },
            873,
        );
        assert_eq!(unsafe { gcd_single::<1>(smallvec![7], 3, 0) }, 1);
    }
}
