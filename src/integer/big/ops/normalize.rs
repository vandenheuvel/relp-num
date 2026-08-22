use std::cmp::{max, min, Ordering};

use smallvec::{smallvec, SmallVec};

use crate::integer::big::BITS_PER_WORD;
use crate::integer::big::ops::building_blocks::{is_well_formed, is_well_formed_non_zero, mul_1, submul_1};
use crate::integer::big::ops::div::{div_assign_by_odd, div_assign_double, div_assign_one_word, remainder_one_word};
use crate::integer::big::ops::non_zero::{both_not_one_non_zero, is_one_non_zero, shl_mut, shr, shr_mut, sub};
use crate::integer::big::properties::cmp;

/// Do two values share no factor larger than one?
///
/// # Safety
///
/// Both values have to be well formed and not zero.
#[must_use]
pub unsafe fn is_coprime_non_zero(left: &[usize], right: &[usize]) -> bool {
    debug_assert!(is_well_formed_non_zero(left), "the left operand has to be well formed and not zero");
    debug_assert!(is_well_formed_non_zero(right), "the right operand has to be well formed and not zero");

    const S: usize = 8;

    // SAFETY: The caller guarantees that neither operand is empty.
    if !unsafe { both_not_one_non_zero(left, right) } {
        // One of them is one, which shares nothing with anything.
        return true;
    }

    // Neither is one, so two equal values share themselves.
    if left == right {
        return false;
    }

    // SAFETY: As above: index zero is in bounds for both.
    let both_even = unsafe { left.get_unchecked(0).is_multiple_of(2) && right.get_unchecked(0).is_multiple_of(2) };
    if both_even {
        return false;
    }

    // SAFETY: The caller guarantees that both operands are well formed and not zero.
    let (left_zero_words, left_zero_bits) = unsafe { trailing_zeros(left) };
    // SAFETY: As above.
    let (right_zero_words, right_zero_bits) = unsafe { trailing_zeros(right) };
    let left_odd = shr::<S>(left, left_zero_words, left_zero_bits);
    let right_odd = shr::<S>(right, right_zero_words, right_zero_bits);

    // At most one of the two is even, so the odd part of the one that is has no factor two left to
    // share. An odd part of one then means the operand is a power of two that the other, odd
    // operand shares nothing with.
    // SAFETY: Shifting the trailing zeros out of a non zero value leaves it well formed and not
    // empty.
    if !unsafe { both_not_one_non_zero(&left_odd, &right_odd) } {
        return true;
    }

    // SAFETY: Both odd parts are well formed, not empty and odd, and neither is one.
    let gcd = unsafe { binary_gcd(left_odd, right_odd) };
    // SAFETY: A gcd of two non zero values is not zero and so not empty.
    unsafe { is_one_non_zero(&gcd) }
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

/// Split off the powers of two of a small value, and count the ones it shares with a large value.
///
/// The large value is left alone: its odd part is what a gcd with an odd value depends on, and
/// [`gcd_single`] takes the factors two of its large operand in its stride. Copying the large
/// value only to shift them away would be work for nothing.
///
/// # Returns
///
/// A tuple with the odd part of `right` and the number of factors two that the two values share.
/// That last number is always smaller than [`BITS_PER_WORD`], because `right` is a single, nonzero
/// word.
#[inline]
/// # Safety
///
/// `left` has to be well formed and not zero, and `right` has to be non zero.
pub unsafe fn prepare_gcd_single(left: &[usize], right: usize) -> (usize, u32) {
    // `trailing_zeros` scans upward with unchecked indexing and stops only on a non-zero word, so
    // an operand that is not well formed reads past the end. Note the requirement is well
    // formedness, not just non-emptiness: an all zero vector is non-empty and still runs off.
    debug_assert!(is_well_formed_non_zero(left), "the operand has to be well formed and not zero");
    debug_assert_ne!(right, 0);

    // `left[0]` can be zero, in which case the number of trailing zero bits doesn't fit in a single
    // word: the number of whole zero words is reported separately.
    // SAFETY: `left` is well formed and not zero, which the assertion above establishes.
    let (left_zero_words, left_zero_bits) = unsafe { trailing_zeros(left) };
    let right_zero_bits = right.trailing_zeros();

    (
        right >> right_zero_bits,
        shared_zero_bits(left_zero_words, left_zero_bits, right_zero_bits),
    )
}

/// Divide out the powers of two that a large and a small value share.
///
/// `left` is shifted right by the number of factors two the two values share. It is not made odd:
/// what factors two it has left over are not shared, so no caller needs them gone.
///
/// # Returns
///
/// A tuple with the small value shifted right by the shared number of factors two, and the odd
/// part of the small value.
#[inline]
/// # Safety
///
/// `left` has to be well formed and not zero, and `right` has to be non zero.
pub unsafe fn prepare_gcd_single_mut<const S: usize>(
    left: &mut SmallVec<[usize; S]>, right: usize,
) -> (usize, usize) {
    // `trailing_zeros` scans upward with unchecked indexing and stops only on a non-zero word, so
    // an operand that is not well formed reads past the end. Note the requirement is well
    // formedness, not just non-emptiness: an all zero vector is non-empty and still runs off.
    debug_assert!(is_well_formed_non_zero(left), "the operand has to be well formed and not zero");
    debug_assert_ne!(right, 0);

    // `left[0]` can be zero, in which case the number of trailing zero bits doesn't fit in a single
    // word: the number of whole zero words is reported separately.
    // SAFETY: `left` is well formed and not zero, which the assertion above establishes.
    let (left_zero_words, left_zero_bits) = unsafe { trailing_zeros(left) };
    let right_zero_bits = right.trailing_zeros();

    let zero_bits = shared_zero_bits(left_zero_words, left_zero_bits, right_zero_bits);
    shr_mut(left, 0, zero_bits);

    (right >> zero_bits, right >> right_zero_bits)
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

/// The greatest common divisor of a large and a small value, shifted left by `bits`.
///
/// `large` does not have to be odd: `small` is, so the factors two of `large` are not shared and
/// do not affect the result. `bits` is the number of factors two the caller split off before
/// calling, which are shifted back into the result.
#[inline]
/// # Safety
///
/// `large` has to be well formed and not zero, and `small` has to be odd.
pub unsafe fn gcd_single(large: &[usize], small: usize, bits: u32) -> usize {
    debug_assert!(is_well_formed_non_zero(large), "the operand has to be well formed and not zero");
    debug_assert_eq!(small % 2, 1);

    let left = if large.len() > 1 {
        // `gcd(large, small) == gcd(small, large % small)`, and that remainder is a single word.
        // One division pass replaces a subtract and shift loop that gives up about two bits of
        // `large` per step while walking all of its words on every one of them.
        // SAFETY: `large` is well formed and not zero by this function's contract, and `small` is
        // not zero because it is odd.
        let remainder = unsafe { remainder_one_word(large, small) };
        if remainder == 0 {
            // `small` divides `large`.
            return small << bits;
        }

        remainder
    } else {
        // SAFETY: `large` is not empty, so index zero is in bounds.
        unsafe { *large.get_unchecked(0) }
    };

    // `small` is odd, so it shares no factor two with the other operand.
    gcd_scalar_odd(left >> left.trailing_zeros(), small) << bits
}

/// The greatest common divisor of two odd, non zero words.
///
/// Both operands staying odd is what makes the shift below exact: their difference is even, and
/// shifting its factors two away cannot drop a factor the two share.
///
/// Which operand is the larger is a coin flip on every round, so a comparison that picks a branch
/// mispredicts half the time. Phrased as `min`/`max`, both halves of the choice compile to
/// conditional moves and the loop carries no branch other than its exit. The zero count runs on
/// the wrapped difference, which has the trailing zeros of the absolute one, so it does not wait
/// for the sign to be resolved.
#[inline]
fn gcd_scalar_odd(mut left: usize, mut right: usize) -> usize {
    debug_assert_eq!(left % 2, 1);
    debug_assert_eq!(right % 2, 1);

    loop {
        let difference = left.wrapping_sub(right);
        if difference == 0 {
            break left;
        }

        let zeros = difference.trailing_zeros();
        let smaller = min(left, right);
        let larger = left.max(right);
        right = smaller;
        left = (larger - smaller) >> zeros;
    }
}

#[inline]
pub fn gcd_scalar(left: usize, right: usize) -> usize {
    debug_assert_ne!(left, 0);
    debug_assert_ne!(right, 0);
    debug_assert_ne!(left, right);

    let left_zeros = left.trailing_zeros();
    let right_zeros = right.trailing_zeros();

    gcd_scalar_odd(left >> left_zeros, right >> right_zeros) << min(left_zeros, right_zeros)
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
    let (mut right, right_odd) = unsafe { prepare_gcd_single_mut(left, right) };

    if right_odd > 1 {
        // `right_odd` is odd, so the factors two that `left` has left over are not shared with it
        // and cannot divide the gcd: `left` goes in as it is, rather than as an odd copy.
        // SAFETY: Shifting a non zero value right by factors two it has leaves it well formed and
        // not empty, and `right_odd` is odd.
        let gcd = unsafe { gcd_single(left, right_odd, 0) };

        if gcd > 1 {
            right /= gcd;
            // SAFETY: `gcd` divides the odd part of `left`, so it divides `left` exactly, and it
            // is odd because it divides the odd `right_odd`.
            unsafe { div_assign_one_word(left, gcd) };
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
                    // `right` is `left` times a power of two, so the fraction reduces to that
                    // power of two over one.
                    left.truncate(1);
                    left[0] = 1;
                    right.truncate(words_to_shift + 1);
                    right[..words_to_shift].fill(0);
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
                    // As above, with the roles reversed.
                    right.truncate(1);
                    right[0] = 1;
                    left.truncate(words_to_shift + 1);
                    left[..words_to_shift].fill(0);
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

/// The number of words that fit in the widest type the reduction can finish in.
const DOUBLE_WORDS: usize = (128 / BITS_PER_WORD) as usize;

/// Finish a reduction whose operands both fit in [`DOUBLE_WORDS`] words.
///
/// The buffer of `left` is reused for the result, so this allocates nothing.
#[inline]
fn finish_in_registers<const S: usize>(
    mut left: SmallVec<[usize; S]>, right: &[usize],
) -> SmallVec<[usize; S]> {
    debug_assert!(!left.is_empty() && left.len() <= DOUBLE_WORDS);
    debug_assert!(!right.is_empty() && right.len() <= DOUBLE_WORDS);

    if left.len() == 1 && right.len() == 1 {
        // A single word each is the common case and does not need the double width arithmetic,
        // which costs several instructions per operation rather than one.
        // SAFETY: Both have exactly one word, so index zero is in bounds for both.
        let value = unsafe { gcd_scalar_odd(*left.get_unchecked(0), *right.get_unchecked(0)) };
        // SAFETY: As above.
        unsafe { *left.get_unchecked_mut(0) = value };

        return left;
    }

    finish_in_double(left, right)
}

/// The double width half of [`finish_in_registers`].
///
/// Kept out of line deliberately. Its caller is inlined into code that reduces small fractions,
/// where this arm is never reached, and letting the double width arithmetic and the write back
/// land there costs those callers more than the call costs this one.
#[inline(never)]
fn finish_in_double<const S: usize>(
    mut left: SmallVec<[usize; S]>, right: &[usize],
) -> SmallVec<[usize; S]> {
    let mut value = gcd_double_odd(to_double(&left), to_double(right));
    debug_assert_ne!(value, 0);

    left.clear();
    while value > 0 {
        left.push(value as usize);
        value >>= BITS_PER_WORD;
    }

    left
}

#[inline]
fn to_double(values: &[usize]) -> u128 {
    debug_assert!(values.len() <= DOUBLE_WORDS);

    let mut result = 0;
    for (index, value) in values.iter().enumerate() {
        result |= (*value as u128) << (index as u32 * BITS_PER_WORD);
    }

    result
}

/// The greatest common divisor of two odd, non zero double width values.
///
/// This is [`gcd_scalar_odd`] one type wider; see there for why the shift is exact and why the
/// loop is phrased without a swap.
///
/// Every double width operation below costs a multiple of its single width version, while the
/// reduction shrinks both operands by a couple of bits per round: once both fit in a word, which
/// is most of every reduction's rounds, the single width loop finishes the job in a fraction of
/// the time. A Euclid style loop with register sized quotients was tried here and lost: its
/// quotient tests branch on data that is an even coin flip per step, and the mispredictions cost
/// more than the larger steps saved, where this loop decides everything with conditional moves.
#[inline]
fn gcd_double_odd(mut left: u128, mut right: u128) -> u128 {
    debug_assert_eq!(left % 2, 1);
    debug_assert_eq!(right % 2, 1);

    loop {
        if (left | right) >> BITS_PER_WORD == 0 {
            break gcd_scalar_odd(left as usize, right as usize) as u128;
        }

        let difference = left.wrapping_sub(right);
        if difference == 0 {
            break left;
        }

        let zeros = difference.trailing_zeros();
        let smaller = min(left, right);
        let larger = left.max(right);
        right = smaller;
        left = (larger - smaller) >> zeros;
    }
}

#[inline]
pub(crate) unsafe fn binary_gcd<const S: usize>(mut left: SmallVec<[usize; S]>, mut right: SmallVec<[usize; S]>) -> SmallVec<[usize; S]> {
    debug_assert!(!left.is_empty() && is_well_formed(&left));
    debug_assert!(!right.is_empty() && is_well_formed(&right));

    loop {
        debug_assert_eq!(left[0] % 2, 1);
        debug_assert_eq!(right[0] % 2, 1);

        if left.len() <= DOUBLE_WORDS && right.len() <= DOUBLE_WORDS {
            // Both operands have shrunk to values that fit in registers, so the rest of the
            // reduction needs none of the machinery below. Every reduction ends here, whatever
            // size it started at.
            break finish_in_registers(left, &right);
        }

        let (large, small) = match cmp(&left, &right) {
            Ordering::Less => (&mut right, &mut left),
            Ordering::Equal => break left,
            Ordering::Greater => (&mut left, &mut right),
        };

        let large_bits = bit_length(large);
        let small_bits = bit_length(small);
        if large_bits > small_bits + BITS_PER_WORD as usize {
            // The quotient of the two does not fit in a word, so no round of simulated steps can
            // bridge the difference: its quotients are single words, and a round would grind the
            // gap down a word at a time at best. One word of schoolbook division per pass closes
            // in on the smaller value faster, and the round below takes over once quotients fit.
            reduce_gap(large, small, large_bits, small_bits);
            continue;
        }

        // One Lehmer round: simulate Euclid steps on the leading bits of both operands in
        // registers, then apply the accumulated matrix to the full values in a single pass each.
        // A subtraction pass over the full operands gives up only a bit or two of their length;
        // a round gives up what the simulated steps consumed, typically most of a word, for the
        // same number of passes.
        let shift = large_bits - (2 * BITS_PER_WORD - 1) as usize;
        let matrix = simulate_euclid_steps(
            high_double_word(large, shift),
            high_double_word(small, shift),
        );
        // The first simulated step always commits: either the leading bits decide a quotient, or
        // they are too close to call, which the operands being unequal resolves to a quotient of
        // one. The matrix is therefore never the identity.
        debug_assert_ne!(matrix.small_factors.0, 0);

        let (new_large, new_small) = matrix.apply(large, small);

        // The simulated steps are true Euclid steps, so the results are members of the remainder
        // sequence of the two operands: a step landing exactly on zero ends the reduction with the
        // other value, which divides both operands and is their gcd.
        if new_small.is_empty() {
            debug_assert!(!new_large.is_empty());
            break new_large;
        }
        if new_large.is_empty() {
            break new_small;
        }

        // The gcd of two odd values is odd, so the factors two a remainder picks up are not part
        // of it and shrink the operands for free.
        // SAFETY: Both values were just checked to be non zero, and `apply` normalizes.
        let (zero_words, zero_bits) = unsafe { trailing_zeros(&new_large) };
        *large = new_large;
        shr_mut(large, zero_words, zero_bits);
        // SAFETY: As above.
        let (zero_words, zero_bits) = unsafe { trailing_zeros(&new_small) };
        *small = new_small;
        shr_mut(small, zero_words, zero_bits);
    }
}

/// The number of bits in a value, which is one more than the position of its highest set bit.
#[inline]
fn bit_length(values: &[usize]) -> usize {
    debug_assert!(is_well_formed_non_zero(values));

    values.len() * BITS_PER_WORD as usize - values.last().unwrap().leading_zeros() as usize
}

/// The value divided by `2 ** shift`, of which the caller knows that it fits in a double word.
#[inline]
fn high_double_word(values: &[usize], shift: usize) -> u128 {
    debug_assert!(bit_length(values) <= shift + 2 * BITS_PER_WORD as usize);

    let word = shift / BITS_PER_WORD as usize;
    let bit = (shift % BITS_PER_WORD as usize) as u32;

    // A shorter value simply has zeros beyond its top; the quotient is what matters, not the
    // length, so the missing words are read as such rather than making the caller align anything.
    let get = |index: usize| values.get(index).copied().unwrap_or(0) as u128;

    let low = get(word) | (get(word + 1) << BITS_PER_WORD);
    if bit > 0 {
        (low >> bit) | (get(word + 2) << (2 * BITS_PER_WORD - bit))
    } else {
        low
    }
}

/// Cosequence magnitudes accumulated by [`simulate_euclid_steps`].
///
/// The fields hold the two columns of the matrix taking the original operands to the current
/// remainder pair: the factors that multiply the larger operand and those that multiply the
/// smaller one. In terms of those magnitudes `(a, c)` and `(b, d)`, the matrix is
/// `[[+a, -b], [-c, +d]]` after an even number of Euclid steps and `[[-a, +b], [+c, -d]]` after
/// an odd number: every step swaps the rows and flips the signs of one of them, so the signs
/// alternate with the parity and never need to be stored.
struct StepMatrix {
    large_factors: (usize, usize),
    small_factors: (usize, usize),
    even: bool,
}

/// Simulate Euclid steps on the leading bits of two values.
///
/// `a_hat` and `b_hat` are the leading bits of two values `a >= b`, cut off at the same bit
/// position, so that `a = (a_hat + x) * 2 ** shift` and `b = (b_hat + y) * 2 ** shift` for some
/// unknown `x` and `y` in `[0, 1)`. The returned matrix `M` is unimodular and such that
/// `M * (a, b)` is a pair of consecutive members of a valid remainder sequence of `a` and `b`: it
/// shares their gcd, and both entries are non negative.
///
/// Each simulated step uses a quotient that provably does not exceed the quotient of the true
/// values, whatever `x` and `y` are. An underestimated quotient still makes a valid remainder
/// step; it merely leaves more for the next step, so certainty about the quotient's exact value
/// is not needed, and the single lower bound below replaces the classical test that computes the
/// quotient from both ends of the uncertainty interval.
#[inline]
fn simulate_euclid_steps(mut a_hat: u128, mut b_hat: u128) -> StepMatrix {
    debug_assert!(a_hat >= b_hat);
    debug_assert!(a_hat < 1_u128 << (2 * BITS_PER_WORD - 1));

    let (mut a0, mut b0): (usize, usize) = (1, 0);
    let (mut c0, mut d0): (usize, usize) = (0, 1);
    let mut even = true;

    loop {
        // The true current remainders lie in `(a_hat - numerator_sub, a_hat + _)` and
        // `(b_hat - _, b_hat + denominator_add)`: the uncertainty `x` and `y` of the original
        // operands, amplified by the matrix entries. Shrinking the numerator and growing the
        // denominator by those margins makes the quotient below a lower bound on the true one.
        let (numerator_sub, denominator_add) = if even { (b0, d0) } else { (a0, c0) };

        if a_hat < numerator_sub as u128 {
            break;
        }
        let numerator = a_hat - numerator_sub as u128;
        let denominator = b_hat + denominator_add as u128;

        let quotient = if numerator < denominator {
            if b0 == 0 {
                // No step is committed yet, and the caller guarantees `a >= b`... but the leading
                // bits are too close to call. `a > b` holds whenever the operands differ (the
                // caller broke off on equality), so a first step with quotient one is valid even
                // though the leading bits cannot confirm it.
                1
            } else {
                break;
            }
        } else if numerator >> 1 < denominator {
            // Small quotients dominate: each value `q` shows up in about `log2(1 + 1 / (q * (q + 2)))`
            // of all steps, so one through seven cover five out of every six. Comparing against
            // small multiples of the denominator resolves them exactly for a fraction of what the
            // division below costs. Exactly, because an underestimate here is a false economy: a
            // step short of the true quotient leaves a remainder above the denominator, and the
            // step that cleans that up costs more than the division that was saved.
            1
        } else if numerator < denominator * 3 {
            2
        } else if numerator >> 2 < denominator {
            3
        } else if numerator >> 3 < denominator {
            if numerator < denominator * 6 {
                if numerator < denominator * 5 { 4 } else { 5 }
            } else if numerator < denominator * 7 {
                6
            } else {
                7
            }
        } else {
            // A single word division on the leading word of the numerator. Cutting both operands
            // by the same amount and dividing by one more than the cut denominator keeps the
            // quotient an underestimate whatever is cut off, so no double width division is ever
            // needed; while the denominator reaches past the cut, the estimate is off by at most
            // about one part in `2 ** (BITS_PER_WORD - 1)`, and when it does not, the estimate is
            // merely crude and the steps that follow pick up what it left behind.
            let cut = (2 * BITS_PER_WORD - numerator.leading_zeros()).saturating_sub(BITS_PER_WORD);
            // The denominator is at most half the numerator here, so the `+ 1` cannot overflow.
            (numerator >> cut) as usize / ((denominator >> cut) as usize + 1)
        };

        // The updated entries are sums of products of previous ones, so they are additive in the
        // magnitudes whatever the signs; overflowing a word is the natural end of the round,
        // checked before anything is committed.
        let Some(c_new) = quotient.checked_mul(c0).and_then(|value| value.checked_add(a0)) else {
            break;
        };
        let Some(d_new) = quotient.checked_mul(d0).and_then(|value| value.checked_add(b0)) else {
            break;
        };

        // The quotient is at most `a_hat / b_hat`, so this product does not exceed `a_hat`.
        let product = quotient as u128 * b_hat;
        debug_assert!(product <= a_hat);

        (a0, c0) = (c0, c_new);
        (b0, d0) = (d0, d_new);
        (a_hat, b_hat) = (b_hat, a_hat - product);
        even = !even;
    }

    StepMatrix { large_factors: (a0, c0), small_factors: (b0, d0), even }
}

/// Subtract a word sized multiple of `small`, shifted up under the top of `large`, from `large`.
///
/// This is one word of schoolbook division, keeping only the remainder: the multiplier is an
/// underestimate of `large / (small * 2 ** exponent)` computed from the leading bits of both, with
/// the exponent lining the product up one word below the top of `large`. Each pass removes almost
/// a whole word of `large`'s length. Subtracting an underestimate rather than the exact quotient
/// keeps the result non negative without a correction step, at the price of leaving at most a few
/// bits more behind for the next pass.
///
/// `large` stays odd: the subtracted multiple carries the factor `2 ** exponent`, which is even.
#[inline]
fn reduce_gap<const S: usize>(
    large: &mut SmallVec<[usize; S]>, small: &[usize], large_bits: usize, small_bits: usize,
) {
    debug_assert_eq!(bit_length(large), large_bits);
    debug_assert_eq!(bit_length(small), small_bits);
    debug_assert!(large_bits > small_bits + BITS_PER_WORD as usize);

    let exponent = large_bits - small_bits - BITS_PER_WORD as usize;
    let words = exponent / BITS_PER_WORD as usize;
    let bits = (exponent % BITS_PER_WORD as usize) as u32;

    // An underestimate of `large / (small * 2 ** exponent)`, which by the choice of exponent is
    // about a word: divide the leading bits of `large` by one more than the leading bits of
    // `small`, scale correction and word cap included. This single wide division pays for a whole
    // word of progress.
    let cut = small_bits.saturating_sub((BITS_PER_WORD - 1) as usize);
    let small_top = high_double_word(small, cut);
    let mut quotient = high_double_word(large, large_bits - (2 * BITS_PER_WORD - 1) as usize) / (small_top + 1);
    if small_bits < (BITS_PER_WORD - 1) as usize {
        quotient >>= (BITS_PER_WORD - 1) as usize - small_bits;
    }
    let quotient = usize::try_from(quotient).unwrap_or(usize::MAX);
    debug_assert!(quotient >= 1);

    // `small << bits`, at most one word longer than `small` itself.
    let mut shifted: SmallVec<[usize; S]> = SmallVec::with_capacity(small.len() + 1);
    if bits > 0 {
        let mut previous = 0;
        for &word in small {
            shifted.push((word << bits) | (previous >> (BITS_PER_WORD - bits)));
            previous = word;
        }
        let top = previous >> (BITS_PER_WORD - bits);
        if top > 0 {
            shifted.push(top);
        }
    } else {
        shifted.extend_from_slice(small);
    }

    let mut borrow = submul_1(&mut large[words..], &shifted, quotient);
    for word in &mut large[words + shifted.len()..] {
        let (value, underflow) = word.overflowing_sub(borrow);
        *word = value;
        borrow = usize::from(underflow);
        if borrow == 0 {
            break;
        }
    }
    // The subtracted multiple does not exceed `large`, so nothing borrows out of the top.
    debug_assert_eq!(borrow, 0);

    while let Some(0) = large.last() {
        large.pop();
    }
}

impl StepMatrix {
    /// Multiply the matrix onto a pair of values, producing the remainder pair it encodes.
    ///
    /// The results are members of the remainder sequence of `large` and `small`, so both are
    /// smaller than `large` and non negative; either can be zero, which comes back as an empty
    /// value.
    #[inline]
    fn apply<const S: usize>(
        &self, large: &[usize], small: &[usize],
    ) -> (SmallVec<[usize; S]>, SmallVec<[usize; S]>) {
        let StepMatrix { large_factors: (a0, c0), small_factors: (b0, d0), even } = *self;

        if even {
            (mul_sub(a0, large, b0, small), mul_sub(d0, small, c0, large))
        } else {
            (mul_sub(b0, small, a0, large), mul_sub(c0, large, d0, small))
        }
    }
}

/// The value `p * x - q * y` for single word `p` and `q`.
///
/// The caller guarantees the result to be non negative and, like any member of a remainder
/// sequence, to fit in the longer of the two operands. Zero comes back as an empty value.
#[inline]
fn mul_sub<const S: usize>(p: usize, x: &[usize], q: usize, y: &[usize]) -> SmallVec<[usize; S]> {
    debug_assert_ne!(p, 0);
    debug_assert!(!x.is_empty() && !y.is_empty());

    let length = max(x.len(), y.len());
    let mut result: SmallVec<[usize; S]> = smallvec![0; length];

    let carry = mul_1(&mut result[..x.len()], x, p);
    let mut top = 0;
    if x.len() < length {
        result[x.len()] = carry;
    } else {
        // The word that carries out of the buffer has nowhere to go; the subtraction below
        // borrows it back out exactly, because the result fits in the buffer.
        top = carry;
    }

    let mut borrow = submul_1(&mut result, y, q);
    for word in &mut result[y.len()..] {
        let (value, underflow) = word.overflowing_sub(borrow);
        *word = value;
        borrow = usize::from(underflow);
        if borrow == 0 {
            break;
        }
    }
    debug_assert_eq!(borrow, top);

    while let Some(0) = result.last() {
        result.pop();
    }

    result
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
    use crate::integer::big::ops::building_blocks::{carrying_add_mut, is_well_formed};
    use crate::integer::big::ops::non_zero::mul_non_zero;
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

    /// Cross check the multi word reduction against gcds computed with exact arithmetic.
    ///
    /// The cases mix operand sizes, a shared factor of a few hundred bits, a shared factor two and
    /// no shared factor at all, so that the reduction runs its multi word loop before it hands the
    /// rest over to the register sized fall back.
    #[test]
    fn test_gcd_reference_values() {
        fn check(left: &str, right: &str, expected: &str) {
            let left = from_str_radix::<10, 8>(left).unwrap();
            let right = from_str_radix::<10, 8>(right).unwrap();
            let expected = from_str_radix::<10, 8>(expected).unwrap();

            assert_eq!(unsafe { gcd::<8>(&left, &right) }, expected);
            // The gcd does not depend on the order of its operands
            assert_eq!(unsafe { gcd::<8>(&right, &left) }, expected);
        }

        check("5980220570715833490615347621719249082293063617401987405914", "6041796650217286684758509240821568029314711084489978334511", "1");
        check("96186139669315669286795890417045573988776571354132943926392606084135974944448", "5342870304023229578347254063586389621433946210795527438856", "8");
        check("1377344265989479829734791070787953490665239224694232894392180246934971164638904198212151838925852", "280898646957146188696570948218805650555", "1");
        check("3440389326964952843057260961354545726333197307600201480504243646518405419454294551421652300611776", "3780409380902139358048957106916618941864663041505879825848189151278812980010694720952466069937376", "1581229434425844153644537079707791400096");
        check("33040940719343206864890271868662550629599584254689061382445833219573830485726360115105125280517123110050141791522156379031270294812843917600738861577836514744378686471012473725", "127371735598373583861786076011736002916090731578758352346735603802015902323072221277058585892476235791542148686414154044996791675557695025", "3700128231432930918326766317075445671211554162448679302139275");
        check("1023252987299016841533870263425231730508862118967216225750764660190838265954255348065817221787128", "1293952258958624867620379547592971490806513826554373256803404505348879862627623245817342285447304", "33467907793400953496");
        check("1805470657352698014196789547994947146325104095726116408477835014627109088790297405931869796673469", "2058527418669397385879012659391228444069189964404255587402144910976167759048288184781847570037608", "1");
        check("16719076066866201936912145143271387284233845045525627699043748426168633999699788800261397671426974604915276030965422650447171652549468043641170769558268775240279605758916779627084117447704336623156643711571400949636670246553631789248231248444568", "2813909279938232501258637705332641443573692088462671992360262407309344264411975071031104431295428451930775178161770529981685118781355014974374688179279571115684871313651622971594739901360", "1653650929223887310197130497400344829595384098828559533780726349020130812745509712258905464");
    }

    /// Cross check the multi word reduction against an independent implementation, over random
    /// operands shaped to reach every path: plain random pairs, pairs with a planted many word
    /// common factor, near equal pairs whose leading bits agree, and pairs of very different
    /// lengths.
    #[test]
    fn test_binary_gcd_against_reference() {
        use std::cmp::Ordering;

        /// Subtract and shift binary gcd on odd operands, written directly against `Vec` and
        /// shared with nothing under test.
        fn reference_gcd(mut left: Vec<usize>, mut right: Vec<usize>) -> Vec<usize> {
            fn compare(left: &[usize], right: &[usize]) -> Ordering {
                left.len().cmp(&right.len()).then_with(|| left.iter().rev().cmp(right.iter().rev()))
            }

            /// `left - right` for `left >= right`, normalized.
            fn subtract(left: &[usize], right: &[usize]) -> Vec<usize> {
                let mut result = Vec::with_capacity(left.len());
                let mut borrow = false;
                for (index, &word) in left.iter().enumerate() {
                    let (value, first) = word.overflowing_sub(right.get(index).copied().unwrap_or(0));
                    let (value, second) = value.overflowing_sub(usize::from(borrow));
                    result.push(value);
                    borrow = first || second;
                }
                assert!(!borrow);
                while result.last() == Some(&0) {
                    result.pop();
                }
                result
            }

            /// Shift out all trailing zeros of a non zero value.
            fn make_odd(value: &mut Vec<usize>) {
                let words = value.iter().position(|&word| word != 0).unwrap();
                value.drain(..words);
                let bits = value[0].trailing_zeros();
                if bits > 0 {
                    for index in 0..value.len() {
                        value[index] >>= bits;
                        if let Some(&next) = value.get(index + 1) {
                            value[index] |= next << (usize::BITS - bits);
                        }
                    }
                    while value.last() == Some(&0) {
                        value.pop();
                    }
                }
            }

            loop {
                match compare(&left, &right) {
                    Ordering::Equal => break left,
                    Ordering::Greater => {
                        left = subtract(&left, &right);
                        make_odd(&mut left);
                    }
                    Ordering::Less => {
                        right = subtract(&right, &left);
                        make_odd(&mut right);
                    }
                }
            }
        }

        let mut state = 0x853c49e6748fea9b_u64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state as usize
        };

        fn random_odd(words: usize, next: &mut impl FnMut() -> usize) -> SV {
            let mut value: SV = (0..words).map(|_| next()).collect();
            value[0] |= 1;
            while let Some(0) = value.last() {
                value.pop();
            }
            value
        }

        for round in 0..2_000 {
            let (left, right): (SV, SV) = match round % 4 {
                0 => {
                    // Plain random pairs of up to eight words
                    (random_odd(1 + next() % 8, &mut next), random_odd(1 + next() % 8, &mut next))
                }
                1 => {
                    // A planted common factor of up to three words
                    let shared = random_odd(1 + next() % 3, &mut next);
                    let left = unsafe { mul_non_zero::<8>(&random_odd(1 + next() % 5, &mut next), &shared) };
                    let right = unsafe { mul_non_zero::<8>(&random_odd(1 + next() % 5, &mut next), &shared) };
                    (left, right)
                }
                2 => {
                    // Near equal pairs, whose leading bits agree for several words
                    let base = random_odd(3 + next() % 6, &mut next);
                    let mut other = base.clone();
                    let difference = next() >> (next() % (usize::BITS as usize));
                    // Adding an even difference to an odd value keeps it odd, and any carry stays
                    // within one extra word.
                    let mut carry = false;
                    carrying_add_mut(&mut other[0], difference & !1, &mut carry);
                    let mut index = 1;
                    while carry {
                        if index == other.len() {
                            other.push(0);
                        }
                        carrying_add_mut(&mut other[index], 0, &mut carry);
                        index += 1;
                    }
                    (base, other)
                }
                _ => {
                    // Very different lengths, which the leading bits cannot bridge
                    (random_odd(1 + next() % 2, &mut next), random_odd(5 + next() % 4, &mut next))
                }
            };

            if left == right {
                continue;
            }

            let expected = reference_gcd(left.to_vec(), right.to_vec());
            let result = unsafe { binary_gcd(left.clone(), right.clone()) };
            assert_eq!(result.to_vec(), expected, "gcd({left:?}, {right:?})");
            assert!(is_well_formed(&result));
        }
    }

    /// Cross check the register sized fall back of the reduction against `u128` arithmetic.
    #[test]
    fn test_binary_gcd_against_u128() {
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

        for _ in 0..(1 << 14) {
            // `binary_gcd` takes odd operands, over one or two words each so that both arms of the
            // fall back are covered, including the two where the lengths differ
            let mut make = || {
                let low = next() | 1;
                let high = next().checked_shr((next() % 128) as u32).unwrap_or(0);
                let mut value: SV = smallvec![low];
                if high > 0 {
                    value.push(high);
                }
                value
            };
            let left = make();
            let right = make();

            let as_u128 = |value: &SV| value.iter().rev().fold(0_u128, |acc, word| (acc << 64) | *word as u128);
            let expected = gcd_reference(as_u128(&left), as_u128(&right));

            let result = unsafe { binary_gcd(left.clone(), right.clone()) };
            assert_eq!(as_u128(&result), expected, "gcd({:?}, {:?})", left, right);
            assert!(is_well_formed(&result));
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
        // 2 ** 64, odd right hand side: nothing is shared
        let x: SV = smallvec![0, 1];
        assert_eq!(unsafe { prepare_gcd_single(&x, 274177) }, (274177, 0));

        // 3 * 2 ** 128 and 6 share exactly one factor two
        let x: SV = smallvec![0, 0, 3];
        assert_eq!(unsafe { prepare_gcd_single(&x, 6) }, (3, 1));

        // An odd right hand side shares nothing, whatever the left hand side is
        let x: SV = smallvec![990];
        assert_eq!(unsafe { prepare_gcd_single(&x, 141) }, (141, 0));

        // Both even: the smaller number of factors two is shared
        let x: SV = smallvec![990]; // 2 * 495
        assert_eq!(unsafe { prepare_gcd_single(&x, 12) }, (3, 1));
        let x: SV = smallvec![1 << 4];
        assert_eq!(unsafe { prepare_gcd_single(&x, 12) }, (3, 2));
    }

    #[test]
    fn test_prepare_gcd_single_mut_word_multiple() {
        let mut x: SV = smallvec![0, 1]; // 2 ** 64
        // The right hand side is odd, so nothing is shared and nothing is shifted away
        assert_eq!(unsafe { prepare_gcd_single_mut(&mut x, 274177) }, (274177, 274177));
        let expected: SV = smallvec![0, 1];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 0, 3]; // 3 * 2 ** 128
        assert_eq!(unsafe { prepare_gcd_single_mut(&mut x, 6) }, (3, 3));
        let expected: SV = smallvec![0, 1 << 63, 1]; // 3 * 2 ** 127
        assert_eq!(x, expected);

        let mut x: SV = smallvec![990];
        assert_eq!(unsafe { prepare_gcd_single_mut(&mut x, 141) }, (141, 141));
        let expected: SV = smallvec![990];
        assert_eq!(x, expected);

        // Both even: the one shared factor two comes out of both
        let mut x: SV = smallvec![990]; // 2 * 495
        assert_eq!(unsafe { prepare_gcd_single_mut(&mut x, 12) }, (6, 3));
        let expected: SV = smallvec![495];
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
                1 => next().unbounded_shl((next() % 128) as u32),
                _ => next(),
            };
            let high = next().unbounded_shr((next() % 128) as u32);
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
        assert_eq!(unsafe { gcd_single(&[1, 1], 3, 0) }, 1);
        assert_eq!(unsafe { gcd_single(&[1, 2], 3, 0) }, 3);
        assert_eq!(unsafe { gcd_single(&[13835058055282163747, 1 << 3], (1 << 62) + 1, 0) }, (1 << 62) + 1);
        assert_eq!(unsafe { gcd_single(
                &[4611686018427388777, (1 << 7) + (1 << 6) + (1 << 4) + (1 << 3) + (1 << 1)],
                (1 << 62) + 1,
                0,
            ) },
            (1 << 62) + 1,
        );
        assert_eq!(unsafe { gcd_single(
                &[4611686018427388777, (1 << 7) + (1 << 6) + (1 << 4) + (1 << 3) + (1 << 1)],
                873,
                0,
            ) },
            873,
        );
        assert_eq!(unsafe { gcd_single(&[7], 3, 0) }, 1);

        // The large operand does not have to be odd: `small` is, so shared factors two cannot
        // exist and the caller does not have to shift them away first.
        assert_eq!(unsafe { gcd_single(&[0, 3], 3, 0) }, 3);
        assert_eq!(unsafe { gcd_single(&[12], 9, 0) }, 3);
        // The shared factors two the caller split off are shifted back into the result.
        assert_eq!(unsafe { gcd_single(&[0, 3], 3, 2) }, 3 << 2);
    }

    /// Cross check `gcd_single` against `u128` arithmetic, over values of one and two words.
    #[test]
    fn test_gcd_single_against_u128() {
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

        for _ in 0..(1 << 14) {
            // Cover values with many factors two and values that are a multiple of `2 ** 64` and
            // so have a zero lowest word
            let low = match next() % 4 {
                0 => 0,
                1 => next().unbounded_shl((next() % 128) as u32),
                _ => next(),
            };
            let high = next().unbounded_shr((next() % 128) as u32);
            let small = (next() >> (next() % 64)) | 1;

            let mut large: SV = smallvec![low];
            if high > 0 {
                large.push(high);
            } else if low == 0 {
                continue;
            }

            let value = ((high as u128) << 64) | low as u128;
            let expected = gcd_reference(value, small as u128) as usize;

            assert_eq!(unsafe { gcd_single(&large, small, 0) }, expected, "gcd({value}, {small})");
        }
    }
}
