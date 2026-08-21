use std::cmp::Ordering;

use smallvec::SmallVec;

use crate::integer::big::ops::building_blocks::{borrowing_sub_mut, is_well_formed_non_zero};
use crate::integer::big::ops::div::{div_assign_by_odd, div_assign_one_word};
use crate::integer::big::ops::non_zero::{add_assign, add_assign_single_non_zero, both_not_one_non_zero, is_one_non_zero, mul_assign_single_non_zero, mul_non_zero, shr_mut, subtracting_cmp, subtracting_cmp_ne_single};
use crate::integer::big::ops::normalize::{gcd_scalar, gcd_single, is_coprime_non_zero, prepare_gcd_single, remove_shared_two_factors_mut, simplify_fraction_gcd, simplify_fraction_gcd_single, simplify_fraction_without_info};
use crate::integer::big::properties::cmp;
use crate::rational::big::ops::div_by_odd_or_even;
use crate::rational::big::ops::gcd;

#[must_use]
fn is_well_formed_fraction_non_zero(left: &[usize], right: &[usize]) -> bool {
    is_well_formed_non_zero(left) &&
        is_well_formed_non_zero(right) &&
        unsafe {
            // SAFETY: We just checked that the numbers are well-formed and non zero
            is_coprime_non_zero(left, right)
        }
}

#[must_use]
fn is_well_formed_fraction(left: &[usize], right: &[usize]) -> bool {
    (
        // fraction equals zero
        left.is_empty() && right.len() == 1 && right[0] == 1
    ) || is_well_formed_fraction_non_zero(left, right)
}

/// Cancel the greatest common divisor of a numerator and a denominator.
///
/// [`simplify_fraction_gcd`] runs a binary gcd over both values in full, giving up about a bit per
/// step while walking every word of both operands on each one. When either side fits in a single
/// word, [`simplify_fraction_gcd_single`] reaches the same answer with one division pass followed
/// by a scalar gcd, so the widths are worth checking before the general routine is entered.
///
/// Cancelling is symmetric, so it does not matter which of the two is the single word: the small
/// side is passed by value and the large one is divided in place.
///
/// # Safety
///
/// Both operands have to be well formed and not zero, neither may be one, and they may not be
/// equal.
#[inline]
unsafe fn simplify_fraction_gcd_dispatch<const S: usize>(
    left: &mut SmallVec<[usize; S]>, right: &mut SmallVec<[usize; S]>,
) {
    debug_assert!(is_well_formed_non_zero(left));
    debug_assert!(is_well_formed_non_zero(right));

    if right.len() == 1 {
        // SAFETY: `right` has exactly one word, so index zero is in bounds. That word is neither
        // zero nor one, and `left` is well formed, not zero and not one, by this function's
        // contract.
        unsafe {
            let reduced = simplify_fraction_gcd_single(left, *right.get_unchecked(0));
            *right.get_unchecked_mut(0) = reduced;
        }
    } else if left.len() == 1 {
        // SAFETY: As above with the two sides exchanged, which cancelling permits.
        unsafe {
            let reduced = simplify_fraction_gcd_single(right, *left.get_unchecked(0));
            *left.get_unchecked_mut(0) = reduced;
        }
    } else {
        // SAFETY: Both are well formed, not zero, not one and not equal by this function's
        // contract.
        unsafe { simplify_fraction_gcd(left, right) };
    }
}

#[inline]
pub unsafe fn add_assign_fraction_non_zero<const S: usize>(
    left_numerator: &mut SmallVec<[usize; S]>, left_denominator: &mut SmallVec<[usize; S]>, 
    right_numerator: &[usize], right_denominator: &[usize],
) {
    debug_assert!(is_well_formed_fraction_non_zero(left_numerator, left_denominator));
    debug_assert!(is_well_formed_fraction_non_zero(right_numerator, right_denominator));

    if left_denominator.as_slice() == right_denominator {
        add_assign(left_numerator, right_numerator);

        // Numerator can't be zero

        match cmp(left_numerator, left_denominator) {
            Ordering::Equal => {
                left_numerator.truncate(1);
                left_denominator.truncate(1);
                // SAFETY: Both operands are non zero and so not empty, and truncating a non empty
                // value to one word leaves exactly one word behind, so index zero is in bounds.
                unsafe {
                    *left_numerator.get_unchecked_mut(0) = 1;
                    *left_denominator.get_unchecked_mut(0) = 1;
                }
            },
            Ordering::Less | Ordering::Greater => {
                // SAFETY: Neither operand is empty: the denominator is non zero by the caller's
                // guarantee, and the numerator is a sum of two non zero magnitudes.
                if unsafe { both_not_one_non_zero(left_numerator, left_denominator) } {
                    // SAFETY: Both are well formed and not empty, the check above established that
                    // neither is one, and this arm is the one where they differ.
                    unsafe { simplify_fraction_gcd(left_numerator, left_denominator) };
                }
            }
        }
    } else {
        // SAFETY: All four operands are non zero and so not empty.
        if unsafe { is_one_non_zero(left_denominator) } {
            // SAFETY: All four operands are well formed and not empty, so the product is too.
            *left_numerator = unsafe { mul_non_zero(left_numerator, right_denominator) };
            add_assign(left_numerator, right_numerator);
            *left_denominator = SmallVec::from_slice(right_denominator);

            // The result `(a * d + c) / d` is already in lowest terms, so it is left as it is: a
            // common divisor of the numerator and `d` divides `a * d`, so it divides `c` as well,
            // and `c / d` is in lowest terms by the caller's guarantee. Reducing here would walk
            // the whole binary gcd only to divide both sides by one.
        // SAFETY: All four operands are non zero and so not empty.
        } else if unsafe { is_one_non_zero(right_denominator) } {
            // SAFETY: All four operands are well formed and not empty.
            let numerator = unsafe { mul_non_zero::<S>(right_numerator, left_denominator) };
            // TODO(PERFORMANCE): Try reusing storage of `numerator`.
            add_assign(left_numerator, &numerator);

            // The result `(a + c * b) / b` is already in lowest terms, by the argument above with
            // the roles of the two fractions exchanged: a common divisor of the numerator and `b`
            // divides `c * b`, so it divides `a` as well, and `a / b` is in lowest terms.
        } else {
            // Neither denominator is 1
            // TODO(OPTIMIZATION): Should powers of two be kept out of the gcd?
            // SAFETY: Both denominators are well formed and not empty, neither is one by the two
            // checks above, and they differ because this is the branch where they are not equal.
            let mut gcd = unsafe { gcd(left_denominator, right_denominator) };

            // SAFETY: A greatest common divisor of two non zero values is itself non zero.
            if !unsafe { is_one_non_zero(&gcd) } {
                if cmp(right_denominator, &gcd) == Ordering::Equal {
                    // No need to modify numerator
                } else {
                    // SAFETY: `gcd` divides `right_denominator` and the two are not equal here, so
                    // `right_denominator` is the larger and the division comes out exact. `gcd` is
                    // not one by the check above.
                    let left = unsafe { div_by_odd_or_even::<S>(right_denominator, &gcd) };
                    // SAFETY: Both factors are well formed and not empty.
                    *left_numerator = unsafe { mul_non_zero(left_numerator, &left) };
                }

                // SAFETY: Both are well formed and not zero. `gcd` divides `left_denominator`, so
                // it has no more factors two than it does, which means the shared count is all of
                // them and `gcd` comes out odd.
                unsafe { remove_shared_two_factors_mut(left_denominator, &mut gcd) };
                if cmp(left_denominator, &gcd) == Ordering::Equal {
                    left_denominator.truncate(1);
                    left_denominator[0] = 1;
                    add_assign(left_numerator, right_numerator);
                    *left_denominator = SmallVec::from_slice(right_denominator);
                } else {
                    // SAFETY: `gcd` is not empty.
                    if !unsafe { is_one_non_zero(&gcd) } {
                        // SAFETY: `gcd` is odd, as noted above, and larger than one by the check
                        // just made. It still divides `left_denominator`, because both were shifted
                        // right by the same amount, and the two are not equal in this arm, so
                        // `left_denominator` is the larger.
                        unsafe { div_assign_by_odd(left_denominator, &gcd) };
                    }
                    // SAFETY: Every operand is well formed and not empty, and so is every product.
                    unsafe {
                        let right = mul_non_zero::<S>(right_numerator, left_denominator);
                        add_assign(left_numerator, &right);
                        *left_denominator = mul_non_zero(right_denominator, left_denominator);
                    }
                }
                // SAFETY: The denominator is a multiple of `right_denominator`, which is not one.
                // The numerator is a sum of non zero terms of which at least one is a multiple of a
                // value larger than one, so it is not one either. They are not equal: both input
                // fractions are in lowest terms, and writing the sum over the least common multiple
                // of the two denominators leaves a numerator that shares no factor with it, so a
                // numerator equal to the denominator would make the sum one over one.
                unsafe { simplify_fraction_gcd(left_numerator, left_denominator) };
            } else {
                // SAFETY: Every operand is well formed and not empty, and so is every product. The
                // denominators are coprime here, so the result needs no further simplification.
                unsafe {
                    *left_numerator = mul_non_zero(left_numerator, right_denominator);
                    let right = mul_non_zero::<S>(right_numerator, left_denominator);
                    // TODO(PERFORMANCE): Try reusing storage or `right`
                    add_assign(left_numerator, &right);
                    *left_denominator = mul_non_zero(left_denominator, right_denominator);
                }
            }
        }
    }

    debug_assert!(is_well_formed_fraction_non_zero(left_numerator, left_denominator));
}

pub enum SignChange {
    None,
    Flip,
    Zero,
}

#[inline]
pub unsafe fn sub_assign_fraction_non_zero<const S: usize>(
    left_numerator: &mut SmallVec<[usize; S]>, left_denominator: &mut SmallVec<[usize; S]>,
    right_numerator: &[usize], right_denominator: &[usize],
) -> SignChange {
    debug_assert!(is_well_formed_fraction_non_zero(left_numerator, left_denominator));
    debug_assert!(is_well_formed_fraction_non_zero(right_numerator, right_denominator));

    let sign_change = if left_denominator.as_slice() == right_denominator {
        let sign_change = match subtracting_cmp(left_numerator, right_numerator) {
            Ordering::Less => SignChange::Flip,
            Ordering::Equal => {
                left_denominator[0] = 1;
                left_denominator.truncate(1);
                return SignChange::Zero;
            }
            Ordering::Greater => SignChange::None,
        };

        match cmp(left_numerator, left_denominator) {
            Ordering::Equal => {
                left_numerator.truncate(1);
                left_denominator.truncate(1);
                // SAFETY: The difference is non zero, because the equal case returned above, and
                // the denominator is non zero by the caller's guarantee. Truncating a non empty
                // value to one word leaves exactly one word behind, so index zero is in bounds.
                unsafe {
                    *left_numerator.get_unchecked_mut(0) = 1;
                    *left_denominator.get_unchecked_mut(0) = 1;
                }
            },
            Ordering::Less | Ordering::Greater => {
                // SAFETY: Neither operand is empty, as above.
                if unsafe { both_not_one_non_zero(left_numerator, left_denominator) } {
                    // SAFETY: Both are well formed and not empty, neither is one by the check
                    // above, and this arm is the one where they differ.
                    unsafe { simplify_fraction_gcd(left_numerator, left_denominator) };
                }
            }
        }

        sign_change
    } else {
        // SAFETY: All four operands are non zero and so not empty.
        if unsafe { is_one_non_zero(left_denominator) } {
            // SAFETY: All four operands are well formed and not empty, so the product is too.
            *left_numerator = unsafe { mul_non_zero(left_numerator, right_denominator) };

            let sign_change = match subtracting_cmp(left_numerator, right_numerator) {
                Ordering::Less => SignChange::Flip,
                Ordering::Greater => SignChange::None,
                Ordering::Equal => panic!(),
            };

            *left_denominator = SmallVec::from_slice(right_denominator);

            // The result `|a * d - c| / d` is already in lowest terms, so it is left as it is: a
            // common divisor of the numerator and `d` divides `a * d`, so it divides `c` as well,
            // and `c / d` is in lowest terms by the caller's guarantee. Reducing here would walk
            // the whole binary gcd only to divide both sides by one.

            sign_change
        // SAFETY: All four operands are non zero and so not empty.
        } else if unsafe { is_one_non_zero(right_denominator) } {
            // SAFETY: All four operands are well formed and not empty.
            let numerator = unsafe { mul_non_zero::<S>(right_numerator, left_denominator) };

            let sign_change = match subtracting_cmp(left_numerator, &numerator) {
                Ordering::Less => SignChange::Flip,
                Ordering::Greater => SignChange::None,
                Ordering::Equal => panic!(),
            };

            // The result `|a - c * b| / b` is already in lowest terms, by the argument above with
            // the roles of the two fractions exchanged: a common divisor of the numerator and `b`
            // divides `c * b`, so it divides `a` as well, and `a / b` is in lowest terms.

            sign_change
        } else {
            // Neither denominator is 1
            // SAFETY: Both denominators are well formed and not empty, neither is one by the two
            // checks above, and they differ because this is the branch where they are not equal.
            let mut gcd = unsafe { gcd(left_denominator, right_denominator) };

            // SAFETY: A greatest common divisor of two non zero values is itself non zero.
            if !unsafe { is_one_non_zero(&gcd) } {
                if cmp(right_denominator, &gcd) == Ordering::Equal {
                    // No need to modify numerator
                } else {
                    // SAFETY: `gcd` divides `right_denominator` and the two are not equal here, so
                    // `right_denominator` is the larger and the division comes out exact. `gcd` is
                    // not one by the check above.
                    let left = unsafe { div_by_odd_or_even::<S>(right_denominator, &gcd) };
                    // SAFETY: Both factors are well formed and not empty.
                    *left_numerator = unsafe { mul_non_zero(left_numerator, &left) };
                }

                // SAFETY: Both are well formed and not zero. `gcd` divides `left_denominator`, so
                // it has no more factors two than it does, which means the shared count is all of
                // them and `gcd` comes out odd.
                unsafe { remove_shared_two_factors_mut(left_denominator, &mut gcd) };
                let sign_change = if cmp(left_denominator, &gcd) == Ordering::Equal {
                    left_denominator.truncate(1);
                    left_denominator[0] = 1;

                    *left_denominator = SmallVec::from_slice(right_denominator);
                    match subtracting_cmp(left_numerator, right_numerator) {
                        Ordering::Less => SignChange::Flip,
                        Ordering::Greater => SignChange::None,
                        Ordering::Equal => panic!(),
                    }
                } else {
                    // SAFETY: `gcd` is not empty.
                    if !unsafe { is_one_non_zero(&gcd) } {
                        // SAFETY: `gcd` is odd, as noted above, and larger than one by the check
                        // just made. It still divides `left_denominator`, because both were shifted
                        // right by the same amount, and the two are not equal in this arm, so
                        // `left_denominator` is the larger.
                        unsafe { div_assign_by_odd(left_denominator, &gcd) };
                    }
                    // SAFETY: Every operand is well formed and not empty, and so is every product.
                    let right = unsafe { mul_non_zero::<S>(right_numerator, left_denominator) };

                    // SAFETY: As above.
                    *left_denominator = unsafe { mul_non_zero(right_denominator, left_denominator) };
                    match subtracting_cmp(left_numerator, &right) {
                        Ordering::Less => SignChange::Flip,
                        Ordering::Greater => SignChange::None,
                        Ordering::Equal => panic!(),
                    }
                };

                // SAFETY: Every equal case above panics, so the difference is non zero and so not
                // empty.
                if !unsafe { is_one_non_zero(left_numerator) } {
                    // SAFETY: The numerator is not one by the check above, and the denominator is a
                    // multiple of a denominator larger than one. They are not equal: both input
                    // fractions are in lowest terms, and writing the difference over the least
                    // common multiple of the two denominators leaves a numerator that shares no
                    // factor with it, so the two can only coincide at one over one.
                    unsafe { simplify_fraction_gcd(left_numerator, left_denominator) };
                }

                sign_change
            } else {
                // SAFETY: Every operand is well formed and not empty, and so is every product. The
                // denominators are coprime here, so the result needs no further simplification.
                let right = unsafe {
                    *left_numerator = mul_non_zero(left_numerator, right_denominator);
                    let right = mul_non_zero::<S>(right_numerator, left_denominator);
                    *left_denominator = mul_non_zero(left_denominator, right_denominator);
                    right
                };
                match subtracting_cmp(left_numerator, &right) {
                    Ordering::Less => SignChange::Flip,
                    Ordering::Greater => SignChange::None,
                    Ordering::Equal => panic!(),
                }
            }
        }
    };

    debug_assert!(is_well_formed_fraction(left_numerator, left_denominator));

    sign_change
}

#[inline]
pub unsafe fn mul_assign_fraction_non_zero<const S: usize>(
    left_numerator: &mut SmallVec<[usize; S]>, left_denominator: &mut SmallVec<[usize; S]>,
    mut right_numerator: SmallVec<[usize; S]>, mut right_denominator: SmallVec<[usize; S]>
) {
    debug_assert!(is_well_formed_fraction_non_zero(left_numerator, left_denominator));
    debug_assert!(is_well_formed_fraction_non_zero(&right_numerator, &right_denominator));

    // SAFETY: All four operands are non zero and so not empty.
    if unsafe { both_not_one_non_zero(&right_denominator, left_numerator) } {
        // TODO(PERFORMANCE): Check for equality here as a special case, or not?

        match cmp(&right_denominator, left_numerator) {
            Ordering::Equal => {
                *left_numerator = right_numerator;
                // SAFETY: The numerator is now `right_numerator` and the denominator is untouched;
                // both are well formed and non zero.
                unsafe { simplify_fraction_without_info(left_numerator, left_denominator) };
                return;
            }
            Ordering::Less | Ordering::Greater => {
                // SAFETY: Both are well formed and not empty, neither is one by the check above,
                // and this arm is the one where they differ.
                unsafe { simplify_fraction_gcd_dispatch(left_numerator, &mut right_denominator) };
            }
        }
    }

    // SAFETY: Both are non zero and so not empty. `simplify_fraction_gcd` above may have divided
    // them down, but it leaves both of its operands well formed and non zero, and it did not touch
    // these two in any case.
    if unsafe { both_not_one_non_zero(left_denominator, &right_numerator) } {
        // TODO(PERFORMANCE): Check for equality here as a special case, or not?
        match cmp(&right_numerator, left_denominator) {
            Ordering::Equal => {
                *left_denominator = right_denominator;
                // SAFETY: Both are well formed and non zero, as above.
                unsafe { simplify_fraction_without_info(left_numerator, left_denominator) };
                return;
            }
            Ordering::Less | Ordering::Greater => {
                // SAFETY: Both are well formed and not empty, neither is one by the check above,
                // and this arm is the one where they differ.
                unsafe { simplify_fraction_gcd_dispatch(&mut right_numerator, left_denominator) };
            }
        }
    }

    // SAFETY: All four operands are still well formed and not empty.
    unsafe {
        *left_numerator = mul_non_zero(left_numerator, &right_numerator);
        *left_denominator = mul_non_zero(left_denominator, &right_denominator);
    }

    debug_assert!(is_well_formed_fraction_non_zero(left_numerator, left_denominator));
}

#[must_use]
fn is_well_formed_fraction_small(left: usize, right: usize) -> bool {
    match (left, right) {
        (_, 1) => true,
        (1, denominator) if denominator > 0 => true,
        (numerator, denominator) if denominator > 0 => gcd_scalar(numerator, denominator) == 1,
        _ => false,
    }
}

#[inline]
pub unsafe fn add_small<const S: usize>(
    left_numerator: &mut SmallVec<[usize; S]>, left_denominator: &mut SmallVec<[usize; S]>,
    right_numerator: usize, right_denominator: usize,
) {
    debug_assert!(is_well_formed_fraction_non_zero(left_numerator, left_denominator));
    debug_assert!(is_well_formed_fraction_small(right_numerator, right_denominator));

    if right_denominator == left_denominator[0] && left_denominator.len() == 1 {
        add_assign_single_non_zero(left_numerator, right_numerator);

        // numerator can't be zero

        let denominator = left_denominator.first_mut().unwrap();
        if left_numerator[0] == *denominator && left_numerator.len() == 1 {
            left_numerator[0] = 1;
            *denominator = 1;
        } else {
            if *denominator != 1 {
                // numerator can't be 1 because two positive things were added
                // SAFETY: The numerator is well formed and not empty, and larger than one because
                // two positive magnitudes were added. The denominator is the single, non zero word
                // of a well formed value, and it is not one by the check just made.
                *denominator = unsafe { simplify_fraction_gcd_single(left_numerator, *denominator) };
            }
        }
    } else {
        if right_denominator == 1 {
            let mut rhs_numerator = left_denominator.clone();
            mul_assign_single_non_zero(&mut rhs_numerator, right_numerator);
            // TODO(PERFORMANCE): Try reusing storage of right_numerator
            add_assign(left_numerator, &rhs_numerator);
        // SAFETY: The denominator is non zero and so not empty.
        } else if unsafe { is_one_non_zero(left_denominator) } {
            mul_assign_single_non_zero(left_numerator, right_denominator);
            add_assign_single_non_zero(left_numerator, right_numerator);
            // SAFETY: The denominator is one, so it is exactly one word long and index zero is in
            // bounds.
            unsafe { *left_denominator.get_unchecked_mut(0) = right_denominator };
        } else {
            // SAFETY: The denominator is well formed and not zero by this function's contract,
            // and the right denominator is non zero because it is a fraction's denominator.
            let (small, bits) = unsafe {
                prepare_gcd_single(left_denominator, right_denominator)
            };
            // SAFETY: The denominator is well formed and not zero, and `small` is the odd part of
            // a non zero word and so odd itself.
            let gcd = unsafe { gcd_single(left_denominator, small, bits) };

            mul_assign_single_non_zero(left_numerator, right_denominator / gcd);

            shr_mut(left_denominator, 0, bits);
            if gcd >> bits != 1 {
                // SAFETY: The denominator is well formed and not empty. `gcd_single` returns its
                // odd result shifted left by `bits`, so `gcd >> bits` is odd, and it divides the
                // denominator, which was shifted right by those same `bits` just above.
                unsafe { div_assign_one_word(left_denominator, gcd >> bits) };
            }

            let mut c_times = left_denominator.clone();
            mul_assign_single_non_zero(&mut c_times, right_numerator);

            // TODO(PERFORMANCE): Try reusing storage of c_times
            add_assign(left_numerator, &c_times);

            mul_assign_single_non_zero(left_denominator, right_denominator);

            // Whatever is left to cancel divides `gcd`, so it fits in a single word.
            //
            // The sum stands over `lcm(b, d)` with numerator `a * (d / g) + c * (b / g)`, writing
            // `g` for `gcd`. A prime dividing both has to divide `b` as well as `d`: one dividing
            // `b` alone divides `c * (b / g)` but not `a * (d / g)`, because `a / b` is in lowest
            // terms, so it cannot divide their sum, and the same argument with the two fractions
            // exchanged rules out one dividing `d` alone. So it divides `g`. Since `g` divides the
            // least common multiple too, the common factor sought is exactly the gcd of the
            // numerator and `g`, which a single word gcd finds.
            //
            // SAFETY: The numerator is a sum of positive magnitudes, so it is not empty.
            if gcd != 1 && !unsafe { is_one_non_zero(left_numerator) } {
                // SAFETY: The numerator is well formed, not zero and not one by the check above,
                // and `gcd` is neither zero nor one by the check beside it.
                let remaining = unsafe { simplify_fraction_gcd_single(left_numerator, gcd) };

                // `simplify_fraction_gcd_single` divided the numerator by the common factor and
                // returned what is left of `gcd`, so their quotient is that factor.
                let cancelled = gcd / remaining;
                shr_mut(left_denominator, 0, cancelled.trailing_zeros());
                let cancelled_odd = cancelled >> cancelled.trailing_zeros();
                if cancelled_odd != 1 {
                    // SAFETY: The denominator is well formed and not empty, and `cancelled_odd` is
                    // odd by construction. It divides the denominator, which is a multiple of `g`.
                    unsafe { div_assign_one_word(left_denominator, cancelled_odd) };
                }
            }
        }
    }

    debug_assert!(is_well_formed_fraction_non_zero(left_numerator, left_denominator));
}

#[inline]
pub unsafe fn sub_small<const S: usize>(
    left_numerator: &mut SmallVec<[usize; S]>, left_denominator: &mut SmallVec<[usize; S]>,
    right_numerator: usize, right_denominator: usize,
) -> SignChange {
    debug_assert!(is_well_formed_fraction_non_zero(left_numerator, left_denominator));
    debug_assert!(is_well_formed_fraction_small(right_numerator, right_denominator));

    let sign_change = if right_denominator == *left_denominator.first().unwrap() && left_denominator.len() == 1 {
        let denominator = left_denominator.first_mut().unwrap();

        if left_numerator.len() == 1 {
            // result might be negative
            let sign_change = match left_numerator[0].cmp(&right_numerator) {
                Ordering::Less => {
                    left_numerator[0] = right_numerator - left_numerator[0];
                    SignChange::Flip
                }
                Ordering::Equal => {
                    left_numerator.clear();
                    *denominator = 1;
                    return SignChange::Zero;
                },
                Ordering::Greater => {
                    left_numerator[0] -= right_numerator;
                    SignChange::None
                },
            };

            if left_numerator[0] == *denominator && left_numerator.len() == 1 {
                left_numerator[0] = 1;
                left_denominator[0] = 1;
            } else {
                // SAFETY: The numerator is one word long and that word is not zero: the equal case
                // returned above, so the difference of the two single words is positive.
                if !unsafe { is_one_non_zero(left_numerator) } && *denominator != 1 { // denominator.len() == 1
                    // SAFETY: The numerator is well formed, not empty and not one by the check
                    // above. The denominator is the single, non zero word of a well formed value
                    // and is not one by the check above either.
                    *denominator = unsafe { simplify_fraction_gcd_single(left_numerator, *denominator) };
                }
            }

            sign_change
        } else {
            // result won't be negative
            let mut carry = false;
            borrowing_sub_mut(&mut left_numerator[0], right_numerator, &mut carry);

            let mut i = 1;
            while carry {
                borrowing_sub_mut(&mut left_numerator[i], 0, &mut carry);
                i += 1;
            }

            while let Some(0) = left_numerator.last() {
                left_numerator.pop();
            }

            // SAFETY: The numerator started out more than one word long, so it is larger than any
            // single word and stays positive, and so not empty, after the subtraction.
            if *denominator != 1 && !unsafe { is_one_non_zero(left_numerator) } {
                // SAFETY: The numerator is well formed, not empty and not one by the check above.
                // The denominator is the single, non zero word of a well formed value and is not
                // one by the check above either.
                *denominator = unsafe { simplify_fraction_gcd_single(left_numerator, *denominator) };
            }

            SignChange::None
        }
    } else {
        if right_denominator == 1 {
            let mut product = left_denominator.clone();
            mul_assign_single_non_zero(&mut product, right_numerator);
            match subtracting_cmp(left_numerator, &product) {
                Ordering::Less => SignChange::Flip,
                Ordering::Greater => SignChange::None,
                Ordering::Equal => panic!(),
            }
        // SAFETY: The denominator is non zero and so not empty.
        } else if unsafe { is_one_non_zero(left_denominator) } {
            mul_assign_single_non_zero(left_numerator, right_denominator);
            *left_denominator.first_mut().unwrap() = right_denominator;
            match subtracting_cmp_ne_single(left_numerator, right_numerator) {
                Ordering::Less => SignChange::Flip,
                Ordering::Greater => SignChange::None,
                Ordering::Equal => panic!(),
            }
        } else {
            // SAFETY: The denominator is well formed and not zero by this function's contract,
            // and the right denominator is non zero because it is a fraction's denominator.
            let (small, bits) = unsafe {
                prepare_gcd_single(left_denominator, right_denominator)
            };
            // SAFETY: The denominator is well formed and not zero, and `small` is the odd part of
            // a non zero word and so odd itself.
            let gcd = unsafe { gcd_single(left_denominator, small, bits) };

            mul_assign_single_non_zero(left_numerator, right_denominator / gcd);

            shr_mut(left_denominator, 0, bits);
            if gcd >> bits > 1 {
                // SAFETY: The denominator is well formed and not empty. `gcd_single` returns its
                // odd result shifted left by `bits`, so `gcd >> bits` is odd, and it divides the
                // denominator, which was shifted right by those same `bits` just above.
                unsafe { div_assign_one_word(left_denominator, gcd >> bits) };
            }
            let mut c_times = left_denominator.clone();
            mul_assign_single_non_zero(&mut c_times, right_numerator);

            let sign_change = match subtracting_cmp(left_numerator, &c_times) {
                Ordering::Less => SignChange::Flip,
                Ordering::Greater => SignChange::None,
                Ordering::Equal => panic!(),
            };
            mul_assign_single_non_zero(left_denominator, right_denominator);

            // Whatever is left to cancel divides `gcd`, so it fits in a single word, by the same
            // argument as in `add_small`: divisibility does not care that the numerator is now a
            // difference rather than a sum.
            //
            // SAFETY: The equal case panics above, so the difference is non zero and not empty.
            if gcd != 1 && !unsafe { is_one_non_zero(left_numerator) } {
                // SAFETY: The numerator is well formed, not zero and not one by the check above,
                // and `gcd` is neither zero nor one by the check beside it.
                let remaining = unsafe { simplify_fraction_gcd_single(left_numerator, gcd) };

                // `simplify_fraction_gcd_single` divided the numerator by the common factor and
                // returned what is left of `gcd`, so their quotient is that factor.
                let cancelled = gcd / remaining;
                shr_mut(left_denominator, 0, cancelled.trailing_zeros());
                let cancelled_odd = cancelled >> cancelled.trailing_zeros();
                if cancelled_odd != 1 {
                    // SAFETY: The denominator is well formed and not empty, and `cancelled_odd` is
                    // odd by construction. It divides the denominator, which is a multiple of `g`.
                    unsafe { div_assign_one_word(left_denominator, cancelled_odd) };
                }
            }

            sign_change
        }
    };

    debug_assert!(is_well_formed_fraction(left_numerator, left_denominator));

    sign_change
}

/// Multiply a fraction by a fraction that fits in two words, in place.
///
/// # Safety
///
/// The left fraction has to be well formed, non zero and in lowest terms, and the right fraction
/// has to be in lowest terms with a non zero denominator **and a non zero numerator**. The
/// `is_well_formed_fraction_small` check below is weaker than that: it admits `0 / 1`. Every caller
/// dispatches on the sign first and only reaches this for a non zero right hand side, which is what
/// keeps the zero out. A zero numerator would reach `mul_assign_single_non_zero` below, which would
/// leave a denormalized `[0, ..]` behind, and later reads of that value scan past the end of it.
#[inline]
pub unsafe fn mul_small<const S: usize>(
    left_numerator: &mut SmallVec<[usize; S]>, left_denominator: &mut SmallVec<[usize; S]>,
    mut right_numerator: usize, mut right_denominator: usize,
) {
    debug_assert!(is_well_formed_fraction_non_zero(left_numerator, left_denominator));
    debug_assert!(is_well_formed_fraction_small(right_numerator, right_denominator));
    debug_assert_ne!(right_numerator, 0);

    // SAFETY: The left numerator is non zero and so not empty.
    if right_denominator != 1 && !unsafe { is_one_non_zero(left_numerator) } {
        // SAFETY: The numerator is well formed, not empty and not one by the check above, and the
        // right denominator is neither zero nor one.
        right_denominator = unsafe { simplify_fraction_gcd_single(left_numerator, right_denominator) }
    }

    // SAFETY: The left denominator is non zero and so not empty.
    if right_numerator != 1 && !unsafe { is_one_non_zero(left_denominator) } {
        // SAFETY: The denominator is well formed, not empty and not one by the check above. The
        // right numerator is not one by the check above and not zero by this function's contract.
        right_numerator = unsafe { simplify_fraction_gcd_single(left_denominator, right_numerator) }
    }

    mul_assign_single_non_zero(left_numerator, right_numerator);
    mul_assign_single_non_zero(left_denominator, right_denominator);

    debug_assert!(is_well_formed_fraction_non_zero(left_numerator, left_denominator));
}
