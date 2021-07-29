use std::cmp::Ordering;

use smallvec::SmallVec;

use crate::integer::big::ops::building_blocks::{carrying_sub_mut, is_well_formed_non_zero};
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
                *left_numerator.get_unchecked_mut(0) = 1;
                left_denominator.truncate(1);
                *left_denominator.get_unchecked_mut(0) = 1;
            },
            Ordering::Less | Ordering::Greater => {
                if both_not_one_non_zero(left_numerator, left_denominator) {
                    simplify_fraction_gcd(left_numerator, left_denominator);
                }
            }
        }
    } else {
        if is_one_non_zero(left_denominator) {
            *left_numerator = mul_non_zero(left_numerator, right_denominator);
            add_assign(left_numerator, right_numerator);
            *left_denominator = SmallVec::from_slice(right_denominator);

            if !is_one_non_zero(left_numerator) {
                simplify_fraction_gcd(left_numerator, left_denominator);
            }
        } else if is_one_non_zero(right_denominator) {
            let numerator = mul_non_zero::<S>(right_numerator, left_denominator);
            // TODO(PERFORMANCE): Try reusing storage of `numerator`.
            add_assign(left_numerator, &numerator);
            if !is_one_non_zero(left_numerator) {
                simplify_fraction_gcd(left_numerator, left_denominator);
            }
        } else {
            // Neither denominator is 1
            // TODO(OPTIMIZATION): Should powers of two be kept out of the gcd?
            let mut gcd = gcd(left_denominator, right_denominator);

            if !is_one_non_zero(&gcd) {
                if cmp(right_denominator, &gcd) == Ordering::Equal {
                    // No need to modify numerator
                } else {
                    let left = div_by_odd_or_even::<S>(right_denominator, &gcd);
                    *left_numerator = mul_non_zero(left_numerator, &left);
                }

                remove_shared_two_factors_mut(left_denominator, &mut gcd);
                if cmp(left_denominator, &gcd) == Ordering::Equal {
                    left_denominator.truncate(1);
                    left_denominator[0] = 1;
                    add_assign(left_numerator, right_numerator);
                    *left_denominator = SmallVec::from_slice(right_denominator);
                } else {
                    if !is_one_non_zero(&gcd) {
                        div_assign_by_odd(left_denominator, &gcd);
                    }
                    let right = mul_non_zero::<S>(right_numerator, left_denominator);
                    add_assign(left_numerator, &right);
                    *left_denominator = mul_non_zero(right_denominator, left_denominator);
                }
                simplify_fraction_gcd(left_numerator, left_denominator);
            } else {
                *left_numerator = mul_non_zero(left_numerator, right_denominator);
                let right = mul_non_zero::<S>(right_numerator, left_denominator);
                // TODO(PERFORMANCE): Try reusing storage or `right`
                add_assign(left_numerator, &right);
                *left_denominator = mul_non_zero(left_denominator, right_denominator);
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
                *left_numerator.get_unchecked_mut(0) = 1;
                left_denominator.truncate(1);
                *left_denominator.get_unchecked_mut(0) = 1;
            },
            Ordering::Less | Ordering::Greater => {
                if both_not_one_non_zero(left_numerator, left_denominator) {
                    simplify_fraction_gcd(left_numerator, left_denominator);
                }
            }
        }

        sign_change
    } else {
        if is_one_non_zero(left_denominator) {
            *left_numerator = mul_non_zero(left_numerator, right_denominator);

            let sign_change = match subtracting_cmp(left_numerator, right_numerator) {
                Ordering::Less => SignChange::Flip,
                Ordering::Greater => SignChange::None,
                Ordering::Equal => panic!(),
            };

            *left_denominator = SmallVec::from_slice(right_denominator);
            if !is_one_non_zero(left_numerator) {
                simplify_fraction_gcd(left_numerator, left_denominator);
            }

            sign_change
        } else if is_one_non_zero(right_denominator) {
            let numerator = mul_non_zero::<S>(right_numerator, left_denominator);

            let sign_change = match subtracting_cmp(left_numerator, &numerator) {
                Ordering::Less => SignChange::Flip,
                Ordering::Greater => SignChange::None,
                Ordering::Equal => panic!(),
            };

            if !is_one_non_zero(left_numerator) {
                simplify_fraction_gcd(left_numerator, left_denominator);
            }

            sign_change
        } else {
            // Neither denominator is 1
            let mut gcd = gcd(left_denominator, right_denominator);

            if !is_one_non_zero(&gcd) {
                if cmp(right_denominator, &gcd) == Ordering::Equal {
                    // No need to modify numerator
                } else {
                    let left = div_by_odd_or_even::<S>(right_denominator, &gcd);
                    *left_numerator = mul_non_zero(left_numerator, &left);
                }

                remove_shared_two_factors_mut(left_denominator, &mut gcd);
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
                    if !is_one_non_zero(&gcd) {
                        div_assign_by_odd(left_denominator, &gcd);
                    }
                    let right = mul_non_zero::<S>(right_numerator, left_denominator);

                    *left_denominator = mul_non_zero(right_denominator, left_denominator);
                    match subtracting_cmp(left_numerator, &right) {
                        Ordering::Less => SignChange::Flip,
                        Ordering::Greater => SignChange::None,
                        Ordering::Equal => panic!(),
                    }
                };

                if !is_one_non_zero(left_numerator) {
                    simplify_fraction_gcd(left_numerator, left_denominator);
                }

                sign_change
            } else {
                *left_numerator = mul_non_zero(left_numerator, right_denominator);
                let right = mul_non_zero::<S>(right_numerator, left_denominator);
                *left_denominator = mul_non_zero(left_denominator, right_denominator);
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

    if both_not_one_non_zero(&right_denominator, left_numerator) {
        // TODO(PERFORMANCE): Check for equality here as a special case, or not?

        match cmp(&right_denominator, left_numerator) {
            Ordering::Equal => {
                *left_numerator = right_numerator;
                simplify_fraction_without_info(left_numerator, left_denominator);
                return;
            }
            Ordering::Less | Ordering::Greater => {
                simplify_fraction_gcd(left_numerator, &mut right_denominator);
            }
        }
    }

    if both_not_one_non_zero(left_denominator, &right_numerator) {
        // TODO(PERFORMANCE): Check for equality here as a special case, or not?
        match cmp(&right_numerator, left_denominator) {
            Ordering::Equal => {
                *left_denominator = right_denominator;
                simplify_fraction_without_info(left_numerator, left_denominator);
                return;
            }
            Ordering::Less | Ordering::Greater => {
                simplify_fraction_gcd(&mut right_numerator, left_denominator);
            }
        }
    }

    *left_numerator = mul_non_zero(left_numerator, &right_numerator);
    *left_denominator = mul_non_zero(left_denominator, &right_denominator);

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
                *denominator = simplify_fraction_gcd_single(left_numerator, *denominator);
            }
        }
    } else {
        if right_denominator == 1 {
            let mut rhs_numerator = left_denominator.clone();
            mul_assign_single_non_zero(&mut rhs_numerator, right_numerator);
            // TODO(PERFORMANCE): Try reusing storage of right_numerator
            add_assign(left_numerator, &rhs_numerator);
        } else if is_one_non_zero(left_denominator) {
            mul_assign_single_non_zero(left_numerator, right_denominator);
            add_assign_single_non_zero(left_numerator, right_numerator);
            *left_denominator.get_unchecked_mut(0) = right_denominator;
        } else {
            let (left, small, bits) = prepare_gcd_single::<S>(left_denominator, right_denominator);
            let gcd = gcd_single(left, small, bits);

            mul_assign_single_non_zero(left_numerator, right_denominator / gcd);

            shr_mut(left_denominator, 0, bits);
            if gcd >> bits != 1 {
                div_assign_one_word(left_denominator, gcd >> bits);
            }

            let mut c_times = left_denominator.clone();
            mul_assign_single_non_zero(&mut c_times, right_numerator);

            // TODO(PERFORMANCE): Try reusing storage of c_times
            add_assign(left_numerator, &c_times);

            mul_assign_single_non_zero(left_denominator, right_denominator);

            if !is_one_non_zero(left_numerator) {
                simplify_fraction_gcd(left_numerator, left_denominator);
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
                if !is_one_non_zero(left_numerator) && *denominator != 1 { // denominator.len() == 1
                    *denominator = simplify_fraction_gcd_single(left_numerator, *denominator);
                }
            }

            sign_change
        } else {
            // result won't be negative
            let mut carry = carrying_sub_mut(&mut left_numerator[0], right_numerator, false);

            let mut i = 1;
            while carry {
                carry = carrying_sub_mut(&mut left_numerator[i], 0, true);
                i += 1;
            }

            while let Some(0) = left_numerator.last() {
                left_numerator.pop();
            }

            if *denominator != 1 && !is_one_non_zero(left_numerator) {
                *denominator = simplify_fraction_gcd_single(left_numerator, *denominator);
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
        } else if is_one_non_zero(left_denominator) {
            mul_assign_single_non_zero(left_numerator, right_denominator);
            *left_denominator.first_mut().unwrap() = right_denominator;
            match subtracting_cmp_ne_single(left_numerator, right_numerator) {
                Ordering::Less => SignChange::Flip,
                Ordering::Greater => SignChange::None,
                Ordering::Equal => panic!(),
            }
        } else {
            let (left, small, bits) = prepare_gcd_single::<S>(left_denominator, right_denominator);
            let gcd = gcd_single(left, small, bits);

            mul_assign_single_non_zero(left_numerator, right_denominator / gcd);

            shr_mut(left_denominator, 0, bits);
            if gcd >> bits > 1 {
                div_assign_one_word(left_denominator, gcd >> bits);
            }
            let mut c_times = left_denominator.clone();
            mul_assign_single_non_zero(&mut c_times, right_numerator);

            let sign_change = match subtracting_cmp(left_numerator, &c_times) {
                Ordering::Less => SignChange::Flip,
                Ordering::Greater => SignChange::None,
                Ordering::Equal => panic!(),
            };
            mul_assign_single_non_zero(left_denominator, right_denominator);

            if !is_one_non_zero(left_numerator) {
                simplify_fraction_gcd(left_numerator, left_denominator);
            }

            sign_change
        }
    };

    debug_assert!(is_well_formed_fraction(left_numerator, left_denominator));

    sign_change
}

#[inline]
pub unsafe fn mul_small<const S: usize>(
    left_numerator: &mut SmallVec<[usize; S]>, left_denominator: &mut SmallVec<[usize; S]>,
    mut right_numerator: usize, mut right_denominator: usize,
) {
    debug_assert!(is_well_formed_fraction_non_zero(left_numerator, left_denominator));
    debug_assert!(is_well_formed_fraction_small(right_numerator, right_denominator));

    if right_denominator != 1 && !is_one_non_zero(left_numerator) {
        right_denominator = simplify_fraction_gcd_single(left_numerator, right_denominator)
    }

    if right_numerator != 1 && !is_one_non_zero(left_denominator) {
        right_numerator = simplify_fraction_gcd_single(left_denominator, right_numerator)
    }

    mul_assign_single_non_zero(left_numerator, right_numerator);
    mul_assign_single_non_zero(left_denominator, right_denominator);

    debug_assert!(is_well_formed_fraction_non_zero(left_numerator, left_denominator));
}
