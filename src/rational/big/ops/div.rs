use std::cmp::Ordering;
use std::ptr::copy;

use smallvec::{smallvec, SmallVec};

use crate::rational::big::ops::{BITS_PER_WORD, cmp, is_well_formed};
use crate::rational::big::ops::building_blocks::{add_2, add_assign_slice, mul, shl, shl_mut_overflowing, shr, sub_2, sub_assign_slice, submul_slice};
use crate::rational::big::ops::normalize::trailing_zeros;

#[inline]
pub fn div_assign_double<const S: usize>(
    values_one: &mut SmallVec<[usize; S]>,
    values_two: &mut SmallVec<[usize; S]>,
    rhs: SmallVec<[usize; S]>,
) {
    debug_assert!(is_well_formed(values_one));
    debug_assert!(is_well_formed(values_two));
    debug_assert!(!values_one.is_empty());
    debug_assert!(!values_two.is_empty());
    debug_assert!(is_well_formed(&rhs));
    debug_assert!(!rhs.is_empty());
    let one: SmallVec<[usize; S]> = smallvec![1];
    debug_assert_ne!(rhs, one);
    debug_assert_eq!(rhs[0] % 2, 1);
    debug_assert_eq!(cmp(values_one, &rhs), Ordering::Greater);
    debug_assert_eq!(cmp(values_two, &rhs), Ordering::Greater);

    match rhs.len() {
        1 => {
            // TODO(PERFORMANCE): Ensure that after inlining, code is dedupliated
            div_assign_one_word(values_one, rhs[0]);
            div_assign_one_word(values_two, rhs[0]);
        }
        2 => {
            // TODO(PERFORMANCE): Ensure that after inlining, code is dedupliated
            div_assign_two_words(values_one, rhs[1], rhs[0]);
            div_assign_two_words(values_two, rhs[1], rhs[0]);
        }
        _ => div_assign_n_words_double(values_one, values_two, rhs),
    }
}

#[inline]
pub fn div_assign_n_words_double<const S: usize>(
    values_one: &mut SmallVec<[usize; S]>,
    values_two: &mut SmallVec<[usize; S]>,
    mut rhs: SmallVec<[usize; S]>,
) {
    debug_assert!(is_well_formed(values_one));
    debug_assert!(values_one.len() > 2);
    debug_assert!(is_well_formed(values_two));
    debug_assert!(values_two.len() > 2);
    debug_assert!(rhs.len() > 2);
    debug_assert_eq!(rhs[0] % 2, 1);
    // We assume that values % rhs == 0

    let rhs_high = *rhs.last().unwrap();
    let leading_zeros = rhs_high.leading_zeros();

    if leading_zeros > 0 {
        unsafe {
            // TODO(PERFORMANCE): Avoid this allocation before `values` gets smaller
            let carry = shl_mut_overflowing(values_one, leading_zeros);
            if let Some(carry) = carry {
                values_one.push(carry.get())
            }
            let carry = shl_mut_overflowing(values_two, leading_zeros);
            if let Some(carry) = carry {
                values_two.push(carry.get())
            }
        }

        unsafe { shl_mut_overflowing(&mut rhs, leading_zeros); }
    }
    debug_assert!(values_one.len() > rhs.len());
    debug_assert!(values_two.len() > rhs.len());

    let divisor_length = rhs.len();
    let divisor_inverse = invert_pi(rhs[divisor_length - 1], rhs[divisor_length - 2]);

    div_assign_n_words_helper(values_one, &rhs, divisor_inverse);
    div_assign_n_words_helper(values_two, &rhs, divisor_inverse);
}

#[inline]
pub fn div<const S: usize>(
    values: &SmallVec<[usize; S]>,
    rhs: &SmallVec<[usize; S]>,
) -> SmallVec<[usize; S]> {
    // Assume that the do divide without remainder
    debug_assert_eq!(cmp(values, rhs), Ordering::Greater);

    let (zero_words, zero_bits) = unsafe { trailing_zeros(&rhs) };
    let mut left = shr(values, zero_words, zero_bits);
    let right = shr(rhs, zero_words, zero_bits);

    // right is odd now
    if !(right[0] == 1 && right.len() == 1) {
        div_assign_by_odd(&mut left, &right);
    }

    left
}

/// Divide a number by a divisor.
///
/// Used in the normalization of fractions after the GCD was computed (which is the `rhs` argument).
///
/// # Arguments
///
/// * `values`: A nonzero, >1
#[inline]
pub fn div_assign_by_odd<const S: usize>(
    values: &mut SmallVec<[usize; S]>,
    rhs: &SmallVec<[usize; S]>,
) {
    debug_assert!(is_well_formed(values));
    debug_assert!(!values.is_empty());
    debug_assert!(is_well_formed(rhs));
    debug_assert!(!rhs.is_empty());
    let one: SmallVec<[usize; S]> = smallvec![1];
    debug_assert_ne!(rhs, &one);
    debug_assert_eq!(rhs[0] % 2, 1);
    debug_assert_eq!(cmp(values, rhs), Ordering::Greater);

    // We assume that values % rhs == 0

    match rhs.len() {
        1 => div_assign_one_word(values, rhs[0]),
        2 => div_assign_two_words(values, rhs[1], rhs[0]),
        _ => {
            // rhs.len() > 2
            div_assign_n_words(values, rhs);
        }
    }
}

#[inline]
pub fn div_assign_one_word<const S: usize>(values: &mut SmallVec<[usize; S]>, rhs: usize) {
    debug_assert!(is_well_formed(values));
    debug_assert!(!values.is_empty());
    debug_assert_eq!(rhs % 2, 1);
    // We assume that values % rhs == 0

    if values.len() == 1 {
        values[0] /= rhs;
        return
    }

    let divisor_zeros = rhs.leading_zeros();
    match divisor_zeros {
        0 => {
            // rhs > usize::MAX / 2

            let mut remainder = *values.last().unwrap();
            if remainder < rhs {
                values.pop();
            } else {
                remainder -= rhs;
                *values.last_mut().unwrap() = 1;
            };

            let rhs_inverse = invert(rhs);
            for i in (0..values.len()).rev() {
                let (quotient, new_remainder) = div_preinv(remainder, values[i], rhs, rhs_inverse);
                remainder = new_remainder;

                values[i] = quotient;
            }

            // The last remainder is a valid value
        }
        _ => {
            // rhs <= usize::MAX / 2

            let last = *values.last().unwrap();
            let mut remainder = if last < rhs {
                values.pop();
                last
            } else {
                0
            };

            let divisor = rhs << divisor_zeros;
            let bits_per_word_minus_divisor_zeros = BITS_PER_WORD as u32 - divisor_zeros;

            let divisor_inverse = invert(divisor);
            let mut edit_higher = *values.last().unwrap();

            remainder = (remainder << divisor_zeros) | (edit_higher >> bits_per_word_minus_divisor_zeros);
            for i in (1..values.len()).rev() {
                let edit_lower = values[i - 1];
                let shifted = (edit_higher << divisor_zeros) | (edit_lower >> bits_per_word_minus_divisor_zeros);

                let (quotient, new_quotient) = div_preinv(remainder, shifted, divisor, divisor_inverse);
                remainder = new_quotient;
                values[i] = quotient;
                edit_higher = edit_lower;
            }

            let shifted = edit_higher << divisor_zeros;
            let (q, _remainder) = div_preinv(remainder, shifted, divisor, divisor_inverse);
            values[0] = q;

            // The last remainder is a valid value
        }
    }
}

#[inline]
pub fn div_preinv(high: usize, low: usize, divisor: usize, divisor_inverted: usize) -> (usize, usize) {
    let (quotient_high, quotient_low) = mul(divisor_inverted, high);
    let (mut quotient_high, quotient_low) = add_2(quotient_high, quotient_low, high + 1, low);

    let mut remainder = low.wrapping_sub(quotient_high.wrapping_mul(divisor));
    if remainder > quotient_low {
        quotient_high = quotient_high.wrapping_sub(1);
        remainder = remainder.wrapping_add(divisor);
    }

    if remainder >= divisor {
        quotient_high = quotient_high.wrapping_add(1);
        remainder = remainder.wrapping_sub(divisor);
    }

    (quotient_high, remainder)
}

#[inline]
pub fn invert(value: usize) -> usize {
    debug_assert_ne!(value, 0);
    debug_assert!(value.leading_zeros() == 0); // value > usize::MAX / 2

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    fn inner(high: usize, low: usize, divisor: usize) -> usize {
        let mut quotient;

        unsafe {
            asm!(
            "div {d}",
            d = in(reg) divisor,

            in("rdx") high,
            inout("rax") low => quotient,
            );
        }

        quotient
    }

    inner(!value, usize::MAX, value)
}

#[inline]
pub fn div_assign_two_words<const S: usize>(
    values: &mut SmallVec<[usize; S]>,
    mut divisor_high: usize, mut divisor_low: usize,
) {
    let zero_count = divisor_high.leading_zeros();
    match zero_count {
        0 => {
            // divisor_high > usize::MAX / 2

            unsafe {
                let most_significant_quotient = div_assign_two_words_helper(values, divisor_high, divisor_low);
                if most_significant_quotient > 0 {
                    *values.last_mut().unwrap() = most_significant_quotient;
                } else {
                    values.pop();
                }
            }
        }
        _ => {
            divisor_high <<= zero_count;
            divisor_high |= divisor_low >> (BITS_PER_WORD - zero_count);
            divisor_low <<= zero_count;

            let carry = unsafe {
                let carry = shl_mut_overflowing(values, zero_count);
                if let Some(carry) = carry {
                    values.push(carry.get());
                }
                carry
            };

            debug_assert!(is_well_formed(values));

            unsafe {
                let most_significant_quotient = div_assign_two_words_helper(values, divisor_high, divisor_low);
                if carry.is_none() && most_significant_quotient > 0 {
                    *values.last_mut().unwrap() = most_significant_quotient;
                } else {
                    values.pop();
                }
            }
        }
    }
}

#[inline]
unsafe fn div_assign_two_words_helper<const S: usize>(
    values: &mut SmallVec<[usize; S]>,
    divisor_high: usize, divisor_low: usize,
) -> usize {
    let nr_values = values.len();
    let mut remainder_high = values[nr_values - 1];
    let mut remainder_low = values[nr_values - 2];

    values.pop();

    let mut most_significant_q_word = 0;
    if remainder_high >= divisor_high && (remainder_high > divisor_high || remainder_low >= divisor_low) {
        let (remainder_high_new, remainder_low_new) = sub_2(remainder_high, remainder_low, divisor_high, divisor_low);
        remainder_high = remainder_high_new;
        remainder_low = remainder_low_new;
        most_significant_q_word = 1;
    }

    let divisor_inverse = invert_pi(divisor_high, divisor_low);

    for i in (0..nr_values - 2).rev() {
        let value = values[i];
        let (quotient, remainder_high_new, remainder_low_new) =
            divrem_3by2(remainder_high, remainder_low, value, divisor_high, divisor_low, divisor_inverse);
        remainder_high = remainder_high_new;
        remainder_low = remainder_low_new;

        values[i] = quotient;
    }

    most_significant_q_word
}

#[inline]
pub fn div_assign_n_words<const S: usize>(
    values: &mut SmallVec<[usize; S]>,
    rhs: &SmallVec<[usize; S]>,
) {
    debug_assert!(is_well_formed(values));
    debug_assert!(values.len() > 2);
    debug_assert!(rhs.len() > 2);
    debug_assert_eq!(rhs[0] % 2, 1);
    // We assume that values % rhs == 0

    let rhs_high = *rhs.last().unwrap();
    let leading_zeros = rhs_high.leading_zeros();

    let divisor = if leading_zeros > 0 {
        unsafe {
            let carry = shl_mut_overflowing(values, leading_zeros);
            if let Some(carry) = carry {
                // TODO(PERFORMANCE): Avoid this allocation before `values` gets smaller
                values.push(carry.get())
            }
        }

        shl(rhs, leading_zeros)
    } else {
        rhs.clone()
    };
    debug_assert!(values.len() > rhs.len());

    let divisor_length = divisor.len();
    let divisor_inverse = invert_pi(divisor[divisor_length - 1], divisor[divisor_length - 2]);
    let length_difference = values.len() - divisor.len();
    debug_assert!(length_difference >= 1);

    div_assign_n_words_helper(values, &divisor, divisor_inverse);
}

#[inline]
pub fn div_assign_n_words_helper<const S: usize>(
    values: &mut SmallVec<[usize; S]>,
    divisor: &SmallVec<[usize; S]>,
    divisor_inverse: usize,
) {
    debug_assert!(*divisor.last().unwrap() > usize::MAX / 2);
    debug_assert!(values.len() >= divisor.len());
    debug_assert!(divisor.len() > 2);

    let length_difference = values.len() - divisor.len();
    let max_word = match cmp(&values[length_difference..], divisor) {
        Ordering::Less => 0,
        Ordering::Equal | Ordering::Greater => {
            unsafe { sub_assign_slice(&mut values[length_difference..], divisor) };
            1
        },
    };

    let divisor_high = divisor[divisor.len() - 1];
    let divisor_low = divisor[divisor.len() - 2];

    let mut value_high = *values.last().unwrap();
    for i in (0..length_difference).rev() {
        let value_middle = values[i + divisor.len() - 1];
        let value_low = values[i + divisor.len() - 2];

        let q = if value_high == divisor_high && value_middle == divisor_low {
            unsafe {
                submul_slice(&mut values[i..(i + divisor.len())], divisor, !0);
            }
            value_high = values[i + divisor.len() - 1];
            !0
        } else {
            let (q, remainder_high, mut remainder_low) = divrem_3by2(
                value_high, value_middle, value_low,
                divisor_high, divisor_low, divisor_inverse,
            );

            let carry = unsafe {
                submul_slice(&mut values[i..(i + (divisor.len() - 2))], &divisor[..(divisor.len() - 2)], q)
            };

            value_high = remainder_high;

            let carryx = remainder_low < carry;
            remainder_low = remainder_low.wrapping_sub(carry);
            let carry = value_high < carryx as usize;
            if carryx {
                value_high = value_high.wrapping_sub(1);
            }
            values[i + divisor.len() - 2] = remainder_low;

            if carry {
                let carry = unsafe {
                    add_assign_slice(
                        &mut values[i..(i + divisor.len() - 1)],
                        &divisor[..(divisor.len() - 1)],
                    )
                };
                value_high = divisor_high.wrapping_add(value_high).wrapping_add(carry as usize);
                q - 1
            } else {
                q
            }
        };

        values[i + 3] = q;
    }

    unsafe {
        copy(values[3..].as_ptr(), values.as_mut_ptr(), length_difference);
    }
    values.truncate(length_difference);

    if max_word > 0 {
        values.push(max_word);
    }
}

#[inline]
pub fn invert_pi(high: usize, low: usize) -> usize {
    let mut inverse = invert(high);
    let (mut result, carry) = high.wrapping_mul(inverse).overflowing_add(low);

    if carry {
        inverse = inverse.wrapping_sub(1);
        let mask = if result >= high { !0 } else { 0 };
        result = result.wrapping_sub(high);
        inverse = inverse.wrapping_add(mask);
        result = result.wrapping_sub(mask & high);
    }

    let (result_high, _result_low) = mul(low, inverse);
    result = result.wrapping_add(result_high);

    if result < result_high {
        inverse = inverse.wrapping_sub(1);
        if result >= high && (result > high || result_high >= low) {
            inverse = inverse.wrapping_sub(1);
        }
    }

    inverse
}

#[inline]
pub fn divrem_3by2(
    numerator_high: usize, numerator_middle: usize, numerator_low: usize,
    divisor_high: usize, divisor_low: usize,
    divisor_inverse: usize,
) -> (usize, usize, usize) {
    let (quotient_high, quotient_low) = mul(numerator_high, divisor_inverse);
    let (quotient_high, quotient_low) = add_2(quotient_high, quotient_low, numerator_high, numerator_middle);

    let remainder_high = numerator_middle.wrapping_sub(divisor_high.wrapping_mul(quotient_high));
    let (remainder_high, remainder_low) = sub_2(remainder_high, numerator_low, divisor_high, divisor_low);
    let (result_high, result_low) = mul(divisor_low, quotient_high);
    let (remainder_high, remainder_low) = sub_2(remainder_high, remainder_low, result_high, result_low);

    let quotient_high = quotient_high.wrapping_add(1);
    let mask = if remainder_high >= quotient_low { !0 } else { 0 };

    let quotient_high = quotient_high.wrapping_add(mask);
    let (remainder_high, remainder_low) = add_2(remainder_high, remainder_low, mask & divisor_high, mask & divisor_low);

    if remainder_high >= divisor_high && (remainder_high > divisor_high || remainder_low >= divisor_low) {
        let (remainder_high, remainder_low) = sub_2(remainder_high, remainder_low, divisor_high, divisor_low);
        (quotient_high + 1, remainder_high, remainder_low)
    } else {
        (quotient_high, remainder_high, remainder_low)
    }
}

#[cfg(test)]
mod test {
    use smallvec::smallvec;

    use crate::rational::big::ops::div::{div_assign_n_words, div_assign_one_word, div_assign_two_words, div_preinv, invert};
    use crate::rational::big::ops::test::SV;

    #[test]
    fn test_invert() {
        let divisor = (1 << 63) + 1;
        assert!(divisor > usize::MAX / 2);
        let inverted = invert(divisor);
        assert_eq!(div_preinv(1, (1 << 63) + 3, divisor, inverted), (3, 0));

        let divisor = (1 << 63) + 3;
        assert!(divisor > usize::MAX / 2);
        let inverted = invert(divisor);
        assert_eq!(div_preinv(1, (1 << 63) + 9, divisor, inverted), (3, 0));

        let divisor = 0b11101011_11101011_11101011_11101011_11101011_11101011_11101011_11101011;
        assert!(divisor > usize::MAX / 2);
        let inverted = invert(divisor);
        assert_eq!(
            div_preinv(0xebebebdd_39fa0c38, 0x23232331_d51502d6, divisor, inverted),
            (18446744005223104770, 0),
        );
        assert_eq!(
            div_preinv(0xebebebdd_39fa0c38, 0x23232331_d51502d6 + 1, divisor, inverted),
            (18446744005223104770, 1),
        );
    }

    #[test]
    fn test_div_assign_one_word() {
        let mut x: SV = smallvec![(1 << 63) + 3, 1];
        div_assign_one_word(&mut x, (1 << 63) + 1);
        let expected: SV = smallvec![3];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![7, 5];
        div_assign_one_word(&mut x, 3);
        let expected: SV = smallvec![0b10101010_10101010_10101010_10101010_10101010_10101010_10101010_10101101, 1];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![10, 5];
        div_assign_one_word(&mut x, 3);
        let expected: SV = smallvec![0b10101010_10101010_10101010_10101010_10101010_10101010_10101010_10101110, 1];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![13, 5];
        div_assign_one_word(&mut x, 3);
        let expected: SV = smallvec![0b10101010_10101010_10101010_10101010_10101010_10101010_10101010_10101111, 1];
        assert_eq!(x, expected);
    }

    #[test]
    fn test_div_assign_two_words() {
        let mut x: SV = smallvec![0xc71b661b8e833636, 0x89ef44975a72d747, 0xbe134785635c9c];
        div_assign_two_words(&mut x, 0xdbc78074cfd441a, 0x436471cb87f32d37);
        let expected: SV = smallvec![0xdd669098c22a67a];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0x495341ae0c1d4c9d, 0xafc3a84744e1bdd7, 0x9f2665d7750936b];
        div_assign_two_words(&mut x, 0x1e625595920b59de, 0x4cd07b317475f15b);
        let expected: SV = smallvec![0x53ce9359a2696367];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0x502283b127ece68a, 0x677d3aecfcf1bc3c, 0x68f95794dd6087d9];
        div_assign_two_words(&mut x, 0x882181dcbd42a060, 0xe7925f29a32f6c15);
        let expected: SV = smallvec![0xc5687a4d9e248ce2];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0x07a772cd1404bcfa, 0xfac7fe101218ac41, 0x60d2d048dcff4cf9];
        div_assign_two_words(&mut x, 0xd90be64d0b59e0fc, 0x1e2b418209d3b1c3);
        let expected: SV = smallvec![0x723352fc3ea4d57e];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0x07a772cd1404bcfa, 0xfac7fe101218ac41, 0x60d2d048dcff4cf9];
        div_assign_two_words(&mut x, 0xd90be64d0b59e0fc, 0x1e2b418209d3b1c3);
        let expected: SV = smallvec![0x723352fc3ea4d57e];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0x49e095c30a7834ba, 0x43c2cd86733285dd];
        div_assign_two_words(&mut x, 0x9eb298b9, 0x24dfd1ac14277c6f);
        let expected: SV = smallvec![0x6d4ea7e6];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![2, 2];
        div_assign_two_words(&mut x, 1, 1);
        let expected: SV = smallvec![2];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![3, 3];
        div_assign_two_words(&mut x, 1, 1);
        let expected: SV = smallvec![3];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![4, 4];
        div_assign_two_words(&mut x, 1, 1);
        let expected: SV = smallvec![4];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![5, 5];
        div_assign_two_words(&mut x, 1, 1);
        let expected: SV = smallvec![5];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0x7c480047c60bb55e, 0xeb062cb4eecc1962, 0xf3d645eaefdafcbb, 0xaa438e52cea2f67];
        div_assign_two_words(&mut x, 0x1, 0x89b95e707df60d03);
        let expected: SV = smallvec![0xbe18d24aca377bca, 0xdf9674145900d1b2, 0x6eb4b1c4f2a7557];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![
            0x433,
            0xf7747cec3a9fe67f,
            0xb59c9be2ad81279a,
            0x0b83c9fa41b63a26,
            0xfa1894e7722a708f,
            0xded7355f4c85a8d7,
            0xbf30b813a65f7c5f,
            0x8f2a109f6bc181ec,
            0xe4f6a541276877e1,
            0x30d897894b487313,
            0x34514e0c2155ff80,
            0x91593095743ee9f7,
            0xb5a16a4d2ebd92dd,
            0x17726c637e1f2095,
            0x4576a2783977bf94,
            0x18c1ff62b47c966b,
        ];
        x.reverse();
        div_assign_two_words(&mut x, 0xf8d25129fe48034e, 0xce2ac7f28b9e32a7);
        let mut expected: SV = smallvec![
            0x453,
            0x020e462a9467a570,
            0xa98089d62f0cf3fb,
            0x7cce73193ce9a5ba,
            0x5212767b5668ec0c,
            0xe03e13e6745c98f5,
            0x20028ba3039e5ad7,
            0x24aa943e20d58e45,
            0x67abab1049c7cd02,
            0x7e195ef4a0ea3721,
            0xbb9fcf0be8438259,
            0xc8c5f013d96c0bac,
            0x4472187b4055934e,
            0x510168e6363b0a9d,
        ];
        expected.reverse();
        assert_eq!(x, expected);
    }

    #[test]
    fn test_div_assign_n_words() {
        let mut x: SV = smallvec![3, 3, 3];
        let divisor: SV = smallvec![1, 1, 1];
        div_assign_n_words(&mut x, &divisor);
        let expected: SV = smallvec![3];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![3, 3, 3, 3];
        let divisor: SV = smallvec![1, 1, 1, 1];
        div_assign_n_words(&mut x, &divisor);
        let expected: SV = smallvec![3];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![1, 2, 2, 1];
        let divisor: SV = smallvec![1, 1, 1];
        div_assign_n_words(&mut x, &divisor);
        let expected: SV = smallvec![1, 1];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![
            0x426c694a49d8e6e8,
            0xf7110260b98b2714,
            0xd77eaaba0c9edebb,
            0x1ebf6edad66a22f9,
            0xec91987b2f52425e,
            0x7146b08a5e154,
        ];
        let divisor: SV = smallvec![0x2090b6d374079b2f, 0xd14fd230f03d41d8, 0x2cd0de4066];
        div_assign_n_words(&mut x, &divisor);
        let expected: SV = smallvec![
            0xf1ca2432006aad98,
            0x249ebfb74debc642,
            0x00a2b24c5fc31f96,
            0x2871,
        ];
        assert_eq!(x, expected);
    }
}
