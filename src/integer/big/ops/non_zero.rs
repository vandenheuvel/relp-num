use std::cmp::{min, Ordering};
use std::iter::repeat;
use std::num::NonZeroUsize;
use std::ptr;

use smallvec::SmallVec;

use crate::integer::big::BITS_PER_WORD;
use crate::integer::big::ops::building_blocks::{addmul_1, carrying_add, carrying_add_mut, carrying_sub, carrying_sub_mut, is_well_formed, is_well_formed_non_zero, mul_1, sub_assign_slice, sub_n, to_twos_complement, widening_mul};
use crate::integer::big::properties::cmp;
use crate::rational::big::properties::cmp_single;

#[inline]
pub fn shr_mut<const S: usize>(values: &mut SmallVec<[usize; S]>, words: usize, bits: u32) {
    debug_assert_shr_constraints(values, words, bits);

    let original_number_words = values.len();

    if bits > 0 {
        for i in 0..(original_number_words - words - 1) {
            values[i] = values[i + words] >> bits;
            values[i] |= values[i + words + 1] << (BITS_PER_WORD - bits);
        }

        let last_shifted = values.last().unwrap() >> bits;
        let words_to_keep = if last_shifted > 0 {
            values[original_number_words - words - 1] = last_shifted;
            original_number_words - words
        } else {
            original_number_words - words - 1
        };

        values.truncate(words_to_keep);
    } else {
        let remaining_words = original_number_words - words;
        unsafe {
            ptr::copy(values[words..].as_ptr(), values.as_mut_ptr(), remaining_words);
        }
        values.truncate(remaining_words);
    }

    debug_assert!(is_well_formed(values));
}

#[inline]
pub fn shr<const S: usize>(values: &[usize], words_to_remove: usize, bits: u32) -> SmallVec<[usize; S]> {
    debug_assert_shr_constraints(values, words_to_remove, bits);

    if bits > 0 {
        let last_shifted = values.last().unwrap() >> bits;
        let words_to_keep = if last_shifted > 0 {
            values.len() - words_to_remove
        } else {
            values.len() - words_to_remove - 1
        };

        let mut result = SmallVec::with_capacity(words_to_keep);
        for i in 0..(values.len() - words_to_remove - 1) {
            let mut result_word = values[i + words_to_remove] >> bits;
            result_word |= values[i + words_to_remove + 1] << (BITS_PER_WORD - bits);
            result.push(result_word);
        }

        if last_shifted > 0 {
            result.push(last_shifted);
        }

        result
    } else {
        SmallVec::from_slice(&values[words_to_remove..])
    }
}

#[inline]
pub fn shl_mut<const S: usize>(values: &mut SmallVec<[usize; S]>, words: usize, bits: u32) {
    debug_assert!(is_well_formed_non_zero(values));

    if bits > 0 {
        let original_length = values.len();

        let overflows = bits > values.last().unwrap().leading_zeros();
        if overflows {
            // These values will be overwritten
            values.extend(repeat(0).take(words + 1));
            *values.last_mut().unwrap() = values[original_length - 1] >> (BITS_PER_WORD - bits);
        } else {
            // These values will be overwritten
            values.extend(repeat(0).take(words));
        }

        for i in (1..original_length).rev() {
            values[words + i] = values[i] << bits;
            values[words + i] |= values[i - 1] >> (BITS_PER_WORD - bits);
        }
        values[words] = values[0] << bits;
    } else {
        values.reserve(words);
        let old_length = values.len();
        unsafe {
            values.set_len(old_length + words);
            ptr::copy(values.as_ptr(), values.as_mut_ptr().add(words),old_length);
        }
    }

    values[..words].fill(0);

    debug_assert!(is_well_formed_non_zero(values));
}

#[inline]
pub unsafe fn shl_mut_overflowing<const S: usize>(values: &mut SmallVec<[usize; S]>, bits: u32) -> Option<NonZeroUsize> {
    debug_assert_ne!(bits, 0);
    debug_assert!(bits < BITS_PER_WORD);

    let original_number_words = values.len();

    let value_highest = values.last().unwrap();
    let leading_zeros = value_highest.leading_zeros();
    let carry = if bits > leading_zeros {
        Some(NonZeroUsize::new(value_highest >> (BITS_PER_WORD - bits)).unwrap())
    } else {
        None
    };

    for i in (1..original_number_words).rev() {
        values[i] <<= bits;
        if bits > 0 {
            values[i] |= values[i - 1] >> (BITS_PER_WORD - bits);
        }
    }

    values[0] <<= bits;

    carry
}

#[inline]
pub fn shl<const S: usize>(values: &[usize], bits: u32) -> SmallVec<[usize; S]> {
    debug_assert_ne!(bits, 0);
    debug_assert!(bits < BITS_PER_WORD);
    debug_assert!(bits <= values.last().unwrap().leading_zeros());

    let mut result = SmallVec::with_capacity(values.len());
    result.push(values[0] << bits);
    for i in 1..values.len() {
        let mut result_value = values[i] << bits;
        if bits > 0 {
            result_value |= values[i - 1] >> (BITS_PER_WORD - bits);
        }
        result.push(result_value);
    }

    result
}

#[inline]
pub fn debug_assert_shr_constraints(values: &[usize], words_to_remove: usize, bits: u32) {
    debug_assert!(is_well_formed_non_zero(values));
    debug_assert!(!values.is_empty(), "Should not be called on a zero value");
    debug_assert!(words_to_remove < values.len(), "Can't shift away all words");
    debug_assert!(bits < BITS_PER_WORD, "Use the `words` argument to shift with entire words");
}

#[inline]
pub fn add_assign<const S: usize>(values: &mut SmallVec<[usize; S]>, rhs: &[usize]) {
    debug_assert!(is_well_formed(values));
    debug_assert!(is_well_formed(rhs));

    let mut i = 0;

    let mut carry = false;
    while i < values.len() && i < rhs.len() {
        carry = carrying_add_mut(&mut values[i], rhs[i], carry);
        i += 1;
    }

    while i < rhs.len() {
        let (new_value, new_carry) = rhs[i].overflowing_add(carry as usize);
        values.push(new_value);
        carry = new_carry;
        i += 1;
    }

    while carry && i < values.len() {
        let (new_value, new_carry) = values[i].overflowing_add(carry as usize);
        values[i] = new_value;
        carry = new_carry;
        i += 1;
    }

    if carry {
        values.push(1);
    }
}

#[inline]
pub fn add_assign_single_non_zero<const S: usize>(
    values: &mut SmallVec<[usize; S]>,
    rhs: usize,
) {
    let mut carry = carrying_add_mut(&mut values[0], rhs, false);
    let mut i = 1;
    while carry && i < values.len() {
        carry = carrying_add_mut(&mut values[i], 0, true);
        i += 1;
    }
    if carry {
        values.push(1);
    }
}

#[inline]
pub(crate) fn mul_assign_single_non_zero<const S: usize>(
    values: &mut SmallVec<[usize; S]>, rhs: usize,
) {
    debug_assert!(!values.is_empty());
    
    let (mut previous_high, low) = widening_mul(values[0], rhs);
    values[0] = low;
    let mut carry = false;
    for i in 1..values.len() {
        let (high, low) = widening_mul(values[i], rhs);
        let (value_new, carry_new) = carrying_add(previous_high, low, carry);
        values[i] = value_new;
        carry = carry_new;
        previous_high = high;
    }

    let (value_new, carry) = carrying_add(previous_high, 0, carry);
    if value_new > 0 {
        values.push(value_new);
        if carry {
            values.push(1);
        }
    }
}

#[must_use]
#[inline]
pub unsafe fn mul_non_zero<const S: usize>(values: &[usize], rhs: &[usize]) -> SmallVec<[usize; S]> {
    debug_assert!(is_well_formed(values));
    debug_assert!(is_well_formed(rhs));
    debug_assert!(!values.is_empty());
    debug_assert!(!rhs.is_empty());

    let mut result = SmallVec::with_capacity(values.len() + rhs.len());

    let (large, small) = if rhs.len() > values.len() {
        (rhs, values)
    } else {
        (values, rhs)
    };

    let carry = mul_1(&mut result, large, small[0]);
    result.set_len(large.len());
    result.push(carry);

    for i in 1..small.len() {
        let carry = addmul_1(&mut result[i..], large, large.len() as i32, small[i]);
        result.push(carry);
    }

    if *result.last().unwrap() == 0 {
        result.pop();
    }

    debug_assert!(is_well_formed(&result));

    result
}

#[inline]
pub unsafe fn sub<const S: usize>(
    values: &SmallVec<[usize; S]>,
    rhs: &SmallVec<[usize; S]>,
) -> SmallVec<[usize; S]> {
    debug_assert!(is_well_formed(values));
    debug_assert!(is_well_formed(rhs));
    debug_assert_eq!(cmp(values, rhs), Ordering::Greater);

    let mut result = SmallVec::with_capacity(values.len());
    // Will be overwritten in the unsafe block, but this is safe and extends the length
    result.extend(repeat(0).take(rhs.len()));

    let mut carry = {
        sub_n(&mut result, values, rhs, rhs.len() as i32) > 0
    };

    while carry {
        debug_assert!(values.len() > rhs.len());
        let (value, new_carry) = carrying_sub(values[result.len()], 0, carry);
        carry = new_carry;
        result.push(value);
    }

    if result.len() < values.len() {
        result.extend_from_slice(&values[result.len()..]);
    } else {
        while let Some(0) = result.last() {
            result.pop();
        }
    }

    result
}

/// Subtract assign from a value.
///
/// # Arguments
///
/// * `values`: is larger than `rhs` but might have the most significant word(s) already removed, if
/// they were equal to `rhs`. It is as such not necessarily well formed and can't be easily compared
/// to `rhs`.
/// * `rhs`: value to subtract.
#[inline]
pub unsafe fn sub_assign_result_positive<const S: usize>(
    values: &mut SmallVec<[usize; S]>,
    rhs: &SmallVec<[usize; S]>,
) {
    let smallest = min(values.len(), rhs.len());
    let mut carry = sub_assign_slice(&mut values[..smallest], &rhs[..smallest]);

    let mut index = 0;
    while carry {
        debug_assert!(values.len() > rhs.len());
        carry = carrying_sub_mut(&mut values[rhs.len() + index], 0, true);
        index += 1;
    }

    while let Some(0) = values.last() {
        values.pop();
    }

    debug_assert!(is_well_formed(values));
}

#[inline]
pub fn sub_assign_single_result_positive<const S: usize>(
    values: &mut SmallVec<[usize; S]>, rhs: usize,
) {
    debug_assert!(is_well_formed_non_zero(values));
    debug_assert_eq!(cmp_single(values, rhs), Ordering::Greater);

    let mut carry = carrying_sub_mut(&mut values[0], rhs, false);

    debug_assert!(is_well_formed_non_zero(values));

    let mut index = 0;
    while carry {
        debug_assert!(values.len() > 1);
        carry = carrying_sub_mut(&mut values[1 + index], 0, carry);
        index += 1;
    }

    while let Some(0) = values.last() {
        values.pop();
    }

    debug_assert!(is_well_formed_non_zero(values));
}

#[inline]
pub(crate) fn subtracting_cmp<const S: usize>(left: &mut SmallVec<[usize; S]>, right: &[usize]) -> Ordering {
    debug_assert!(is_well_formed_non_zero(left));
    debug_assert!(is_well_formed_non_zero(right));

    match left.len().cmp(&right.len()) {
        Ordering::Less => {
            let mut carry = false;
            let mut i = 0;
            while i < left.len() {
                // TODO(PERFORMANCE): Is assembler faster?
                let (new_value, new_carry) = carrying_sub(right[i], left[i], carry);
                left[i] = new_value;
                carry = new_carry;
                i += 1;
            }

            while carry {
                let (new_value, new_carry) = carrying_sub(right[i], 0, true);
                left.push(new_value);
                carry = new_carry;
                i += 1;
            }

            left.extend_from_slice(&right[i..]);

            while *left.last().unwrap() == 0 {
                left.pop();
            }

            Ordering::Less
        }
        Ordering::Equal => {
            let mut carry = false;
            for i in 0..left.len() {
                // TODO(PERFORMANCE): Is assembler faster?
                carry = carrying_sub_mut(&mut left[i], right[i], carry);
            }

            if carry {
                // result is negative
                to_twos_complement(left);
                while *left.last().unwrap() == 0 {
                    left.pop();
                }
                Ordering::Less
            } else {
                // result is zero or positive

                while let Some(0) = left.last() {
                    left.pop();
                }

                // TODO(PERFORMANCE): This test is often not necessary, as it is known in advance
                //  whether the result can be zero or not.
                if left.is_empty() {
                    Ordering::Equal
                } else {
                    Ordering::Greater
                }
            }
        }
        Ordering::Greater => {
            let mut carry = unsafe { sub_assign_slice(&mut left[..right.len()], right) };
            let mut i = 0;
            while carry && i + right.len() < left.len() {
                carry = carrying_sub_mut(&mut left[i + right.len()], 0, true);
                i += 1;
            }
            debug_assert!(!carry);
            while *left.last().unwrap() == 0 {
                left.pop();
            }

            Ordering::Greater
        }
    }
}

#[inline]
pub(crate) fn subtracting_cmp_ne_single<const S: usize>(left: &mut SmallVec<[usize; S]>, right: usize) -> Ordering {
    debug_assert!(is_well_formed_non_zero(left));
    debug_assert_ne!(right, 0);
    debug_assert!(left.len() > 1 || left[0] != right);

    if left.len() > 1 {
        // result won't be negative
        let mut carry = carrying_sub_mut(&mut left[0], right, false);

        let mut i = 1;
        while carry {
            carry = carrying_sub_mut(&mut left[i], 0, true);
            i += 1;
        }

        while let Some(0) = left.last() {
            left.pop();
        }

        Ordering::Greater
    } else {
        // result might be negative
        if left[0] < right {
            left[0] = right - left[0];
            Ordering::Less
        } else {
            // left[0] > right
            left[0] -= right;
            Ordering::Greater
        }
    }
}

#[must_use]
#[inline]
pub unsafe fn is_one_non_zero(values: &[usize]) -> bool {
    debug_assert!(is_well_formed(values));
    debug_assert!(!values.is_empty());

    *values.get_unchecked(0) == 1 && values.len() == 1
}

#[inline]
pub unsafe fn both_not_one_non_zero(left: &[usize], right: &[usize]) -> bool {
    debug_assert!(!left.is_empty());
    debug_assert!(!right.is_empty());

    (*left.get_unchecked(0) != 1 || left.len() > 1) && (*right.get_unchecked(0) != 1 || right.len() > 1)
}

#[cfg(test)]
mod test {
    use std::mem;
    use std::num::NonZeroUsize;

    use smallvec::{smallvec, SmallVec};

    use crate::integer::big::BITS_PER_WORD;
    use crate::integer::big::io::from_str_radix;
    use crate::integer::big::ops::non_zero::{both_not_one_non_zero, shl_mut, shl_mut_overflowing, shr, shr_mut};

    #[test]
    fn test_shr() {
        type SV = SmallVec<[usize; 4]>;

        let x: SV = smallvec![1];
        let expected: SV = smallvec![1];
        assert_eq!(shr::<4>(&x, 0, 0), expected);

        let x: SV = smallvec![0, 1];
        let expected: SV = smallvec![1];
        assert_eq!(shr::<4>(&x, 1, 0), expected);

        let x: SV = smallvec![0, 1];
        let expected: SV = smallvec![1 << (mem::size_of::<usize>() * 8 - 1)];
        assert_eq!(shr::<4>(&x, 0, 1), expected);

        let x: SV = smallvec![0, 0, 0, 1];
        let expected: SV = smallvec![0, 1 << (mem::size_of::<usize>() * 8 - 1)];
        assert_eq!(shr::<4>(&x, 1, 1), expected);

        let x: SV = smallvec![0, 1];
        let expected: SV = smallvec![2];
        assert_eq!(shr::<4>(&x, 0, (mem::size_of::<usize>() * 8 - 1) as u32), expected);

        // 15588921427233345156 // 4
        let x: SV = smallvec![15588921427233345156];
        let expected: SV = smallvec![3897230356808336289];
        assert_eq!(shr::<4>(&x, 0, 2), expected);

        // 15588921427233345156 // 4
        let x: SV = smallvec![131522304505784511, 2433];
        assert_eq!(shr::<4>(&x, 0, 0), x);
    }

    #[test]
    fn test_shr_mut() {
        type SV = SmallVec<[usize; 4]>;

        let mut x: SV = smallvec![1];
        shr_mut(&mut x, 0, 0);
        let expected: SV = smallvec![1];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![1];
        shr_mut(&mut x, 0, 1);
        let expected: SV = smallvec![];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 1];
        shr_mut(&mut x, 1, 1);
        let expected: SV = smallvec![];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![6184, 1];
        shr_mut(&mut x, 1, 1);
        let expected: SV = smallvec![];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 1];
        shr_mut(&mut x, 1, 0);
        let expected: SV = smallvec![1];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 1];
        shr_mut(&mut x, 0, 1);
        let expected: SV = smallvec![1 << (mem::size_of::<usize>() * 8 - 1)];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 0, 0, 1];
        shr_mut(&mut x, 1, 1);
        let expected: SV = smallvec![0, 1 << (mem::size_of::<usize>() * 8 - 1)];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 1];
        shr_mut(&mut x, 0, (mem::size_of::<usize>() * 8 - 1) as u32);
        let expected: SV = smallvec![2];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 1 << (80 - 64)];
        shr_mut(&mut x, 0, 0);
        let expected: SV = smallvec![0, 1 << (80 - 64)];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 12511854210725346487, 1932217123071064976, 10302437120704275430, 18852552];
        shr_mut(&mut x, 1, 0);
        let expected: SV = smallvec![12511854210725346487, 1932217123071064976, 10302437120704275430, 18852552];
        assert_eq!(x, expected);
    }

    #[test]
    fn test_shl_mut_overflowing() {
        type SV = SmallVec<[usize; 4]>;

        let mut x: SV = smallvec![0, 1];
        let carry = unsafe { shl_mut_overflowing(&mut x, 1) };
        let expected: SV = smallvec![0, 2];
        assert_eq!(x, expected);
        assert_eq!(carry, None);

        let mut x: SV = smallvec![0, 0, 0, 1];
        let carry = unsafe { shl_mut_overflowing(&mut x, 1) };
        let expected: SV = smallvec![0, 0, 0, 2];
        assert_eq!(x, expected);
        assert_eq!(carry, None);

        let mut x: SV = smallvec![0, 0, 2_usize.pow((mem::size_of::<usize>() * 8 - 2) as u32)];
        let carry = unsafe { shl_mut_overflowing(&mut x, 1) };
        let expected: SV = smallvec![0, 0, 2_usize.pow((mem::size_of::<usize>() * 8 - 1) as u32)];
        assert_eq!(x, expected);
        assert_eq!(carry, None);

        let mut x: SV = smallvec![0, 0, 2_usize.pow((mem::size_of::<usize>() * 8 - 1) as u32)];
        let carry = unsafe { shl_mut_overflowing(&mut x, 1) };
        let expected: SV = smallvec![0, 0, 0];
        assert_eq!(x, expected);
        assert_eq!(carry, Some(NonZeroUsize::new(1).unwrap()));
    }

    #[test]
    fn test_shl_mut() {
        type SV = SmallVec<[usize; 4]>;

        let mut x: SV = smallvec![0, 1];
        shl_mut(&mut x, 0, 1);
        let expected: SV = smallvec![0, 2];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 0, 0, 1];
        shl_mut(&mut x, 2, 1);
        let expected: SV = smallvec![0, 0, 0, 0, 0, 2];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 0, 0, 1];
        shl_mut(&mut x, 2, 0);
        let expected: SV = smallvec![0, 0, 0, 0, 0, 1];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 0, 0, 1];
        shl_mut(&mut x, 0, 0);
        let expected: SV = smallvec![0, 0, 0, 1];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 0, 2_usize.pow((BITS_PER_WORD - 2) as u32)];
        shl_mut(&mut x, 1,1);
        let expected: SV = smallvec![0, 0, 0, 2_usize.pow((BITS_PER_WORD - 1) as u32)];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 0, 2_usize.pow((BITS_PER_WORD - 1) as u32)];
        shl_mut(&mut x, 2,1);
        let expected: SV = smallvec![0, 0, 0, 0, 0, 1];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 1 << (80 - 64)];
        shl_mut(&mut x, 0, 0);
        let expected: SV = smallvec![0, 1 << (80 - 64)];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![8128280416544428961, 8274854478500297142, 3587444469682918757];
        shl_mut(&mut x, 1, 1);
        let expected: SV = from_str_radix::<10, 4>("45037507812500000000000000000000000000000000000000000000000000000000000000000").unwrap();
        assert_eq!(x, expected);
    }

    #[test]
    fn test_both_one() {
        unsafe {
            assert!(!both_not_one_non_zero(&[1], &[1]));
            assert!(!both_not_one_non_zero(&[1], &[2]));
            assert!(!both_not_one_non_zero(&[2], &[1]));
            assert!(!both_not_one_non_zero(&[1], &[1, 2]));
            assert!(!both_not_one_non_zero(&[1, 2], &[1]));
            assert!(both_not_one_non_zero(&[6], &[7]));
            assert!(both_not_one_non_zero(&[6], &[1, 2]));
            assert!(both_not_one_non_zero(&[1, 6], &[3]));
            assert!(both_not_one_non_zero(&[6, 2], &[7, 2]));
            assert!(both_not_one_non_zero(&[1, 2], &[7, 2]));
            assert!(both_not_one_non_zero(&[2, 2], &[1, 2]));
            assert!(both_not_one_non_zero(&[1, 2], &[1, 2]));
        }
    }
}
