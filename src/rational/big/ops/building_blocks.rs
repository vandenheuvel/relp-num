use std::iter::repeat;
use std::num::NonZeroUsize;
use std::ptr;

use smallvec::SmallVec;

use crate::rational::big::ops::{BITS_PER_WORD, is_well_formed};
use std::intrinsics::assume;

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
pub fn shr<const S: usize>(values: &SmallVec<[usize; S]>, words_to_remove: usize, bits: u32) -> SmallVec<[usize; S]> {
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
    debug_assert!(is_well_formed(values));

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

    debug_assert!(is_well_formed(values) && !values.is_empty());
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
    debug_assert!(is_well_formed(values));
    debug_assert!(!values.is_empty(), "Should not be called on a zero value");
    debug_assert!(words_to_remove < values.len(), "Can't shift away all words");
    debug_assert!(bits < BITS_PER_WORD, "Use the `words` argument to shift with entire words");
}

#[inline]
pub fn mul(left: usize, right: usize) -> (usize, usize) {
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    fn inner(left: usize, right: usize) -> (usize, usize) {
        let mut high_out;
        let mut low_out;

        unsafe {
            asm!(
                "mul {v}",
                v = in(reg) right,

                inout("rax") left => low_out,
                out("rdx") high_out,
            );
        }

        (high_out, low_out)
    }

    inner(left, right)
}

#[inline]
pub fn add_2(left_high: usize, left_low: usize, right_high: usize, right_low: usize) -> (usize, usize) {
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    fn inner(left_high: usize, left_low: usize, right_high: usize, right_low: usize) -> (usize, usize) {
        let mut high_out;
        let mut low_out;

        unsafe {
            asm!(
                "add {0}, {right_low}",
                "adc {1}, {right_high}",
                inout(reg) left_low => low_out,
                inout(reg) left_high => high_out,
                right_low = in(reg) right_low,
                right_high = in(reg) right_high,
            );
        }

        (high_out, low_out)
    }

    inner(left_high, left_low, right_high, right_low)
}

#[inline]
pub fn sub_2(left_high: usize, left_low: usize, right_high: usize, right_low: usize) -> (usize, usize) {
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    fn inner(left_high: usize, left_low: usize, right_high: usize, right_low: usize) -> (usize, usize) {
        let mut high_out;
        let mut low_out;

        unsafe {
            asm!(
                "sub {0}, {right_low}",
                "sbb {1}, {right_high}",
                inout(reg) left_low => low_out,
                inout(reg) left_high => high_out,
                right_low = in(reg) right_low,
                right_high = in(reg) right_high,
            );
        }

        (high_out, low_out)
    }

    inner(left_high, left_low, right_high, right_low)
}

/// Copying addition (not necessarily in place)
#[inline]
pub unsafe fn add_n(target: &mut [usize], left: &[usize], right: &[usize], size: i32) -> usize {
    extern "C" {
        fn ramp_add_n(wp: *mut usize, xp: *const usize, yp: *const usize, n: i32) -> usize;
    }

    debug_assert!(size >= 1);

    return ramp_add_n(target.as_mut_ptr(), left.as_ptr(), right.as_ptr(), size);
}

/// Copying subtraction (not necessarily in place)
#[inline]
pub unsafe fn sub_n(wp: &mut [usize], xp: &[usize], yp: &[usize], n: i32) -> usize {
    extern "C" {
        fn ramp_sub_n(wp: *mut usize, xp: *const usize, yp: *const usize, n: i32) -> usize;
    }

    debug_assert!(n >= 1);

    return ramp_sub_n(wp.as_mut_ptr(), xp.as_ptr(), yp.as_ptr(), n);
}

#[inline]
pub unsafe fn mul_1(wp: &mut [usize], xp: &[usize], vl: usize) -> usize {
    extern "C" {
        fn ramp_mul_1(wp: *mut usize, xp: *const usize, n: i32, vl: usize) -> usize;
    }

    ramp_mul_1(wp.as_mut_ptr(), xp.as_ptr(), xp.len() as i32, vl)
}

#[inline]
pub unsafe fn addmul_1(wp: &mut [usize], xp: &[usize], n: i32, vl: usize) -> usize {
    extern "C" {
        fn ramp_addmul_1(wp: *mut usize, xp: *const usize, n: i32, vl: usize) -> usize;
    }

    ramp_addmul_1(wp.as_mut_ptr(), xp.as_ptr(), n, vl)
}

#[inline]
pub unsafe fn submul_slice(value: &mut [usize], rhs: &[usize], rhs_value: usize) -> usize {
    debug_assert_eq!(value.len(), rhs.len());

    submul_1(value, rhs, value.len() as i32, rhs_value)
}

#[inline]
pub unsafe fn submul_1(wp: &mut [usize], xp: &[usize], n: i32, vl: usize) -> usize {
    extern "C" {
        fn ramp_submul_1(wp: *mut usize, xp: *const usize, n: i32, vl: usize) -> usize;
    }

    ramp_submul_1(wp.as_mut_ptr(), xp.as_ptr(), n, vl)
}

/// Call only on negative values (highest bit need not be zero to represent that, it's context dependent)
#[inline]
pub fn to_twos_complement<const S: usize>(values: &mut SmallVec<[usize; S]>) {
    let mut carry = true;

    for value in values.iter_mut() {
        carry = carrying_sub_mut(value, 0, carry);
        *value = !*value;
    }

    if carry {
        values.push(0);
    } else {
        while let Some(0) = values.last() {
            values.pop();
        }
    }
}

#[inline]
pub unsafe fn add_assign_slice(values: &mut [usize], rhs: &[usize]) -> bool {
    debug_assert_eq!(values.len(), rhs.len());

    let mut carry = false;
    for (value, rhs_value) in values.iter_mut().zip(rhs.iter()) {
        carry = carrying_add_mut(value, *rhs_value, carry);
    }

    carry
}

#[inline]
pub unsafe fn sub_assign_slice(values: &mut [usize], rhs: &[usize]) -> bool {
    debug_assert_eq!(values.len(), rhs.len());

    let mut carry = false;
    for (value, rhs_value) in values.iter_mut().zip(rhs.iter()) {
        carry = carrying_sub_mut(value, *rhs_value, carry);
    }

    carry
}

#[inline]
pub fn carrying_add_mut(value: &mut usize, rhs: usize, carry: bool) -> bool {
    let (new_value, new_carry) = carrying_add(*value, rhs, carry);
    *value = new_value;
    new_carry
}

// Copied from an open pr on rust
#[inline]
pub fn carrying_add(value: usize, rhs: usize, carry: bool) -> (usize, bool) {
    let (a, b) = value.overflowing_add(rhs);
    let (c, d) = a.overflowing_add(carry as usize);
    (c, b | d)
}

#[inline]
pub fn carrying_sub_mut(value: &mut usize, rhs: usize, carry: bool) -> bool {
    let (new_value, new_carry) = carrying_sub(*value, rhs, carry);
    *value = new_value;
    new_carry
}

// Copied from an open pr on rust
#[inline]
pub fn carrying_sub(value: usize, rhs: usize, carry: bool) -> (usize, bool) {
    let (a, b) = value.overflowing_sub(rhs);
    let (c, d) = a.overflowing_sub(carry as usize);
    (c, b | d)
}

#[inline]
pub fn is_zero(values: &[usize]) -> bool {
    debug_assert!(is_well_formed(values));

    values.is_empty()
}

#[inline]
pub fn is_one(values: &[usize]) -> bool {
    debug_assert!(is_well_formed(values));

    values.len() == 1 && values[0] == 1
}

#[inline]
pub fn nonzero_is_one(values: &[usize]) -> bool {
    debug_assert!(is_well_formed(values));
    debug_assert!(!values.is_empty());

    unsafe {
        assume(!values.is_empty());
    }

    values[0] == 1 && values.len() == 1
}

#[inline]
pub fn both_not_one(left: &[usize], right: &[usize]) -> bool {
    debug_assert!(!is_zero(left));
    debug_assert!(!is_zero(right));

    unsafe {
        assume(!left.is_empty());
        assume(!right.is_empty());
    }

    (left[0] != 1 || left.len() > 1) && (right[0] != 1 || right.len() > 1)
}

#[cfg(test)]
mod test {
    use std::mem;
    use std::num::NonZeroUsize;

    use smallvec::smallvec;

    use crate::rational::big::creation::int_from_str;
    use crate::rational::big::ops::BITS_PER_WORD;
    use crate::rational::big::ops::building_blocks::{add_2, both_not_one, carrying_add_mut, mul, shl_mut, shl_mut_overflowing, shr, shr_mut, sub_n, to_twos_complement};
    use crate::rational::big::ops::test::SV;

    #[test]
    fn test_shr() {
        let x: SV = smallvec![1];
        let expected: SV = smallvec![1];
        assert_eq!(shr(&x, 0, 0), expected);

        let x: SV = smallvec![0, 1];
        let expected: SV = smallvec![1];
        assert_eq!(shr(&x, 1, 0), expected);

        let x: SV = smallvec![0, 1];
        let expected: SV = smallvec![1 << (mem::size_of::<usize>() * 8 - 1)];
        assert_eq!(shr(&x, 0, 1), expected);

        let x: SV = smallvec![0, 0, 0, 1];
        let expected: SV = smallvec![0, 1 << (mem::size_of::<usize>() * 8 - 1)];
        assert_eq!(shr(&x, 1, 1), expected);

        let x: SV = smallvec![0, 1];
        let expected: SV = smallvec![2];
        assert_eq!(shr(&x, 0, (mem::size_of::<usize>() * 8 - 1) as u32), expected);

        // 15588921427233345156 // 4
        let x: SV = smallvec![15588921427233345156];
        let expected: SV = smallvec![3897230356808336289];
        assert_eq!(shr(&x, 0, 2), expected);

        // 15588921427233345156 // 4
        let x: SV = smallvec![131522304505784511, 2433];
        assert_eq!(shr(&x, 0, 0), x);
    }

    #[test]
    fn test_shr_mut() {
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
        let expected: SV = int_from_str("45037507812500000000000000000000000000000000000000000000000000000000000000000", 10).unwrap();
        assert_eq!(x, expected);
    }

    #[test]
    fn test_mul() {
        assert_eq!(mul(0, 2), (0, 0));
        assert_eq!(mul(2, 2), (0, 4));
        assert_eq!(mul(1 << 32, 1 << 32), (1, 0));
        assert_eq!(mul(1 << 63, 3), (1, 1 << 63));
    }

    #[test]
    fn test_add_2() {
        assert_eq!(add_2(0, 0, 0, 0), (0, 0));
        assert_eq!(add_2(1, 2, 3, 4), (4, 6));
    }

    #[test]
    fn test_sub_n() {
        let mut x: SV = smallvec![0, 0];
        let carry = unsafe { sub_n(&mut x, &[2, 3], &[1, 1], 2) };
        assert_eq!(carry, 0);
        let expected: SV = smallvec![1, 2];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 0];
        let carry = unsafe { sub_n(&mut x, &[2, 3], &[4, 1], 2) };
        assert_eq!(carry, 0);
        let expected: SV = smallvec![usize::MAX - 1, 1];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 0];
        let carry = unsafe { sub_n(&mut x, &[4, 1], &[4, 1], 2) };
        assert_eq!(carry, 0);
        let expected: SV = smallvec![0, 0];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0];
        let carry = unsafe { sub_n(&mut x, &[0], &[1], 1) };
        assert_eq!(carry, 1);
        let expected: SV = smallvec![usize::MAX];
        assert_eq!(x, expected);
        to_twos_complement(&mut x);
        let expected: SV = smallvec![1];
        assert_eq!(x, expected);
    }

    #[test]
    fn test_to_twos_complement() {
        let mut value: SV = smallvec![0xffffffffffffffff];
        to_twos_complement(&mut value);
        let expected: SV = smallvec![1];
        assert_eq!(value, expected);

        let mut value: SV = smallvec![0xfffffffffffffffe];
        to_twos_complement(&mut value);
        let expected: SV = smallvec![2];
        assert_eq!(value, expected);

        let mut value: SV = smallvec![0xfffffffffffffffd, 0xffffffffffffffff];
        to_twos_complement(&mut value);
        let expected: SV = smallvec![3];
        assert_eq!(value, expected);

        let mut value: SV = smallvec![0xfffffffffffffffc, 0xffffffffffffffff, 0xffffffffffffffff];
        to_twos_complement(&mut value);
        let expected: SV = smallvec![4];
        assert_eq!(value, expected);
    }

    #[test]
    fn test_carrying_add_mut() {
        let mut value = 1;
        let carry = carrying_add_mut(&mut value, 1, false);
        assert_eq!((value, carry), (2, false));

        let mut value = 1;
        let carry = carrying_add_mut(&mut value, 0, true);
        assert_eq!((value, carry), (2, false));

        let mut value = 1;
        let carry = carrying_add_mut(&mut value, usize::MAX, false);
        assert_eq!((value, carry), (0, true));

        let mut value = 2;
        let carry = carrying_add_mut(&mut value, usize::MAX, false);
        assert_eq!((value, carry), (1, true));

        let mut value = 1;
        let carry = carrying_add_mut(&mut value, usize::MAX, true);
        assert_eq!((value, carry), (1, true));
    }

    #[test]
    fn test_both_one() {
        assert!(!both_not_one(&[1], &[1]));
        assert!(!both_not_one(&[1], &[2]));
        assert!(!both_not_one(&[2], &[1]));
        assert!(!both_not_one(&[1], &[1, 2]));
        assert!(!both_not_one(&[1, 2], &[1]));
        assert!(both_not_one(&[6], &[7]));
        assert!(both_not_one(&[6], &[1, 2]));
        assert!(both_not_one(&[1, 6], &[3]));
        assert!(both_not_one(&[6, 2], &[7, 2]));
        assert!(both_not_one(&[1, 2], &[7, 2]));
        assert!(both_not_one(&[2, 2], &[1, 2]));
        assert!(both_not_one(&[1, 2], &[1, 2]));
    }
}
