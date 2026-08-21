//! # Building blocks
//!
//! Primitive operations on slices of words, used to implement the arbitrary precision integer
//! types.
//!
//! A few of these operations have a hand written assembly implementation in
//! `src/integer/big/ops/asm`. Those sources hard code the System V argument registers, an eight
//! byte limb stride and ELF specific assembler directives, so `build.rs` compiles them only for
//! 64 bit x86 ELF targets and sets the `ramp_asm` cfg exactly when it did. Every routine that has
//! an assembly implementation also has a portable Rust implementation, suffixed `_fallback`, which
//! is compiled unconditionally: it is what is called on every other target, it is what the
//! cross-check tests at the bottom of this file compare the assembly against, and it is what is
//! called under Miri, which cannot execute foreign functions.

use smallvec::SmallVec;

/// The assembly implementations, compiled from `src/integer/big/ops/asm/*.S` by `build.rs`.
///
/// The wrappers are safe: each checks the preconditions of the routine it calls, which are not
/// checked by the assembly itself. `ramp_sub_n` falls through to a three word tail when `n == 0`,
/// reading and writing out of bounds, while `ramp_mul_1`, `ramp_addmul_1` and `ramp_submul_1`
/// always process a first word and then decrement `n`, looping about `2 ** 32` times when it
/// started out as zero.
#[cfg(all(ramp_asm, not(miri)))]
mod asm {
    unsafe extern "C" {
        /// `wp[..n] = xp[..n] - yp[..n]`, returning the borrow out.
        ///
        /// `n` is declared `usize` rather than a 32 bit type on purpose: the routine does
        /// `shr $2, %rcx` and `jrcxz` on the full 64 bit register, while the System V ABI leaves
        /// the upper half of a register holding a 32 bit argument undefined.
        fn ramp_sub_n(wp: *mut usize, xp: *const usize, yp: *const usize, n: usize) -> usize;
        /// `wp[..n] = xp[..n] * vl`, returning the high word.
        ///
        /// `n` is declared `u32` because the routine reads it as `%edx` only; a `usize` argument
        /// would be silently truncated. The wrapper rejects lengths that do not fit.
        fn ramp_mul_1(wp: *mut usize, xp: *const usize, n: u32, vl: usize) -> usize;
        /// `wp[..n] += xp[..n] * vl`, returning the carry out. `n` is read as `%edx` only.
        fn ramp_addmul_1(wp: *mut usize, xp: *const usize, n: u32, vl: usize) -> usize;
        /// `wp[..n] -= xp[..n] * vl`, returning the borrow out. `n` is read as `%edx` only.
        fn ramp_submul_1(wp: *mut usize, xp: *const usize, n: u32, vl: usize) -> usize;
    }

    #[inline]
    pub fn sub_n(wp: &mut [usize], xp: &[usize], yp: &[usize], n: usize) -> usize {
        assert!(n >= 1, "the assembly reads out of bounds for a zero length operand");
        assert!(wp.len() >= n && xp.len() >= n && yp.len() >= n, "operand too short");

        // SAFETY: All three slices are at least `n` words long and `n` is not zero.
        unsafe { ramp_sub_n(wp.as_mut_ptr(), xp.as_ptr(), yp.as_ptr(), n) }
    }

    #[inline]
    pub fn mul_1(wp: &mut [usize], xp: &[usize], n: usize, vl: usize) -> usize {
        let n = check(wp, xp, n);

        // SAFETY: Both slices are at least `n` words long and `n` is neither zero nor truncated.
        unsafe { ramp_mul_1(wp.as_mut_ptr(), xp.as_ptr(), n, vl) }
    }

    #[inline]
    pub fn addmul_1(wp: &mut [usize], xp: &[usize], n: usize, vl: usize) -> usize {
        let n = check(wp, xp, n);

        // SAFETY: Both slices are at least `n` words long and `n` is neither zero nor truncated.
        unsafe { ramp_addmul_1(wp.as_mut_ptr(), xp.as_ptr(), n, vl) }
    }

    #[inline]
    pub fn submul_1(wp: &mut [usize], xp: &[usize], n: usize, vl: usize) -> usize {
        let n = check(wp, xp, n);

        // SAFETY: Both slices are at least `n` words long and `n` is neither zero nor truncated.
        unsafe { ramp_submul_1(wp.as_mut_ptr(), xp.as_ptr(), n, vl) }
    }

    /// Check the preconditions shared by the three multiplication routines.
    #[inline]
    fn check(wp: &[usize], xp: &[usize], n: usize) -> u32 {
        assert!(n >= 1, "the assembly loops about `2 ** 32` times for a zero length operand");
        assert!(wp.len() >= n && xp.len() >= n, "operand too short");
        // Would need `2 ** 32` words, so 32 GiB, of operand; the assembly reads `n` as `%edx`.
        u32::try_from(n).expect("operand length does not fit in the assembly's word count")
    }
}

#[must_use]
pub fn is_well_formed(values: &[usize]) -> bool {
    match values.last() {
        None => true,
        Some(&value) => value != 0,
    }
}

#[must_use]
pub fn is_well_formed_non_zero(values: &[usize]) -> bool {
    values.last().is_some_and(|&last| last != 0)
}

/// Add two double word values, wrapping on overflow of the high word.
#[must_use]
#[inline]
pub fn add_2(left_high: usize, left_low: usize, right_high: usize, right_low: usize) -> (usize, usize) {
    let (low, carry) = left_low.overflowing_add(right_low);
    let (high, _) = left_high.carrying_add(right_high, carry);

    (high, low)
}

/// Subtract two double word values, wrapping on underflow of the high word.
#[must_use]
#[inline]
pub fn sub_2(left_high: usize, left_low: usize, right_high: usize, right_low: usize) -> (usize, usize) {
    let (low, borrow) = left_low.overflowing_sub(right_low);
    let (high, _) = left_high.borrowing_sub(right_high, borrow);

    (high, low)
}

/// Copying subtraction (not necessarily in place).
///
/// Computes `wp[..n] = xp[..n] - yp[..n]` and returns the borrow out, which is `0` or `1`.
///
/// # Panics
///
/// If `n` is zero, or if any of the three slices is shorter than `n`.
#[inline]
pub fn sub_n(wp: &mut [usize], xp: &[usize], yp: &[usize], n: usize) -> usize {
    #[cfg(all(ramp_asm, not(miri)))]
    { asm::sub_n(wp, xp, yp, n) }
    #[cfg(not(all(ramp_asm, not(miri))))]
    { sub_n_fallback(wp, xp, yp, n) }
}

/// Portable implementation of [`sub_n`].
#[cfg_attr(all(ramp_asm, not(miri)), allow(dead_code, reason = "only the cross-check tests call it"))]
#[inline]
pub fn sub_n_fallback(wp: &mut [usize], xp: &[usize], yp: &[usize], n: usize) -> usize {
    assert!(n >= 1, "should not be called on an empty operand");
    assert!(wp.len() >= n && xp.len() >= n && yp.len() >= n, "operand too short");

    let mut borrow = false;
    for ((target, &left), &right) in wp[..n].iter_mut().zip(&xp[..n]).zip(&yp[..n]) {
        let (value, new_borrow) = left.borrowing_sub(right, borrow);
        *target = value;
        borrow = new_borrow;
    }

    borrow as usize
}

/// Multiply a slice by a single word, writing the result to a different slice.
///
/// Computes `wp[..xp.len()] = xp * vl` and returns the word that carries out of the top.
///
/// # Panics
///
/// If `xp` is empty or `wp` is shorter than `xp`.
#[inline]
pub fn mul_1(wp: &mut [usize], xp: &[usize], vl: usize) -> usize {
    let n = xp.len();

    #[cfg(all(ramp_asm, not(miri)))]
    { asm::mul_1(wp, xp, n, vl) }
    #[cfg(not(all(ramp_asm, not(miri))))]
    { mul_1_fallback(wp, xp, n, vl) }
}

/// Portable implementation of [`mul_1`].
#[cfg_attr(all(ramp_asm, not(miri)), allow(dead_code, reason = "only the cross-check tests call it"))]
#[inline]
pub fn mul_1_fallback(wp: &mut [usize], xp: &[usize], n: usize, vl: usize) -> usize {
    assert!(n >= 1, "should not be called on an empty operand");
    assert!(wp.len() >= n && xp.len() >= n, "operand too short");

    let mut carry = 0;
    for (target, &value) in wp[..n].iter_mut().zip(&xp[..n]) {
        // Computes `value * vl + carry`, which is at most `(2 ** BITS - 1) ** 2 + 2 ** BITS - 1`
        // and as such always fits in the two words returned.
        let (low, high) = value.carrying_mul(vl, carry);
        *target = low;
        carry = high;
    }

    carry
}

/// Add the product of a slice and a single word to another slice.
///
/// Computes `wp[..xp.len()] += xp * vl` and returns the word that carries out of the top.
///
/// # Panics
///
/// If `xp` is empty or `wp` is shorter than `xp`.
#[inline]
pub fn addmul_1(wp: &mut [usize], xp: &[usize], vl: usize) -> usize {
    let n = xp.len();

    #[cfg(all(ramp_asm, not(miri)))]
    { asm::addmul_1(wp, xp, n, vl) }
    #[cfg(not(all(ramp_asm, not(miri))))]
    { addmul_1_fallback(wp, xp, n, vl) }
}

/// Portable implementation of [`addmul_1`].
#[cfg_attr(all(ramp_asm, not(miri)), allow(dead_code, reason = "only the cross-check tests call it"))]
#[inline]
pub fn addmul_1_fallback(wp: &mut [usize], xp: &[usize], n: usize, vl: usize) -> usize {
    assert!(n >= 1, "should not be called on an empty operand");
    assert!(wp.len() >= n && xp.len() >= n, "operand too short");

    let mut carry = 0;
    for (target, &value) in wp[..n].iter_mut().zip(&xp[..n]) {
        let (low, high) = value.carrying_mul(vl, carry);
        let (new_value, overflow) = target.overflowing_add(low);
        *target = new_value;
        // `high` equals `usize::MAX` only when `low` is zero, in which case the addition above
        // does not overflow, so this addition never does either.
        carry = high + overflow as usize;
    }

    carry
}

/// Subtract the product of `rhs` and a single word from a slice of the same length.
///
/// Computes `value -= rhs * rhs_value` and returns the word that borrows out of the top.
///
/// # Panics
///
/// If the two slices are empty or of different lengths.
#[inline]
pub fn submul_slice(value: &mut [usize], rhs: &[usize], rhs_value: usize) -> usize {
    debug_assert_eq!(value.len(), rhs.len());

    submul_1(value, rhs, rhs_value)
}

/// Subtract the product of a slice and a single word from another slice.
///
/// Computes `wp[..xp.len()] -= xp * vl` and returns the word that borrows out of the top.
///
/// # Panics
///
/// If `xp` is empty or `wp` is shorter than `xp`.
#[inline]
pub fn submul_1(wp: &mut [usize], xp: &[usize], vl: usize) -> usize {
    let n = xp.len();

    #[cfg(all(ramp_asm, not(miri)))]
    { asm::submul_1(wp, xp, n, vl) }
    #[cfg(not(all(ramp_asm, not(miri))))]
    { submul_1_fallback(wp, xp, n, vl) }
}

/// Portable implementation of [`submul_1`].
#[cfg_attr(all(ramp_asm, not(miri)), allow(dead_code, reason = "only the cross-check tests call it"))]
#[inline]
pub fn submul_1_fallback(wp: &mut [usize], xp: &[usize], n: usize, vl: usize) -> usize {
    assert!(n >= 1, "should not be called on an empty operand");
    assert!(wp.len() >= n && xp.len() >= n, "operand too short");

    let mut borrow = 0;
    for (target, &value) in wp[..n].iter_mut().zip(&xp[..n]) {
        let (low, high) = value.carrying_mul(vl, borrow);
        let (new_value, overflow) = target.overflowing_sub(low);
        *target = new_value;
        // `high` equals `usize::MAX` only when `low` is zero, in which case the subtraction above
        // does not underflow, so this addition never overflows.
        borrow = high + overflow as usize;
    }

    borrow
}

/// Negate a value in place, interpreting it as a two's complement number.
///
/// Call only on negative values (the highest bit need not be zero to represent that, it's context
/// dependent). The result is normalized, that is, trailing zero words are removed.
#[inline]
pub fn to_twos_complement<const S: usize>(values: &mut SmallVec<[usize; S]>) {
    // Negating is complementing after subtracting one: `-x == !x + 1 == !(x - 1)`.
    let mut carry = true;

    for value in values.iter_mut() {
        borrowing_sub_mut(value, 0, &mut carry);
        *value = !*value;
    }

    // The borrow can only survive the loop when every word was zero, which the contract excludes.
    // Should it happen anyway, all words are now zero and the loop below normalizes the value to
    // the empty representation of zero, rather than leaving a denormalized value behind.
    debug_assert!(!carry, "should not be called on a zero value");

    while let Some(0) = values.last() {
        values.pop();
    }
}

/// Add `rhs` to `values` in place, both of the same length.
///
/// Returns whether the addition carries out of the top word.
///
/// # Panics
///
/// In debug mode, if the two slices have different lengths.
#[must_use]
#[inline]
pub fn add_assign_slice(values: &mut [usize], rhs: &[usize]) -> bool {
    debug_assert_eq!(values.len(), rhs.len());

    let mut carry = false;
    for (value, rhs_value) in values.iter_mut().zip(rhs.iter()) {
        carrying_add_mut(value, *rhs_value, &mut carry);
    }

    carry
}

/// Subtract `rhs` from `values` in place, both of the same length.
///
/// Returns whether the subtraction borrows out of the top word.
///
/// # Panics
///
/// In debug mode, if the two slices have different lengths.
#[inline]
pub fn sub_assign_slice(values: &mut [usize], rhs: &[usize]) -> bool {
    debug_assert_eq!(values.len(), rhs.len());

    let mut carry = false;
    for (value, rhs_value) in values.iter_mut().zip(rhs.iter()) {
        borrowing_sub_mut(value, *rhs_value, &mut carry);
    }

    carry
}

#[inline]
pub fn carrying_add_mut(value: &mut usize, rhs: usize, carry: &mut bool) {
    let (new_value, new_carry) = value.carrying_add(rhs, *carry);
    *value = new_value;
    *carry = new_carry;
}

#[inline]
pub fn borrowing_sub_mut(value: &mut usize, rhs: usize, carry: &mut bool) {
    let (new_value, new_carry) = value.borrowing_sub(rhs, *carry);
    *value = new_value;
    *carry = new_carry;
}

#[cfg(test)]
mod test {
    use smallvec::{smallvec, SmallVec};

    use crate::integer::big::ops::building_blocks::{add_2, addmul_1_fallback, is_well_formed, mul_1_fallback, sub_2, sub_n, sub_n_fallback, submul_1_fallback, to_twos_complement};

    #[test]
    fn test_is_well_formed() {
        pub type SV = SmallVec<[usize; 8]>;

        // TODO(DOCUMENTATION): Move this comment
        // Empty values are allowed, they represent zero. In many methods, that is invalid input,
        // however.
        let x: SV = smallvec![];
        assert!(is_well_formed(&x));

        let x: SV = smallvec![0, 1];
        assert!(is_well_formed(&x));

        let x: SV = smallvec![648, 64884, 1];
        assert!(is_well_formed(&x));

        // Ends with zero

        let x: SV = smallvec![564, 6448, 84, 0];
        assert!(!is_well_formed(&x));

        let x: SV = smallvec![0];
        assert!(!is_well_formed(&x));

        let x: SV = smallvec![0, 0, 0, 0];
        assert!(!is_well_formed(&x));
    }

    #[test]
    fn test_add_2() {
        assert_eq!(add_2(0, 0, 0, 0), (0, 0));
        assert_eq!(add_2(1, 2, 3, 4), (4, 6));

        // Carry out of the low word
        assert_eq!(add_2(0, usize::MAX, 0, 1), (1, 0));
        assert_eq!(add_2(3, usize::MAX, 4, usize::MAX), (8, usize::MAX - 1));

        // Wrapping out of the high word
        assert_eq!(add_2(usize::MAX, 0, 1, 0), (0, 0));
        assert_eq!(add_2(usize::MAX, usize::MAX, 0, 1), (0, 0));
        assert_eq!(add_2(usize::MAX, usize::MAX, usize::MAX, usize::MAX), (usize::MAX, usize::MAX - 1));
    }

    #[test]
    fn test_sub_2() {
        assert_eq!(sub_2(0, 0, 0, 0), (0, 0));
        assert_eq!(sub_2(4, 6, 1, 2), (3, 4));

        // Borrow out of the low word
        assert_eq!(sub_2(1, 0, 0, 1), (0, usize::MAX));
        assert_eq!(sub_2(8, 0, 4, usize::MAX), (3, 1));

        // Wrapping out of the high word
        assert_eq!(sub_2(0, 0, 0, 1), (usize::MAX, usize::MAX));
        assert_eq!(sub_2(0, 0, 1, 0), (usize::MAX, 0));
    }

    #[test]
    fn test_sub_n() {
        type SV = SmallVec<[usize; 4]>;

        let mut x: SV = smallvec![0, 0];
        let carry = sub_n(&mut x, &[2, 3], &[1, 1], 2);
        assert_eq!(carry, 0);
        let expected: SV = smallvec![1, 2];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 0];
        let carry = sub_n(&mut x, &[2, 3], &[4, 1], 2);
        assert_eq!(carry, 0);
        let expected: SV = smallvec![usize::MAX - 1, 1];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0, 0];
        let carry = sub_n(&mut x, &[4, 1], &[4, 1], 2);
        assert_eq!(carry, 0);
        let expected: SV = smallvec![0, 0];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![0];
        let carry = sub_n(&mut x, &[0], &[1], 1);
        assert_eq!(carry, 1);
        let expected: SV = smallvec![usize::MAX];
        assert_eq!(x, expected);
        to_twos_complement(&mut x);
        let expected: SV = smallvec![1];
        assert_eq!(x, expected);
    }

    #[test]
    fn test_to_twos_complement() {
        type SV = SmallVec<[usize; 4]>;

        let mut value: SV = smallvec![usize::MAX];
        to_twos_complement(&mut value);
        let expected: SV = smallvec![1];
        assert_eq!(value, expected);

        let mut value: SV = smallvec![usize::MAX - 1];
        to_twos_complement(&mut value);
        let expected: SV = smallvec![2];
        assert_eq!(value, expected);

        let mut value: SV = smallvec![usize::MAX - 2, usize::MAX];
        to_twos_complement(&mut value);
        let expected: SV = smallvec![3];
        assert_eq!(value, expected);

        let mut value: SV = smallvec![usize::MAX - 3, usize::MAX, usize::MAX];
        to_twos_complement(&mut value);
        let expected: SV = smallvec![4];
        assert_eq!(value, expected);

        // A borrow that travels through several words
        let mut value: SV = smallvec![0, 0, 1];
        to_twos_complement(&mut value);
        let expected: SV = smallvec![0, 0, usize::MAX];
        assert_eq!(value, expected);
    }

    /// The inputs the portable and assembly implementations are compared on.
    ///
    /// Covers single and multiple words, maximum valued words, and carries and borrows that
    /// propagate all the way through.
    fn cross_check_operands() -> Vec<(Vec<usize>, Vec<usize>)> {
        let patterns: Vec<Vec<usize>> = vec![
            vec![0],
            vec![1],
            vec![usize::MAX],
            vec![0, 0],
            vec![1, 0],
            vec![0, 1],
            vec![usize::MAX, usize::MAX],
            vec![usize::MAX, 0],
            vec![0, usize::MAX],
            vec![1, 2, 3],
            vec![usize::MAX, usize::MAX, usize::MAX],
            vec![usize::MAX, 0, usize::MAX],
            vec![0, usize::MAX, 0],
            vec![1, usize::MAX, usize::MAX, usize::MAX],
            vec![usize::MAX, usize::MAX, usize::MAX, usize::MAX],
            vec![usize::MAX; 5],
            vec![usize::MAX; 6],
            vec![usize::MAX; 7],
            // Longer than the four word unrolled loop of the assembly, with every tail length.
            (1..=8).collect(),
            (1..=9).map(|i| usize::MAX - i).collect(),
            vec![usize::MAX; 11],
            (0..17).map(|i| usize::MAX / (i + 1)).collect(),
        ];

        let mut combinations = Vec::new();
        for left in &patterns {
            for right in &patterns {
                if left.len() == right.len() {
                    combinations.push((left.clone(), right.clone()));
                }
            }
        }

        combinations
    }

    /// The single word multipliers the multiplication routines are compared on.
    fn cross_check_multipliers() -> Vec<usize> {
        vec![0, 1, 2, usize::MAX / 2, usize::MAX - 1, usize::MAX]
    }

    /// Values `wp` is filled with before the in place routines are called.
    fn cross_check_targets(n: usize) -> Vec<Vec<usize>> {
        vec![
            vec![0; n],
            vec![usize::MAX; n],
            (0..n).map(|i| i * 7 + 1).collect(),
            (0..n).map(|i| usize::MAX - i).collect(),
        ]
    }

    #[test]
    fn test_sub_n_fallback() {
        type SV = SmallVec<[usize; 4]>;

        let mut x: SV = smallvec![0, 0];
        assert_eq!(sub_n_fallback(&mut x, &[2, 3], &[1, 1], 2), 0);
        let expected: SV = smallvec![1, 2];
        assert_eq!(x, expected);

        // A borrow that propagates through the whole length
        let mut x: SV = smallvec![0; 3];
        assert_eq!(sub_n_fallback(&mut x, &[0, 0, 0], &[1, 0, 0], 3), 1);
        let expected: SV = smallvec![usize::MAX; 3];
        assert_eq!(x, expected);

        // Only the first `n` words are touched
        let mut x: SV = smallvec![7, 7, 7];
        assert_eq!(sub_n_fallback(&mut x, &[5, 5, 5], &[1, 1, 1], 2), 0);
        let expected: SV = smallvec![4, 4, 7];
        assert_eq!(x, expected);
    }

    #[test]
    fn test_mul_1_fallback() {
        let mut x = vec![0; 3];

        assert_eq!(mul_1_fallback(&mut x, &[1, 2, 3], 3, 0), 0);
        assert_eq!(x, vec![0, 0, 0]);

        assert_eq!(mul_1_fallback(&mut x, &[1, 2, 3], 3, 1), 0);
        assert_eq!(x, vec![1, 2, 3]);

        assert_eq!(mul_1_fallback(&mut x, &[usize::MAX, usize::MAX, usize::MAX], 3, usize::MAX), usize::MAX - 1);
        assert_eq!(x, vec![1, usize::MAX, usize::MAX]);

        let mut x = vec![0; 1];
        assert_eq!(mul_1_fallback(&mut x, &[usize::MAX], 1, 2), 1);
        assert_eq!(x, vec![usize::MAX - 1]);
    }

    #[test]
    fn test_addmul_1_fallback() {
        // A carry that propagates through the whole length
        let mut x = vec![usize::MAX; 3];
        assert_eq!(addmul_1_fallback(&mut x, &[1, 0, 0], 3, 1), 1);
        assert_eq!(x, vec![0, 0, 0]);

        let mut x = vec![1, 2, 3];
        assert_eq!(addmul_1_fallback(&mut x, &[1, 1, 1], 3, 0), 0);
        assert_eq!(x, vec![1, 2, 3]);

        let mut x = vec![usize::MAX; 2];
        assert_eq!(addmul_1_fallback(&mut x, &[usize::MAX, usize::MAX], 2, usize::MAX), usize::MAX);
        // (2 ** 128 - 1) + (2 ** 64 - 1) * (2 ** 128 - 1) / ... checked against the assembly below
        assert_eq!(x, vec![0, usize::MAX]);
    }

    #[test]
    fn test_submul_1_fallback() {
        // A borrow that propagates through the whole length
        let mut x = vec![0; 3];
        assert_eq!(submul_1_fallback(&mut x, &[1, 0, 0], 3, 1), 1);
        assert_eq!(x, vec![usize::MAX; 3]);

        let mut x = vec![1, 2, 3];
        assert_eq!(submul_1_fallback(&mut x, &[1, 1, 1], 3, 0), 0);
        assert_eq!(x, vec![1, 2, 3]);

        let mut x = vec![usize::MAX; 3];
        assert_eq!(submul_1_fallback(&mut x, &[usize::MAX, usize::MAX, usize::MAX], 3, 1), 0);
        assert_eq!(x, vec![0, 0, 0]);
    }

    /// Compare the portable implementations against a straightforward wide integer model.
    ///
    /// This is a second opinion on the fallbacks for targets without the assembly, where the
    /// cross-check below does not run. The model is exact only while the operands fit in the
    /// widest integer type, so it uses single word operands for the multiplications and at most
    /// two word operands for the subtraction.
    #[test]
    #[cfg(target_pointer_width = "64")]
    fn test_fallback_against_model() {
        fn to_u128(words: &[usize]) -> u128 {
            words.iter().rev().fold(0_u128, |total, &word| (total << 64) | word as u128)
        }

        let words = [0_usize, 1, 2, 3, usize::MAX / 3, usize::MAX / 2, usize::MAX - 1, usize::MAX];

        // Subtraction of one and two word values
        for &left_low in &words {
            for &left_high in &words {
                for &right_low in &words {
                    for &right_high in &words {
                        let left = [left_low, left_high];
                        let right = [right_low, right_high];

                        for n in 1..=2 {
                            let mut target = vec![0; n];
                            let borrow = sub_n_fallback(&mut target, &left, &right, n);

                            // Two words are as wide as the model gets, so the modulus is the
                            // largest value representable plus one, which doesn't fit itself.
                            let mask = if n == 1 { u64::MAX as u128 } else { u128::MAX };
                            let (left, right) = (to_u128(&left[..n]), to_u128(&right[..n]));
                            assert_eq!(to_u128(&target), left.wrapping_sub(right) & mask);
                            assert_eq!(borrow, (left < right) as usize);
                        }
                    }
                }
            }
        }

        // Multiplication by a single word
        for &value in &words {
            for &multiplier in &words {
                for &initial in &words {
                    let mut target = [0];
                    let high = mul_1_fallback(&mut target, &[value], 1, multiplier);
                    assert_eq!(
                        to_u128(&target) + ((high as u128) << 64),
                        value as u128 * multiplier as u128,
                    );

                    let mut target = [initial];
                    let carry = addmul_1_fallback(&mut target, &[value], 1, multiplier);
                    assert_eq!(
                        to_u128(&target) + ((carry as u128) << 64),
                        initial as u128 + value as u128 * multiplier as u128,
                    );

                    // `initial - value * multiplier == target - borrow * 2 ** 64`, rearranged so
                    // that every term is non-negative and fits in a `u128`.
                    let mut target = [initial];
                    let borrow = submul_1_fallback(&mut target, &[value], 1, multiplier);
                    assert_eq!(
                        initial as u128 + ((borrow as u128) << 64),
                        to_u128(&target) + value as u128 * multiplier as u128,
                    );
                }
            }
        }
    }

    /// Compare the portable implementations against the assembly on the same inputs.
    ///
    /// Only compiled where the assembly is compiled in, which is where both implementations exist.
    #[cfg(all(ramp_asm, not(miri)))]
    mod against_assembly {
        use crate::integer::big::ops::building_blocks::{addmul_1_fallback, asm, mul_1_fallback, sub_n_fallback, submul_1_fallback};

        use super::{cross_check_multipliers, cross_check_operands, cross_check_targets};

        #[test]
        fn test_sub_n() {
            for (left, right) in cross_check_operands() {
                for n in 1..=left.len() {
                    // Some extra words to catch writes past the end
                    let mut from_asm = vec![0x5a; left.len() + 3];
                    let mut from_rust = vec![0x5a; left.len() + 3];

                    let asm_borrow = asm::sub_n(&mut from_asm, &left, &right, n);
                    let rust_borrow = sub_n_fallback(&mut from_rust, &left, &right, n);

                    assert_eq!(asm_borrow, rust_borrow, "{left:?} - {right:?}, n = {n}");
                    assert_eq!(from_asm, from_rust, "{left:?} - {right:?}, n = {n}");
                }
            }
        }

        #[test]
        fn test_mul_1() {
            for (left, _) in cross_check_operands() {
                for multiplier in cross_check_multipliers() {
                    for n in 1..=left.len() {
                        let mut from_asm = vec![0x5a; left.len() + 3];
                        let mut from_rust = vec![0x5a; left.len() + 3];

                        let asm_carry = asm::mul_1(&mut from_asm, &left, n, multiplier);
                        let rust_carry = mul_1_fallback(&mut from_rust, &left, n, multiplier);

                        assert_eq!(asm_carry, rust_carry, "{left:?} * {multiplier}, n = {n}");
                        assert_eq!(from_asm, from_rust, "{left:?} * {multiplier}, n = {n}");
                    }
                }
            }
        }

        #[test]
        fn test_addmul_1() {
            for (left, _) in cross_check_operands() {
                for multiplier in cross_check_multipliers() {
                    for n in 1..=left.len() {
                        for initial in cross_check_targets(left.len() + 3) {
                            let mut from_asm = initial.clone();
                            let mut from_rust = initial.clone();

                            let asm_carry = asm::addmul_1(&mut from_asm, &left, n, multiplier);
                            let rust_carry = addmul_1_fallback(&mut from_rust, &left, n, multiplier);

                            assert_eq!(asm_carry, rust_carry, "{initial:?} += {left:?} * {multiplier}, n = {n}");
                            assert_eq!(from_asm, from_rust, "{initial:?} += {left:?} * {multiplier}, n = {n}");
                        }
                    }
                }
            }
        }

        #[test]
        fn test_submul_1() {
            for (left, _) in cross_check_operands() {
                for multiplier in cross_check_multipliers() {
                    for n in 1..=left.len() {
                        for initial in cross_check_targets(left.len() + 3) {
                            let mut from_asm = initial.clone();
                            let mut from_rust = initial.clone();

                            let asm_borrow = asm::submul_1(&mut from_asm, &left, n, multiplier);
                            let rust_borrow = submul_1_fallback(&mut from_rust, &left, n, multiplier);

                            assert_eq!(asm_borrow, rust_borrow, "{initial:?} -= {left:?} * {multiplier}, n = {n}");
                            assert_eq!(from_asm, from_rust, "{initial:?} -= {left:?} * {multiplier}, n = {n}");
                        }
                    }
                }
            }
        }
    }
}
