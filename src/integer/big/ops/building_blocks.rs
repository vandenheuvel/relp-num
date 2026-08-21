//! # Building blocks
//!
//! Primitive operations on slices of words, used to implement the arbitrary precision integer
//! types.
//!
//! Four of them, [`sub_n`], [`mul_1`], [`addmul_1`] and [`submul_1`], are the inner loops those
//! types spend most of their time in, and are written against what the code generator makes of a
//! carry chain rather than in the most obvious way; on x86_64 the addition and subtraction chains
//! go through the carry flag intrinsics (see [`sub_word`]). Each is compared against a
//! straightforward reference implementation in the tests at the bottom of this file.

use smallvec::SmallVec;

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

/// The number of words the inner loops below handle at a time.
///
/// A carry chain is serial: every word waits on the flag the word before it produced, so there is
/// no parallelism to unlock here. What a block buys is the loop overhead it amortises, and that
/// the carry crosses the block in the processor's carry flag, touching a register only at the
/// back edge, where updating the loop counter clobbers the flag anyway. Eight words is where the
/// measurements stopped improving.
const BLOCK: usize = 8;

/// A carry or borrow between two words of a chain, always zero or one.
///
/// On x86_64 this is the byte the carry flag intrinsics in [`sub_word`] and [`add_word`] traffic
/// in, everywhere else the `bool` of the `carrying_add` family.
#[cfg(target_arch = "x86_64")]
type Flag = u8;
#[cfg(not(target_arch = "x86_64"))]
type Flag = bool;

/// One link of a subtraction chain: `left - right - borrow`, and the borrow out.
///
/// This is [`usize::borrowing_sub`], and on most platforms that is also how it is written. On
/// x86_64 it goes through the carry flag intrinsic instead: handing the byte one `_subborrow_u64`
/// returned straight to the next compiles to the borrow simply staying in the carry flag, one
/// `sbb` per word, materialized into a register only where a loop back edge interrupts the chain.
/// The `bool` version costs two comparisons at the head of every block to re-derive the flag,
/// which is a few cycles of latency per block on a chain that otherwise moves a word per cycle.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn sub_word(left: usize, right: usize, borrow: Flag) -> (usize, Flag) {
    let mut value = 0;
    // SAFETY: `sbb` is a baseline x86_64 instruction and the intrinsic has no preconditions.
    // Recent toolchains make it a safe function, hence the `allow`.
    #[allow(unused_unsafe)]
    let borrow = unsafe { std::arch::x86_64::_subborrow_u64(borrow, left as u64, right as u64, &mut value) };

    (value as usize, borrow)
}

#[cfg(not(target_arch = "x86_64"))]
#[inline(always)]
fn sub_word(left: usize, right: usize, borrow: Flag) -> (usize, Flag) {
    left.borrowing_sub(right, borrow)
}

/// One link of an addition chain: `left + right + carry`, and the carry out.
///
/// The addition counterpart of [`sub_word`], with `adc` in the place of `sbb`.
#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn add_word(left: usize, right: usize, carry: Flag) -> (usize, Flag) {
    let mut value = 0;
    // SAFETY: as in `sub_word`.
    #[allow(unused_unsafe)]
    let carry = unsafe { std::arch::x86_64::_addcarry_u64(carry, left as u64, right as u64, &mut value) };

    (value as usize, carry)
}

#[cfg(not(target_arch = "x86_64"))]
#[inline(always)]
fn add_word(left: usize, right: usize, carry: Flag) -> (usize, Flag) {
    left.carrying_add(right, carry)
}

/// The routines below accumulate the product of two words in a `u128`, which holds it exactly only
/// while a word is at most half that wide.
const _: () = assert!(usize::BITS <= 64);

/// Copying subtraction (not necessarily in place).
///
/// Computes `wp[..n] = xp[..n] - yp[..n]` and returns the borrow out, which is `0` or `1`.
///
/// # Panics
///
/// If `n` is zero, or if any of the three slices is shorter than `n`.
#[inline]
pub fn sub_n(wp: &mut [usize], xp: &[usize], yp: &[usize], n: usize) -> usize {
    assert!(n >= 1, "should not be called on an empty operand");
    assert!(wp.len() >= n && xp.len() >= n && yp.len() >= n, "operand too short");

    let (wp, xp, yp) = (&mut wp[..n], &xp[..n], &yp[..n]);
    let mut borrow = Flag::default();

    // Operands this short never fill a block, and the chunking is pure overhead for them.
    if n < BLOCK {
        for ((target, &left), &right) in wp.iter_mut().zip(xp).zip(yp) {
            (*target, borrow) = sub_word(left, right, borrow);
        }

        return usize::from(borrow);
    }

    let (w_blocks, w_tail) = wp.as_chunks_mut::<BLOCK>();
    let (x_blocks, x_tail) = xp.as_chunks::<BLOCK>();
    let (y_blocks, y_tail) = yp.as_chunks::<BLOCK>();

    for ((target, left), right) in w_blocks.iter_mut().zip(x_blocks).zip(y_blocks) {
        for word in 0..BLOCK {
            (target[word], borrow) = sub_word(left[word], right[word], borrow);
        }
    }
    for ((target, &left), &right) in w_tail.iter_mut().zip(x_tail).zip(y_tail) {
        (*target, borrow) = sub_word(left, right, borrow);
    }

    usize::from(borrow)
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
    assert!(n >= 1, "should not be called on an empty operand");
    assert!(wp.len() >= n, "operand too short");
    let wp = &mut wp[..n];

    // An operand this short does not reach a block to begin with, and would never earn back the
    // load and branch of the feature test below.
    if n < BLOCK {
        return mul_1_words(wp, xp, vl, 0);
    }

    mul_1_long(wp, xp, vl)
}

/// The part of [`mul_1`] a short operand never reaches.
///
/// Kept out of line so that what is left of [`mul_1`] is small enough for its callers to inline,
/// which on a one or two word operand is worth more than everything the block loop does. The other
/// three routines here have one path fewer and no feature test, and stay under that bar as they
/// are.
fn mul_1_long(wp: &mut [usize], xp: &[usize], vl: usize) -> usize {
    #[cfg(target_arch = "x86_64")]
    if has_wide_multiply() {
        // SAFETY: `bmi2` was just detected on this processor.
        return unsafe { mul_1_wide(wp, xp, vl) };
    }

    mul_1_blocks(wp, xp, vl)
}

/// [`mul_1`] one word at a time, picking up an incoming carry and returning the outgoing one.
///
/// The largest value the accumulator takes is `(2 ** BITS - 1) ** 2 + (2 ** BITS - 1)`, which is
/// below `2 ** (2 * BITS)`, so the double width product never overflows.
///
/// Always inlined for the reason given on [`mul_1_wide`].
#[inline(always)]
fn mul_1_words(wp: &mut [usize], xp: &[usize], vl: usize, mut carry: usize) -> usize {
    for (target, &value) in wp.iter_mut().zip(xp) {
        let accumulator = value as u128 * vl as u128 + carry as u128;
        *target = accumulator as usize;
        carry = (accumulator >> usize::BITS) as usize;
    }

    carry
}

/// [`mul_1_words`] a block at a time, with a word at a time tail.
///
/// Always inlined for the reason given on [`mul_1_wide`].
#[inline(always)]
fn mul_1_blocks(wp: &mut [usize], xp: &[usize], vl: usize) -> usize {
    let (w_blocks, w_tail) = wp.as_chunks_mut::<BLOCK>();
    let (x_blocks, x_tail) = xp.as_chunks::<BLOCK>();

    let mut carry = 0;
    for (target, value) in w_blocks.iter_mut().zip(x_blocks) {
        carry = mul_1_words(target, value, vl, carry);
    }

    mul_1_words(w_tail, x_tail, vl, carry)
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
    assert!(n >= 1, "should not be called on an empty operand");
    assert!(wp.len() >= n, "operand too short");
    let wp = &mut wp[..n];

    if n < BLOCK {
        return addmul_1_words(wp, xp, vl, 0);
    }

    let (w_blocks, w_tail) = wp.as_chunks_mut::<BLOCK>();
    let (x_blocks, x_tail) = xp.as_chunks::<BLOCK>();

    let mut carry = 0;
    for (target, value) in w_blocks.iter_mut().zip(x_blocks) {
        carry = addmul_1_words(target, value, vl, carry);
    }

    addmul_1_words(w_tail, x_tail, vl, carry)
}

/// [`addmul_1`] one word at a time, picking up an incoming carry and returning the outgoing one.
///
/// One accumulator absorbs the product, the word it is added to and the incoming carry all at
/// once: the largest value it can take is `(2 ** BITS - 1) ** 2 + 2 * (2 ** BITS - 1)`, which is
/// exactly `2 ** (2 * BITS) - 1`. Splitting the product into two words first, and only then adding
/// the target to the low one, means the same work plus an overflow to fold back into the carry.
#[inline]
fn addmul_1_words(wp: &mut [usize], xp: &[usize], vl: usize, mut carry: usize) -> usize {
    for (target, &value) in wp.iter_mut().zip(xp) {
        let accumulator = value as u128 * vl as u128 + *target as u128 + carry as u128;
        *target = accumulator as usize;
        carry = (accumulator >> usize::BITS) as usize;
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
    assert!(n >= 1, "should not be called on an empty operand");
    assert!(wp.len() >= n, "operand too short");
    let wp = &mut wp[..n];

    if n < BLOCK {
        return submul_1_words(wp, xp, vl, 0);
    }

    let (w_blocks, w_tail) = wp.as_chunks_mut::<BLOCK>();
    let (x_blocks, x_tail) = xp.as_chunks::<BLOCK>();

    let mut borrow = 0;
    for (target, value) in w_blocks.iter_mut().zip(x_blocks) {
        borrow = submul_1_words(target, value, vl, borrow);
    }

    submul_1_words(w_tail, x_tail, vl, borrow)
}

/// [`submul_1`] one word at a time, picking up an incoming borrow and returning the outgoing one.
///
/// The product and the incoming borrow share an accumulator the way they do in [`addmul_1_words`],
/// but the target cannot join them, because it is subtracted rather than added.
#[inline]
fn submul_1_words(wp: &mut [usize], xp: &[usize], vl: usize, mut borrow: usize) -> usize {
    for (target, &value) in wp.iter_mut().zip(xp) {
        let accumulator = value as u128 * vl as u128 + borrow as u128;
        let (value, underflow) = target.overflowing_sub(accumulator as usize);
        *target = value;
        // The high word is `2 ** BITS - 1` only when the low word is zero, in which case the
        // subtraction above cannot underflow, so this addition cannot overflow either.
        borrow = (accumulator >> usize::BITS) as usize + underflow as usize;
    }

    borrow
}

/// Whether this processor has the wide multiply [`mul_1`] asks for.
#[cfg(target_arch = "x86_64")]
#[inline]
fn has_wide_multiply() -> bool {
    std::arch::is_x86_feature_detected!("bmi2")
}

/// [`mul_1_blocks`] compiled a second time, with `mulx` available.
///
/// `mul` writes the fixed `rdx:rax` pair, so neighbouring products cannot be in flight at the same
/// time and each one needs a move to get its high word out of the way before the next. `mulx`
/// names both of its outputs and leaves the flags alone, which on a long operand is worth more
/// than everything else in this file put together. It is not part of the baseline `x86-64` target,
/// so the only way to reach it is a second copy of the loop behind a runtime test.
///
/// The second copy only exists if the loop is inlined here: `#[target_feature]` applies to the
/// body of this function, and the loop it calls is compiled for the baseline target like any
/// other. Left to itself the code generator emits one shared copy of that loop and calls it from
/// both places, which is correct, is not slow enough to look like a mistake, and quietly leaves no
/// `mulx` in the binary at all. `#[inline]` is a hint and does not prevent that, while
/// `#[inline(always)]` is a requirement and does, so the loop and everything it calls carry it.
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "bmi2")]
fn mul_1_wide(wp: &mut [usize], xp: &[usize], vl: usize) -> usize {
    mul_1_blocks(wp, xp, vl)
}

/// Negate a value in place, interpreting it as a two's complement number.
///
/// Call only on negative values (the highest bit need not be zero to represent that, it's context
/// dependent). The result is normalized, that is, trailing zero words are removed.
#[inline]
pub fn to_twos_complement<const S: usize>(values: &mut SmallVec<[usize; S]>) {
    // Negating is complementing after subtracting one: `-x == !(x - 1)`. Words below the lowest
    // set word are zero and stay zero, the borrow of the `- 1` dies in the lowest set word, which
    // is thereby negated on its own, and every word above it is simply complemented; no carry
    // travels between words at all.
    let Some(lowest) = values.iter().position(|&value| value != 0) else {
        // Only a zero value has no set word, which the contract excludes. Should it happen
        // anyway, normalize to the empty representation of zero rather than leave a
        // denormalized value behind.
        debug_assert!(false, "should not be called on a zero value");
        values.clear();
        return;
    };

    values[lowest] = values[lowest].wrapping_neg();
    for value in &mut values[lowest + 1..] {
        *value = !*value;
    }

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

    let shared = values.len().min(rhs.len());
    let (values, rhs) = (&mut values[..shared], &rhs[..shared]);
    let mut carry = Flag::default();

    // Operands this short never fill a block, and the chunking is pure overhead for them.
    if shared < BLOCK {
        for (value, &rhs_value) in values.iter_mut().zip(rhs) {
            (*value, carry) = add_word(*value, rhs_value, carry);
        }

        return usize::from(carry) == 1;
    }

    let (v_blocks, v_tail) = values.as_chunks_mut::<BLOCK>();
    let (r_blocks, r_tail) = rhs.as_chunks::<BLOCK>();

    for (value, rhs_value) in v_blocks.iter_mut().zip(r_blocks) {
        for word in 0..BLOCK {
            (value[word], carry) = add_word(value[word], rhs_value[word], carry);
        }
    }
    for (value, &rhs_value) in v_tail.iter_mut().zip(r_tail) {
        (*value, carry) = add_word(*value, rhs_value, carry);
    }

    usize::from(carry) == 1
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

    let shared = values.len().min(rhs.len());
    let (values, rhs) = (&mut values[..shared], &rhs[..shared]);
    let mut borrow = Flag::default();

    // Operands this short never fill a block, and the chunking is pure overhead for them.
    if shared < BLOCK {
        for (value, &rhs_value) in values.iter_mut().zip(rhs) {
            (*value, borrow) = sub_word(*value, rhs_value, borrow);
        }

        return usize::from(borrow) == 1;
    }

    let (v_blocks, v_tail) = values.as_chunks_mut::<BLOCK>();
    let (r_blocks, r_tail) = rhs.as_chunks::<BLOCK>();

    for (value, rhs_value) in v_blocks.iter_mut().zip(r_blocks) {
        for word in 0..BLOCK {
            (value[word], borrow) = sub_word(value[word], rhs_value[word], borrow);
        }
    }
    for (value, &rhs_value) in v_tail.iter_mut().zip(r_tail) {
        (*value, borrow) = sub_word(*value, rhs_value, borrow);
    }

    usize::from(borrow) == 1
}

/// Subtract `values` from `rhs`, storing the result in `values`, both of the same length.
///
/// The mirror image of [`sub_assign_slice`]: it computes `values = rhs - values` where that one
/// computes `values -= rhs`. Returns whether the subtraction borrows out of the top word.
///
/// # Panics
///
/// In debug mode, if the two slices have different lengths.
#[inline]
pub fn sub_from_slice(values: &mut [usize], rhs: &[usize]) -> bool {
    debug_assert_eq!(values.len(), rhs.len());

    let shared = values.len().min(rhs.len());
    let (values, rhs) = (&mut values[..shared], &rhs[..shared]);
    let mut borrow = Flag::default();

    // Operands this short never fill a block, and the chunking is pure overhead for them.
    if shared < BLOCK {
        for (value, &rhs_value) in values.iter_mut().zip(rhs) {
            (*value, borrow) = sub_word(rhs_value, *value, borrow);
        }

        return usize::from(borrow) == 1;
    }

    let (v_blocks, v_tail) = values.as_chunks_mut::<BLOCK>();
    let (r_blocks, r_tail) = rhs.as_chunks::<BLOCK>();

    for (value, rhs_value) in v_blocks.iter_mut().zip(r_blocks) {
        for word in 0..BLOCK {
            (value[word], borrow) = sub_word(rhs_value[word], value[word], borrow);
        }
    }
    for (value, &rhs_value) in v_tail.iter_mut().zip(r_tail) {
        (*value, borrow) = sub_word(rhs_value, *value, borrow);
    }

    usize::from(borrow) == 1
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

    use crate::integer::big::ops::building_blocks::{add_2, addmul_1, is_well_formed, mul_1, sub_2, sub_n, submul_1, to_twos_complement};

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

        // A borrow that propagates through the whole length
        let mut x: SV = smallvec![0; 3];
        assert_eq!(sub_n(&mut x, &[0, 0, 0], &[1, 0, 0], 3), 1);
        let expected: SV = smallvec![usize::MAX; 3];
        assert_eq!(x, expected);

        // Only the first `n` words are touched
        let mut x: SV = smallvec![7, 7, 7];
        assert_eq!(sub_n(&mut x, &[5, 5, 5], &[1, 1, 1], 2), 0);
        let expected: SV = smallvec![4, 4, 7];
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
            // Longer than one block, so that every tail length is covered.
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
    fn test_mul_1() {
        let mut x = vec![0; 3];

        assert_eq!(mul_1(&mut x, &[1, 2, 3], 0), 0);
        assert_eq!(x, vec![0, 0, 0]);

        assert_eq!(mul_1(&mut x, &[1, 2, 3], 1), 0);
        assert_eq!(x, vec![1, 2, 3]);

        assert_eq!(mul_1(&mut x, &[usize::MAX, usize::MAX, usize::MAX], usize::MAX), usize::MAX - 1);
        assert_eq!(x, vec![1, usize::MAX, usize::MAX]);

        let mut x = vec![0; 1];
        assert_eq!(mul_1(&mut x, &[usize::MAX], 2), 1);
        assert_eq!(x, vec![usize::MAX - 1]);
    }

    #[test]
    fn test_addmul_1() {
        // A carry that propagates through the whole length
        let mut x = vec![usize::MAX; 3];
        assert_eq!(addmul_1(&mut x, &[1, 0, 0], 1), 1);
        assert_eq!(x, vec![0, 0, 0]);

        let mut x = vec![1, 2, 3];
        assert_eq!(addmul_1(&mut x, &[1, 1, 1], 0), 0);
        assert_eq!(x, vec![1, 2, 3]);

        let mut x = vec![usize::MAX; 2];
        assert_eq!(addmul_1(&mut x, &[usize::MAX, usize::MAX], usize::MAX), usize::MAX);
        // `(2 ** 128 - 1) + (2 ** 64 - 1) * (2 ** 128 - 1)`, truncated to two words
        assert_eq!(x, vec![0, usize::MAX]);
    }

    #[test]
    fn test_submul_1() {
        // A borrow that propagates through the whole length
        let mut x = vec![0; 3];
        assert_eq!(submul_1(&mut x, &[1, 0, 0], 1), 1);
        assert_eq!(x, vec![usize::MAX; 3]);

        let mut x = vec![1, 2, 3];
        assert_eq!(submul_1(&mut x, &[1, 1, 1], 0), 0);
        assert_eq!(x, vec![1, 2, 3]);

        let mut x = vec![usize::MAX; 3];
        assert_eq!(submul_1(&mut x, &[usize::MAX, usize::MAX, usize::MAX], 1), 0);
        assert_eq!(x, vec![0, 0, 0]);
    }

    /// Compare the routines against a straightforward wide integer model.
    ///
    /// Where the cross-check below only says that two implementations agree, this says that they
    /// are right. The model is exact only while the operands fit in the widest integer type, so it
    /// uses single word operands for the multiplications and at most two word operands for the
    /// subtraction.
    #[test]
    #[cfg(target_pointer_width = "64")]
    fn test_against_model() {
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
                            let borrow = sub_n(&mut target, &left, &right, n);

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
                    let high = mul_1(&mut target, &[value], multiplier);
                    assert_eq!(
                        to_u128(&target) + ((high as u128) << 64),
                        value as u128 * multiplier as u128,
                    );

                    let mut target = [initial];
                    let carry = addmul_1(&mut target, &[value], multiplier);
                    assert_eq!(
                        to_u128(&target) + ((carry as u128) << 64),
                        initial as u128 + value as u128 * multiplier as u128,
                    );

                    // `initial - value * multiplier == target - borrow * 2 ** 64`, rearranged so
                    // that every term is non-negative and fits in a `u128`.
                    let mut target = [initial];
                    let borrow = submul_1(&mut target, &[value], multiplier);
                    assert_eq!(
                        initial as u128 + ((borrow as u128) << 64),
                        to_u128(&target) + value as u128 * multiplier as u128,
                    );
                }
            }
        }
    }

    /// Compare the routines against a reference implementation on the same inputs.
    ///
    /// The routines handle their words in blocks, and [`mul_1`] has a second copy of its loop for
    /// processors with a wide multiply. The references below are the same arithmetic written one
    /// word at a time, with no block, no tail and no dispatch, so a mistake in any of that shows
    /// up as a disagreement here.
    mod against_reference {
        use crate::integer::big::ops::building_blocks::{add_assign_slice, addmul_1, mul_1, sub_assign_slice, sub_from_slice, sub_n, submul_1};

        use super::{cross_check_multipliers, cross_check_operands, cross_check_targets};

        fn sub_n_reference(wp: &mut [usize], xp: &[usize], yp: &[usize], n: usize) -> usize {
            let mut borrow = false;
            for ((target, &left), &right) in wp[..n].iter_mut().zip(&xp[..n]).zip(&yp[..n]) {
                (*target, borrow) = left.borrowing_sub(right, borrow);
            }

            borrow as usize
        }

        fn add_assign_reference(values: &mut [usize], rhs: &[usize]) -> bool {
            let mut carry = false;
            for (value, &rhs_value) in values.iter_mut().zip(rhs) {
                (*value, carry) = value.carrying_add(rhs_value, carry);
            }

            carry
        }

        fn sub_assign_reference(values: &mut [usize], rhs: &[usize]) -> bool {
            let mut borrow = false;
            for (value, &rhs_value) in values.iter_mut().zip(rhs) {
                (*value, borrow) = value.borrowing_sub(rhs_value, borrow);
            }

            borrow
        }

        fn mul_1_reference(wp: &mut [usize], xp: &[usize], vl: usize) -> usize {
            let mut carry = 0;
            for (target, &value) in wp.iter_mut().zip(xp) {
                (*target, carry) = value.carrying_mul(vl, carry);
            }

            carry
        }

        fn addmul_1_reference(wp: &mut [usize], xp: &[usize], vl: usize) -> usize {
            let mut carry = 0;
            for (target, &value) in wp.iter_mut().zip(xp) {
                let (low, high) = value.carrying_mul(vl, carry);
                let (value, overflow) = target.overflowing_add(low);
                *target = value;
                carry = high + overflow as usize;
            }

            carry
        }

        fn submul_1_reference(wp: &mut [usize], xp: &[usize], vl: usize) -> usize {
            let mut borrow = 0;
            for (target, &value) in wp.iter_mut().zip(xp) {
                let (low, high) = value.carrying_mul(vl, borrow);
                let (value, underflow) = target.overflowing_sub(low);
                *target = value;
                borrow = high + underflow as usize;
            }

            borrow
        }

        #[test]
        fn test_sub_n() {
            for (left, right) in cross_check_operands() {
                for n in 1..=left.len() {
                    // Some extra words to catch writes past the end
                    let mut from_routine = vec![0x5a; left.len() + 3];
                    let mut from_reference = vec![0x5a; left.len() + 3];

                    let routine = sub_n(&mut from_routine, &left, &right, n);
                    let reference = sub_n_reference(&mut from_reference, &left, &right, n);

                    assert_eq!(routine, reference, "{left:?} - {right:?}, n = {n}");
                    assert_eq!(from_routine, from_reference, "{left:?} - {right:?}, n = {n}");
                }
            }
        }

        #[test]
        fn test_add_assign_slice() {
            for (left, right) in cross_check_operands() {
                for n in 1..=left.len() {
                    let mut from_routine = left.clone();
                    let mut from_reference = left.clone();

                    let routine = add_assign_slice(&mut from_routine[..n], &right[..n]);
                    let reference = add_assign_reference(&mut from_reference[..n], &right[..n]);

                    assert_eq!(routine, reference, "{left:?} += {right:?}, n = {n}");
                    assert_eq!(from_routine, from_reference, "{left:?} += {right:?}, n = {n}");
                }
            }
        }

        #[test]
        fn test_sub_assign_slice() {
            for (left, right) in cross_check_operands() {
                for n in 1..=left.len() {
                    let mut from_routine = left.clone();
                    let mut from_reference = left.clone();

                    let routine = sub_assign_slice(&mut from_routine[..n], &right[..n]);
                    let reference = sub_assign_reference(&mut from_reference[..n], &right[..n]);

                    assert_eq!(routine, reference, "{left:?} -= {right:?}, n = {n}");
                    assert_eq!(from_routine, from_reference, "{left:?} -= {right:?}, n = {n}");
                }
            }
        }

        #[test]
        fn test_sub_from_slice() {
            for (left, right) in cross_check_operands() {
                for n in 1..=left.len() {
                    let mut from_routine = left.clone();
                    // The same subtraction through `sub_assign_slice`, with the operands the
                    // other way around.
                    let mut from_reference = right.clone();

                    let routine = sub_from_slice(&mut from_routine[..n], &right[..n]);
                    let reference = sub_assign_reference(&mut from_reference[..n], &left[..n]);

                    assert_eq!(routine, reference, "{right:?} - {left:?}, n = {n}");
                    assert_eq!(from_routine[..n], from_reference[..n], "{right:?} - {left:?}, n = {n}");
                }
            }
        }

        #[test]
        fn test_mul_1() {
            for (left, _) in cross_check_operands() {
                for multiplier in cross_check_multipliers() {
                    for n in 1..=left.len() {
                        let mut from_routine = vec![0x5a; left.len() + 3];
                        let mut from_reference = vec![0x5a; left.len() + 3];

                        let routine = mul_1(&mut from_routine, &left[..n], multiplier);
                        let reference = mul_1_reference(&mut from_reference[..n], &left[..n], multiplier);

                        assert_eq!(routine, reference, "{left:?} * {multiplier}, n = {n}");
                        assert_eq!(from_routine, from_reference, "{left:?} * {multiplier}, n = {n}");
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
                            let mut from_routine = initial.clone();
                            let mut from_reference = initial.clone();

                            let routine = addmul_1(&mut from_routine, &left[..n], multiplier);
                            let reference = addmul_1_reference(&mut from_reference[..n], &left[..n], multiplier);

                            assert_eq!(routine, reference, "{initial:?} += {left:?} * {multiplier}, n = {n}");
                            assert_eq!(from_routine, from_reference, "{initial:?} += {left:?} * {multiplier}, n = {n}");
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
                            let mut from_routine = initial.clone();
                            let mut from_reference = initial.clone();

                            let routine = submul_1(&mut from_routine, &left[..n], multiplier);
                            let reference = submul_1_reference(&mut from_reference[..n], &left[..n], multiplier);

                            assert_eq!(routine, reference, "{initial:?} -= {left:?} * {multiplier}, n = {n}");
                            assert_eq!(from_routine, from_reference, "{initial:?} -= {left:?} * {multiplier}, n = {n}");
                        }
                    }
                }
            }
        }
    }
}
