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
    values.last().map_or(false, |&last| last != 0)
}

#[must_use]
#[inline]
pub fn widening_mul(left: usize, right: usize) -> (usize, usize) {
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

#[must_use]
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

#[must_use]
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
#[allow(dead_code)]
pub unsafe fn add_n(target: &mut [usize], left: &[usize], right: &[usize], size: i32) -> usize {
    extern "C" {
        fn ramp_add_n(wp: *mut usize, xp: *const usize, yp: *const usize, n: i32) -> usize;
    }

    debug_assert!(size >= 1);

    ramp_add_n(target.as_mut_ptr(), left.as_ptr(), right.as_ptr(), size)
}

/// Copying subtraction (not necessarily in place)
#[inline]
pub unsafe fn sub_n(wp: &mut [usize], xp: &[usize], yp: &[usize], n: i32) -> usize {
    extern "C" {
        fn ramp_sub_n(wp: *mut usize, xp: *const usize, yp: *const usize, n: i32) -> usize;
    }

    debug_assert!(n >= 1);

    ramp_sub_n(wp.as_mut_ptr(), xp.as_ptr(), yp.as_ptr(), n)
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

#[must_use]
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
#[must_use]
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
#[must_use]
#[inline]
pub fn carrying_sub(value: usize, rhs: usize, carry: bool) -> (usize, bool) {
    let (a, b) = value.overflowing_sub(rhs);
    let (c, d) = a.overflowing_sub(carry as usize);
    (c, b | d)
}

#[cfg(test)]
mod test {
    use smallvec::{smallvec, SmallVec};

    use crate::integer::big::ops::building_blocks::{add_2, carrying_add_mut, is_well_formed, sub_n, to_twos_complement, widening_mul};

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
    fn test_mul() {
        assert_eq!(widening_mul(0, 2), (0, 0));
        assert_eq!(widening_mul(2, 2), (0, 4));
        assert_eq!(widening_mul(1 << 32, 1 << 32), (1, 0));
        assert_eq!(widening_mul(1 << 63, 3), (1, 1 << 63));
    }

    #[test]
    fn test_add_2() {
        assert_eq!(add_2(0, 0, 0, 0), (0, 0));
        assert_eq!(add_2(1, 2, 3, 4), (4, 6));
    }

    #[test]
    fn test_sub_n() {
        type SV = SmallVec<[usize; 4]>;

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
        type SV = SmallVec<[usize; 4]>;

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
}
