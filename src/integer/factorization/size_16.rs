use std::intrinsics::assume;
use std::num::NonZeroU16;

use crate::integer::factorization::prime::primes::SMALL_ODD_PRIMES_16;

pub fn factorize(value: NonZeroU16) -> Vec<(u16, u32)> {
    let mut x = value.get();
    // 2 * 3 * 5 * 7 * 11 * 13 * 17 > 2 ** 16, so six values are enough
    let mut factors = Vec::with_capacity(6);

    let two_powers = x.trailing_zeros();
    if two_powers > 0 {
        x >>= two_powers;
        factors.push((2, two_powers));
    }

    for divisor in SMALL_ODD_PRIMES_16 {
        unsafe { assume(divisor != 0); }

        let mut count = 0;
        while x % divisor == 0 {
            x /= divisor;
            count += 1;
        }

        if count > 0 {
            factors.push((divisor, count));
        }

        if x == 1 {
            break;
        }
    }

    if x != 1 {
        factors.push((x, 1));
    }

    factors
}
