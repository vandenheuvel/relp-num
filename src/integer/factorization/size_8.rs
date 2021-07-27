use std::num::NonZeroU8;

use crate::integer::factorization::prime::primes::SMALL_ODD_PRIMES_8;

#[must_use]
#[inline]
pub fn factorize(value: NonZeroU8) -> Vec<(u8, u32)> {
    let mut x = value.get();

    // 2 * 3 * 5 * 7 * 11 > 2 ** 8, so four values are enough
    let mut factors = Vec::with_capacity(4);

    let two_powers = x.trailing_zeros();
    if two_powers > 0 {
        x >>= two_powers;
        factors.push((2, two_powers));
    }

    for divisor in SMALL_ODD_PRIMES_8 {
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
