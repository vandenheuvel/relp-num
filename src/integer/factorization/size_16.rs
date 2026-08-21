use std::hint::assert_unchecked;
use std::num::NonZeroU16;

use crate::integer::factorization::prime::primes::SMALL_ODD_PRIMES_16;

/// Factorize a value that fits in two bytes, completely.
///
/// # Return value
///
/// The `(factor, power)` tuples and the residual, the part of the value that was not decomposed.
/// This residual is always one: `SMALL_ODD_PRIMES_16` contains every odd prime below 256, so the
/// smallest composite coprime to all of them is `257 * 257 = 66049`, which doesn't fit in two
/// bytes. Whatever is left after trial division is therefore either one or a prime.
pub fn factorize(value: NonZeroU16) -> (Vec<(u16, u32)>, u16) {
    let mut x = value.get();
    // 2 * 3 * 5 * 7 * 11 * 13 * 17 > 2 ** 16, so six values are enough
    let mut factors = Vec::with_capacity(6);

    let two_powers = x.trailing_zeros();
    if two_powers > 0 {
        x >>= two_powers;
        factors.push((2, two_powers));
    }

    for divisor in SMALL_ODD_PRIMES_16 {
        unsafe { assert_unchecked(divisor != 0); }

        let mut count = 0;
        while x.is_multiple_of(divisor) {
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
        // `x` is prime, see the doc comment
        factors.push((x, 1));
    }

    (factors, 1)
}
