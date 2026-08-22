use std::num::NonZeroU8;

use crate::integer::factorization::prime::primes::SMALL_ODD_PRIMES_8;

/// Factorize a value that fits in a byte, completely.
///
/// # Return value
///
/// The `(factor, power)` tuples and the residual, the part of the value that was not decomposed.
/// This residual is always one: the smallest composite that is coprime to `3 * 5 * 7 * 11 * 13` is
/// `17 * 17 = 289`, which doesn't fit in a byte, so whatever is left after trial division by these
/// primes is either one or a prime.
#[must_use]
#[inline]
pub fn factorize(value: NonZeroU8) -> (Vec<(u8, u32)>, u8) {
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
