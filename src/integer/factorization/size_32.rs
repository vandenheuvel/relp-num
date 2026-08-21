use std::hint::assert_unchecked;
use std::num::NonZeroU32;

use crate::integer::factorization::{NR_SMALL_PRIMES, start};
use crate::integer::factorization::prime::primes::SMALL_ODD_PRIMES;
use crate::Prime;

/// Factorize a value that fits in four bytes, completely.
///
/// # Return value
///
/// The `(factor, power)` tuples and the residual, the part of the value that was not decomposed.
/// This residual is always one: trial division continues up to the square root of what is left, and
/// stops early once that is prime, so the loop always runs to completion.
pub fn factorize(value: NonZeroU32) -> (Vec<(u32, u32)>, u32) {
    let mut x = value.get();

    // Product of the first 10 primes is larger than 2 ** 32
    let mut factors = Vec::with_capacity(9);

    let two_powers = x.trailing_zeros();
    if two_powers > 0 {
        x >>= two_powers;
        factors.push((2, two_powers));
    }

    'odd_trial_division: {
        // smallest
        for divisor in &SMALL_ODD_PRIMES[..NR_SMALL_PRIMES] {
            let divisor = *divisor as u32;

            unsafe { assert_unchecked(divisor != 0); }

            let mut counter = 0;
            while x.is_multiple_of(divisor) {
                x /= divisor;
                counter += 1;
            }

            if counter > 0 {
                factors.push((divisor, counter));
            }

            if x == 1 {
                break 'odd_trial_division;
            }
        }
        // small
        let mut divisor = start(NR_SMALL_PRIMES) as u32;
        let mut sqrt = ((x as f64).sqrt() + 2_f64) as u32;
        // `x` only changes when a factor is found, so its primality is only worth recomputing
        // there. Testing it in the loop condition instead costs a full Miller-Rabin per candidate
        // divisor, which dominates the loop by orders of magnitude.
        let mut is_prime = x.is_prime();
        while x > 1 && divisor <= sqrt && !is_prime {
            let mut counter = 0;
            while x.is_multiple_of(divisor) {
                x /= divisor;
                counter += 1;
            }

            if counter > 0 {
                factors.push((divisor, counter));
                sqrt = ((x as f64).sqrt() + 2_f64) as u32;
                is_prime = x.is_prime();
            }

            divisor += 2;
        }

        if x > 1 {
            // `x` is prime, see the doc comment
            factors.push((x, 1));
        }
    }

    (factors, 1)
}
