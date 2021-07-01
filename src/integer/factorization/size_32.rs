use std::intrinsics::assume;
use std::num::NonZeroU32;

use crate::integer::factorization::prime::primes::SMALL_ODD_PRIMES;
use crate::Prime;

pub fn factorize(value: NonZeroU32) -> Vec<(u32, u32)> {
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
        for divisor in SMALL_ODD_PRIMES {
            let divisor = divisor as u32;

            unsafe { assume(divisor != 0); }

            let mut counter = 0;
            while x % divisor == 0 {
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
        let mut divisor = *SMALL_ODD_PRIMES.last().unwrap() as u32 + 2;
        let mut sqrt = ((x as f64).sqrt() + 2_f64) as u32;
        while x > 1 && divisor <= sqrt && !x.is_prime() {
            let mut counter = 0;
            while x % divisor == 0 {
                x /= divisor;
                counter += 1;
            }

            if counter > 0 {
                factors.push((divisor, counter));
                sqrt = ((x as f64).sqrt() + 2_f64) as u32;
            }

            divisor += 2;
        }

        if x > 1 {
            factors.push((x, 1));
        }
    }

    factors
}
