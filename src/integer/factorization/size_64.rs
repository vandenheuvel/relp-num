use gcd::Gcd;

use crate::{NonZeroFactorizable, NonZeroFactorization, NonZeroSign, NonZeroSigned, Prime};
use crate::integer::factorization::prime::primes::SMALL_ODD_PRIMES;
use std::intrinsics::assume;

impl NonZeroFactorizable for i64 {
    type Factor = u64;
    type Power = u8;

    fn factorize(&self) -> NonZeroFactorization<Self::Factor, Self::Power> {
        let sign = NonZeroSigned::signum(self);
        let NonZeroFactorization {
            factors, ..
        } = self.unsigned_abs().factorize();
        NonZeroFactorization { sign, factors }
    }
}

// TODO(PERFORMANCE): How far should this loop go?
const TRIAL_DIVISION_LIMIT: u64 = 1_000;

impl NonZeroFactorizable for u64 {
    type Factor = u64;
    type Power = u8;

    fn factorize(&self) -> NonZeroFactorization<Self::Factor, Self::Power> {
        debug_assert_ne!(*self, 0);

        let mut x = *self;
        // Product of the first 16 primes is larger than 2 ** 64
        let mut factors = Vec::with_capacity(15);

        // Trial division
        // 2
        let two_powers = x.trailing_zeros();
        if two_powers > 0 {
            x >>= two_powers;
            factors.push((2, two_powers as u8));
        }

        'odd: {
            // smallest
            for divisor in SMALL_ODD_PRIMES {
                let divisor = divisor as u64;
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
                    break 'odd;
                }
            }
            // small
            let mut divisor = *SMALL_ODD_PRIMES.last().unwrap() as u64 + 2;
            let mut sqrt = ((x as f64).sqrt() + 2_f64) as u64;
            while x > 1 && divisor < TRIAL_DIVISION_LIMIT && divisor <= sqrt && !x.is_prime() {
                let mut counter = 0;
                while x % divisor == 0 {
                    x /= divisor;
                    counter += 1;
                }

                if counter > 0 {
                    factors.push((divisor, counter));
                    sqrt = ((x as f64).sqrt() + 2_f64) as u64;
                }

                divisor += 2;
            }

            if x > 1 && x.is_prime() {
                factors.push((x, 1));
                break 'odd;
            }

            // Prime test and Pollard's rho
            let mut unsorted_factors = Vec::new();
            rho_loop(x, &mut unsorted_factors);

            // Sort and aggregate the factors
            unsorted_factors.sort_unstable();
            let mut iter = unsorted_factors.into_iter();
            let mut factor = iter.next().unwrap();
            let mut counter = 1;
            for new_factor in iter {
                if new_factor == factor {
                    counter += 1;
                } else {
                    factors.push((factor, counter));
                    factor = new_factor;
                    counter = 1;
                }
            }
            factors.push((factor, counter));
        }

        NonZeroFactorization { sign: NonZeroSign::Positive, factors }
    }
}

// TODO(PERFORMANCE): How long should this be tried?
const RHO_BASE_LIMIT: u64 = 20;

fn rho_loop(mut x: u64, factors: &mut Vec<u64>) {
    debug_assert_ne!(x, 0);

    let mut e = 2;
    while x > 1 {
        if x.is_prime() || e == RHO_BASE_LIMIT {
            factors.push(x);
            break;
        }

        match rho(x, e) {
            None | Some(1) => {
                // TODO(PERFORMANCE): Odd values only?
                e += 1;
            }
            Some(factor) => {
                if factor.is_prime() {
                    factors.push(factor);
                } else {
                    // TODO(PERFORMANCE): Should the `e` variable be passed to the inner call?
                    rho_loop(factor, factors);
                }
                x /= factor;
            }
        }
    }
}

/// Pollard's rho function generates a divisor.
///
/// Up to minor adaptions, this code is from the reikna repository developed by Phillip Heikoop.
pub fn rho(value: u64, entropy: u64) -> Option<u64> {
    debug_assert_ne!(value, 0);
    debug_assert_ne!(value, 1);
    debug_assert_ne!(value, 2);

    let entropy = entropy.wrapping_mul(value);
    let c = entropy & 0xff;
    let u = entropy & 0x7f;

    let mut r: u64 = 1;
    let mut q: u64 = 1;
    let mut y: u64 = entropy & 0xf;

    let mut factor = 1;

    let mut y_old = 0;
    let mut x = 0;

    let f = |x: u64| (x.wrapping_mul(x) + c) % value;

    while factor == 1 {
        x = y;

        for _ in 0..r {
            y = f(y);
        }

        let mut k = 0;
        while k < r && factor == 1 {
            y_old = y;

            for _ in 0..u64::min(u, r - k) {
                y = f(y);

                if x > y {
                    q = q.wrapping_mul(x - y) % value;
                } else {
                    q = q.wrapping_mul(y - x) % value;
                }
            }

            factor = Gcd::gcd(q, value);
            k += u;
        }

        r *= 2;
    }

    while factor == value || factor <= 1 {
        y_old = f(y_old);

        if x > y_old {
            factor = Gcd::gcd(x - y_old, value);
        } else if x < y_old {
            factor = Gcd::gcd(y_old - x, value);
        } else {
            // the algorithm has failed for this entropy,
            // return the factor as-is
            return None;
        }
    }

    Some(factor)
}
