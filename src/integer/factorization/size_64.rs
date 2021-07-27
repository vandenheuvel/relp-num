use std::intrinsics::assume;
use std::num::NonZeroU64;

use gcd::Gcd;

use crate::integer::factorization::prime::primes::SMALL_ODD_PRIMES;
use crate::integer::factorization::start;
use crate::Prime;

/// Approximately factorize a number.
///
/// This factorization is not necessarily exact; large factors might be missing, depending on the
/// parameters chosen.
///
/// # Arguments
///
/// * `NR_SMALL_PRIMES`: The number of odd small primes to do trial division with.
/// * `TRIAL_DIVISION_LIMIT`: Largest odd number to do trial division with after small primes are
/// exhausted. If it is zero, this method is not used.
/// * `RHO_BASE_LIMIT`: Number of rounds to use with Pollard's rho method. If it is zero, this
/// method is not used.
/// * `KEEP_RESIDUAL`: Whether the (potentially non-prime) remainder after the previous three
/// methods should be added as a factor.
pub fn factorize<
    const NR_SMALL_PRIMES: usize,
    const TRIAL_DIVISION_LIMIT: u64,
    const RHO_BASE_LIMIT: u64,
    const KEEP_RESIDUAL: bool,
>(value: NonZeroU64) -> Vec<(u64, u32)> {
    let mut x = value.get();

    // Product of the first 16 primes is larger than 2 ** 64
    let mut factors = Vec::with_capacity(15);

    // Powers of two
    let two_powers = x.trailing_zeros();
    if two_powers > 0 {
        x >>= two_powers;
        factors.push((2, two_powers));
    }

    'odd: {
        // smallest
        for divisor in &SMALL_ODD_PRIMES[..NR_SMALL_PRIMES] {
            let divisor = *divisor as u64;
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

        if TRIAL_DIVISION_LIMIT != 0 {
            let start = start(NR_SMALL_PRIMES) as u64;
            x = trial_division::<TRIAL_DIVISION_LIMIT>(x, start, &mut factors);

            if x == 1 {
                break 'odd;
            }
        }

        if KEEP_RESIDUAL {
            if x.is_prime() {
                factors.push((x, 1));
                break 'odd;
            }
        }

        if RHO_BASE_LIMIT != 0 {
            x = pollards_rho::<RHO_BASE_LIMIT>(x, &mut factors);
        }

        if KEEP_RESIDUAL {
            if x > 1 {
                factors.push((x, 1));
            }
        }
    }

    factors
}

// TODO(PERFORMANCE): Make `start` a const parameter
fn trial_division<const END: u64>(mut x: u64, start: u64, factors: &mut Vec<(u64, u32)>) -> u64 {
    let mut divisor = start;
    let mut sqrt = ((x as f64).sqrt() + 2_f64) as u64;
    while x > 1 && divisor < END && divisor <= sqrt && !x.is_prime() {
        unsafe {
            assume(divisor != 0);
        }

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

    x
}

fn pollards_rho<const BASE_LIMIT: u64>(mut x: u64, factors: &mut Vec<(u64, u32)>) -> u64 {
    // Prime test and Pollard's rho
    let mut unsorted_factors = Vec::new();
    rho_loop::<BASE_LIMIT>(x, &mut unsorted_factors);

    // Sort and aggregate the factors
    unsorted_factors.sort_unstable();
    let mut iter = unsorted_factors.into_iter();
    let mut factor = iter.next().unwrap();
    let mut counter = 1;
    for new_factor in iter {
        x /= new_factor;

        if new_factor == factor {
            counter += 1;
        } else {
            factors.push((factor, counter));
            factor = new_factor;
            counter = 1;
        }
    }
    factors.push((factor, counter));
    x /= factor;

    x
}

fn rho_loop<const LIMIT: u64>(mut x: u64, factors: &mut Vec<u64>) {
    debug_assert_ne!(x, 0);

    let mut e = 2;
    while x > 1 {
        if x.is_prime() || e == LIMIT {
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
                    rho_loop::<LIMIT>(factor, factors);
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

#[cfg(test)]
mod test {
    use std::num::NonZeroU64;

    use crate::integer::factorization::size_64::factorize;

    #[test]
    fn test_composite() {
        let composite = NonZeroU64::new(2_u64.pow(36) - 7).unwrap();
        assert_eq!(
            factorize::<256, 10_000, 20, true>(composite),
            vec![(3, 1), (22906492243, 1)],
        );
        let composite = NonZeroU64::new(2_u64.pow(60) - 95).unwrap();
        assert_eq!(
            factorize::<256, 10_000, 20, true>(composite),
            vec![(3457, 1), (6203, 1), (53764867411, 1)],
        );
        let composite = NonZeroU64::new(2_u64.pow(53) - 113).unwrap();
        assert_eq!(
            factorize::<256, 10_000, 20, true>(composite),
            vec![(3, 2), (43, 1), (642739, 1), (36211303, 1)],
        );
    }
}
