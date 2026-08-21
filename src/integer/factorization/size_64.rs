use std::cmp::Ordering;
use std::hint::assert_unchecked;
use std::num::NonZeroU64;

use gcd::Gcd;

use crate::integer::factorization::prime::primes::SMALL_ODD_PRIMES;
use crate::integer::factorization::start;
use crate::Prime;

/// Approximately factorize a number.
///
/// This factorization is not necessarily exact; large factors might be missing, depending on the
/// parameters chosen. Whatever was not decomposed is returned as the residual, so the value is
/// always described completely.
///
/// # Arguments
///
/// * `NR_SMALL_PRIMES`: The number of odd small primes to do trial division with.
/// * `TRIAL_DIVISION_LIMIT`: Largest odd number to do trial division with after small primes are
///   exhausted. If it is zero, this method is not used.
/// * `RHO_BASE_LIMIT`: Number of rounds to use with Pollard's rho method. If it is zero, this
///   method is not used.
/// * `KEEP_RESIDUAL`: Whether an extra primality test should be spent on the remainder after the
///   previous three methods: when it is prime, it is a genuine factor and moved into `factors`
///   instead of being returned as the residual. A remainder that is not proven prime is never
///   added as a factor, it is always returned as the residual.
///
/// # Return value
///
/// The `(factor, power)` tuples and the residual: the part of the value that was not decomposed.
/// The residual is one when the factorization is complete, and
/// `value == residual * product(factor ^ power)` always holds.
pub fn factorize<
    const NR_SMALL_PRIMES: usize,
    const TRIAL_DIVISION_LIMIT: u64,
    const RHO_BASE_LIMIT: u64,
    const KEEP_RESIDUAL: bool,
>(value: NonZeroU64) -> (Vec<(u64, u32)>, u64) {
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

        // A remainder that is proven prime is a genuine factor, so it is moved out of the residual.
        // Note that `x` is set to one, such that it is not counted twice.
        if KEEP_RESIDUAL
            && x.is_prime() {
                factors.push((x, 1));
                x = 1;
                break 'odd;
            }

        if RHO_BASE_LIMIT != 0 {
            x = pollards_rho::<RHO_BASE_LIMIT>(x, &mut factors);
        }

        // Whatever is left is not proven prime, so it stays in the residual rather than being
        // reported as a factor.
    }

    (factors, x)
}

// TODO(PERFORMANCE): Make `start` a const parameter
fn trial_division<const END: u64>(mut x: u64, start: u64, factors: &mut Vec<(u64, u32)>) -> u64 {
    let mut divisor = start;
    let mut sqrt = ((x as f64).sqrt() + 2_f64) as u64;
    // `x` only changes when a factor is found, so its primality is only worth recomputing there.
    // Testing it in the loop condition instead costs a full Miller-Rabin per candidate divisor,
    // which dominates the loop by orders of magnitude.
    let mut is_prime = x.is_prime();
    while x > 1 && divisor < END && divisor <= sqrt && !is_prime {
        unsafe {
            assert_unchecked(divisor != 0);
        }

        let mut counter = 0;
        while x.is_multiple_of(divisor) {
            x /= divisor;
            counter += 1;
        }

        if counter > 0 {
            factors.push((divisor, counter));
            sqrt = ((x as f64).sqrt() + 2_f64) as u64;
            is_prime = x.is_prime();
        }

        divisor += 2;
    }

    x
}

/// Split `x` into prime factors with Pollard's rho method.
///
/// Only factors that are proven prime are appended to `factors`. Whatever could not be split within
/// the budget is returned as the residual, such that
/// `x == residual * product(factor ^ power over the appended factors)`.
fn pollards_rho<const BASE_LIMIT: u64>(x: u64, factors: &mut Vec<(u64, u32)>) -> u64 {
    debug_assert_ne!(x, 0);

    if x == 1 {
        // Nothing to do; note that the loop below would have nothing to aggregate.
        return 1;
    }

    // Prime test and Pollard's rho
    let mut unsorted_factors = Vec::new();
    let mut residual = 1;
    rho_loop::<BASE_LIMIT>(x, &mut unsorted_factors, &mut residual);

    // Sort and aggregate the factors
    unsorted_factors.sort_unstable();
    let mut iter = unsorted_factors.into_iter();
    if let Some(first) = iter.next() {
        let mut factor = first;
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

    residual
}

/// Recursively split `x`, appending the primes found to `factors`.
///
/// Everything that could not be split is multiplied into `residual`; because these values are
/// divisors of `x`, their product is a divisor of `x` too and can't overflow.
fn rho_loop<const LIMIT: u64>(mut x: u64, factors: &mut Vec<u64>, residual: &mut u64) {
    debug_assert_ne!(x, 0);

    let mut e = 2;
    while x > 1 {
        if x.is_prime() {
            factors.push(x);
            return;
        }

        // Note the inequality: with `LIMIT < 2` an equality test would never fire, and the loop
        // would keep trying entropies forever.
        if e >= LIMIT {
            // Out of budget. `x` is composite, so it would be a lie to report it as a factor.
            *residual *= x;
            return;
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
                    rho_loop::<LIMIT>(factor, factors, residual);
                }
                x /= factor;
            }
        }
    }
}

/// The largest batch size [`rho`] works with before it gives up on an entropy.
///
/// The collision search needs on the order of the fourth root of the value many steps, so at most
/// about `2 ** 16` for a value below `2 ** 64`. This bound is far above that; it exists to make the
/// search terminate in all cases, not to cut short a search that is still likely to succeed.
const MAX_STEPS: u64 = 1 << 24;

/// Pollard's rho function generates a divisor.
///
/// Returns `None` when this entropy didn't yield a proper divisor; the caller should then try
/// again with a different entropy. When a value is returned, it is a proper divisor of `value`:
/// larger than one and smaller than `value`. It is not necessarily prime.
///
/// Up to minor adaptions, this code is from the reikna repository developed by Phillip Heikoop.
pub fn rho(value: u64, entropy: u64) -> Option<u64> {
    debug_assert_ne!(value, 0);
    debug_assert_ne!(value, 1);
    debug_assert_ne!(value, 2);

    let entropy = entropy.wrapping_mul(value);
    let c = entropy & 0xff;
    // The number of steps per batch must be at least one, or no work would be done at all and the
    // loop below would never terminate.
    let u = (entropy & 0x7f).max(1);

    let mut r: u64 = 1;
    let mut q: u64 = 1;
    let mut y: u64 = entropy & 0xf;

    let mut factor = 1;

    let mut y_old = 0;
    let mut x = 0;

    // The intermediate values don't fit in 64 bits once `value` exceeds 32 bits, so they are
    // computed in 128 bits. Doing this with wrapping arithmetic instead would break the method:
    // `f(y) mod p` would no longer be a function of `y mod p`, which is exactly the property that
    // makes the collision search find a factor.
    let value_wide = value as u128;
    let f = |x: u64| (((x as u128) * (x as u128) + c as u128) % value_wide) as u64;
    let mul_mod = |a: u64, b: u64| (((a as u128) * (b as u128)) % value_wide) as u64;

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
                    q = mul_mod(q, x - y);
                } else {
                    q = mul_mod(q, y - x);
                }
            }

            factor = Gcd::gcd(q, value);
            k += u;
        }

        // Each round costs about `r` evaluations, and the batch size doubles afterwards. Give up
        // rather than search unboundedly: a value below `2 ** 64` has a factor within about
        // `2 ** 16` steps of the collision search, so a search that got this far isn't going to
        // succeed with this entropy. It also keeps `r` from wrapping around to zero, which would
        // leave the loop spinning without doing any work.
        if r > MAX_STEPS {
            return None;
        }
        r *= 2;
    }

    // Walk the cycle back one step at a time to isolate the collision. At most `r` steps are needed,
    // as that is how far the batch above advanced; the bound also guarantees termination.
    let mut steps_left = r;
    while factor == value || factor <= 1 {
        if steps_left == 0 {
            // the algorithm has failed for this entropy
            return None;
        }
        steps_left -= 1;

        y_old = f(y_old);

        match x.cmp(&y_old) {
            Ordering::Less => factor = Gcd::gcd(y_old - x, value),
            Ordering::Equal => {
                // the algorithm has failed for this entropy,
                // return the factor as-is
                return None;
            }
            Ordering::Greater => factor = Gcd::gcd(x - y_old, value),
        }
    }

    Some(factor)
}

#[cfg(test)]
mod test {
    use std::num::NonZeroU64;

    use crate::integer::factorization::size_64::{factorize, rho};
    use crate::Prime;

    #[test]
    fn test_composite() {
        let composite = NonZeroU64::new(2_u64.pow(36) - 7).unwrap();
        assert_eq!(
            factorize::<256, 10_000, 20, true>(composite),
            (vec![(3, 1), (22906492243, 1)], 1),
        );
        let composite = NonZeroU64::new(2_u64.pow(60) - 95).unwrap();
        assert_eq!(
            factorize::<256, 10_000, 20, true>(composite),
            (vec![(3457, 1), (6203, 1), (53764867411, 1)], 1),
        );
        let composite = NonZeroU64::new(2_u64.pow(53) - 113).unwrap();
        assert_eq!(
            factorize::<256, 10_000, 20, true>(composite),
            (vec![(3, 2), (43, 1), (642739, 1), (36211303, 1)], 1),
        );
    }

    /// Whatever the parameters, `value == residual * product(factor ^ power)`.
    fn assert_describes(value: u64, factors: &[(u64, u32)], residual: u64) {
        let mut total = residual;
        for &(factor, power) in factors {
            assert!(factor > 1, "{factor} is not a factor of {value}");
            for _ in 0..power {
                total = total.checked_mul(factor).expect("at most the original value");
            }
        }
        assert_eq!(total, value, "factors {factors:?} and residual {residual} of {value}");
    }

    /// The crate wide constants leave the cofactor alone, so it shows up as the residual.
    #[test]
    fn test_residual_is_the_cofactor() {
        // A prime that is not among the small primes
        let value = NonZeroU64::new(2_u64.pow(36) - 5).unwrap();
        assert_eq!(factorize::<256, 0, 0, false>(value), (vec![], value.get()));

        // The same value, but now the routine is allowed to check whether it is prime
        assert_eq!(factorize::<256, 0, 0, true>(value), (vec![(value.get(), 1)], 1));

        // A composite of two large primes; even proving that the cofactor is not prime doesn't make
        // it a factor, so it stays in the residual.
        let value = NonZeroU64::new(1_000_003 * 1_000_033).unwrap();
        assert_eq!(factorize::<256, 0, 0, true>(value), (vec![], value.get()));
    }

    /// Pollard's rho isn't used with the crate wide constants, but it works when it is enabled.
    ///
    /// The values here need it: their factors are larger than the small primes and larger than the
    /// trial division limit.
    #[test]
    fn test_pollards_rho() {
        let values = [
            1_000_003 * 1_000_003,
            1_000_003 * 1_000_033,
            2_u64.pow(53) - 113,
            (2_u64.pow(31) - 1) * (2_u64.pow(31) - 19),
            3 * 5 * 7 * (1_000_003 * 1_000_033),
        ];

        for value in values {
            let (factors, residual) = factorize::<256, 0, 100, true>(NonZeroU64::new(value).unwrap());

            assert_describes(value, &factors, residual);
            assert_eq!(residual, 1, "{value} was not factorized completely");
            for &(factor, _) in &factors {
                assert!(factor.is_prime(), "{factor} of {value} is not prime");
            }
        }

        // The square of a prime, which the wrapping arithmetic that this code used to do never
        // split; it reported the composite as if it were a prime factor.
        assert_eq!(
            factorize::<256, 0, 100, true>(NonZeroU64::new(1_000_003 * 1_000_003).unwrap()),
            (vec![(1_000_003, 2)], 1),
        );
    }

    /// Products of two primes that are well beyond the small primes are split by rho.
    ///
    /// The primes are generated deterministically; the point is to cover a wider range than the
    /// handful of hardcoded values above, because the modular arithmetic that rho depends on used
    /// to be wrong for values that don't fit in 32 bits.
    #[test]
    fn test_pollards_rho_semiprimes() {
        // A linear congruential generator, so that the cases are the same on every run
        let mut state = 0x2545_f491_4f6c_dd1d_u64;
        let mut next_prime_in = |below: u64| loop {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let candidate = (state % below) | 1;
            if candidate > 1_000_000 && candidate.is_prime() {
                break candidate;
            }
        };

        for bound in [2_u64.pow(24), 2_u64.pow(28), 2_u64.pow(31)] {
            for _ in 0..4 {
                let left = next_prime_in(bound);
                let right = next_prime_in(bound);
                let value = left * right;

                let (factors, residual) = factorize::<256, 0, 100, true>(NonZeroU64::new(value).unwrap());

                assert_describes(value, &factors, residual);
                assert_eq!(residual, 1, "{value} = {left} * {right} was not factorized completely");
                let expected = if left == right {
                    vec![(left, 2)]
                } else {
                    let (small, large) = (u64::min(left, right), u64::max(left, right));
                    vec![(small, 1), (large, 1)]
                };
                assert_eq!(factors, expected);
            }
        }
    }

    /// Any divisor that is found is a proper divisor, and the search always terminates.
    #[test]
    fn test_rho_divisors() {
        let values = [
            1_000_003 * 1_000_003,
            1_000_003 * 1_000_033,
            23_274_416_678_917,
            (2_u64.pow(31) - 1) * (2_u64.pow(31) - 19),
        ];

        for value in values {
            for entropy in 2..20 {
                if let Some(divisor) = rho(value, entropy) {
                    assert!(divisor > 1 && divisor < value, "{divisor} is not a proper divisor of {value}");
                    assert_eq!(value % divisor, 0, "{divisor} does not divide {value}");
                }
            }
        }
    }

    /// An entropy for which the number of steps per batch used to come out as zero.
    ///
    /// The inner loop would then do no work while the counter didn't advance either, so the search
    /// spun forever.
    #[test]
    fn test_rho_zero_step_size() {
        let value: u64 = 23_274_416_678_917;
        let entropy: u64 = 128;
        debug_assert_eq!(entropy.wrapping_mul(value) & 0x7f_u64, 0, "this entropy has no step size");

        if let Some(divisor) = rho(value, entropy) {
            assert_eq!(value % divisor, 0);
        }
    }
}
