use std::num::NonZeroU64;

use smallvec::SmallVec;

use crate::{NonZeroFactorizable, NonZeroFactorization, NonZeroSign, Ubig};
use crate::integer::big::{BITS_PER_WORD, NonZeroUbig};
use crate::integer::big::ops::div::div_assign_one_word;
use crate::integer::big::ops::non_zero::{is_one_non_zero, shr};
use crate::integer::big::ops::normalize::trailing_zeros;
use crate::integer::factorization::{KEEP_RESIDUAL, NR_SMALL_PRIMES, size_64, start, TRIAL_DIVISION_LIMIT};
use crate::integer::factorization::prime::primes::SMALL_ODD_PRIMES;
use crate::non_zero::NonZero;
use crate::Prime;
use crate::traits::factorization::FactorizationResidual;

/// A big integer that was not decomposed entirely leaves a big integer behind.
impl<const S: usize> FactorizationResidual for Ubig<S> {
    #[inline]
    fn one() -> Self {
        <Self as num_traits::One>::one()
    }

    #[inline]
    fn is_one(&self) -> bool {
        <Self as num_traits::One>::is_one(self)
    }
}

macro_rules! define {
    ($ty:ident) => {
        impl<const S: usize> NonZeroFactorizable for $ty<S> {
            type Factor = usize;
            type Power = u32;
            /// A cofactor that could not be decomposed can be larger than a machine word, so it
            /// doesn't fit in a `Factor`.
            ///
            /// Both `Ubig` and `NonZeroUbig` use this same type, such that a `Ratio` of the two has
            /// a residual with two halves of the same type.
            type Residual = Ubig<S>;

            fn factorize(&self) -> NonZeroFactorization<Self::Factor, Self::Power, Self::Residual> {
                assert!(self.is_not_zero(), "attempt to factorize zero");

                let (factors, residual) = factorize::<
                    NR_SMALL_PRIMES, TRIAL_DIVISION_LIMIT, KEEP_RESIDUAL, S
                >(self.inner());
                let residual = unsafe {
                    // SAFETY: The residual is a divisor of a nonzero value, so it is nonzero, and
                    // it was normalized by the routines that produced it
                    Ubig::from_inner_unchecked(residual)
                };

                NonZeroFactorization { sign: NonZeroSign::Positive, factors, residual }
            }
        }
    }
}

define!(Ubig);
define!(NonZeroUbig);

/// Approximately factorize a big integer.
///
/// # Return value
///
/// The `(factor, power)` tuples and the residual: the part of the value that was not decomposed.
/// The residual is one when the factorization is complete, and
/// `value == residual * product(factor ^ power)` always holds.
fn factorize<
    const NR_SMALL_PRIMES: usize,
    const TRIAL_DIVISION_LIMIT: u64,
    const KEEP_RESIDUAL: bool,
    const S: usize,
>(values: &[usize]) -> (Vec<(usize, u32)>, SmallVec<[usize; S]>) {
    let (words, bits) = unsafe {
        // SAFETY: The value is consistent so ends in a nonzero, and is not zero
        trailing_zeros(values)
    };

    let mut x = shr::<S>(values, words, bits);
    let total = words as u32 * BITS_PER_WORD + bits;
    let mut factors = vec![];
    if total > 0 {
        factors.push((2, total));
    }

    if x.len() == 1 {
        let as_small = unsafe {
            // SAFETY: The value is not zero
            NonZeroU64::new_unchecked(x[0] as u64)
        };
        let (small, residual) = size_64::factorize::<
            NR_SMALL_PRIMES, TRIAL_DIVISION_LIMIT, 0, KEEP_RESIDUAL,
        >(as_small);
        for (factor, power) in small {
            factors.push((factor as usize, power));
        }
        // Propagate the residual of the single word routine; it is nonzero, so `x` stays well
        // formed. Note that `x.len() == 1`.
        x[0] = residual as usize;
    } else {
        // x.len() > 1
        'odd: {
            for divisor in &SMALL_ODD_PRIMES[..NR_SMALL_PRIMES] {
                let divisor = *divisor as usize;

                let mut counter = 0;
                loop {
                    let mut copy = x.clone();
                    let remainder = unsafe {
                        // SAFETY: divisor is nonzero and odd, copy is not zero
                        div_assign_one_word(&mut copy, divisor)
                    };
                    if remainder == 0 {
                        counter += 1;
                        x = copy;
                    } else {
                        break;
                    }
                }

                if counter > 0 {
                    factors.push((divisor, counter));
                }

                if unsafe { is_one_non_zero(&x) } {
                    break 'odd;
                }
            }

            if TRIAL_DIVISION_LIMIT != 0 {
                let start = start(NR_SMALL_PRIMES) as usize;
                trial_division::<TRIAL_DIVISION_LIMIT, S>(&mut x, start, &mut factors);

                if unsafe { is_one_non_zero(&x) } {
                    break 'odd;
                }
            }

            // A remainder that fits in a single word and is proven prime is a genuine factor, so it
            // is moved out of the residual. Note that `x` is set to one, such that it is not
            // counted twice. Anything else stays in the residual: a larger remainder doesn't even
            // fit in a `Factor`, and one that isn't proven prime would be a lie as a factor.
            if KEEP_RESIDUAL && let &[value] = x.as_slice() && (value as u64).is_prime() {
                factors.push((value, 1));
                x[0] = 1;
            }
        }
    }

    (factors, x)
}

// TODO(PERFORMANCE): Make `start` a const parameter
fn trial_division<
    const END: u64,
    const S: usize,
>(
    x: &mut SmallVec<[usize; S]>,
    start: usize,
    factors: &mut Vec<(usize, u32)>,
) {
    // The words are stored little endian, so the most significant word is the last one.
    let get_x_bits = |y: &[usize]| {
        let most_significant = *y.last().expect("the value is nonzero, so it has a word");
        (y.len() as u32 - 1) * BITS_PER_WORD + most_significant.bit_width()
    };

    let mut divisor = start;
    let mut x_bits = get_x_bits(x);
    while {
        let not_one = unsafe { !is_one_non_zero(x) };
        let below_limit = divisor as u64 <= END;
        let below_sqrt = {
            let divisor_bits = divisor.bit_width();
            2 * divisor_bits <= x_bits
        };

        not_one && below_limit && below_sqrt
    } {
        let mut counter = 0;
        loop {
            let mut copy = x.clone();
            let remainder = unsafe {
                // SAFETY: divisor is nonzero and odd, copy is not zero
                div_assign_one_word(&mut copy, divisor)
            };
            if remainder == 0 {
                counter += 1;
                *x = copy;
            } else {
                break;
            }
        }

        if counter > 0 {
            factors.push((divisor, counter));
            x_bits = get_x_bits(x);
        }

        divisor += 2;
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use num_traits::One;
    use smallvec::smallvec;

    use crate::{NonZeroFactorizable, NonZeroFactorization, NonZeroSign, NonZeroUbig, Ubig};
    use crate::integer::factorization::size_large::factorize;

    #[test]
    fn test_factor() {
        assert_eq!(
            NonZeroUbig::<4>::one().factorize(),
            NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![], residual: Ubig::one() },
        );
        assert_eq!(
            NonZeroUbig::<4>::new(4).unwrap().factorize(),
            NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(2, 2)], residual: Ubig::one() },
        );
        // The crate wide constants don't attempt to split the cofactor, so it ends up in the
        // residual rather than being dropped.
        assert_eq!(
            unsafe { NonZeroUbig::<2>::from_inner_unchecked(smallvec![0, 351684787688]) }.factorize(),
            NonZeroFactorization {
                sign: NonZeroSign::Positive,
                factors: vec![
                    (2, 64 + 3),
                    (13, 1),
                ],
                residual: Ubig::new(3381584497),
            },
        );
        assert_eq!(
            factorize::<5, 0, true, 2>(&[0, 351684787688]),
            (vec![(2, 64 + 3), (13, 1), (3381584497, 1)], smallvec![1]),
        );
        let composite = NonZeroUbig::<8>::from_str("22429238517634168458101140012627848499653000000").unwrap();
        assert_eq!(
            factorize::<256, 100, true, 8>(&composite),
            (vec![(2, 6), (3, 18), (5, 6), (11, 12), (18446744073709551437, 1)], smallvec![1]),
        );
    }

    /// A cofactor that spans more than one word must survive in the residual.
    #[test]
    fn test_multi_word_residual() {
        // Two primes just below `2 ** 64`, so their product needs two words.
        let left = 2_u128.pow(64) - 59;
        let right = 2_u128.pow(64) - 83;
        let product = left * right;

        let value = NonZeroUbig::<2>::new_u128(product).unwrap();
        let NonZeroFactorization { sign, factors, residual } = value.factorize();
        assert_eq!(sign, NonZeroSign::Positive);
        assert_eq!(factors, vec![]);
        assert_eq!(residual, Ubig::<2>::new_u128(product));

        // Even with the residual explicitly kept as a factor, a multi word cofactor can't be one,
        // so it stays in the residual.
        let (factors, residual) = factorize::<256, 0, true, 2>(value.inner());
        assert_eq!(factors, vec![]);
        assert_eq!(residual.as_slice(), value.inner().as_slice());
    }
}
