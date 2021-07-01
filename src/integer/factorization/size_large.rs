use std::num::NonZeroU64;

use smallvec::SmallVec;

use crate::{NonZeroFactorizable, NonZeroFactorization, NonZeroSign, Ubig};
use crate::integer::big::{BITS_PER_WORD, NonZeroUbig};
use crate::integer::big::ops::div::div_assign_one_word;
use crate::integer::big::ops::non_zero::{is_one_non_zero, shr};
use crate::integer::big::ops::normalize::trailing_zeros;
use crate::integer::factorization::{KEEP_RESIDUAL, NR_SMALL_PRIMES, size_64, start, TRIAL_DIVISION_LIMIT, TRIAL_DIVISION_LIMIT_USIZE};
use crate::integer::factorization::prime::primes::SMALL_ODD_PRIMES;
use crate::non_zero::NonZero;

macro_rules! define {
    ($ty:ident) => {
        impl<const S: usize> NonZeroFactorizable for $ty<S> {
            type Factor = usize;
            type Power = u32;

            fn factorize(&self) -> NonZeroFactorization<Self::Factor, Self::Power> {
                assert!(self.is_not_zero(), "attempt to factorize zero");

                let factors = factorize::<
                    NR_SMALL_PRIMES, TRIAL_DIVISION_LIMIT, TRIAL_DIVISION_LIMIT_USIZE, KEEP_RESIDUAL, S
                >(self.inner());
                NonZeroFactorization { sign: NonZeroSign::Positive, factors }
            }
        }
    }
}

define!(Ubig);
define!(NonZeroUbig);

fn factorize<
    const NR_SMALL_PRIMES: usize,
    const TRIAL_DIVISION_LIMIT: u64,
    const TRIAL_DIVISION_LIMIT_USIZE: usize,
    const KEEP_RESIDUAL: bool,
    const S: usize,
>(values: &[usize]) -> Vec<(usize, u32)> {
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
        let small = size_64::factorize::<
            NR_SMALL_PRIMES, TRIAL_DIVISION_LIMIT, 0, KEEP_RESIDUAL,
        >(as_small);
        for (factor, power) in small {
            factors.push((factor as usize, power));
        }
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
                trial_division::<TRIAL_DIVISION_LIMIT_USIZE, S>(&mut x, start, &mut factors);

                if unsafe { is_one_non_zero(&x) } {
                    break 'odd;
                }
            }

            if KEEP_RESIDUAL {
                if let &[value] = x.as_slice() {
                    factors.push((value, 1));
                }
            }
        }
    }

    factors
}

// TODO(PERFORMANCE): Make `start` a const parameter
fn trial_division<
    const END: usize,
    const S: usize,
>(
    x: &mut SmallVec<[usize; S]>,
    start: usize,
    factors: &mut Vec<(usize, u32)>,
) {
    let get_x_bits = |y: &[usize]| y.len() as u32 * BITS_PER_WORD - y[0].leading_zeros();

    let mut divisor = start;
    let mut x_bits = get_x_bits(x);
    while {
        let not_one = unsafe { !is_one_non_zero(x) };
        let below_limit = divisor <= END;
        let below_sqrt = {
            let divisor_bits = BITS_PER_WORD - divisor.leading_zeros();
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

    use crate::{NonZeroFactorizable, NonZeroFactorization, NonZeroSign, NonZeroUbig};
    use crate::integer::factorization::size_large::factorize;

    #[test]
    fn test_factor() {
        assert_eq!(NonZeroUbig::<4>::one().factorize(), NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![]});
        assert_eq!(
            NonZeroUbig::<4>::new(4).unwrap().factorize(),
            NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(2, 2)] },
        );
        assert_eq!(
            unsafe { NonZeroUbig::<2>::from_inner_unchecked(smallvec![0, 351684787688]) }.factorize(),
            NonZeroFactorization {
                sign: NonZeroSign::Positive,
                factors: vec![
                    (2, 64 + 3),
                    (13, 1),
                    // (3381584497, 1),
                ],
            },
        );
        assert_eq!(
            factorize::<5, 0, 0, true, 2>(&[0, 351684787688]),
            vec![(2, 64 + 3), (13, 1), (3381584497, 1)],
        );
        let composite = NonZeroUbig::<8>::from_str("22429238517634168458101140012627848499653000000").unwrap();
        assert_eq!(
            factorize::<256, 100, 100, true, 8>(&composite),
            vec![(2, 6), (3, 18), (5, 6), (11, 12), (18446744073709551437, 1)],
        );
    }
}
