use std::num::NonZeroU64;
use std::str::FromStr;

use num_traits::One;

use crate::{NonZeroUbig, Ubig};
use crate::integer::factorization::prime::primes::SMALL_ODD_PRIMES_16;
use crate::non_zero::NonZeroSign;
use crate::traits::factorization::{NonZeroFactorizable, NonZeroFactorization};

macro_rules! shared {
    ($mod_name:ident, $ity:ty, $uty:ty) => {
        mod $mod_name {
            use super::*;

            #[test]
            fn test_factorize_one() {
                assert_eq!((1 as $uty).factorize(), NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![], residual: 1});
                assert_eq!((-1 as $ity).factorize(), NonZeroFactorization { sign: NonZeroSign::Negative, factors: vec![], residual: 1});
                assert!((1 as $uty).factorize().is_complete());
            }

            #[test]
            fn test_two_powers() {
                assert_eq!((2 as $uty).factorize().factors, vec![(2, 1)]);
                assert_eq!((4 as $uty).factorize().factors, vec![(2, 2)]);
                assert_eq!((-2 as $ity).factorize(), NonZeroFactorization { sign: NonZeroSign::Negative, factors: vec![(2, 1)], residual: 1});
            }

            #[test]
            fn test_three_powers() {
                assert_eq!((3 as $uty).factorize().factors, vec![(3, 1)]);
                assert_eq!((9 as $uty).factorize().factors, vec![(3, 2)]);
                assert_eq!((27 as $uty).factorize().factors, vec![(3, 3)]);
                assert_eq!((81 as $uty).factorize().factors, vec![(3, 4)]);
                assert_eq!((-3 as $ity).factorize(), NonZeroFactorization { sign: NonZeroSign::Negative, factors: vec![(3, 1)], residual: 1});
            }

            #[test]
            fn test_six_powers() {
                assert_eq!((6 as $uty).factorize().factors, vec![(2, 1), (3, 1)]);
                assert_eq!((36 as $uty).factorize().factors, vec![(2, 2), (3, 2)]);
                assert_eq!((216 as $uty).factorize().factors, vec![(2, 3), (3, 3)]);
                assert_eq!((-6 as $ity).factorize(), NonZeroFactorization { sign: NonZeroSign::Negative, factors: vec![(2, 1), (3, 1)], residual: 1});
            }

            #[test]
            fn test_fifteen_powers() {
                assert_eq!((15 as $uty).factorize().factors, vec![(3, 1), (5, 1)]);
                assert_eq!((225 as $uty).factorize().factors, vec![(3, 2), (5, 2)]);
            }

            #[test]
            fn test_prime() {
                for prime in SMALL_ODD_PRIMES_16 {
                    assert_eq!((prime as $uty).factorize().factors, vec![(prime as $uty, 1)]);
                    assert!((prime as $uty).factorize().is_complete());
                }
            }
        }
    }
}

shared!(size_8, i8, u8);
shared!(size_16, i16, u16);
shared!(size_32, i32, u32);
shared!(size_64, i64, u64);


#[test]
fn test_factorize_two_powers() {
    assert_eq!(
        2_u32.pow(16).factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(2, 16)], residual: 1 },
    );
    assert_eq!(
        2_u64.pow(16).factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(2, 16)], residual: 1 },
    );
}

#[test]
fn test_factorize_three_powers() {
    assert_eq!(
        3_u32.pow(16).factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(3, 16)], residual: 1 },
    );
    assert_eq!(
        3_u64.pow(16).factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(3, 16)], residual: 1 },
    );
}

#[test]
fn test_factorize_mixed() {
    assert_eq!(
        6_u32.pow(12).factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(2, 12), (3, 12)], residual: 1 },
    );
    assert_eq!(
        6_u64.pow(16).factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(2, 16), (3, 16)], residual: 1 },
    );
}

#[test]
fn test_factorize_large_prime() {
    // The 32-bit routine trial divides all the way up to the square root, so it is always complete.
    let prime = 2_u32.pow(31) - 1;
    assert_eq!(
        prime.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(prime, 1)], residual: 1 },
    );
    let prime = 2_u32.pow(18) - 5;
    assert_eq!(
        prime.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(prime, 1)], residual: 1 },
    );
    let prime = 2_u32.pow(20) - 3;
    assert_eq!(
        prime.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(prime, 1)], residual: 1 },
    );

    // The 64-bit routine is tuned to give up after the small primes, so a large prime is reported
    // as a residual: nothing was decomposed, but the value is still described completely.
    let prime = 2_u64.pow(36) - 5;
    assert_eq!(
        prime.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![], residual: prime },
    );
    assert!(!prime.factorize().is_complete());
    let prime = 2_u64.pow(60) - 93;
    assert_eq!(
        prime.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![], residual: prime },
    );
    let prime = 2_u64.pow(53) - 111;
    assert_eq!(
        prime.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![], residual: prime },
    );
}

#[test]
fn test_factorize_large_composite() {
    let composite = 2_u32.pow(31) - 3;
    assert_eq!(
        composite.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(5, 1), (19, 1), (22605091, 1)], residual: 1 },
    );
    let composite = 2_u32.pow(18) - 7;
    assert_eq!(
        composite.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(3, 1), (59, 1), (1481, 1)], residual: 1 },
    );
    let composite = 2_u32.pow(20) - 7;
    assert_eq!(
        composite.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(3, 1), (193, 1), (1811, 1)], residual: 1 },
    );

    // [(3, 1), (22906492243, 1)]
    let composite = 2_u64.pow(36) - 7;
    assert_eq!(
        composite.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(3, 1)], residual: 22906492243 },
    );
    // [(3457, 1), (6203, 1), (53764867411, 1)], none of which are small primes
    let composite = 2_u64.pow(60) - 95;
    assert_eq!(
        composite.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![], residual: composite },
    );
    // [(3, 2), (43, 1), (642739, 1), (36211303, 1)]
    let composite = 2_u64.pow(53) - 113;
    assert_eq!(
        composite.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(3, 2), (43, 1)], residual: 23274416678917 },
    );
    let composite = NonZeroU64::new(2_u64.pow(53) - 113).unwrap();
    assert_eq!(
        composite.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(3, 2), (43, 1)], residual: 23274416678917 },
    );
}

/// Multiply a factorization back together: `residual * product(factor ^ power)`.
fn reconstruct(factorization: &NonZeroFactorization<u64, u32, u64>) -> u64 {
    let mut total = factorization.residual;
    for &(factor, power) in &factorization.factors {
        assert!(factor > 1, "a factor is larger than one");
        for _ in 0..power {
            total = total.checked_mul(factor).expect("the product is at most the original value");
        }
    }

    total
}

/// The factorization always describes the entire value, however it was tuned.
#[test]
fn test_reconstruction_unsigned() {
    let large_prime = 2_u64.pow(36) - 5;
    let semiprime = (2_u64.pow(31) - 1) * (2_u64.pow(31) - 19);
    let smooth = 2_u64 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29;
    let values = [
        1,
        2,
        2_u64.pow(40),
        smooth,
        large_prime,
        semiprime,
        1_000_003 * 1_000_033,
        u64::MAX,
    ];

    for value in values {
        let factorization = value.factorize();
        assert_eq!(factorization.sign, NonZeroSign::Positive);
        assert_eq!(reconstruct(&factorization), value, "reconstructing {value}");
        assert_eq!(factorization.is_complete(), factorization.residual == 1);
    }

    // The values that the small primes decompose entirely
    assert!(1_u64.factorize().is_complete());
    assert!(2_u64.pow(40).factorize().is_complete());
    assert!(smooth.factorize().is_complete());
    // The values that they don't
    assert!(!large_prime.factorize().is_complete());
    assert_eq!(large_prime.factorize().residual, large_prime);
    assert!(!semiprime.factorize().is_complete());
    assert_eq!(semiprime.factorize().residual, semiprime);
}

/// The sign is separate from the factors and the residual, which are both positive.
#[test]
fn test_reconstruction_signed() {
    let value = -((2_i64.pow(36) - 5) * 6);
    let factorization = value.factorize();

    assert_eq!(factorization.sign, NonZeroSign::Negative);
    assert_eq!(factorization.factors, vec![(2, 1), (3, 1)]);
    assert_eq!(factorization.residual, 2_u64.pow(36) - 5);

    let magnitude = reconstruct(&NonZeroFactorization {
        sign: NonZeroSign::Positive,
        factors: factorization.factors.clone(),
        residual: factorization.residual,
    });
    assert_eq!(magnitude, value.unsigned_abs());
}

/// A cofactor that doesn't fit in a single word ends up in the residual, rather than being dropped.
#[test]
fn test_reconstruction_big() {
    // Two primes just below `2 ** 61`; their product needs two words.
    let semiprime = 2_305_843_009_213_693_951_u128 * 2_305_843_009_213_693_921;
    let value = NonZeroUbig::<4>::new_u128(semiprime * 4).unwrap();

    let NonZeroFactorization { sign, factors, residual } = value.factorize();
    assert_eq!(sign, NonZeroSign::Positive);
    assert_eq!(factors, vec![(2, 2)]);
    assert_eq!(residual, Ubig::<4>::new_u128(semiprime));

    let mut total = residual;
    for (factor, power) in factors {
        for _ in 0..power {
            total = total * Ubig::<4>::new(factor);
        }
    }
    assert_eq!(total, Ubig::<4>::new_u128(semiprime * 4));

    // A value that is decomposed entirely
    let smooth = NonZeroUbig::<4>::from_str("1298074214633706907132624082305024").unwrap(); // 2^110
    let factorization = smooth.factorize();
    assert_eq!(factorization.factors, vec![(2, 110)]);
    assert!(factorization.is_complete());
    assert!(NonZeroUbig::<4>::one().factorize().is_complete());
}
