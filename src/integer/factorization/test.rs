use std::num::NonZeroU64;

use crate::integer::factorization::prime::primes::SMALL_ODD_PRIMES_16;
use crate::non_zero::NonZeroSign;
use crate::traits::factorization::{NonZeroFactorizable, NonZeroFactorization};

macro_rules! shared {
    ($mod_name:ident, $ity:ty, $uty:ty) => {
        mod $mod_name {
            use super::*;

            #[test]
            fn test_factorize_one() {
                assert_eq!((1 as $uty).factorize(), NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![]});
                assert_eq!((-1 as $ity).factorize(), NonZeroFactorization { sign: NonZeroSign::Negative, factors: vec![]});
            }

            #[test]
            fn test_two_powers() {
                assert_eq!((2 as $uty).factorize().factors, vec![(2, 1)]);
                assert_eq!((4 as $uty).factorize().factors, vec![(2, 2)]);
                assert_eq!((-2 as $ity).factorize(), NonZeroFactorization { sign: NonZeroSign::Negative, factors: vec![(2, 1)]});
            }

            #[test]
            fn test_three_powers() {
                assert_eq!((3 as $uty).factorize().factors, vec![(3, 1)]);
                assert_eq!((9 as $uty).factorize().factors, vec![(3, 2)]);
                assert_eq!((27 as $uty).factorize().factors, vec![(3, 3)]);
                assert_eq!((81 as $uty).factorize().factors, vec![(3, 4)]);
                assert_eq!((-3 as $ity).factorize(), NonZeroFactorization { sign: NonZeroSign::Negative, factors: vec![(3, 1)]});
            }

            #[test]
            fn test_six_powers() {
                assert_eq!((6 as $uty).factorize().factors, vec![(2, 1), (3, 1)]);
                assert_eq!((36 as $uty).factorize().factors, vec![(2, 2), (3, 2)]);
                assert_eq!((216 as $uty).factorize().factors, vec![(2, 3), (3, 3)]);
                assert_eq!((-6 as $ity).factorize(), NonZeroFactorization { sign: NonZeroSign::Negative, factors: vec![(2, 1), (3, 1)]});
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
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(2, 16)] },
    );
    assert_eq!(
        2_u64.pow(16).factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(2, 16)] },
    );
}

#[test]
fn test_factorize_three_powers() {
    assert_eq!(
        3_u32.pow(16).factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(3, 16)] },
    );
    assert_eq!(
        3_u64.pow(16).factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(3, 16)] },
    );
}

#[test]
fn test_factorize_mixed() {
    assert_eq!(
        6_u32.pow(12).factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(2, 12), (3, 12)] },
    );
    assert_eq!(
        6_u64.pow(16).factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(2, 16), (3, 16)] },
    );
}

#[test]
fn test_factorize_large_prime() {
    let prime = 2_u32.pow(31) - 1;
    assert_eq!(
        prime.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(prime, 1)] },
    );
    let prime = 2_u32.pow(18) - 5;
    assert_eq!(
        prime.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(prime, 1)] },
    );
    let prime = 2_u32.pow(20) - 3;
    assert_eq!(
        prime.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(prime, 1)] },
    );
    let prime = 2_u64.pow(36) - 5;
    assert_eq!(
        prime.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![] },
    );
    let prime = 2_u64.pow(60) - 93;
    assert_eq!(
        prime.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![] },
    );
    let prime = 2_u64.pow(53) - 111;
    assert_eq!(
        prime.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![] },
    );
}

#[test]
fn test_factorize_large_composite() {
    let composite = 2_u32.pow(31) - 3;
    assert_eq!(
        composite.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(5, 1), (19, 1), (22605091, 1)] },
    );
    let composite = 2_u32.pow(18) - 7;
    assert_eq!(
        composite.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(3, 1), (59, 1), (1481, 1)] },
    );
    let composite = 2_u32.pow(20) - 7;
    assert_eq!(
        composite.factorize(),
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(3, 1), (193, 1), (1811, 1)] },
    );
    let composite = 2_u64.pow(36) - 7;
    assert_eq!(
        composite.factorize(),
        // [(3, 1), (22906492243, 1)]
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(3, 1)] },
    );
    let composite = 2_u64.pow(60) - 95;
    assert_eq!(
        composite.factorize(),
        // [(3457, 1), (6203, 1), (53764867411, 1)]
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![] },
    );
    let composite = 2_u64.pow(53) - 113;
    assert_eq!(
        composite.factorize(),
        // [(3, 2), (43, 1), (642739, 1), (36211303, 1)]
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(3, 2), (43, 1)] },
    );
    let composite = NonZeroU64::new(2_u64.pow(53) - 113).unwrap();
    assert_eq!(
        composite.factorize(),
        // [(3, 2), (43, 1), (642739, 1), (36211303, 1)]
        NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(3, 2), (43, 1)] },
    );
}
