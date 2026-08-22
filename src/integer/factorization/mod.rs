//! # Factorizing integers
use std::num::{NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8};
use std::num::{NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8};

use crate::{NonZeroFactorizable, NonZeroFactorization, NonZeroSign, NonZeroSigned};
use crate::integer::factorization::prime::primes::SMALL_ODD_PRIMES;

pub mod prime;
mod size_8;
mod size_16;
mod size_32;
mod size_64;
mod size_large;

macro_rules! forwards {
    ($nzity:ty, $nzuty:ty, $ity:ty, $uty:ty, $method_name:path) => {
        impl NonZeroFactorizable for $ity {
            type Factor = $uty;
            type Power = u32;
            /// The value is factorized through its absolute value, so the residual is positive and
            /// the sign is kept separately.
            type Residual = $uty;

            fn factorize(&self) -> NonZeroFactorization<Self::Factor, Self::Power, Self::Residual> {
                let as_non_zero = <$nzity>::new(*self)
                    .expect("attempt to factorize zero");
                as_non_zero.factorize()
            }
        }

        impl NonZeroFactorizable for $nzity {
            type Factor = $uty;
            type Power = u32;
            /// The value is factorized through its absolute value, so the residual is positive and
            /// the sign is kept separately.
            type Residual = $uty;

            fn factorize(&self) -> NonZeroFactorization<Self::Factor, Self::Power, Self::Residual> {
                let sign = self.non_zero_signum();
                let (factors, residual) = $method_name(self.unsigned_abs());

                NonZeroFactorization { sign, factors, residual }
            }
        }

        impl NonZeroFactorizable for $uty {
            type Factor = $uty;
            type Power = u32;
            type Residual = $uty;

            fn factorize(&self) -> NonZeroFactorization<Self::Factor, Self::Power, Self::Residual> {
                let as_non_zero = <$nzuty>::new(*self)
                    .expect("attempt to factorize zero");
                let (factors, residual) = $method_name(as_non_zero);

                NonZeroFactorization { sign: NonZeroSign::Positive, factors, residual }
            }
        }

        impl NonZeroFactorizable for $nzuty {
            type Factor = $uty;
            type Power = u32;
            type Residual = $uty;

            fn factorize(&self) -> NonZeroFactorization<Self::Factor, Self::Power, Self::Residual> {
                let (factors, residual) = $method_name(*self);

                NonZeroFactorization { sign: NonZeroSign::Positive, factors, residual }
            }
        }
    }
}

forwards!(NonZeroI8, NonZeroU8, i8, u8, size_8::factorize);
forwards!(NonZeroI16, NonZeroU16, i16, u16, size_16::factorize);
forwards!(NonZeroI32, NonZeroU32, i32, u32, size_32::factorize);

// TODO(PERFORMANCE): Tune these values
const NR_SMALL_PRIMES: usize = 256;
const TRIAL_DIVISION_LIMIT: u64 = 0;
const RHO_BASE_LIMIT: u64 = 0;
const KEEP_RESIDUAL: bool = false;

fn factorize64(value: NonZeroU64) -> (Vec<(u64, u32)>, u64) {
    size_64::factorize::<
        NR_SMALL_PRIMES,
        TRIAL_DIVISION_LIMIT,
        RHO_BASE_LIMIT,
        KEEP_RESIDUAL,
    >(value)
}

forwards!(NonZeroI64, NonZeroU64, i64, u64, factorize64);

pub const fn start(nr_small_primes: usize) -> u16 {
    if nr_small_primes < SMALL_ODD_PRIMES.len() {
        // Get next prime
        SMALL_ODD_PRIMES[nr_small_primes]
    } else {
        // Largest prime + 2
        SMALL_ODD_PRIMES[nr_small_primes - 1] + 2
    }
}

#[cfg(test)]
mod test;
