use crate::{NonZeroFactorizable, NonZeroFactorization, NonZeroSign, NonZeroSigned, NonZero};
use crate::integer::factorization::prime::primes::SMALL_ODD_PRIMES_16;
use std::intrinsics::assume;

impl NonZeroFactorizable for i16 {
    type Factor = u16;
    type Power = u8;

    fn factorize(&self) -> NonZeroFactorization<Self::Factor, Self::Power> {
        debug_assert!(self.is_not_zero());

        let sign = NonZeroSigned::signum(self);
        let NonZeroFactorization {
            factors, ..
        } = self.unsigned_abs().factorize();
        NonZeroFactorization { sign, factors }
    }
}

impl NonZeroFactorizable for u16 {
    type Factor = u16;
    type Power = u8;

    fn factorize(&self) -> NonZeroFactorization<Self::Factor, Self::Power> {
        debug_assert!(self.is_not_zero());

        let mut x = *self;
        // 2 * 3 * 5 * 7 * 11 * 13 * 17 > 2 ** 16, so six values are enough
        let mut factors = Vec::with_capacity(6);

        let two_powers = x.trailing_zeros();
        if two_powers > 0 {
            x >>= two_powers;
            factors.push((2, two_powers as u8));
        }

        for divisor in SMALL_ODD_PRIMES_16 {
            unsafe { assume(divisor != 0); }

            let mut count = 0;
            while x % divisor == 0 {
                x /= divisor;
                count += 1;
            }

            if count > 0 {
                factors.push((divisor, count));
            }

            if x == 1 {
                break;
            }
        }

        if x != 1 {
            factors.push((x, 1));
        }

        NonZeroFactorization { sign: NonZeroSign::Positive, factors }
    }
}
