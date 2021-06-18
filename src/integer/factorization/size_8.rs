use crate::{NonZero, NonZeroFactorizable, NonZeroFactorization, NonZeroSign, NonZeroSigned};
use crate::integer::factorization::prime::primes::SMALL_ODD_PRIMES_8;

impl NonZeroFactorizable for i8 {
    type Factor = u8;
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

impl NonZeroFactorizable for u8 {
    type Factor = u8;
    type Power = u8;

    fn factorize(&self) -> NonZeroFactorization<Self::Factor, Self::Power> {
        debug_assert!(self.is_not_zero());

        let mut x = *self;
        // 2 * 3 * 5 * 7 * 11 > 2 ** 8, so four values are enough
        let mut factors = Vec::with_capacity(4);

        let two_powers = x.trailing_zeros();
        if two_powers > 0 {
            x >>= two_powers;
            factors.push((2, two_powers as u8));
        }

        for divisor in SMALL_ODD_PRIMES_8 {
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
