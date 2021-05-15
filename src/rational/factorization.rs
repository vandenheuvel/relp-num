use std::convert::identity;
use std::ops::{Neg, Sub};

use crate::non_zero::NonZero;
use crate::rational::Ratio;
use crate::rational::utilities::merge_sparse_indices;
use crate::traits::factorization::{NonZeroFactorizable, NonZeroFactorization};

impl<Numerator, Denominator, Factor, Power> NonZeroFactorizable for Ratio<Numerator, Denominator>
where
    Numerator: NonZeroFactorizable<Factor=Factor, Power=Power>,
    Denominator: NonZeroFactorizable<Factor=Factor, Power=Power>,
    Factor: Ord + NonZero + Clone,
    Power: Neg<Output=Power> + Sub<Output=Power> + Eq + NonZero + Copy + Clone,
    Ratio<Numerator, Denominator>: NonZero,
{
    type Factor = Factor;
    type Power = Power;

    fn factorize(&self) -> NonZeroFactorization<Self::Factor, Self::Power> {
        debug_assert!(self.numerator.is_not_zero() && self.denominator.is_not_zero());

        let NonZeroFactorization { factors: n_factors, .. } = self.numerator.factorize();
        let NonZeroFactorization { factors: d_factors, .. } = self.denominator.factorize();

        let factors = merge_sparse_indices(
            n_factors.into_iter(), d_factors.into_iter(),
            Sub::sub, identity, |x| -x,
        );

        NonZeroFactorization { sign: self.sign.into(), factors }
    }
}

#[cfg(test)]
mod test {
    use crate::non_zero::NonZeroSign;
    use crate::rational::Ratio;
    use crate::sign::Sign;
    use crate::traits::factorization::{NonZeroFactorizable, NonZeroFactorization};

    #[test]
    fn test_factorize() {
        let ratio: Ratio<u64, u64> = Ratio { sign: Sign::Positive, numerator: 1, denominator: 2 };
        let expected = NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(2, -1)] };
        assert_eq!(ratio.factorize(), expected);

        let ratio: Ratio<u64, u64> = Ratio { sign: Sign::Positive, numerator: 161, denominator: 3 };
        let expected = NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(3, -1), (7, 1), (23, 1)] };
        assert_eq!(ratio.factorize(), expected);

        let ratio: Ratio<u64, u64> = Ratio { sign: Sign::Positive, numerator: 2, denominator: 1 };
        let expected = NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(2, 1)] };
        assert_eq!(ratio.factorize(), expected);

        let ratio: Ratio<u64, u64> = Ratio { sign: Sign::Negative, numerator: 1, denominator: 1 };
        let expected = NonZeroFactorization { sign: NonZeroSign::Negative, factors: vec![] };
        assert_eq!(ratio.factorize(), expected);
    }
}
