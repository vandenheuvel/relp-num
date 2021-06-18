use crate::non_zero::NonZero;
use crate::rational::Ratio;
use crate::rational::utilities::merge_sparse_indices;
use crate::traits::factorization::{NonZeroFactorizable, NonZeroFactorization};
use std::fmt::Debug;
use num_traits::One;

impl<Numerator, Denominator, Factor> NonZeroFactorizable for Ratio<Numerator, Denominator>
where
    Ratio<Numerator, Denominator>: NonZero + One,
    Numerator: NonZeroFactorizable<Factor=Factor, Power=u8>,
    Denominator: NonZeroFactorizable<Factor=Factor, Power=u8>,
    Factor: Ord + NonZero + Clone + Debug,
{
    type Factor = Factor;
    type Power = i8;

    fn factorize(&self) -> NonZeroFactorization<Self::Factor, Self::Power> {
        debug_assert!(self.numerator.is_not_zero());
        let all_powers_small = |factors: &[(Factor, u8)]| {
            factors.iter().all(|&(_, p)| p <= i8::MAX as u8)
        };

        let NonZeroFactorization { factors: n_factors, .. } = self.numerator.factorize();
        debug_assert!(all_powers_small(&n_factors));
        let NonZeroFactorization { factors: d_factors, .. } = self.denominator.factorize();
        debug_assert!(all_powers_small(&d_factors));

        let factors = merge_sparse_indices(
            n_factors.into_iter(), d_factors.into_iter(),
            |left, right| left as i8 - right as i8,
            |x| x as i8, |x| -(x as i8),
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
