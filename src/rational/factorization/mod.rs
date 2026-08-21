use std::fmt::Debug;
use std::hash::Hash;

use index_utils::merge_sparse_indices;
use num_traits::One;

use crate::non_zero::NonZero;
use crate::NonZeroSign;
use crate::rational::Ratio;
use crate::Sign;
use crate::traits::factorization::{NonZeroFactorizable, NonZeroFactorization};

macro_rules! impl_with_sign {
    ($sign:ty) => {
        impl<Numerator, Denominator, Factor> NonZeroFactorizable for Ratio<$sign, Numerator, Denominator>
        where
            Self: One,
            Numerator: NonZeroFactorizable<Factor=Factor, Power=u32>,
            Denominator: NonZeroFactorizable<Factor=Factor, Power=u32>,
            Factor: Ord + NonZero + Hash + Clone + Debug,
        {
            type Factor = Factor;
            type Power = i32;
            /// The `(numerator residual, denominator residual)` pair.
            ///
            /// Both sides of the fraction leave a part that was not decomposed, and these two can't
            /// be merged into a single value: their quotient is generally not an integer, and in
            /// the big case the two sides don't even have the same type. The pair is one, and the
            /// factorization complete, exactly when both halves are one.
            type Residual = (Numerator::Residual, Denominator::Residual);

            fn factorize(&self) -> NonZeroFactorization<Self::Factor, Self::Power, Self::Residual> {
                debug_assert!(self.is_not_zero());

                let all_powers_small = |factors: &[(Factor, u32)]| {
                    factors.iter().all(|&(_, p)| p <= i32::MAX as u32)
                };

                let NonZeroFactorization {
                    factors: n_factors, sign: n_sign, residual: n_residual,
                } = self.numerator.factorize();
                debug_assert!(all_powers_small(&n_factors));
                let NonZeroFactorization {
                    factors: d_factors, sign: d_sign, residual: d_residual,
                } = self.denominator.factorize();
                debug_assert!(all_powers_small(&d_factors));

                let factors = merge_sparse_indices(
                    n_factors.into_iter(), d_factors.into_iter(),
                    |left, right| left as i32 - right as i32,
                    |x| x as i32, |x| -(x as i32),
                    NonZero::is_not_zero,
                );

                NonZeroFactorization {
                    sign: NonZeroSign::from(self.sign) * n_sign * d_sign,
                    factors,
                    residual: (n_residual, d_residual),
                }
            }
        }
    }
}
impl_with_sign!(Sign);
impl_with_sign!(NonZeroSign);

#[cfg(test)]
mod test {
    use num_traits::{One, Zero};

    use crate::{NonZeroRationalBig, RationalBig, Ubig};
    use crate::non_zero::NonZeroSign;
    use crate::rational::Ratio;
    use crate::traits::factorization::{NonZeroFactorizable, NonZeroFactorization};

    #[test]
    fn test_factorize() {
        let ratio: Ratio<_, u64, u64> = Ratio { sign: NonZeroSign::Positive, numerator: 1, denominator: 2 };
        let expected = NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(2, -1)], residual: (1, 1) };
        assert_eq!(ratio.factorize(), expected);
        assert!(ratio.factorize().is_complete());

        let ratio: Ratio<_, u64, u64> = Ratio { sign: NonZeroSign::Positive, numerator: 161, denominator: 3 };
        let expected = NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(3, -1), (7, 1), (23, 1)], residual: (1, 1) };
        assert_eq!(ratio.factorize(), expected);

        let ratio: Ratio<_, u64, u64> = Ratio { sign: NonZeroSign::Positive, numerator: 2, denominator: 1 };
        let expected = NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(2, 1)], residual: (1, 1) };
        assert_eq!(ratio.factorize(), expected);

        let ratio: Ratio<_, u64, u64> = Ratio { sign: NonZeroSign::Negative, numerator: 1, denominator: 1 };
        let expected = NonZeroFactorization { sign: NonZeroSign::Negative, factors: vec![], residual: (1, 1) };
        assert_eq!(ratio.factorize(), expected);

        let ratio = NonZeroRationalBig::one();
        let expected = NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![], residual: (Ubig::one(), Ubig::one()) };
        assert_eq!(ratio.factorize(), expected);
        let ratio = RationalBig::one();
        let expected = NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![], residual: (Ubig::one(), Ubig::one()) };
        assert_eq!(ratio.factorize(), expected);
    }

    /// A cofactor that the routines gave up on is reported, not dropped.
    ///
    /// Before the residual existed, this factorization claimed that the value was `1 / 7`.
    #[test]
    fn test_factorize_incomplete() {
        let prime = 1_000_003_u64;
        let ratio: Ratio<_, u64, u64> = Ratio { sign: NonZeroSign::Positive, numerator: prime, denominator: 7 };

        let factorization = ratio.factorize();
        assert_eq!(factorization.factors, vec![(7, -1)]);
        assert_eq!(factorization.residual, (prime, 1));
        assert!(!factorization.is_complete());

        // The value is described completely: sign * (numerator residual / denominator residual) *
        // product(factor ^ power).
        let (numerator_residual, denominator_residual) = factorization.residual;
        let mut numerator = numerator_residual;
        let mut denominator = denominator_residual;
        for (factor, power) in factorization.factors {
            for _ in 0..power.abs() {
                if power > 0 {
                    numerator *= factor;
                } else {
                    denominator *= factor;
                }
            }
        }
        assert_eq!(numerator, prime);
        assert_eq!(denominator, 7);
    }

    #[test]
    #[should_panic]
    fn test_factorize_zero() {
        RationalBig::zero().factorize();
    }
}
