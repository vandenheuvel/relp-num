use std::fmt::Debug;
use std::hash::Hash;

use index_utils::merge_sparse_indices;
use num_traits::One;

use crate::non_zero::NonZero;
use crate::NonZeroSign;
use crate::rational::Rational;
use crate::sign::Signed;
use crate::traits::factorization::{NonZeroFactorizable, NonZeroFactorization};


impl<R, Factor> NonZeroFactorizable for R
where
    Self: One,
    R: Rational<
        Sign: Signed,
        Numerator: NonZeroFactorizable<Factor=Factor, Power=u32>,
        Denominator: NonZeroFactorizable<Factor=Factor, Power=u32>,
    > + NonZero,
    Factor: Ord + NonZero + Hash + Clone + Debug,
{
    type Factor = Factor;
    type Power = i32;

    fn factorize(&self) -> NonZeroFactorization<Self::Factor, Self::Power> {
        debug_assert!(self.is_not_zero());

        let all_powers_small = |factors: &[(Factor, u32)]| {
            factors.iter().all(|&(_, p)| p <= i32::MAX as u32)
        };

        let NonZeroFactorization { factors: n_factors, sign: n_sign } = self.numerator.factorize();
        debug_assert!(all_powers_small(&n_factors));
        let NonZeroFactorization { factors: d_factors, sign: d_sign } = self.denominator.factorize();
        debug_assert!(all_powers_small(&d_factors));

        let factors = merge_sparse_indices(
            n_factors.into_iter(), d_factors.into_iter(),
            |left, right| left as i32 - right as i32,
            |x| x as i32, |x| -(x as i32),
            NonZero::is_not_zero,
        );

        NonZeroFactorization { sign: NonZeroSign::from(self.sign) * n_sign * d_sign, factors }
    }
}

#[cfg(test)]
mod test {
    use num_traits::{One, Zero};

    use crate::{NonZeroRationalBig, RationalBig};
    // use crate::rational::Ratio;
    use crate::traits::factorization::{NonZeroFactorizable, NonZeroFactorization};

    // #[test]
    // fn test_factorize() {
    //     let ratio: Ratio<_, u64, u64> = Ratio { sign: NonZeroSign::Positive, numerator: 1, denominator: 2 };
    //     let expected = NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(2, -1)] };
    //     assert_eq!(ratio.factorize(), expected);
    //
    //     let ratio: Ratio<_, u64, u64> = Ratio { sign: NonZeroSign::Positive, numerator: 161, denominator: 3 };
    //     let expected = NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(3, -1), (7, 1), (23, 1)] };
    //     assert_eq!(ratio.factorize(), expected);
    //
    //     let ratio: Ratio<_, u64, u64> = Ratio { sign: NonZeroSign::Positive, numerator: 2, denominator: 1 };
    //     let expected = NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![(2, 1)] };
    //     assert_eq!(ratio.factorize(), expected);
    //
    //     let ratio: Ratio<_, u64, u64> = Ratio { sign: NonZeroSign::Negative, numerator: 1, denominator: 1 };
    //     let expected = NonZeroFactorization { sign: NonZeroSign::Negative, factors: vec![] };
    //     assert_eq!(ratio.factorize(), expected);
    //
    //     let ratio = NonZeroRationalBig::one();
    //     let expected = NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![] };
    //     assert_eq!(ratio.factorize(), expected);
    //     let ratio = RationalBig::one();
    //     let expected = NonZeroFactorization { sign: NonZeroSign::Positive, factors: vec![] };
    //     assert_eq!(ratio.factorize(), expected);
    // }

    #[test]
    #[should_panic]
    fn test_factorize_zero() {
        RationalBig::zero().factorize();
    }
}
