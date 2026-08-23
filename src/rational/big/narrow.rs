//! # Storing an arbitrary precision rational in a fixed width one
//!
//! Both halves go through the [`ToPrimitive`] implementation that [`Ubig`](crate::Ubig) and
//! [`NonZeroUbig`](crate::NonZeroUbig) already carry. It range checks rather than truncates, and it
//! is the conversion the rest of the crate goes through, so there is no second answer to keep in
//! step with this one.
use num_traits::ToPrimitive;

use crate::rational::Ratio;
use crate::rational::big::Big;
use crate::traits::Narrow;
use crate::{
    Rational8, Rational16, Rational32, Rational64, Rational128, RationalUsize,
};

macro_rules! narrow_to {
    ($($narrow:ty => $to:ident),+ $(,)?) => {$(
        impl<const S: usize> Narrow<$narrow> for Big<S> {
            fn narrow(&self) -> Option<$narrow> {
                Some(Ratio {
                    sign: self.sign,
                    numerator: self.numerator.$to()?,
                    denominator: self.denominator.$to()?,
                })
            }
        }
    )+}
}

narrow_to!(
    Rational8 => to_u8,
    Rational16 => to_u16,
    Rational32 => to_u32,
    Rational64 => to_u64,
    Rational128 => to_u128,
    RationalUsize => to_usize,
);

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::{
        Narrow, Rational8, Rational64, Rational128, RationalBig, Sign, R32, R64, R8, RB,
    };

    #[test]
    fn narrowing_keeps_the_value_or_declines() {
        assert_eq!(RB!(3, 4).narrow(), Some(R8!(3, 4)));
        assert_eq!(RB!(-3, 4).narrow(), Some(R8!(-3, 4)));
        assert_eq!(RB!(0).narrow(), Some(R8!(0)));

        // 300 does not fit in a `u8`, but it does in a `u16` and everything wider.
        assert_eq!(<RationalBig as Narrow<Rational8>>::narrow(&RB!(300)), None);
        assert_eq!(RB!(300).narrow(), Some(R32!(300)));

        // The numerator fits and the denominator does not.
        assert_eq!(<RationalBig as Narrow<Rational8>>::narrow(&RB!(1, 300)), None);
    }

    #[test]
    fn what_does_not_fit_in_any_of_them() {
        let value = RationalBig::from_str("340282366920938463463374607431768211456").unwrap();
        assert_eq!(<RationalBig as Narrow<Rational64>>::narrow(&value), None);
        assert_eq!(<RationalBig as Narrow<Rational128>>::narrow(&value), None);
    }

    /// A value that needs more than one word, and still fits.
    ///
    /// The conversion is word based, so the top of the target is where being off by a word would
    /// show up.
    #[test]
    fn a_multi_word_value_that_fits() {
        // `u128::MAX`, which is two words wide on a 64 bit target.
        let value = RationalBig::from_str("340282366920938463463374607431768211455").unwrap();
        let narrow: Rational128 = value.narrow().unwrap();
        assert_eq!(narrow, Rational128::new_signed(Sign::Positive, u128::MAX, 1).unwrap());
        assert_eq!(RationalBig::from(narrow), value);
    }

    /// What comes back has to widen to what went in.
    #[test]
    fn narrowing_and_widening_are_inverse() {
        for value in [RB!(0), RB!(1), RB!(-1), RB!(7, 9), RB!(-1234, 5678)] {
            let narrow: Rational64 = value.narrow().unwrap();
            assert_eq!(RationalBig::from(narrow), value);
        }
        assert_eq!(R64!(-1234, 5678), R64!(-617, 2839));
    }
}
