//! # Storing a fixed width rational in another one
//!
//! One implementation per pair, including the pair of a type with itself and the pairs that widen.
//!
//! Code that picks a width asks the same question of every candidate, and a gap in the table would
//! show up there as a candidate that cannot be asked about rather than one that does not fit.
use crate::rational::Ratio;
use crate::traits::Narrow;
use crate::{
    Rational8, Rational16, Rational32, Rational64, Rational128, RationalUsize,
};

macro_rules! narrow_small {
    ($source:ty; $($narrow:ty => $unsigned:ty),+ $(,)?) => {$(
        impl Narrow<$narrow> for $source {
            fn narrow(&self) -> Option<$narrow> {
                Some(Ratio {
                    sign: self.sign,
                    numerator: <$unsigned>::try_from(self.numerator).ok()?,
                    denominator: <$unsigned>::try_from(self.denominator).ok()?,
                })
            }
        }
    )+}
}

macro_rules! narrow_all {
    ($($source:ty),+ $(,)?) => {$(
        narrow_small!($source;
            Rational8 => u8,
            Rational16 => u16,
            Rational32 => u32,
            Rational64 => u64,
            Rational128 => u128,
            RationalUsize => usize,
        );
    )+}
}

narrow_all!(
    Rational8,
    Rational16,
    Rational32,
    Rational64,
    Rational128,
    RationalUsize,
);

#[cfg(test)]
mod test {
    use crate::{Narrow, Rational8, Rational16, Rational64, R8, R16, R64};

    #[test]
    fn narrowing_keeps_the_value_or_declines() {
        assert_eq!(R64!(3, 4).narrow(), Some(R8!(3, 4)));
        assert_eq!(R64!(-3, 4).narrow(), Some(R8!(-3, 4)));
        assert_eq!(<Rational64 as Narrow<Rational8>>::narrow(&R64!(300)), None);
        assert_eq!(R64!(300).narrow(), Some(R16!(300)));
    }

    #[test]
    fn a_type_narrows_to_itself_and_to_wider_ones() {
        assert_eq!(<Rational8 as Narrow<Rational8>>::narrow(&R8!(3, 4)), Some(R8!(3, 4)));
        assert_eq!(<Rational8 as Narrow<Rational16>>::narrow(&R8!(3, 4)), Some(R16!(3, 4)));
    }
}
