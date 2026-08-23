//! # Measuring a fixed width rational
use crate::traits::EncodingSize;
use crate::{
    Rational8, Rational16, Rational32, Rational64, Rational128, RationalUsize,
};

macro_rules! size_small {
    ($($name:ty => $unsigned:ty),+ $(,)?) => {$(
        impl EncodingSize for $name {
            fn numerator_bits(&self) -> u32 {
                <$unsigned>::BITS - self.numerator.leading_zeros()
            }

            fn denominator_bits(&self) -> u32 {
                <$unsigned>::BITS - self.denominator.leading_zeros()
            }
        }
    )+}
}

size_small!(
    Rational8 => u8,
    Rational16 => u16,
    Rational32 => u32,
    Rational64 => u64,
    Rational128 => u128,
    RationalUsize => usize,
);

#[cfg(test)]
mod test {
    use crate::{EncodingSize, R8, R16};

    #[test]
    fn the_bits_are_counted_over_the_magnitude() {
        assert_eq!(R8!(0).numerator_bits(), 0);
        assert_eq!(R8!(0).denominator_bits(), 1);
        assert_eq!(R8!(-1).encoding_bits(), 2);
        assert_eq!(R8!(255).numerator_bits(), 8);
        assert_eq!(R16!(256).numerator_bits(), 9);
        assert_eq!(R8!(1, 3).denominator_bits(), 2);
    }
}
