//! # Measuring an arbitrary precision rational
use crate::integer::big::io::bit_length;
use crate::rational::big::Big;
use crate::traits::EncodingSize;

impl<const S: usize> EncodingSize for Big<S> {
    fn numerator_bits(&self) -> u32 {
        bit_length(&self.numerator)
    }

    fn denominator_bits(&self) -> u32 {
        bit_length(&self.denominator)
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::{EncodingSize, RationalBig, RB};

    #[test]
    fn the_bits_are_counted_over_the_magnitude() {
        assert_eq!(RB!(0).numerator_bits(), 0);
        assert_eq!(RB!(0).denominator_bits(), 1);
        assert_eq!(RB!(1).encoding_bits(), 2);
        assert_eq!(RB!(-1).encoding_bits(), 2);
        assert_eq!(RB!(255).numerator_bits(), 8);
        assert_eq!(RB!(256).numerator_bits(), 9);
        assert_eq!(RB!(1, 3).denominator_bits(), 2);
    }

    #[test]
    fn a_value_that_is_small_but_expensive_says_so() {
        // Just under one, and nothing about its magnitude says how much it costs.
        let value = RationalBig::from_str("999999999999999999999/1000000000000000000000").unwrap();
        assert!(value < RB!(1));
        assert!(value.encoding_bits() > 130);
    }
}
