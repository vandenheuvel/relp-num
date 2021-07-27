use std::iter::Sum;
use std::ops::Neg;

use crate::integer::big::ops::div::div as div_by_odd_or_even;
use crate::integer::big::ops::normalize::gcd;
use crate::rational::big::Big;

mod add_sub;
mod mul_div;
pub(super) mod building_blocks;

impl<const S: usize> Sum for Big<S> {
    #[must_use]
    #[inline]
    fn sum<I: Iterator<Item=Self>>(mut iter: I) -> Self {
        let first = iter.next();
        match first {
            None => <Self as num_traits::Zero>::zero(),
            Some(mut total) => {
                while let Some(next_value) = iter.next() {
                    total += next_value;
                }

                total
            }
        }
    }
}

impl<const S: usize> Neg for Big<S> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn neg(mut self) -> Self::Output {
        self.sign = !self.sign;
        self
    }
}

impl<const S: usize> Neg for &Big<S> {
    type Output = Big<S>;

    #[must_use]
    #[inline]
    fn neg(self) -> Self::Output {
        Self::Output {
            sign: !self.sign,
            numerator: self.numerator.clone(),
            denominator: self.denominator.clone(),
        }
    }
}

#[cfg(test)]
mod test;
