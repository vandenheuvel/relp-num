//! # Reading narrow values into an arbitrary precision rational
//!
//! One implementation per pair, each written in terms of the operators that this crate already
//! defines for that pair. Those operators are where the shortcuts live: adding an integer leaves
//! the denominator alone, multiplying by a value that fits in a word takes a single word gcd
//! rather than a binary one over every word, and multiplying by [`One`] touches nothing.
//!
//! Nothing here converts a narrow value and hands it to the general routine unless the pair has no
//! operators at all, and where that happens it is written out by [`absorb_by_widening`] rather
//! than inherited from a default, so it is visible in the source.

use crate::{Absorb, Rational8, Rational16, Rational32, Rational64, Rational128};
use crate::fixed::{Binary, One, SignedOne, Zero};
use crate::rational::big::Big;

/// Read a narrow value through the operators written for it and the wide type.
///
/// The multiplication goes through `MulAssign` on a clone rather than `Mul` on a reference,
/// because the assigning form is the one every narrow type here has.
macro_rules! absorb_by_ops {
    ($($narrow:ty),+ $(,)?) => {$(
        impl<const S: usize> Absorb<$narrow> for Big<S> {
            #[inline]
            fn from_narrow(narrow: &$narrow) -> Self {
                Self::from(*narrow)
            }
            #[inline]
            fn add_narrow(&mut self, narrow: &$narrow) {
                *self += *narrow;
            }
            #[inline]
            fn sub_narrow(&mut self, narrow: &$narrow) {
                *self -= *narrow;
            }
            #[inline]
            fn mul_narrow(&self, narrow: &$narrow) -> Self {
                let mut result = self.clone();
                result *= *narrow;
                result
            }
            #[inline]
            fn add_mul_narrow(&mut self, narrow: &$narrow, other: &Self) {
                let mut product = other.clone();
                product *= *narrow;
                *self += product;
            }
        }
    )+}
}

absorb_by_ops!(u8, u16, u32, u64, usize);
absorb_by_ops!(i8, i16, i32, i64, isize);
absorb_by_ops!(Rational8, Rational16, Rational32, Rational64);

/// Read a narrow value by converting it, for a pair that has no operators of its own.
///
/// This is the body every method would have had by default. It is written out because it is the
/// expensive one: converting produces a value whose denominator carries no information, and the
/// general routine then does the work of finding that out.
macro_rules! absorb_by_widening {
    ($($narrow:ty),+ $(,)?) => {$(
        impl<const S: usize> Absorb<$narrow> for Big<S> {
            #[inline]
            fn from_narrow(narrow: &$narrow) -> Self {
                Self::from(*narrow)
            }
            #[inline]
            fn add_narrow(&mut self, narrow: &$narrow) {
                *self += Self::from(*narrow);
            }
            #[inline]
            fn sub_narrow(&mut self, narrow: &$narrow) {
                *self -= Self::from(*narrow);
            }
            #[inline]
            fn mul_narrow(&self, narrow: &$narrow) -> Self {
                let mut result = self.clone();
                result *= Self::from(*narrow);
                result
            }
            #[inline]
            fn add_mul_narrow(&mut self, narrow: &$narrow, other: &Self) {
                let mut product = other.clone();
                product *= Self::from(*narrow);
                *self += product;
            }
        }
    )+}
}

// `Rational128` converts but has no operators against `Big`, so it goes the long way around.
absorb_by_widening!(Rational128);

impl<const S: usize> Absorb<One> for Big<S> {
    #[inline]
    fn from_narrow(_: &One) -> Self {
        Self::from(One)
    }
    #[inline]
    fn add_narrow(&mut self, _: &One) {
        *self += One;
    }
    #[inline]
    fn sub_narrow(&mut self, _: &One) {
        *self -= One;
    }
    #[inline]
    fn mul_narrow(&self, _: &One) -> Self {
        self.clone()
    }
    #[inline]
    fn add_mul_narrow(&mut self, _: &One, other: &Self) {
        *self += other;
    }
}

impl<const S: usize> Absorb<Zero> for Big<S> {
    #[inline]
    fn from_narrow(_: &Zero) -> Self {
        Self::from(Zero)
    }
    #[inline]
    fn add_narrow(&mut self, _: &Zero) {}
    #[inline]
    fn sub_narrow(&mut self, _: &Zero) {}
    #[inline]
    fn mul_narrow(&self, _: &Zero) -> Self {
        Self::from(Zero)
    }
    #[inline]
    fn add_mul_narrow(&mut self, _: &Zero, _: &Self) {}
}

impl<const S: usize> Absorb<Binary> for Big<S> {
    #[inline]
    fn from_narrow(narrow: &Binary) -> Self {
        Self::from(*narrow)
    }
    #[inline]
    fn add_narrow(&mut self, narrow: &Binary) {
        match narrow {
            Binary::Zero => {}
            Binary::One => *self += One,
        }
    }
    #[inline]
    fn sub_narrow(&mut self, narrow: &Binary) {
        match narrow {
            Binary::Zero => {}
            Binary::One => *self -= One,
        }
    }
    #[inline]
    fn mul_narrow(&self, narrow: &Binary) -> Self {
        match narrow {
            Binary::Zero => Self::from(Zero),
            Binary::One => self.clone(),
        }
    }
    #[inline]
    fn add_mul_narrow(&mut self, narrow: &Binary, other: &Self) {
        match narrow {
            Binary::Zero => {}
            Binary::One => *self += other,
        }
    }
}

impl<const S: usize> Absorb<SignedOne> for Big<S> {
    #[inline]
    fn from_narrow(narrow: &SignedOne) -> Self {
        match narrow {
            SignedOne::PlusOne => Self::from(One),
            SignedOne::MinusOne => -Self::from(One),
        }
    }
    #[inline]
    fn add_narrow(&mut self, narrow: &SignedOne) {
        match narrow {
            SignedOne::PlusOne => *self += One,
            SignedOne::MinusOne => *self -= One,
        }
    }
    #[inline]
    fn sub_narrow(&mut self, narrow: &SignedOne) {
        match narrow {
            SignedOne::PlusOne => *self -= One,
            SignedOne::MinusOne => *self += One,
        }
    }
    #[inline]
    fn mul_narrow(&self, narrow: &SignedOne) -> Self {
        match narrow {
            SignedOne::PlusOne => self.clone(),
            SignedOne::MinusOne => -self.clone(),
        }
    }
    #[inline]
    fn add_mul_narrow(&mut self, narrow: &SignedOne, other: &Self) {
        match narrow {
            SignedOne::PlusOne => *self += other,
            SignedOne::MinusOne => *self -= other,
        }
    }
}

/// The wide type reads itself, which is what makes a bound of `Absorb<F>` on a field cover its own
/// arithmetic as well as the narrow arithmetic.
impl<const S: usize> Absorb<Big<S>> for Big<S> {
    #[inline]
    fn from_narrow(narrow: &Big<S>) -> Self {
        narrow.clone()
    }
    #[inline]
    fn add_narrow(&mut self, narrow: &Big<S>) {
        *self += narrow;
    }
    #[inline]
    fn sub_narrow(&mut self, narrow: &Big<S>) {
        *self -= narrow;
    }
    #[inline]
    fn mul_narrow(&self, narrow: &Big<S>) -> Self {
        self * narrow
    }
    #[inline]
    fn add_mul_narrow(&mut self, narrow: &Big<S>, other: &Self) {
        *self += other * narrow;
    }
}

/// An absent value is zero, so it contributes nothing.
///
/// Sparse rows are stored as `Option`s to keep the zeros out. This lift is written for the wide
/// type rather than once for every wide type at once, because `Self` has to be local to the crate
/// that writes the implementation; a crate defining its own accumulator writes its own.
impl<const S: usize, N> Absorb<Option<N>> for Big<S>
where
    Big<S>: Absorb<N>,
{
    #[inline]
    fn from_narrow(narrow: &Option<N>) -> Self {
        match narrow {
            None => Self::from(Zero),
            Some(value) => <Big<S> as Absorb<N>>::from_narrow(value),
        }
    }
    #[inline]
    fn add_narrow(&mut self, narrow: &Option<N>) {
        if let Some(value) = narrow {
            self.add_narrow(value);
        }
    }
    #[inline]
    fn sub_narrow(&mut self, narrow: &Option<N>) {
        if let Some(value) = narrow {
            self.sub_narrow(value);
        }
    }
    #[inline]
    fn mul_narrow(&self, narrow: &Option<N>) -> Self {
        match narrow {
            None => Self::from(Zero),
            Some(value) => self.mul_narrow(value),
        }
    }
    #[inline]
    fn add_mul_narrow(&mut self, narrow: &Option<N>, other: &Self) {
        if let Some(value) = narrow {
            self.add_mul_narrow(value, other);
        }
    }
}

/// A matrix provider that hands out references to what it stores is read through them.
impl<const S: usize, N> Absorb<&N> for Big<S>
where
    Big<S>: Absorb<N>,
{
    #[inline]
    fn from_narrow(narrow: &&N) -> Self {
        <Big<S> as Absorb<N>>::from_narrow(narrow)
    }
    #[inline]
    fn add_narrow(&mut self, narrow: &&N) {
        self.add_narrow(*narrow);
    }
    #[inline]
    fn sub_narrow(&mut self, narrow: &&N) {
        self.sub_narrow(*narrow);
    }
    #[inline]
    fn mul_narrow(&self, narrow: &&N) -> Self {
        self.mul_narrow(*narrow)
    }
    #[inline]
    fn add_mul_narrow(&mut self, narrow: &&N, other: &Self) {
        self.add_mul_narrow(*narrow, other);
    }
}
