//! # Reading narrow values into a fixed width rational
//!
//! These types are fields, so they can serve as the accumulator too, and generic code that names a
//! field has to be able to act on them with the same narrow values. The bodies go through the
//! operators written for each pair, exactly as the arbitrary precision ones do.
//!
//! An integer wider than the rational it acts on has no operators here and gets no implementation:
//! the conversion could not be relied on to fit.

use crate::{Absorb, Rational8, Rational16, Rational32, Rational64, Rational128, RationalUsize};
use crate::fixed::{Binary, One, SignedOne, Zero};

macro_rules! absorb_small {
    ($name:ty; $($int:ty),* $(,)?) => {
        /// The accumulator reads itself.
        impl Absorb<$name> for $name {
            #[inline]
            fn from_narrow(narrow: &$name) -> Self { *narrow }
            #[inline]
            fn add_narrow(&mut self, narrow: &$name) { *self += narrow }
            #[inline]
            fn sub_narrow(&mut self, narrow: &$name) { *self -= narrow }
            #[inline]
            fn mul_narrow(&self, narrow: &$name) -> Self { let mut r = *self; r *= narrow; r }
            #[inline]
            fn add_mul_narrow(&mut self, narrow: &$name, other: &Self) {
                let mut product = *other;
                product *= narrow;
                *self += product;
            }
        }

        impl Absorb<One> for $name {
            #[inline]
            fn from_narrow(_: &One) -> Self { <Self as num_traits::One>::one() }
            #[inline]
            fn add_narrow(&mut self, _: &One) { *self += One }
            #[inline]
            fn sub_narrow(&mut self, _: &One) { *self -= One }
            #[inline]
            fn mul_narrow(&self, _: &One) -> Self { *self }
            #[inline]
            fn add_mul_narrow(&mut self, _: &One, other: &Self) { *self += other }
        }

        impl Absorb<Zero> for $name {
            #[inline]
            fn from_narrow(_: &Zero) -> Self { <Self as num_traits::Zero>::zero() }
            #[inline]
            fn add_narrow(&mut self, _: &Zero) {}
            #[inline]
            fn sub_narrow(&mut self, _: &Zero) {}
            #[inline]
            fn mul_narrow(&self, _: &Zero) -> Self { <Self as num_traits::Zero>::zero() }
            #[inline]
            fn add_mul_narrow(&mut self, _: &Zero, _: &Self) {}
        }

        impl Absorb<Binary> for $name {
            #[inline]
            fn from_narrow(narrow: &Binary) -> Self {
                match narrow {
                    Binary::Zero => <Self as num_traits::Zero>::zero(),
                    Binary::One => <Self as num_traits::One>::one(),
                }
            }
            #[inline]
            fn add_narrow(&mut self, narrow: &Binary) {
                match narrow { Binary::Zero => {}, Binary::One => *self += One }
            }
            #[inline]
            fn sub_narrow(&mut self, narrow: &Binary) {
                match narrow { Binary::Zero => {}, Binary::One => *self -= One }
            }
            #[inline]
            fn mul_narrow(&self, narrow: &Binary) -> Self {
                match narrow {
                    Binary::Zero => <Self as num_traits::Zero>::zero(),
                    Binary::One => *self,
                }
            }
            #[inline]
            fn add_mul_narrow(&mut self, narrow: &Binary, other: &Self) {
                match narrow { Binary::Zero => {}, Binary::One => *self += other }
            }
        }

        impl Absorb<SignedOne> for $name {
            #[inline]
            fn from_narrow(narrow: &SignedOne) -> Self {
                match narrow {
                    SignedOne::PlusOne => <Self as num_traits::One>::one(),
                    SignedOne::MinusOne => -<Self as num_traits::One>::one(),
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
                    SignedOne::PlusOne => *self,
                    SignedOne::MinusOne => -*self,
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

        $(
            impl Absorb<$int> for $name {
                #[inline]
                fn from_narrow(narrow: &$int) -> Self { Self::from(*narrow) }
                #[inline]
                fn add_narrow(&mut self, narrow: &$int) { *self += *narrow }
                #[inline]
                fn sub_narrow(&mut self, narrow: &$int) { *self -= *narrow }
                #[inline]
                fn mul_narrow(&self, narrow: &$int) -> Self { let mut r = *self; r *= *narrow; r }
                #[inline]
                fn add_mul_narrow(&mut self, narrow: &$int, other: &Self) {
                    let mut product = *other;
                    product *= *narrow;
                    *self += product;
                }
            }
        )*

        /// An absent value is zero, so it contributes nothing.
        impl<N> Absorb<Option<N>> for $name where $name: Absorb<N> {
            #[inline]
            fn from_narrow(narrow: &Option<N>) -> Self {
                match narrow {
                    None => <Self as num_traits::Zero>::zero(),
                    Some(value) => <$name as Absorb<N>>::from_narrow(value),
                }
            }
            #[inline]
            fn add_narrow(&mut self, narrow: &Option<N>) {
                if let Some(value) = narrow { self.add_narrow(value) }
            }
            #[inline]
            fn sub_narrow(&mut self, narrow: &Option<N>) {
                if let Some(value) = narrow { self.sub_narrow(value) }
            }
            #[inline]
            fn mul_narrow(&self, narrow: &Option<N>) -> Self {
                match narrow {
                    None => <Self as num_traits::Zero>::zero(),
                    Some(value) => self.mul_narrow(value),
                }
            }
            #[inline]
            fn add_mul_narrow(&mut self, narrow: &Option<N>, other: &Self) {
                if let Some(value) = narrow { self.add_mul_narrow(value, other) }
            }
        }

        /// A provider that hands out references to what it stores is read through them.
        impl<N> Absorb<&N> for $name where $name: Absorb<N> {
            #[inline]
            fn from_narrow(narrow: &&N) -> Self { <$name as Absorb<N>>::from_narrow(narrow) }
            #[inline]
            fn add_narrow(&mut self, narrow: &&N) { self.add_narrow(*narrow) }
            #[inline]
            fn sub_narrow(&mut self, narrow: &&N) { self.sub_narrow(*narrow) }
            #[inline]
            fn mul_narrow(&self, narrow: &&N) -> Self { self.mul_narrow(*narrow) }
            #[inline]
            fn add_mul_narrow(&mut self, narrow: &&N, other: &Self) {
                self.add_mul_narrow(*narrow, other)
            }
        }
    }
}

absorb_small!(Rational8; u8, i8);
absorb_small!(Rational16; u8, u16, i8, i16);
absorb_small!(Rational32; u8, u16, u32, i8, i16, i32);
absorb_small!(Rational64; u8, u16, u32, u64, i8, i16, i32, i64);
absorb_small!(Rational128; u8, u16, u32, u64, u128, i8, i16, i32, i64, i128);

/// [`RationalUsize`] has neither the marker operators nor a conversion from a machine integer, so
/// its bodies are written against the multiplicative identity instead. That is the slower form —
/// it materialises a one — and it is written out here rather than inherited, so that adding those
/// operators later is visibly an improvement rather than a silent one.
macro_rules! absorb_by_identity {
    ($name:ty) => {
        impl Absorb<$name> for $name {
            #[inline]
            fn from_narrow(narrow: &$name) -> Self { *narrow }
            #[inline]
            fn add_narrow(&mut self, narrow: &$name) { *self += narrow }
            #[inline]
            fn sub_narrow(&mut self, narrow: &$name) { *self -= narrow }
            #[inline]
            fn mul_narrow(&self, narrow: &$name) -> Self { let mut r = *self; r *= narrow; r }
            #[inline]
            fn add_mul_narrow(&mut self, narrow: &$name, other: &Self) {
                let mut product = *other;
                product *= narrow;
                *self += product;
            }
        }

        impl Absorb<One> for $name {
            #[inline]
            fn from_narrow(_: &One) -> Self { <Self as num_traits::One>::one() }
            #[inline]
            fn add_narrow(&mut self, _: &One) { *self += <Self as num_traits::One>::one() }
            #[inline]
            fn sub_narrow(&mut self, _: &One) { *self -= <Self as num_traits::One>::one() }
            #[inline]
            fn mul_narrow(&self, _: &One) -> Self { *self }
            #[inline]
            fn add_mul_narrow(&mut self, _: &One, other: &Self) { *self += other }
        }

        impl Absorb<Zero> for $name {
            #[inline]
            fn from_narrow(_: &Zero) -> Self { <Self as num_traits::Zero>::zero() }
            #[inline]
            fn add_narrow(&mut self, _: &Zero) {}
            #[inline]
            fn sub_narrow(&mut self, _: &Zero) {}
            #[inline]
            fn mul_narrow(&self, _: &Zero) -> Self { <Self as num_traits::Zero>::zero() }
            #[inline]
            fn add_mul_narrow(&mut self, _: &Zero, _: &Self) {}
        }

        impl<N> Absorb<Option<N>> for $name where $name: Absorb<N> {
            #[inline]
            fn from_narrow(narrow: &Option<N>) -> Self {
                match narrow {
                    None => <Self as num_traits::Zero>::zero(),
                    Some(value) => <$name as Absorb<N>>::from_narrow(value),
                }
            }
            #[inline]
            fn add_narrow(&mut self, narrow: &Option<N>) {
                if let Some(value) = narrow { self.add_narrow(value) }
            }
            #[inline]
            fn sub_narrow(&mut self, narrow: &Option<N>) {
                if let Some(value) = narrow { self.sub_narrow(value) }
            }
            #[inline]
            fn mul_narrow(&self, narrow: &Option<N>) -> Self {
                match narrow {
                    None => <Self as num_traits::Zero>::zero(),
                    Some(value) => self.mul_narrow(value),
                }
            }
            #[inline]
            fn add_mul_narrow(&mut self, narrow: &Option<N>, other: &Self) {
                if let Some(value) = narrow { self.add_mul_narrow(value, other) }
            }
        }

        impl<N> Absorb<&N> for $name where $name: Absorb<N> {
            #[inline]
            fn from_narrow(narrow: &&N) -> Self { <$name as Absorb<N>>::from_narrow(narrow) }
            #[inline]
            fn add_narrow(&mut self, narrow: &&N) { self.add_narrow(*narrow) }
            #[inline]
            fn sub_narrow(&mut self, narrow: &&N) { self.sub_narrow(*narrow) }
            #[inline]
            fn mul_narrow(&self, narrow: &&N) -> Self { self.mul_narrow(*narrow) }
            #[inline]
            fn add_mul_narrow(&mut self, narrow: &&N, other: &Self) {
                self.add_mul_narrow(*narrow, other)
            }
        }
    }
}

absorb_by_identity!(RationalUsize);

#[cfg(test)]
mod test {
    use crate::{Absorb, Rational64, RationalUsize, R32, R64, R8};
    use crate::fixed::{Binary, One, SignedOne, Zero};

    /// Every implementation has to agree with converting and then operating, as for the arbitrary
    /// precision accumulator.
    fn check<T>(value: &T, wide: Rational64)
    where
        Rational64: Absorb<T>,
    {
        assert_eq!(Rational64::from_narrow(value), wide, "from_narrow");

        let start = R64!(5, 3);

        let mut by_override = start;
        by_override.add_narrow(value);
        assert_eq!(by_override, start + wide, "add_narrow");

        let mut by_override = start;
        by_override.sub_narrow(value);
        assert_eq!(by_override, start - wide, "sub_narrow");

        assert_eq!(start.mul_narrow(value), wide * start, "mul_narrow");

        for other in [R64!(0), R64!(1), R64!(-7, 5), start] {
            let mut fused = start;
            fused.add_mul_narrow(value, &other);
            assert_eq!(fused, start + wide * other, "add_mul_narrow by {other}");
        }
    }

    #[test]
    fn markers() {
        check(&One, R64!(1));
        check(&Zero, R64!(0));
        check(&Binary::Zero, R64!(0));
        check(&Binary::One, R64!(1));
        check(&SignedOne::PlusOne, R64!(1));
        check(&SignedOne::MinusOne, R64!(-1));
    }

    #[test]
    fn integers_and_self() {
        check(&7_i32, R64!(7));
        check(&-7_i64, R64!(-7));
        check(&0_u8, R64!(0));
        check(&R64!(-9, 4), R64!(-9, 4));
    }

    #[test]
    fn options_and_references() {
        check(&Some(One), R64!(1));
        check(&None::<One>, R64!(0));
        check(&&SignedOne::MinusOne, R64!(-1));
        check(&Some(&7_i32), R64!(7));
    }

    /// A fixed width accumulator is a field, so generic code may pick one, at any of its widths.
    #[test]
    fn every_width_is_an_accumulator() {
        let mut small = R8!(1, 2);
        small.add_narrow(&One);
        assert_eq!(small, R8!(3, 2));
        assert_eq!(small.mul_narrow(&SignedOne::MinusOne), R8!(-3, 2));

        let mut medium = R32!(1, 4);
        medium.add_mul_narrow(&3_i32, &R32!(1, 2));
        assert_eq!(medium, R32!(7, 4));

        // `RationalUsize` has no marker operators, so its bodies go through the identity; the
        // answers have to be the same.
        let mut pointer_width = RationalUsize::new(1, 2).unwrap();
        pointer_width.add_narrow(&One);
        assert_eq!(pointer_width, RationalUsize::new(3, 2).unwrap());
        assert_eq!(
            pointer_width.mul_narrow(&Zero),
            RationalUsize::new(0, 1).unwrap(),
        );
    }
}
