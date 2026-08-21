//! # Acting on a wider accumulator
//!
//! Exact linear programs are stored in narrow number types and computed in wide ones. The
//! constraint matrix of a network problem holds nothing but `1`, `-1` and `0`; the basis inverse
//! that the simplex method builds from it needs arbitrary precision. Widening every coefficient
//! before using it would throw away exactly the information that makes the narrow type worth
//! having: multiplying by [`One`](crate::fixed::One) is a clone, adding [`Zero`](crate::fixed::Zero) is nothing
//! at all.
//!
//! [`Widen`] is the one relation between a narrow value and a wide accumulator. A type states how
//! it widens, and overrides only the operations for which it knows a shortcut.

use crate::rational::big::Big;
use crate::{Field, Rational8, Rational16, Rational32, Rational64};
use crate::fixed::{Binary, One, SignedOne, Zero};

/// A value that can act on a wider accumulator without being widened first.
///
/// [`widen`](Widen::widen) is the only required method; every other method has a correct default
/// body written in terms of it. A narrow type is therefore never partially implemented — it either
/// works with every field or it does not compile. Override a default only where the narrow type
/// admits a genuine shortcut.
///
/// Implementations are written once per narrow type and are generic over the wide type, so the
/// case where the narrow and the wide type coincide is covered by the same impl — `Big<S>` widens
/// into any field it converts into, including itself.
///
/// Two blanket impls are deliberately absent:
///
/// * `impl<W: Field, T: Into<W>> Widen<W> for T` would overlap with every impl below.
/// * `impl<W: Field> Widen<W> for W` would overlap with the `&T` impl, because nothing rules out a
///   reference being a field. Generic code over an unknown field therefore has to state
///   `F: Widen<F>` explicitly; code over a concrete type gets it from that type's own impl.
///
/// # Example
///
/// ```
/// use relp_num::fixed::One;
/// use relp_num::{RationalBig, Widen, RB};
///
/// let wide = RB!(7, 2);
/// // No `RationalBig` is materialised for the multiplication.
/// assert_eq!(One.scale(&wide), RB!(7, 2));
/// assert_eq!(<One as Widen<RationalBig>>::widen(&One), RB!(1));
///
/// let mut accumulator = RB!(1, 2);
/// One.add_to(&mut accumulator);
/// assert_eq!(accumulator, RB!(3, 2));
/// ```
pub trait Widen<W: Field> {
    /// This value in the wide type.
    ///
    /// The remaining methods must agree with this one: `x.add_to(acc)` equals `*acc += x.widen()`,
    /// `x.sub_from(acc)` equals `*acc -= x.widen()`, and `x.scale(y)` equals `x.widen() * y`.
    fn widen(&self) -> W;

    /// Add this value to an accumulator.
    #[inline]
    fn add_to(&self, accumulator: &mut W) {
        *accumulator += self.widen();
    }

    /// Subtract this value from an accumulator.
    #[inline]
    fn sub_from(&self, accumulator: &mut W) {
        *accumulator -= self.widen();
    }

    /// Multiply a wide value by this value.
    #[inline]
    fn scale(&self, value: &W) -> W {
        let mut result = self.widen();
        result *= value;
        result
    }
}

impl<W: Field> Widen<W> for One {
    #[inline]
    fn widen(&self) -> W {
        W::one()
    }
    #[inline]
    fn add_to(&self, accumulator: &mut W) {
        *accumulator += W::one();
    }
    #[inline]
    fn sub_from(&self, accumulator: &mut W) {
        *accumulator -= W::one();
    }
    #[inline]
    fn scale(&self, value: &W) -> W {
        value.clone()
    }
}

impl<W: Field> Widen<W> for Zero {
    #[inline]
    fn widen(&self) -> W {
        W::zero()
    }
    #[inline]
    fn add_to(&self, _: &mut W) {}
    #[inline]
    fn sub_from(&self, _: &mut W) {}
    #[inline]
    fn scale(&self, _: &W) -> W {
        W::zero()
    }
}

impl<W: Field> Widen<W> for Binary {
    #[inline]
    fn widen(&self) -> W {
        match self {
            Binary::Zero => W::zero(),
            Binary::One => W::one(),
        }
    }
    #[inline]
    fn add_to(&self, accumulator: &mut W) {
        match self {
            Binary::Zero => {}
            Binary::One => *accumulator += W::one(),
        }
    }
    #[inline]
    fn sub_from(&self, accumulator: &mut W) {
        match self {
            Binary::Zero => {}
            Binary::One => *accumulator -= W::one(),
        }
    }
    #[inline]
    fn scale(&self, value: &W) -> W {
        match self {
            Binary::Zero => W::zero(),
            Binary::One => value.clone(),
        }
    }
}

impl<W: Field> Widen<W> for SignedOne {
    #[inline]
    fn widen(&self) -> W {
        match self {
            SignedOne::PlusOne => W::one(),
            SignedOne::MinusOne => -W::one(),
        }
    }
    #[inline]
    fn add_to(&self, accumulator: &mut W) {
        match self {
            SignedOne::PlusOne => *accumulator += W::one(),
            SignedOne::MinusOne => *accumulator -= W::one(),
        }
    }
    #[inline]
    fn sub_from(&self, accumulator: &mut W) {
        match self {
            SignedOne::PlusOne => *accumulator -= W::one(),
            SignedOne::MinusOne => *accumulator += W::one(),
        }
    }
    #[inline]
    fn scale(&self, value: &W) -> W {
        match self {
            SignedOne::PlusOne => value.clone(),
            SignedOne::MinusOne => -value.clone(),
        }
    }
}

/// An absent value is zero, so it contributes nothing.
///
/// Sparse cost rows are stored as `Option`s to avoid keeping the zeros around.
impl<W: Field, T: Widen<W>> Widen<W> for Option<T> {
    #[inline]
    fn widen(&self) -> W {
        match self {
            None => W::zero(),
            Some(value) => value.widen(),
        }
    }
    #[inline]
    fn add_to(&self, accumulator: &mut W) {
        if let Some(value) = self {
            value.add_to(accumulator);
        }
    }
    #[inline]
    fn sub_from(&self, accumulator: &mut W) {
        if let Some(value) = self {
            value.sub_from(accumulator);
        }
    }
    #[inline]
    fn scale(&self, value: &W) -> W {
        match self {
            None => W::zero(),
            Some(inner) => inner.scale(value),
        }
    }
}

/// A matrix provider that hands out references to its stored values widens through them.
impl<W: Field, T: Widen<W>> Widen<W> for &T {
    #[inline]
    fn widen(&self) -> W {
        (**self).widen()
    }
    #[inline]
    fn add_to(&self, accumulator: &mut W) {
        (**self).add_to(accumulator);
    }
    #[inline]
    fn sub_from(&self, accumulator: &mut W) {
        (**self).sub_from(accumulator);
    }
    #[inline]
    fn scale(&self, value: &W) -> W {
        (**self).scale(value)
    }
}

/// Widen through a `From` impl.
///
/// Used for the number types that carry a value, where there is no shortcut to exploit: the work
/// of widening has to happen either way. Each invocation covers one narrow type against every wide
/// type it converts into, including itself.
macro_rules! widen_by_conversion {
    ($($narrow:ty),+ $(,)?) => {$(
        impl<W: Field + for<'r> From<&'r $narrow>> Widen<W> for $narrow {
            #[inline]
            fn widen(&self) -> W {
                W::from(self)
            }
        }
    )+}
}

widen_by_conversion!(i8, i16, i32, i64, i128, isize);
widen_by_conversion!(u8, u16, u32, u64, u128, usize);
widen_by_conversion!(Rational8, Rational16, Rational32, Rational64);

/// An arbitrary precision rational is itself a field, so this impl also covers the case where the
/// narrow and the wide type are the same.
impl<const S: usize, W: Field + for<'r> From<&'r Big<S>>> Widen<W> for Big<S> {
    #[inline]
    fn widen(&self) -> W {
        W::from(self)
    }
}

#[cfg(test)]
mod test {
    use crate::{Rational64, RationalBig, Widen, RB};
    use crate::fixed::{Binary, One, SignedOne, Zero};

    /// Every override must agree with the default body written in terms of `widen`.
    fn check<T: Widen<RationalBig>>(value: &T, wide: RationalBig) {
        assert_eq!(value.widen(), wide, "widen");

        let start = RB!(5, 3);

        let mut by_override = start.clone();
        value.add_to(&mut by_override);
        assert_eq!(by_override, start.clone() + wide.clone(), "add_to");

        let mut by_override = start.clone();
        value.sub_from(&mut by_override);
        assert_eq!(by_override, start.clone() - wide.clone(), "sub_from");

        assert_eq!(value.scale(&start), wide.clone() * start.clone(), "scale");
        assert_eq!(value.scale(&RB!(0)), RB!(0), "scale by zero");
    }

    #[test]
    fn markers_agree_with_their_defaults() {
        check(&One, RB!(1));
        check(&Zero, RB!(0));
        check(&Binary::Zero, RB!(0));
        check(&Binary::One, RB!(1));
        check(&SignedOne::PlusOne, RB!(1));
        check(&SignedOne::MinusOne, RB!(-1));
    }

    #[test]
    fn options_and_references_agree_with_their_defaults() {
        check(&Some(One), RB!(1));
        check(&None::<One>, RB!(0));
        check(&Some(SignedOne::MinusOne), RB!(-1));
        check(&&One, RB!(1));
        check(&Some(&SignedOne::MinusOne), RB!(-1));
    }

    #[test]
    fn integers_and_rationals() {
        check(&7_i32, RB!(7));
        check(&-7_i64, RB!(-7));
        check(&0_u8, RB!(0));
        check(&Rational64::new(3, 4).unwrap(), RB!(3, 4));
        check(&RB!(-9, 4), RB!(-9, 4));
    }

    /// The narrow type and the wide type may coincide; no separate impl exists for that.
    #[test]
    fn wide_on_wide() {
        let column: Vec<(usize, RationalBig)> = vec![(0, RB!(2)), (1, RB!(3, 2))];
        let pi = [RB!(5), RB!(4)];
        let mut total = RB!(0);
        for (i, value) in &column {
            total += value.scale(&pi[*i]);
        }
        assert_eq!(total, RB!(16));
    }
}
