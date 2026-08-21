//! # Acting on a wide accumulator with a narrow value
//!
//! Exact linear programs are stored in narrow number types and computed in wide ones. The
//! constraint matrix of a network problem holds nothing but `1`, `-1` and `0`; the basis inverse
//! the simplex method builds from it needs arbitrary precision. Widening every coefficient before
//! using it throws away exactly the information that makes the narrow type worth having:
//! multiplying by [`One`](crate::fixed::One) is a clone, adding [`Zero`](crate::fixed::Zero) is
//! nothing at all, and adding an integer to a fraction leaves its denominator alone.
//!
//! [`Absorb`] is the one relation between the two. It is written from the wide side, and that is
//! the whole point: an implementation names both types concretely, so it can reach the operator
//! that was written for exactly this pair. A trait written from the narrow side and generic over
//! the wide type cannot, because inside such a body the wide type is opaque and converting is the
//! only thing left to do.

use crate::Field;

/// What a wide accumulator does with a narrow value.
///
/// The wide type is `Self`, so every implementation sees both types concretely and can be written
/// in terms of the operators that exist for the pair.
///
/// # No defaults
///
/// Every method has to be written out. A default body would have to be phrased in terms of
/// [`from_narrow`](Absorb::from_narrow), which is the slow path: it materialises a wide value and
/// hands it to the general routine, so a forgotten override would cost orders of magnitude at the
/// larger widths and cost nothing at the smallest, which is where it would be tested. Requiring
/// each body makes leaving one out a compile error rather than a benchmark result.
///
/// Two macros write the bodies, so the burden is one line per pair in practice:
/// `absorb_by_ops!` for a pair that has operators, `absorb_by_widening!` for one that does not.
///
/// # Extending it
///
/// A crate downstream can implement this for its own narrow type against a wide type from here:
/// `impl<const S: usize> Absorb<MyCoefficient> for Big<S>` is a foreign trait for a foreign `Self`
/// with a local type parameter, which the orphan rule permits. Such an implementation sees `Big`
/// concretely and can be as fast as one written here.
///
/// A crate that brings its own wide type implements this for it against the narrow types it wants
/// to read, which is always allowed because `Self` is then local.
///
/// # Agreement
///
/// The four operating methods have to agree with [`from_narrow`](Absorb::from_narrow):
/// `w.add_narrow(n)` equals `w += W::from_narrow(n)`, `w.sub_narrow(n)` equals
/// `w -= W::from_narrow(n)`, `w.mul_narrow(n)` equals `w * W::from_narrow(n)`, and
/// `w.add_mul_narrow(n, v)` equals `w += v * W::from_narrow(n)`. The tests in this crate check
/// every implementation against those four statements.
///
/// # Example
///
/// ```
/// use relp_num::fixed::One;
/// use relp_num::{Absorb, RationalBig, RB};
///
/// let mut accumulator = RB!(1, 2);
/// // No `RationalBig` is materialised, and no gcd is taken: the denominator is added into the
/// // numerator where it stands.
/// accumulator.add_narrow(&One);
/// assert_eq!(accumulator, RB!(3, 2));
///
/// assert_eq!(RB!(7, 2).mul_narrow(&One), RB!(7, 2));
/// assert_eq!(<RationalBig as Absorb<One>>::from_narrow(&One), RB!(1));
/// ```
pub trait Absorb<N>: Sized {
    /// The narrow value in the wide type.
    fn from_narrow(narrow: &N) -> Self;

    /// Add a narrow value to this one.
    fn add_narrow(&mut self, narrow: &N);

    /// Subtract a narrow value from this one.
    fn sub_narrow(&mut self, narrow: &N);

    /// Multiply this value by a narrow one.
    fn mul_narrow(&self, narrow: &N) -> Self;

    /// Add the product of a narrow value and a wide one to this value.
    ///
    /// This is the operation an inner product is made of, and the reason it is a method of its own
    /// rather than a multiplication followed by an addition: for a narrow value that is one, the
    /// multiplication is not a cheap multiplication but no multiplication, and the intermediate it
    /// would have produced is not a cheap allocation but no allocation.
    fn add_mul_narrow(&mut self, narrow: &N, other: &Self);
}

/// A wide accumulator, together with the narrow values it reads.
///
/// Stating `W: AbsorbAll<N>` is stating `W: Field + Absorb<N>`, which is what generic code over a
/// matrix provider's coefficient type wants: a field to compute in, and the ability to act on it
/// with what the provider hands over.
pub trait AbsorbAll<N>: Field + Absorb<N> {}
impl<N, W: Field + Absorb<N>> AbsorbAll<N> for W {}

#[cfg(test)]
mod test {
    use crate::{Absorb, AbsorbAll, Field, FieldRef, Rational8, Rational16, Rational32, Rational64, Rational128, RationalBig, RB};
    use crate::fixed::{Binary, One, SignedOne, Zero};

    /// Every implementation has to agree with converting and then operating.
    ///
    /// This is the contract that makes the whole table trustworthy: the fast bodies are written by
    /// hand against the operators of a pair, and nothing but this check ties them back to what the
    /// narrow value means.
    fn check<T>(value: &T, wide: RationalBig)
    where
        RationalBig: Absorb<T>,
    {
        assert_eq!(RationalBig::from_narrow(value), wide, "from_narrow");

        let start = RB!(5, 3);

        let mut by_override = start.clone();
        by_override.add_narrow(value);
        assert_eq!(by_override, start.clone() + wide.clone(), "add_narrow");

        let mut by_override = start.clone();
        by_override.sub_narrow(value);
        assert_eq!(by_override, start.clone() - wide.clone(), "sub_narrow");

        assert_eq!(start.mul_narrow(value), wide.clone() * start.clone(), "mul_narrow");
        assert_eq!(RB!(0).mul_narrow(value), RB!(0), "mul_narrow by zero");

        // The fused operation, against the two steps it replaces.
        for other in [RB!(0), RB!(1), RB!(-7, 5), start.clone()] {
            let mut fused = start.clone();
            fused.add_mul_narrow(value, &other);
            assert_eq!(
                fused,
                start.clone() + wide.clone() * other.clone(),
                "add_mul_narrow by {other}",
            );
        }
    }

    #[test]
    fn markers_agree_with_converting() {
        check(&One, RB!(1));
        check(&Zero, RB!(0));
        check(&Binary::Zero, RB!(0));
        check(&Binary::One, RB!(1));
        check(&SignedOne::PlusOne, RB!(1));
        check(&SignedOne::MinusOne, RB!(-1));
    }

    #[test]
    fn options_and_references_agree_with_converting() {
        check(&Some(One), RB!(1));
        check(&None::<One>, RB!(0));
        check(&Some(SignedOne::MinusOne), RB!(-1));
        check(&&One, RB!(1));
        check(&Some(&SignedOne::MinusOne), RB!(-1));
        check(&None::<Rational64>, RB!(0));
        check(&Some(Rational64::new(3, 4).unwrap()), RB!(3, 4));
    }

    #[test]
    fn integers_and_rationals_agree_with_converting() {
        check(&7_i32, RB!(7));
        check(&-7_i64, RB!(-7));
        check(&0_u8, RB!(0));
        check(&0_i16, RB!(0));
        check(&Rational8::new(3, 4).unwrap(), RB!(3, 4));
        check(&Rational16::new(-3, 4).unwrap(), RB!(-3, 4));
        check(&Rational32::new(3, 4).unwrap(), RB!(3, 4));
        check(&Rational64::new(3, 4).unwrap(), RB!(3, 4));
        check(&Rational128::new(3, 4).unwrap(), RB!(3, 4));
        check(&RB!(-9, 4), RB!(-9, 4));
    }

    /// The widths that only became reachable once the conversion bound went away.
    ///
    /// These used to be covered by an implementation whose `for<'r> From<&'r Self>` bound
    /// `RationalBig` does not satisfy, so the implementation existed and the trait did not hold,
    /// which showed up at a use site as an error about a conversion nobody asked for.
    #[test]
    fn pointer_widths() {
        check(&7_usize, RB!(7));
        check(&7_isize, RB!(7));
        check(&(-7_isize), RB!(-7));
    }

    /// Generic code over a field, stated the way it has to be stated with [`FieldRef`].
    ///
    /// The bound on the reference is a higher ranked one on a type that is not `Self`, so it is a
    /// requirement on the caller rather than something a `F: Field` bound implies. Moving it onto
    /// the definition of `Field` does not help: it stays a requirement, and one that then has to be
    /// discharged at every use of `Field` instead of every use of the reference operations.
    fn with_field_ref<F: Field>(a: &F, b: &F) -> F
    where
        for<'r> &'r F: FieldRef<F>,
    {
        &(a * b) + a
    }

    /// The same function over [`AbsorbAll`], which is one bound and no higher ranked anything.
    ///
    /// `Absorb<F> for F` is the reference arithmetic: every method already takes its operands by
    /// reference, so there is no reference type left to put a bound on.
    fn with_absorb<F: AbsorbAll<F>>(a: &F, b: &F) -> F {
        let mut result = a.mul_narrow(b);
        result.add_narrow(a);
        result
    }

    #[test]
    fn one_bound_replaces_the_higher_ranked_pair() {
        let a = RB!(3, 2);
        let b = RB!(5, 7);
        assert_eq!(with_field_ref(&a, &b), with_absorb(&a, &b));
        assert_eq!(with_absorb(&a, &b), RB!(3, 2) * RB!(5, 7) + RB!(3, 2));
    }

    /// Mixed narrow and wide arithmetic behind the same single bound.
    ///
    /// This is the shape a sparse inner product has, and the bound is stated once on the
    /// accumulator rather than once per narrow type the caller might bring.
    fn inner_product<W: AbsorbAll<N>, N>(column: &[(usize, N)], pi: &[W]) -> W {
        let mut total = W::zero();
        for (index, value) in column {
            total.add_mul_narrow(value, &pi[*index]);
        }
        total
    }

    #[test]
    fn inner_product_over_any_narrow_type() {
        let pi = [RB!(5), RB!(4), RB!(-1, 2)];

        // A marker column: no multiplication happens at all.
        assert_eq!(inner_product(&[(0, One), (2, One)], &pi), RB!(9, 2));
        assert_eq!(
            inner_product(&[(0, SignedOne::MinusOne), (1, SignedOne::PlusOne)], &pi),
            RB!(-1),
        );
        // A small rational column.
        let column = [(0, Rational64::new(1, 5).unwrap()), (1, Rational64::new(1, 2).unwrap())];
        assert_eq!(inner_product(&column, &pi), RB!(3));
        // An integer column.
        assert_eq!(inner_product(&[(1, 3_i64)], &pi), RB!(12));
        // A column of the wide type itself.
        assert_eq!(inner_product(&[(0, RB!(2))], &pi), RB!(10));
    }

    /// The trait is usable through a reference and an `Option`, which is how a sparse column of a
    /// matrix provider arrives.
    #[test]
    fn references_and_absent_values() {
        let pi = [RB!(5), RB!(4)];
        let column: Vec<(usize, Option<One>)> = vec![(0, Some(One)), (1, None)];
        assert_eq!(inner_product(&column, &pi), RB!(5));

        let stored = [One, One];
        let column: Vec<(usize, &One)> = vec![(0, &stored[0]), (1, &stored[1])];
        assert_eq!(inner_product(&column, &pi), RB!(9));
    }
}
