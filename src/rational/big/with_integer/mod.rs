use std::cmp::Ordering;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

use num_traits::{One, Zero};
use smallvec::SmallVec;

use crate::{Negateable, NonZero, NonZeroUbig, Sign, Ubig};
use crate::integer::big::ops::building_blocks::is_well_formed_non_zero;
use crate::integer::big::ops::non_zero::{add_assign, mul_non_zero, subtracting_cmp};
use crate::integer::big::ops::normalize::simplify_fraction_without_info;
use crate::rational::big::{Big, NonZeroBig};

mod small;

impl<const S: usize> Add<Ubig<S>> for Big<S> {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: Ubig<S>) -> Self::Output {
        AddAssign::add_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Add<&Ubig<S>> for Big<S> {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: &Ubig<S>) -> Self::Output {
        AddAssign::add_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> AddAssign<Ubig<S>> for Big<S> {
    #[inline]
    fn add_assign(&mut self, rhs: Ubig<S>) {
        // TODO(PERFORMANCE): Utilize ownership of `rhs`.
        AddAssign::add_assign(self, &rhs);
    }
}

impl<const S: usize> AddAssign<&Ubig<S>> for Big<S> {
    #[inline]
    fn add_assign(&mut self, rhs: &Ubig<S>) {
        if rhs.is_not_zero() {
            unsafe {
                // SAFETY: rhs is non zero
                self.add_assign_int_non_zero(rhs);
            }
        }
    }
}

impl<const S: usize> Add<NonZeroUbig<S>> for Big<S> {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: NonZeroUbig<S>) -> Self::Output {
        AddAssign::add_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Add<&NonZeroUbig<S>> for Big<S> {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: &NonZeroUbig<S>) -> Self::Output {
        AddAssign::add_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> AddAssign<NonZeroUbig<S>> for Big<S> {
    #[inline]
    fn add_assign(&mut self, rhs: NonZeroUbig<S>) {
        // TODO(PERFORMANCE): Utilize ownership of `rhs`.
        AddAssign::add_assign(self, &rhs);
    }
}

impl<const S: usize> AddAssign<&NonZeroUbig<S>> for Big<S> {
    #[inline]
    fn add_assign(&mut self, rhs: &NonZeroUbig<S>) {
        unsafe {
            // SAFETY: rhs is non zero
            self.add_assign_int_non_zero(rhs);
        }
    }
}

impl<const S: usize> Big<S> {
    #[inline]
    unsafe fn add_assign_int_non_zero(&mut self, rhs: &[usize]) {
        debug_assert!(is_well_formed_non_zero(rhs));

        match self.sign {
            Sign::Positive => {
                // SAFETY: A `NonZeroUbig` is never empty and always well formed, and the caller
                // guarantees the same of `rhs`. The `inner_mut` hands out the numerator's words;
                // adding a magnitude to a non zero numerator leaves it well formed and non zero,
                // and leaves the fraction in lowest terms, because the added term is a multiple of
                // the denominator and so shares no new factor with it.
                unsafe {
                    let difference = mul_non_zero::<S>(&self.denominator, rhs);
                    add_assign(self.numerator.inner_mut(), &difference)
                }
            },
            Sign::Zero => {
                // SAFETY: `rhs` is well formed and non zero by the caller's guarantee, so writing
                // it into the numerator and setting the sign to match leaves the value well
                // formed. The denominator is one for a zero value, so the fraction stays in
                // lowest terms.
                unsafe { *self.numerator.inner_mut() = SmallVec::from_slice(rhs) };
                self.sign = Sign::Positive;
                debug_assert!(self.denominator.is_one());
            }
            Sign::Negative => {
                // SAFETY: As in the positive arm. `subtracting_cmp` leaves the numerator holding
                // the magnitude of the difference, which may be zero; the match below restores the
                // sign, and with it the invariant, for each of the three outcomes.
                let ordering = unsafe {
                    let difference = mul_non_zero::<S>(&self.denominator, rhs);
                    subtracting_cmp(self.numerator.inner_mut(), &difference)
                };

                match ordering {
                    Ordering::Less => self.sign.negate(),
                    Ordering::Equal => self.set_zero(),
                    Ordering::Greater => {}
                }
            }
        }
    }
}

impl<const S: usize> Sub<Ubig<S>> for Big<S> {
    type Output = Self;

    #[inline]
    fn sub(mut self, rhs: Ubig<S>) -> Self::Output {
        SubAssign::sub_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Sub<&Ubig<S>> for Big<S> {
    type Output = Self;

    #[inline]
    fn sub(mut self, rhs: &Ubig<S>) -> Self::Output {
        SubAssign::sub_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> SubAssign<Ubig<S>> for Big<S> {
    #[inline]
    fn sub_assign(&mut self, rhs: Ubig<S>) {
        // TODO(PERFORMANCE): Utilize ownership of `rhs`.
        SubAssign::sub_assign(self, &rhs);
    }
}

impl<const S: usize> SubAssign<&Ubig<S>> for Big<S> {
    #[inline]
    fn sub_assign(&mut self, rhs: &Ubig<S>) {
        if rhs.is_not_zero() {
            unsafe {
                // SAFETY: rhs is non zero
                self.sub_assign_int_non_zero(rhs);
            }
        }
    }
}

impl<const S: usize> Sub<NonZeroUbig<S>> for Big<S> {
    type Output = Self;

    #[inline]
    fn sub(mut self, rhs: NonZeroUbig<S>) -> Self::Output {
        SubAssign::sub_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Sub<&NonZeroUbig<S>> for Big<S> {
    type Output = Self;

    #[inline]
    fn sub(mut self, rhs: &NonZeroUbig<S>) -> Self::Output {
        SubAssign::sub_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> SubAssign<NonZeroUbig<S>> for Big<S> {
    #[inline]
    fn sub_assign(&mut self, rhs: NonZeroUbig<S>) {
        // TODO(PERFORMANCE): Utilize ownership of `rhs`.
        SubAssign::sub_assign(self, &rhs);
    }
}

impl<const S: usize> SubAssign<&NonZeroUbig<S>> for Big<S> {
    #[inline]
    fn sub_assign(&mut self, rhs: &NonZeroUbig<S>) {
        unsafe {
            // SAFETY: rhs is non zero
            self.sub_assign_int_non_zero(rhs);
        }
    }
}

impl<const S: usize> Big<S> {
    #[inline]
    unsafe fn sub_assign_int_non_zero(&mut self, rhs: &[usize]) {
        debug_assert!(is_well_formed_non_zero(rhs));

        match self.sign {
            Sign::Positive => {
                // SAFETY: A `NonZeroUbig` is never empty and always well formed, and the caller
                // guarantees the same of `rhs`. The `inner_mut` hands out the numerator's words;
                // `subtracting_cmp` leaves it holding the magnitude of the difference, which may be
                // zero, and the match below restores the sign, and with it the invariant, for each
                // of the three outcomes.
                let ordering = unsafe {
                    let difference = mul_non_zero::<S>(&self.denominator, rhs);
                    subtracting_cmp(self.numerator.inner_mut(), &difference)
                };

                match ordering {
                    Ordering::Less => self.sign.negate(),
                    Ordering::Equal => self.set_zero(),
                    Ordering::Greater => {}
                }
            }
            Sign::Zero => {
                // SAFETY: `rhs` is well formed and non zero by the caller's guarantee, so writing
                // it into the numerator and setting the sign to match leaves the value well
                // formed. The denominator is one for a zero value, so the fraction stays in
                // lowest terms.
                unsafe { *self.numerator.inner_mut() = SmallVec::from_slice(rhs) };
                self.sign = Sign::Negative;
                debug_assert!(self.denominator.is_one());
            }
            Sign::Negative => {
                // SAFETY: As in the positive arm. Adding a magnitude to a non zero numerator leaves
                // it well formed and non zero, and leaves the fraction in lowest terms, because the
                // added term is a multiple of the denominator.
                unsafe {
                    let difference = mul_non_zero::<S>(&self.denominator, rhs);
                    add_assign(self.numerator.inner_mut(), &difference)
                }
            },
        }
    }
}

impl<const S: usize> Mul<Ubig<S>> for Big<S> {
    type Output = Self;

    #[inline]
    fn mul(mut self, rhs: Ubig<S>) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> MulAssign<Ubig<S>> for Big<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: Ubig<S>) {
        if !rhs.is_zero() {
            if self.is_not_zero() {
                // SAFETY: Every operand is well formed and not empty: `rhs` is non zero (by its type, or by
                // the check just above), and `self` is not zero, so its numerator is not either.
                // The two `inner_mut` calls hand out the words behind the lowest terms invariant,
                // which `mul_assign_int_owning` restores before returning.
                unsafe {
                    mul_assign_int_owning(
                        self.numerator.inner_mut(),
                        self.denominator.inner_mut(),
                        rhs.into_inner(),
                    );
                }
            }
        } else {
            self.set_zero();
        }
    }
}

impl<const S: usize> Mul<NonZeroUbig<S>> for Big<S> {
    type Output = Self;

    #[inline]
    fn mul(mut self, rhs: NonZeroUbig<S>) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> MulAssign<NonZeroUbig<S>> for Big<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: NonZeroUbig<S>) {
        if self.is_not_zero() {
            // SAFETY: Every operand is well formed and not empty: `rhs` is non zero (by its type, or by the
            // check just above), and `self` is not zero, so its numerator is not either. The two
            // `inner_mut` calls hand out the words behind the lowest terms invariant, which
            // `mul_assign_int_owning` restores before returning.
            unsafe {
                mul_assign_int_owning(
                    self.numerator.inner_mut(),
                    self.denominator.inner_mut(),
                    rhs.into_inner(),
                );
            }
        }
    }
}

impl<const S: usize> Mul<NonZeroUbig<S>> for NonZeroBig<S> {
    type Output = Self;

    #[inline]
    fn mul(mut self, rhs: NonZeroUbig<S>) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> MulAssign<NonZeroUbig<S>> for NonZeroBig<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: NonZeroUbig<S>) {
        // SAFETY: Every operand is well formed and not empty: `rhs` is non zero (by its type, or by the
        // check just above), and a `NonZeroBig` is never zero, so its numerator is not either. The
        // two `inner_mut` calls hand out the words behind the lowest terms invariant, which
        // `mul_assign_int_owning` restores before returning.
        unsafe {
            mul_assign_int_owning(
                self.numerator.inner_mut(),
                self.denominator.inner_mut(),
                rhs.into_inner(),
            );
        }
    }
}

impl<const S: usize> Mul<&NonZeroUbig<S>> for NonZeroBig<S> {
    type Output = Self;

    #[inline]
    fn mul(mut self, rhs: &NonZeroUbig<S>) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> MulAssign<&NonZeroUbig<S>> for NonZeroBig<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: &NonZeroUbig<S>) {
        // SAFETY: Every operand is well formed and not empty: `rhs` is non zero (by its type, or by the
        // check just above), and a `NonZeroBig` is never zero, so its numerator is not either. The
        // two `inner_mut` calls hand out the words behind the lowest terms invariant, which
        // `mul_assign_int` restores before returning.
        unsafe {
            mul_assign_int(
                self.numerator.inner_mut(),
                self.denominator.inner_mut(),
                rhs.inner(),
            );
        }
    }
}

impl<const S: usize> MulAssign<&NonZeroUbig<S>> for Big<S> {
    #[inline]
    fn mul_assign(&mut self, rhs: &NonZeroUbig<S>) {
        if self.is_not_zero() {
            // SAFETY: Every operand is well formed and not empty: `rhs` is non zero (by its type, or by the
            // check just above), and `self` is not zero, so its numerator is not either. The two
            // `inner_mut` calls hand out the words behind the lowest terms invariant, which
            // `mul_assign_int` restores before returning.
            unsafe {
                mul_assign_int(
                    self.numerator.inner_mut(),
                    self.denominator.inner_mut(),
                    rhs.inner(),
                );
            }
        }
    }
}

impl<const S: usize> Div<NonZeroUbig<S>> for Big<S> {
    type Output = Self;

    #[inline]
    fn div(mut self, rhs: NonZeroUbig<S>) -> Self::Output {
        DivAssign::div_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> DivAssign<NonZeroUbig<S>> for Big<S> {
    #[inline]
    fn div_assign(&mut self, rhs: NonZeroUbig<S>) {
        if self.is_not_zero() {
            // SAFETY: Every operand is well formed and not empty: `rhs` is non zero (by its type, or by the
            // check just above), and `self` is not zero, so its numerator is not either. The two
            // `inner_mut` calls hand out the words behind the lowest terms invariant, which
            // `mul_assign_int_owning` restores before returning. The numerator and denominator are
            // passed the other way around, because dividing a fraction by an integer is multiplying
            // its denominator by it.
            unsafe {
                mul_assign_int_owning(
                    self.denominator.inner_mut(),
                    self.numerator.inner_mut(),
                    rhs.into_inner(),
                );
            }
        }
    }
}

impl<const S: usize> DivAssign<&NonZeroUbig<S>> for Big<S> {
    #[inline]
    fn div_assign(&mut self, rhs: &NonZeroUbig<S>) {
        if self.is_not_zero() {
            // SAFETY: Every operand is well formed and not empty: `rhs` is non zero (by its type, or by the
            // check just above), and `self` is not zero, so its numerator is not either. The two
            // `inner_mut` calls hand out the words behind the lowest terms invariant, which
            // `mul_assign_int` restores before returning. The numerator and denominator are passed
            // the other way around, because dividing a fraction by an integer is multiplying its
            // denominator by it.
            unsafe {
                mul_assign_int(
                    self.denominator.inner_mut(),
                    self.numerator.inner_mut(),
                    rhs.inner(),
                );
            }
        }
    }
}

impl<const S: usize> Div<Ubig<S>> for Big<S> {
    type Output = Self;

    #[inline]
    fn div(mut self, rhs: Ubig<S>) -> Self::Output {
        DivAssign::div_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> DivAssign<Ubig<S>> for Big<S> {
    #[inline]
    fn div_assign(&mut self, rhs: Ubig<S>) {
        if !rhs.is_zero() {
            if self.is_not_zero() {
                // SAFETY: Every operand is well formed and not empty: `rhs` is non zero (by its type, or by
                // the check just above), and `self` is not zero, so its numerator is not either.
                // The two `inner_mut` calls hand out the words behind the lowest terms invariant,
                // which `mul_assign_int_owning` restores before returning. The numerator and
                // denominator are passed the other way around, because dividing a fraction by an
                // integer is multiplying its denominator by it.
                unsafe {
                    mul_assign_int_owning(
                        self.denominator.inner_mut(),
                        self.numerator.inner_mut(),
                        rhs.into_inner(),
                    );
                }
            }
        } else {
            panic!("attempt to divide by zero");
        }
    }
}

impl<const S: usize> Div<NonZeroUbig<S>> for NonZeroBig<S> {
    type Output = Self;

    #[inline]
    fn div(mut self, rhs: NonZeroUbig<S>) -> Self::Output {
        DivAssign::div_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> DivAssign<NonZeroUbig<S>> for NonZeroBig<S> {
    #[inline]
    fn div_assign(&mut self, rhs: NonZeroUbig<S>) {
        // SAFETY: Every operand is well formed and not empty: `rhs` is non zero (by its type, or by the
        // check just above), and a `NonZeroBig` is never zero, so its numerator is not either. The
        // two `inner_mut` calls hand out the words behind the lowest terms invariant, which
        // `mul_assign_int_owning` restores before returning. The numerator and denominator are
        // passed the other way around, because dividing a fraction by an integer is multiplying its
        // denominator by it.
        unsafe {
            mul_assign_int_owning(
                self.denominator.inner_mut(),
                self.numerator.inner_mut(),
                rhs.into_inner(),
            );
        }
    }
}

impl<const S: usize> Div<&NonZeroUbig<S>> for NonZeroBig<S> {
    type Output = Self;

    #[inline]
    fn div(mut self, rhs: &NonZeroUbig<S>) -> Self::Output {
        DivAssign::div_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> DivAssign<&NonZeroUbig<S>> for NonZeroBig<S> {
    #[inline]
    fn div_assign(&mut self, rhs: &NonZeroUbig<S>) {
        // SAFETY: Every operand is well formed and not empty: `rhs` is non zero (by its type, or by the
        // check just above), and a `NonZeroBig` is never zero, so its numerator is not either. The
        // two `inner_mut` calls hand out the words behind the lowest terms invariant, which
        // `mul_assign_int` restores before returning. The numerator and denominator are passed the
        // other way around, because dividing a fraction by an integer is multiplying its
        // denominator by it.
        unsafe {
            mul_assign_int(
                self.denominator.inner_mut(),
                self.numerator.inner_mut(),
                rhs.inner(),
            );
        }
    }
}

#[inline]
unsafe fn mul_assign_int<const S: usize>(
    left_numerator: &mut SmallVec<[usize; S]>, left_denominator: &mut SmallVec<[usize; S]>,
    right: &[usize],
) {
    debug_assert!(is_well_formed_non_zero(left_numerator));
    debug_assert!(is_well_formed_non_zero(left_denominator));
    debug_assert!(is_well_formed_non_zero(right));

    // SAFETY: All three operands are well formed and not empty, so the product is too, which is
    // what the simplification then needs of both of its operands.
    unsafe {
        *left_numerator = mul_non_zero(left_numerator, right);
        simplify_fraction_without_info(left_numerator, left_denominator);
    }
}

#[inline]
unsafe fn mul_assign_int_owning<const S: usize>(
    left_numerator: &mut SmallVec<[usize; S]>, left_denominator: &mut SmallVec<[usize; S]>,
    mut right: SmallVec<[usize; S]>,
) {
    debug_assert!(is_well_formed_non_zero(left_numerator));
    debug_assert!(is_well_formed_non_zero(left_denominator));
    debug_assert!(is_well_formed_non_zero(&right));

    // SAFETY: All three operands are well formed and not empty. The simplification cancels the
    // denominator against the integer before the multiplication rather than after, and leaves both
    // of them well formed and not empty, so the product that follows is well defined too.
    unsafe {
        simplify_fraction_without_info(left_denominator, &mut right);
        *left_numerator = mul_non_zero(left_numerator, &right);
    }
}

#[cfg(test)]
mod test {
    use std::ops::DivAssign;

    use num_traits::{One, Zero};

    use crate::{NonZeroUbig, RationalBig, Ubig};
    use crate::rational::big::NonZeroBig;
    use crate::RB;

    #[test]
    fn add() {
        assert_eq!(RB!(2, 3) + NonZeroUbig::new(2).unwrap(), RB!(8, 3));
        assert_eq!(RB!(-2, 3) + NonZeroUbig::new(2).unwrap(), RB!(4, 3));
        assert_eq!(RB!(2, 3) + Ubig::zero(), RB!(2, 3));
        assert_eq!(RB!(2, 3) - NonZeroUbig::new(2).unwrap(), RB!(-4, 3));
        assert_eq!(RB!(0) - NonZeroUbig::one(), RB!(-1));
        assert_eq!(RB!(-2, 3) - NonZeroUbig::new(2).unwrap(), RB!(-8, 3));
    }

    #[test]
    fn mul_assign() {
        assert_eq!(RB!(2, 3) * NonZeroUbig::new(2).unwrap(), RB!(4, 3));
        assert_eq!(RB!(2, 3) * Ubig::zero(), RB!(0));
        assert_eq!(RB!(2, 3) / NonZeroUbig::new(2).unwrap(), RB!(1, 3));
        assert_eq!(RB!(0) * NonZeroUbig::one(), RB!(0));
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn mul_panic() {
        RationalBig::one() / Ubig::zero();
    }

    /// `-a / b + n` can cancel exactly: `subtracting_cmp` then returns `Ordering::Equal` and leaves
    /// the numerator empty, so the sign has to be reset as well.
    #[test]
    fn add_int_cancelling_to_zero() {
        let mut x = RB!(-5);
        x += NonZeroUbig::new(5).unwrap();
        assert!(x.is_zero());
        assert_eq!(x, RB!(0));
        assert_eq!(format!("{:?}", x), "0");

        let mut y = RB!(-5);
        y += Ubig::new(5);
        assert!(y.is_zero());
        assert_eq!(y, RB!(0));
        assert_eq!(format!("{:?}", y), "0");
    }

    /// See `add_int_cancelling_to_zero`, the mirrored case `a / b - n`.
    #[test]
    fn sub_int_cancelling_to_zero() {
        let mut x = RB!(5);
        x -= NonZeroUbig::new(5).unwrap();
        assert!(x.is_zero());
        assert_eq!(x, RB!(0));
        assert_eq!(format!("{:?}", x), "0");

        let mut y = RB!(5);
        y -= Ubig::new(5);
        assert!(y.is_zero());
        assert_eq!(y, RB!(0));
        assert_eq!(format!("{:?}", y), "0");
    }

    /// Adding to zero has to set the sign, just like subtracting from zero does.
    #[test]
    fn add_int_to_zero_sets_sign() {
        let mut x = RB!(0);
        x += NonZeroUbig::new(5).unwrap();
        assert!(!x.is_zero());
        assert_eq!(x, RB!(5));
        assert_eq!(format!("{:?}", x), "5");

        let mut y = RB!(0);
        y += Ubig::new(5);
        assert!(!y.is_zero());
        assert_eq!(y, RB!(5));
        assert_eq!(format!("{:?}", y), "5");
    }

    /// `Div` on `NonZeroBig` should divide, not multiply.
    #[test]
    fn div_non_zero_big_by_non_zero_ubig() {
        let two = NonZeroUbig::new(2).unwrap();

        let mut expected = NonZeroBig::<8>::one();
        DivAssign::div_assign(&mut expected, two.clone());

        let owned = NonZeroBig::<8>::one() / two.clone();
        assert!(owned == expected);
        assert!(owned * two.clone() == NonZeroBig::<8>::one());

        let borrowed = NonZeroBig::<8>::one() / &two;
        assert!(borrowed == expected);
        assert!(borrowed * &two == NonZeroBig::<8>::one());
    }

    /// Dividing zero by a `Ubig` should be a no-op instead of touching the empty numerator.
    #[test]
    fn div_zero_by_ubig() {
        let mut x = RB!(0);
        x /= Ubig::<8>::new(2);
        assert!(x.is_zero());
        assert_eq!(x, RB!(0));
        assert_eq!(format!("{:?}", x), "0");

        let y = RB!(0) / Ubig::<8>::new(2);
        assert!(y.is_zero());
        assert_eq!(y, RB!(0));
    }
}
