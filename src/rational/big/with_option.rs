//! # Non-standard impl<const S: usize>ementations
//!
//! Operations with specific types from this crate.
use std::ops::Add;
use std::ops::Mul;

use crate::rational::big::Big;

impl<const S: usize> Add<Option<&Big<S>>> for Big<S> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Option<&Big<S>>) -> Self::Output {
        match rhs {
            None => self,
            Some(rhs) => Add::add(self, rhs),
        }
    }
}

impl<const S: usize> Add<Option<&Big<S>>> for &Big<S> {
    type Output = Big<S>;

    #[inline]
    fn add(self, rhs: Option<&Big<S>>) -> Self::Output {
        match rhs {
            None => self.clone(),
            Some(rhs) => Add::add(self, rhs),
        }
    }
}

impl<const S: usize> Mul<Option<&Big<S>>> for Big<S> {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Option<&Big<S>>) -> Self::Output {
        match rhs {
            None => num_traits::Zero::zero(),
            Some(rhs) => Mul::mul(self, rhs),
        }
    }
}

impl<const S: usize> Mul<Option<&Big<S>>> for &Big<S> {
    type Output = Big<S>;

    #[inline]
    fn mul(self, rhs: Option<&Big<S>>) -> Self::Output {
        match rhs {
            None => <Big<S> as num_traits::Zero>::zero(),
            Some(rhs) => Mul::mul(self, rhs)
        }
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::{Binary, One};
    use crate::rational::big::Big8;
    use crate::RB;

    #[test]
    fn test_one() {
        assert_eq!(RB!(0) + One, RB!(1));
        assert_eq!(RB!(0) - One, RB!(-1));
        assert_eq!(RB!(1) + One, RB!(2));
        assert_eq!(RB!(-1) + One, RB!(0));
        assert_eq!(RB!(-1) - One, RB!(-2));
        assert_eq!(RB!(1) - One, RB!(0));
        assert_eq!(RB!(1, 2) - One, RB!(-1, 2));
        assert_eq!(RB!(1, 2) + One, RB!(3, 2));
        assert_eq!(RB!(618, 648) / &One, RB!(618, 648));

        let x = Big8::from_str("68498984987984986896468746354684684684968/68468465468464168545346854646").unwrap();
        let expected = Big8::from_str("68498984988053455361937210523230031539614/68468465468464168545346854646").unwrap();
        assert_eq!(x + One, expected);

        let x = Big8::from_str("68468465468464168545346854645/68468465468464168545346854646").unwrap();
        let expected = Big8::from_str("-1/68468465468464168545346854646").unwrap();
        assert_eq!(x - One, expected);

        let x = Big8::from_str("-6868468468468465168186546846416565994998987468465468464168545346854644/6868468468468465168186546846416565994998987468465468464168545346854645").unwrap();
        let expected = Big8::from_str("1/6868468468468465168186546846416565994998987468465468464168545346854645").unwrap();
        assert_eq!(x + One, expected);
    }

    #[test]
    fn test_binary() {
        assert_eq!(RB!(135, 6848) * Binary::Zero, RB!(0));
        assert_eq!(RB!(135, 6848) * Binary::One, RB!(135, 6848));
        assert_eq!(RB!(135, 6848) + Binary::One, RB!(135 + 6848, 6848));
        assert_eq!(RB!(135, 6848) + Binary::Zero, RB!(135, 6848));
        assert_eq!(RB!(0) + Binary::Zero, RB!(0));
    }
}
