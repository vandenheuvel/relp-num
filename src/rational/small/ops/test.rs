use crate::{NonZeroSign, Sign, R16};
use crate::rational::small::{NonZeroRational8, Rational64, Rational8};

#[test]
fn mul() {
    let mut x = R16!(21, 1);
    x *= &R16!(1, 7);
    assert_eq!(x, R16!(3));
}

/// The `R8!` macro only reaches `i8`, and these cases need the whole `u8` range.
fn r8(sign: Sign, numerator: u8, denominator: u8) -> Rational8 {
    Rational8::new_signed(sign, numerator, denominator).unwrap()
}

/// Bringing two fractions to a common denominator must not wrap.
///
/// Every case below has a result the type represents without trouble, and every one of them came
/// out wrong in release before: the intermediates were computed in the storage type, so `255 * 2`
/// wrapped and took the answer with it. Two of them came out with the wrong sign as well.
#[test]
fn add_sub_does_not_wrap() {
    use Sign::{Negative, Positive};

    assert_eq!(r8(Positive, 255, 2) + r8(Positive, 255, 2), r8(Positive, 255, 1));
    assert_eq!(r8(Positive, 32, 1) - r8(Positive, 7, 8), r8(Positive, 249, 8));
    assert_eq!(r8(Positive, 3, 8) - r8(Positive, 32, 1), r8(Negative, 253, 8));
    assert_eq!(r8(Positive, 87, 2) - r8(Positive, 5, 3), r8(Positive, 251, 6));
    assert_eq!(r8(Positive, 49, 6) + r8(Positive, 7, 10), r8(Positive, 133, 15));

    // Not specific to the narrowest type: `2 ** 61 - 7 / 8` used to return `-7 / 8`
    let left = Rational64::new_signed(Positive, 1 << 61, 1).unwrap();
    let right = Rational64::new_signed(Positive, 7, 8).unwrap();
    let expected = Rational64::new_signed(Positive, 18_446_744_073_709_551_609, 8).unwrap();
    assert_eq!(left - right, expected);
}

/// A result the type cannot represent has to be refused, never silently wrapped.
#[test]
#[should_panic(expected = "not representable")]
fn add_unrepresentable_panics() {
    // `256 / 15`, whose numerator does not fit
    let _ = r8(Sign::Positive, 1, 1) + r8(Sign::Positive, 241, 15);
}

/// Multiplying denominators can overflow to exactly zero, which poisons the value: `to_i8` then
/// divides by it and panics, `Display` writes `1/0`, and `Ord` reads it as zero.
#[test]
#[should_panic(expected = "not representable")]
fn div_to_zero_denominator_panics() {
    let _ = r8(Sign::Positive, 1, 2) / r8(Sign::Positive, 128, 1);
}

/// Exact cancellation has to produce a canonical zero, sign included.
///
/// The general branch used to report `SignChange::None` for a numerator that had just become zero,
/// leaving a value with a live sign that `is_zero` called non zero and that compared both greater
/// than zero and smaller than every positive value.
#[test]
fn cancellation_is_canonical_zero() {
    for (numerator, denominator) in [(1_u8, 3_u8), (7, 8), (255, 254), (1, 1), (128, 127)] {
        let value = r8(Sign::Positive, numerator, denominator);
        let zero = value - value;

        assert_eq!(zero.sign, Sign::Zero, "{numerator}/{denominator}");
        assert_eq!(zero.numerator, 0, "{numerator}/{denominator}");
        assert_eq!(zero.denominator, 1, "{numerator}/{denominator}");
        assert!(<Rational8 as num_traits::Zero>::is_zero(&zero), "{numerator}/{denominator}");
        assert!(!crate::NonZero::is_not_zero(&zero), "{numerator}/{denominator}");
    }
}

/// A non zero type cannot hold the zero an exact cancellation produces, so it panics.
///
/// The message used to say "attempt to add with overflow", which names the wrong cause: nothing
/// overflowed, the two magnitudes were simply equal.
#[test]
#[should_panic(expected = "is zero, which NonZeroRational8 cannot represent")]
fn non_zero_cancellation_panics() {
    let mut left = NonZeroRational8 { sign: NonZeroSign::Positive, numerator: 1, denominator: 2 };
    let right = NonZeroRational8 { sign: NonZeroSign::Negative, numerator: 1, denominator: 2 };
    left += right;
}
