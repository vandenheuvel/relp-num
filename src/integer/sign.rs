//! # NonZero signs of integers
use std::cmp::Ordering;
use std::num::NonZero;

use crate::Negateable;
use crate::{NonZeroSign, NonZeroSigned};
use crate::Sign;
use crate::Signed;

macro_rules! unsigned {
    ($($ty:ty),+ $(,)?) => {$(
        impl Signed for $ty {
            #[inline]
            fn signum(&self) -> Sign {
                if *self == 0 {
                    Sign::Zero
                } else {
                    Sign::Positive
                }
            }
        }
    )+}
}

unsigned!(u8, u16, u32, u64, u128, usize);

macro_rules! signed {
    ($($ty:ty),+ $(,)?) => {$(
        impl Signed for $ty {
            #[inline]
            fn signum(&self) -> Sign {
                match self.cmp(&0) {
                    Ordering::Less => Sign::Negative,
                    Ordering::Equal => Sign::Zero,
                    Ordering::Greater => Sign::Positive,
                }
            }
        }

        impl Negateable for $ty {
            #[inline]
            #[track_caller]
            fn negate(&mut self) {
                // Two's complement has one more negative value than positive ones, so negating
                // `MIN` has no answer. Plain negation panics on it in debug and returns `MIN`
                // again in release, which leaves a value whose sign did not flip; checking makes
                // both profiles agree and keeps the wrong sign from escaping.
                match self.checked_neg() {
                    Some(negated) => *self = negated,
                    None => panic!(concat!("cannot negate ", stringify!($ty), "::MIN")),
                }
            }
        }
    )+}
}

signed!(i8, i16, i32, i64, i128, isize);

macro_rules! non_zero_unsigned {
    ($($ty:ty),+ $(,)?) => {$(
        impl Signed for NonZero<$ty> {
            #[inline]
            fn signum(&self) -> Sign {
                Sign::Positive
            }
        }

        /// The type cannot represent zero, so there is no failure case.
        impl NonZeroSigned for NonZero<$ty> {
            #[inline]
            fn non_zero_signum(&self) -> NonZeroSign {
                NonZeroSign::Positive
            }
        }
    )+}
}

non_zero_unsigned!(u8, u16, u32, u64, u128, usize);

macro_rules! non_zero_signed {
    ($($ty:ty),+ $(,)?) => {$(
        impl Signed for NonZero<$ty> {
            #[inline]
            fn signum(&self) -> Sign {
                if self.get() > 0 {
                    Sign::Positive
                } else {
                    Sign::Negative
                }
            }
        }

        impl Negateable for NonZero<$ty> {
            #[inline]
            #[track_caller]
            fn negate(&mut self) {
                // See the `signed!` macro: `MIN` has no negation. Wrapping would return `MIN`
                // again, which is still non zero and so still sound, but reports the sign it
                // started with.
                match self.get().checked_neg() {
                    Some(negated) => *self = unsafe {
                        // SAFETY: The negation of a non zero value is non zero.
                        NonZero::new_unchecked(negated)
                    },
                    None => panic!(concat!("cannot negate NonZero<", stringify!($ty), ">::MIN")),
                }
            }
        }

        /// The type cannot represent zero, so there is no failure case.
        impl NonZeroSigned for NonZero<$ty> {
            #[inline]
            fn non_zero_signum(&self) -> NonZeroSign {
                if self.get() > 0 {
                    NonZeroSign::Positive
                } else {
                    NonZeroSign::Negative
                }
            }
        }
    )+}
}

non_zero_signed!(i8, i16, i32, i64, i128, isize);

#[cfg(test)]
mod test {
    use std::num::{NonZeroI8, NonZeroU8};

    use crate::{Negateable, NonZeroSign, NonZeroSigned};

    #[test]
    fn test_zero_sign() {
        assert_eq!(1_u32.non_zero_signum(), NonZeroSign::Positive);
        assert_eq!(-1_u32.non_zero_signum(), NonZeroSign::Negative);

        assert_eq!(NonZeroU8::new(1).unwrap().non_zero_signum(), NonZeroSign::Positive);
        assert_eq!(NonZeroI8::new(1).unwrap().non_zero_signum(), NonZeroSign::Positive);
        assert_eq!(NonZeroI8::new(-1).unwrap().non_zero_signum(), NonZeroSign::Negative);
    }

    #[test]
    #[should_panic]
    fn test_non_zero_on_zero() {
        0_u32.non_zero_signum();
    }

    #[test]
    #[should_panic]
    fn test_non_zero_on_zero_signed() {
        0_i8.non_zero_signum();
    }

    /// Two's complement has no counterpart for `MIN`, so negating it has to fail rather than
    /// return `MIN` again with an unflipped sign, which is what release builds used to do.
    #[test]
    fn test_negate_minimum_panics() {
        macro_rules! check {
            ($ty:ty, $nz:ty) => {
                let mut value = <$ty>::MIN;
                assert!(std::panic::catch_unwind(move || value.negate()).is_err());

                let mut value = <$nz>::new(<$ty>::MIN).unwrap();
                assert!(std::panic::catch_unwind(move || value.negate()).is_err());

                // Everything else still negates, and twice is the identity
                for start in [<$ty>::MIN + 1, -1, 1, <$ty>::MAX] {
                    let mut value = start;
                    value.negate();
                    assert_eq!(value, -start, "{} {start}", stringify!($ty));
                    value.negate();
                    assert_eq!(value, start, "{} {start}", stringify!($ty));
                }
            }
        }

        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));

        check!(i8, std::num::NonZeroI8);
        check!(i16, std::num::NonZeroI16);
        check!(i32, std::num::NonZeroI32);
        check!(i64, std::num::NonZeroI64);
        check!(i128, std::num::NonZeroI128);
        check!(isize, std::num::NonZeroIsize);

        std::panic::set_hook(hook);
    }
}
