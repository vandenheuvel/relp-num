//! # NonZero values
//!
//! Relp often works with sparse structures where many values are zero.
use std::num::{NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize};
use std::num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize};

/// # Nonzero values
///
/// In contexts where this trait is required, implementors should not have value zero.
///
/// This trait is used for debug asserts. Values in sparse data structures should never be zero, and
/// requiring that they implement `num_traits::Zero` prohibits writing number types that can't
/// represent the value 0.
///
/// The `num_traits::Zero` trait is for types that can be zero, this trait is for types that can be
/// a value other than zero. They may or may not be able to represent zero.
pub trait NonZero {
    /// Whether the value is not equal to zero.
    ///
    /// Should always be `true` in the context in which it is called.
    fn is_not_zero(&self) -> bool;
}

macro_rules! could_be_zero {
    ($t:ty) => {
        impl NonZero for $t {
            #[must_use]
            #[inline]
            fn is_not_zero(&self) -> bool {
                !num_traits::Zero::is_zero(self)
            }
        }
    }
}

could_be_zero!(i8);
could_be_zero!(u8);
could_be_zero!(i16);
could_be_zero!(u16);
could_be_zero!(i32);
could_be_zero!(u32);
could_be_zero!(i64);
could_be_zero!(u64);
could_be_zero!(i128);
could_be_zero!(u128);
could_be_zero!(isize);
could_be_zero!(usize);
could_be_zero!(f32);
could_be_zero!(f64);

/// Consider the tuple a ratio (hence the debug assert).
macro_rules! could_be_zero_tuple {
    ($t:ty) => {
        impl NonZero for ($t, $t) {
            #[must_use]
            #[inline]
            fn is_not_zero(&self) -> bool {
                debug_assert!(self.1.is_not_zero());

                self.0.is_not_zero()
            }
        }
    }
}

could_be_zero_tuple!(i8);
could_be_zero_tuple!(u8);
could_be_zero_tuple!(i16);
could_be_zero_tuple!(u16);
could_be_zero_tuple!(i32);
could_be_zero_tuple!(u32);
could_be_zero_tuple!(i64);
could_be_zero_tuple!(u64);
could_be_zero_tuple!(i128);
could_be_zero_tuple!(u128);
could_be_zero_tuple!(isize);
could_be_zero_tuple!(usize);
could_be_zero_tuple!(f32);
could_be_zero_tuple!(f64);

macro_rules! can_not_be_zero {
    ($t:ty) => {
        impl NonZero for $t {
            #[must_use]
            #[inline]
            fn is_not_zero(&self) -> bool {
                true
            }
        }
    }
}

can_not_be_zero!(NonZeroI8);
can_not_be_zero!(NonZeroI16);
can_not_be_zero!(NonZeroI32);
can_not_be_zero!(NonZeroI64);
can_not_be_zero!(NonZeroI128);
can_not_be_zero!(NonZeroIsize);
can_not_be_zero!(NonZeroU8);
can_not_be_zero!(NonZeroU16);
can_not_be_zero!(NonZeroU32);
can_not_be_zero!(NonZeroU64);
can_not_be_zero!(NonZeroU128);
can_not_be_zero!(NonZeroUsize);
