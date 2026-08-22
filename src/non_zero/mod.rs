//! # NonZero values
//!
//! Relp often works with sparse structures where many values are zero.
pub use sign::NonZeroSign as NonZeroSign;
pub use sign::NonZeroSigned as NonZeroSigned;

pub mod sign;

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
    ($($t:ty),+ $(,)?) => {$(
        impl NonZero for $t {
            #[inline]
            fn is_not_zero(&self) -> bool {
                !num_traits::Zero::is_zero(self)
            }
        }
    )+}
}

could_be_zero!(i8, i16, i32, i64, i128, isize);
could_be_zero!(u8, u16, u32, u64, u128, usize);
could_be_zero!(f32, f64);

/// The `std` counterparts, which state the same thing in their type.
///
/// Spelled `std::num::NonZero<..>` rather than imported, because the name would otherwise clash
/// with the trait being implemented.
macro_rules! can_not_be_zero {
    ($($t:ty),+ $(,)?) => {$(
        impl NonZero for std::num::NonZero<$t> {
            #[inline]
            fn is_not_zero(&self) -> bool {
                true
            }
        }
    )+}
}

can_not_be_zero!(i8, i16, i32, i64, i128, isize);
can_not_be_zero!(u8, u16, u32, u64, u128, usize);
