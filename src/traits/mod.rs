//! # Traits
//!
//! A hierarchy of number types is defined. The hierarchy is "mathematically exact", but the
//! implementations aren't. That is, the contracts that these traits define, or their names imply,
//! may not be kept precisely. This is due to finite representation of these numbers and is a
//! fundamental problem that cannot be avoided, but perhaps be dealt with differently.
use std::fmt::{Debug, Display};
use std::iter::Sum;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::non_zero::NonZeroSigned;

mod absorb;
pub use absorb::Absorb;
pub use absorb::AbsorbAll;

pub mod factorization;

/// The simplex algorithm is defined over the ordered fields.
///
/// All methods containing algorithmic logic should be defined to work an ordered field (or a field,
/// if they don't need the ordering). All methods representing a matrix should be defined over a
/// field, because they don't need the additional ordering.
pub trait OrderedField: Ord + NonZeroSigned + Field {}
impl<T: Ord + NonZeroSigned + Field> OrderedField for T {}

/// A reference to an ordered field.
pub trait OrderedFieldRef<Deref>: Ord + FieldRef<Deref> {}
impl<Deref, T: Ord + FieldRef<Deref>> OrderedFieldRef<Deref> for T {}

/// Basic field operations with Self and with references to Self.
///
/// This trait is deliberately **not** blanket-implemented over its bounds. The primitive integers
/// satisfy every one of them, but `i32` is not a field: its division truncates. Because this crate
/// exists to give the simplex method exact arithmetic, a type that silently rounds must not be
/// usable where a field is required. Implement it explicitly for types whose four operations are
/// exact.
pub trait Field:
    Eq + // Equivalence relation
    PartialOrd +
    num_traits::Zero + // Additive identity
    Neg<Output=Self> + // Additive inverse
    num_traits::One + // Multiplicative identity
    // First operation
    Add<Self, Output=Self> +
    for<'r> Add<&'r Self, Output=Self> +
    AddAssign<Self> +
    for<'r> AddAssign<&'r Self> +
    Sum +
    // First operation inverse
    Sub<Self, Output=Self> +
    for<'r> Sub<&'r Self, Output=Self> +
    SubAssign<Self> +
    for<'r> SubAssign<&'r Self> +
    // Second operation
    Mul<Self, Output=Self> +
    for<'r> Mul<&'r Self, Output=Self> +
    MulAssign<Self> +
    for<'r> MulAssign<&'r Self> +
    // Second operation inverse
    Div<Self, Output=Self> +
    for<'r> Div<&'r Self, Output=Self> +
    DivAssign<Self> +
    for<'r> DivAssign<&'r Self> +
    // A fused multiply-add lives on `Absorb` instead, as `add_mul_narrow`. It belongs with the
    // mixed-type operations rather than here: what makes fusing worth anything is a narrow factor
    // that is one, where there is no multiplication to fuse and no intermediate to avoid.

    // Practicalities
    Clone +
    Display +
    Debug +
{}
// No blanket impl: see the note on `Field` above.

/// A reference to a variable that is in a `Field`.
///
/// # On writing this down less often
///
/// Generic code needs `F: Field, for<'r> &'r F: FieldRef<F>`, and the second half is the awkward
/// one. Moving it onto the definition of `Field`, as `trait Field where for<'r> &'r Self:
/// FieldRef<Self>`, does not help and makes things worse: a where clause on a type that is not
/// `Self` is a requirement on implementors, not something a `F: Field` bound implies, so every
/// caller still has to discharge it, and now has to do so even when it uses no reference
/// operations at all.
///
/// What does work is not having a reference type to bound. [`AbsorbAll`](crate::AbsorbAll) takes
/// every operand by reference already, so `F: AbsorbAll<F>` is a single bound with no higher
/// ranked part and gives the same arithmetic through methods rather than operators. This trait
/// stays for code written against the operators.
pub trait FieldRef<Deref>:
    // Equivalence relation
    PartialEq<Self> +
    Neg<Output=Deref> +  // Additive inverse
    // First operation
    Add<Deref, Output=Deref> +
    Add<Output=Deref> +
    // First operation inverse
    Sub<Deref, Output=Deref> +
    Sub<Output=Deref> +
    // Second operation
    Mul<Deref, Output=Deref> +
    Mul<Output=Deref> +
    // Second operation inverse
    Div<Deref, Output=Deref> +
    Div<Output=Deref> +
    // TODO: MulAdd should be possible. Only in specialization?
    //  + MulAdd

    // Practicalities
    Copy +
    Clone +
    Display +
    Debug +
    // Necessary for the Add, Sub, Mul and Div traits. References are sized anyways.
    Sized +
{}
impl<Deref, T> FieldRef<Deref> for T where T:
    // Equivalence relation
    PartialEq<Self> +
    Neg<Output=Deref> +  // Additive inverse
    // First operation
    Add<Deref, Output=Deref> +
    Add<Output=Deref> +
    // First operation inverse
    Sub<Deref, Output=Deref> +
    Sub<Output=Deref> +
    // Second operation
    Mul<Deref, Output=Deref> +
    Mul<Output=Deref> +
    // Second operation inverse
    Div<Deref, Output=Deref> +
    Div<Output=Deref> +
    // TODO: MulAdd should be possible. Only in specialization?
    //  + MulAdd

    // Practicalities
    Copy +
    Clone +
    Display +
    Debug +
    // Necessary for the Add, Sub, Mul and Div traits. References are sized anyways.
    Sized +
{}

/// Absolute value of a number.
///
/// The default body compares against the additive identity and negates. Types that carry their
/// sign separately, such as the crate's rational types, override it with a sign field write
/// and never touch the magnitude. This trait is deliberately not blanket-implemented: a blanket
/// impl would make that override impossible.
pub trait Abs: Neg<Output=Self> + Ord + num_traits::Zero {
    /// The absolute value of a number.
    ///
    /// Compute the additive inverse if the number is smaller than the additive identity.
    fn abs(self) -> Self {
        if self < Self::zero() {
            -self
        } else {
            self
        }
    }
}

macro_rules! abs_by_negation {
    ($($t:ty),+ $(,)?) => {$(
        impl Abs for $t {
            /// # Panics
            ///
            /// In debug builds, when called on the most negative representable value, whose
            /// absolute value does not fit in the type.
            #[inline]
            fn abs(self) -> Self {
                <$t>::abs(self)
            }
        }
    )+}
}
abs_by_negation!(i8, i16, i32, i64, i128, isize);

impl Abs for crate::fixed::Zero {
    #[inline]
    fn abs(self) -> Self {
        self
    }
}

/// Helper macro for tests.
#[macro_export]
macro_rules! F {
    ($value:expr) => {
        {
            <F as $crate::FromPrimitive>::from_f64($value as f64).unwrap()
        }
    };
}
