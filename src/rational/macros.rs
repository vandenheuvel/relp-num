/// Shorthand for creating a rational number in tests.
#[macro_export]
macro_rules! R8 {
    ($value:expr) => {
        <$crate::Rational8 as $crate::FromPrimitive>::from_f64($value as f64).unwrap()
    };
    ($numer:expr, $denom:expr) => {
        $crate::Rational8::new($numer, $denom)
    };
}

/// Shorthand for creating a rational number in tests.
#[macro_export]
macro_rules! R16 {
    ($value:expr) => {
        <$crate::Rational16 as $crate::FromPrimitive>::from_f64($value as f64).unwrap()
    };
    ($numer:expr, $denom:expr) => {
        $crate::Rational16::new($numer, $denom)
    };
}

/// Shorthand for creating a rational number in tests.
#[macro_export]
macro_rules! R32 {
    ($value:expr) => {
        <$crate::Rational32 as $crate::FromPrimitive>::from_f64($value as f64).unwrap()
    };
    ($numer:expr, $denom:expr) => {
        $crate::Rational32::new($numer, $denom)
    };
}

/// Shorthand for creating a rational number in tests.
#[macro_export]
macro_rules! R64 {
    ($value:expr) => {
        <$crate::Rational64 as $crate::FromPrimitive>::from_f64($value as f64).unwrap()
    };
    ($numer:expr, $denom:expr) => {
        $crate::Rational64::new($numer, $denom)
    };
}

/// Shorthand for creating a rational number in tests.
#[macro_export]
macro_rules! R128 {
    ($value:expr) => {
        <$crate::Rational128 as $crate::FromPrimitive>::from_f64($value as f64).unwrap()
    };
    ($numer:expr, $denom:expr) => {
        $crate::Rational128::new($numer, $denom)
    };
}

/// Shorthand for creating a rational number in tests.
#[macro_export]
macro_rules! RB {
    ($value:expr) => {
        <$crate::RationalBig as $crate::FromPrimitive>::from_f64($value as f64).unwrap()
    };
    ($numer:expr, $denom:expr) => {
        $crate::RationalBig::new($numer, $denom)
    };
}
