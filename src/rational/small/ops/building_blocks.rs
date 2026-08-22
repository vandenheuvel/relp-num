//! # Arithmetic on the magnitudes of fixed width rationals
//!
//! Every operation here works on a coprime numerator and denominator pair and leaves another such
//! pair behind. The sign lives with the caller.
//!
//! ## Why the intermediates are computed one type wider
//!
//! Bringing `a / b` and `c / d` to a common denominator forms `a * (d / g)`, `c * (b / g)` and
//! `(b / g) * d`, where `g` is `gcd(b, d)`. Each of those products can be as large as `MAX * MAX`
//! even when the reduced answer is small, so computing them in the storage type wraps: in release
//! `R8!(255, 2) + R8!(255, 2)` used to return `127` where the answer `255` fits without trouble.
//!
//! Computing them in `$wide` instead is not just an improvement, it is exact and complete: it gets
//! every representable result right and detects every unrepresentable one. Two facts make that
//! work. The common denominator `(b / g) * d` is at most `MAX * MAX` and so always fits `$wide`.
//! And the unreduced numerator `t` is coprime to both `b / g` and `d / g` by construction, so the
//! only factor it can share with the common denominator divides `g` — see [`$reduce_name`]. A
//! representable result therefore has `t <= MAX * g <= MAX * MAX`, which means a `t` that does not
//! fit `$wide` was never going to be representable, and rejecting it loses nothing.
//!
//! ## The widest type
//!
//! `u128` has no wider type here, so `$wide` is `u128` again and the products are merely checked.
//! `Rational128` is therefore the one width that can refuse a result it could have represented,
//! namely one whose intermediates need more than 128 bits. It never returns a wrong answer, which
//! is the property that matters; lifting the restriction needs 256 bit intermediates.
//!
//! ## Unrepresentable results panic
//!
//! Returning a wrapped number from an exact arithmetic library is the one outcome that cannot be
//! defended, and debug builds already panicked on these paths. Release builds now agree with them.

use std::cmp::min;
use std::cmp::Ordering;
use std::mem;

pub enum SignChange {
    None,
    Flip,
    Zero,
}

macro_rules! rational {
    (
        $add_name:ident, $sub_name:ident, $common_name:ident, $reduce_name:ident,
        $mul_name: ident, $uty:ty, $wide:ty, $gcd_name:ident, $simplify_name:ident
    ) => {
        /// Bring two fractions over a common denominator, in a type the products fit.
        ///
        /// Returns the two scaled numerators, the common denominator `lcm(b, d)`, and the `g` that
        /// [`$reduce_name`] needs: a bound on the factors the result can still be reduced by.
        #[inline]
        #[allow(clippy::unnecessary_cast, reason = "`$wide` is `$uty` for the widest type")]
        fn $common_name(
            left_numerator: $uty, left_denominator: $uty,
            right_numerator: $uty, right_denominator: $uty,
        ) -> ($wide, $wide, $wide, $uty) {
            debug_assert_ne!(left_denominator, 0);
            debug_assert_ne!(right_denominator, 0);

            // Only reachable for the widest type, where `$wide` does not actually widen.
            #[inline]
            fn multiply(left: $uty, right: $uty) -> $wide {
                match (left as $wide).checked_mul(right as $wide) {
                    Some(product) => product,
                    None => panic!(concat!(
                        "an intermediate value of this ", stringify!($uty),
                        " rational operation does not fit ", stringify!($wide),
                    )),
                }
            }

            if left_denominator == right_denominator {
                // Already common. Anything the sum or difference shares with the denominator
                // divides the denominator, which is what the last field is for.
                (
                    left_numerator as $wide,
                    right_numerator as $wide,
                    left_denominator as $wide,
                    left_denominator,
                )
            } else if left_denominator == 1 {
                // `(a * d +- c) / d` is already in lowest terms: it is congruent to `+-c` modulo
                // `d`, and `c` is coprime to `d`. A `g` of one says there is nothing to divide out.
                (
                    multiply(left_numerator, right_denominator),
                    right_numerator as $wide,
                    right_denominator as $wide,
                    1,
                )
            } else if right_denominator == 1 {
                // Mirror of the previous branch, coprime for the same reason.
                (
                    left_numerator as $wide,
                    multiply(right_numerator, left_denominator),
                    left_denominator as $wide,
                    1,
                )
            } else {
                let g = $gcd_name(left_denominator, right_denominator);
                let left_over_g = left_denominator / g;

                (
                    multiply(left_numerator, right_denominator / g),
                    multiply(right_numerator, left_over_g),
                    // `lcm(b, d)`, at most `MAX * MAX`
                    multiply(left_over_g, right_denominator),
                    g,
                )
            }
        }

        /// Reduce a fraction over a common denominator and narrow it back to the storage type.
        ///
        /// `g` bounds what is left to divide out, as produced by [`$common_name`]. The numerator is
        /// coprime to `b / g` and to `d / g`, so every prime it shares with `(b / g) * d` divides
        /// `g` with the same multiplicity, which makes `gcd(numerator, g)` the full common factor
        /// and keeps the search inside the narrow type.
        ///
        /// # Panics
        ///
        /// When the reduced fraction does not fit the storage type.
        #[inline]
        #[allow(clippy::unnecessary_fallible_conversions, reason = "`$wide` is `$uty` for the widest type")]
        fn $reduce_name(numerator: $wide, denominator: $wide, g: $uty) -> ($uty, $uty) {
            debug_assert_ne!(numerator, 0);
            debug_assert_ne!(denominator, 0);
            debug_assert_ne!(g, 0);

            let common = if g == 1 {
                1
            } else {
                // Fits the narrow type because it is a remainder modulo `g`.
                match (numerator % g as $wide) as $uty {
                    0 => g,
                    1 => 1,
                    remainder => $gcd_name(remainder, g),
                }
            };

            match (
                <$uty>::try_from(numerator / common as $wide),
                <$uty>::try_from(denominator / common as $wide),
            ) {
                (Ok(numerator), Ok(denominator)) => (numerator, denominator),
                _ => panic!(concat!(
                    "the result of this operation is not representable by a ", stringify!($uty),
                    " rational",
                )),
            }
        }

        /// Add two magnitudes, both of which are non zero, so the sum is too.
        #[inline]
        pub fn $add_name(
            left_numerator: &mut $uty, left_denominator: &mut $uty,
            right_numerator: $uty, right_denominator: $uty,
        ) {
            debug_assert_ne!(*left_numerator, 0);
            debug_assert_ne!(right_numerator, 0);

            let (left, right, denominator, g) = $common_name(
                *left_numerator, *left_denominator, right_numerator, right_denominator,
            );

            let numerator = match left.checked_add(right) {
                Some(numerator) => numerator,
                // Only reachable for the widest type: below it, both terms are at most `MAX * MAX`
                // and a sum that leaves `$wide` cannot reduce back into the storage type anyway.
                None => panic!(concat!(
                    "the result of this operation is not representable by a ", stringify!($uty),
                    " rational",
                )),
            };

            let (numerator, denominator) = $reduce_name(numerator, denominator, g);
            *left_numerator = numerator;
            *left_denominator = denominator;
        }

        /// Subtract two magnitudes, reporting what that does to the caller's sign.
        #[inline]
        pub fn $sub_name(
            left_numerator: &mut $uty, left_denominator: &mut $uty,
            right_numerator: $uty, right_denominator: $uty,
        ) -> SignChange {
            debug_assert_ne!(*left_numerator, 0);
            debug_assert_ne!(right_numerator, 0);

            let (left, right, denominator, g) = $common_name(
                *left_numerator, *left_denominator, right_numerator, right_denominator,
            );

            // Both differences are at most `MAX * MAX`, so neither can leave `$wide`.
            let (numerator, sign_change) = match left.cmp(&right) {
                Ordering::Greater => (left - right, SignChange::None),
                Ordering::Less => (right - left, SignChange::Flip),
                Ordering::Equal => {
                    // Exact cancellation. Zero is stored as `0 / 1`, and the caller owns the sign,
                    // which is why this is reported rather than silently absorbed.
                    //
                    // Reachable only from the equal denominator branch: two reduced fractions are
                    // equal exactly when both their numerators and their denominators are, so the
                    // other branches cannot land here. It used to be reachable from all of them,
                    // because a numerator that wrapped to zero looked like an ordinary result.
                    *left_numerator = 0;
                    *left_denominator = 1;
                    return SignChange::Zero;
                }
            };

            let (numerator, denominator) = $reduce_name(numerator, denominator, g);
            *left_numerator = numerator;
            *left_denominator = denominator;

            sign_change
        }

        /// Multiply two magnitudes, both of which are non zero, so the product is too.
        ///
        /// # Panics
        ///
        /// When the product is not representable. Unlike addition, the cross cancellation below is
        /// already minimal, so a product that overflows had no representable answer to begin with.
        #[inline]
        pub fn $mul_name(
            left_numerator: &mut $uty, left_denominator: &mut $uty,
            mut rhs_numerator: $uty, mut rhs_denominator: $uty,
        ) {
            debug_assert_ne!(*left_numerator, 0);
            debug_assert_ne!(rhs_numerator, 0);

            #[inline]
            fn multiply(left: $uty, right: $uty) -> $uty {
                match left.checked_mul(right) {
                    Some(product) => product,
                    None => panic!(concat!(
                        "the result of this operation is not representable by a ", stringify!($uty),
                        " rational",
                    )),
                }
            }

            if *left_numerator != 1 && rhs_denominator != 1 {
                if *left_numerator == rhs_denominator {
                    *left_numerator = rhs_numerator;
                    let (n, d) = $simplify_name(*left_numerator, *left_denominator);
                    *left_numerator = n;
                    *left_denominator = d;
                    return
                }

                let gcd_ad = $gcd_name(*left_numerator, rhs_denominator);
                debug_assert!(gcd_ad > 0);
                *left_numerator /= gcd_ad;
                rhs_denominator /= gcd_ad;
            }

            if rhs_numerator != 1 && *left_denominator != 1 {
                if rhs_numerator == *left_denominator {
                    *left_denominator = rhs_denominator;
                    let (n, d) = $simplify_name(*left_numerator, *left_denominator);
                    *left_numerator = n;
                    *left_denominator = d;
                    return
                }

                let gcd_bc = $gcd_name(*left_denominator, rhs_numerator);
                debug_assert!(gcd_bc > 0);
                rhs_numerator /= gcd_bc;
                *left_denominator /= gcd_bc;
            }

            // A zero denominator would poison the value: `to_i8` divides by it and panics, and
            // `Ord` reads it as zero. Both operands are fully cancelled against each other by now,
            // so an overflow here means the exact result is genuinely out of range.
            *left_numerator = multiply(*left_numerator, rhs_numerator);
            *left_denominator = multiply(*left_denominator, rhs_denominator);
        }

        #[inline]
        pub fn $simplify_name(numerator: $uty, denominator: $uty) -> ($uty, $uty) {
            debug_assert_ne!(numerator, 0);
            debug_assert_ne!(denominator, 0);

            if numerator == 1 || denominator == 1 {
                (numerator, denominator)
            } else {
                let gcd = $gcd_name(numerator, denominator);
                (numerator / gcd, denominator / gcd)
            }
        }

        #[inline]
        pub fn $gcd_name(mut left: $uty, mut right: $uty) -> $uty {
            debug_assert_ne!(left, 0);
            debug_assert_ne!(right, 0);
            debug_assert_ne!(left, 1);
            debug_assert_ne!(right, 1);

            // Callers guarantee non zero arguments, as asserted above, but a zero that slips
            // through in a release build would make the loop below spin forever: `x >> x.bits()`
            // is a no-op, so `right` would never lose its factors of two and never reach `left`.
            // `gcd(0, x) == gcd(x, 0) == x` in any case.
            if left == 0 {
                return right;
            }
            if right == 0 {
                return left;
            }

            let left_trailing = left.trailing_zeros();
            let right_trailing = right.trailing_zeros();
            let min_trailing = min(left_trailing, right_trailing);

            left >>= left_trailing;
            right >>= right_trailing;

            loop {
                debug_assert_eq!(left % 2, 1);
                debug_assert_eq!(left % 2, 1);

                if left == right {
                    break left << min_trailing;
                }

                if left > right {
                    mem::swap(&mut left, &mut right);
                }

                right -= left;

                right >>= right.trailing_zeros();
            }
        }
    }
}
rational!(add8, sub8, common8, reduce8, mul8, u8, u16, gcd8, simplify8);
rational!(add16, sub16, common16, reduce16, mul16, u16, u32, gcd16, simplify16);
rational!(add32, sub32, common32, reduce32, mul32, u32, u64, gcd32, simplify32);
rational!(add64, sub64, common64, reduce64, mul64, u64, u128, gcd64, simplify64);
// No wider type available; see the module documentation.
rational!(add128, sub128, common128, reduce128, mul128, u128, u128, gcd128, simplify128);
// `usize` is at most 64 bits on every supported target, so `u128` widens it.
rational!(add_usize, sub_usize, common_usize, reduce_usize, mul_usize, usize, u128, gcd_usize, simplify_usize);

#[cfg(test)]
mod test {
    use super::{gcd128, gcd16, gcd64, gcd8};

    #[test]
    fn test_gcd() {
        assert_eq!(gcd8(4, 6), 2);
        assert_eq!(gcd16(9, 6), 3);
        assert_eq!(gcd64(2 * 3 * 5, 3 * 7), 3);
        assert_eq!(gcd128(1 << 100, 1 << 60), 1 << 60);
    }

    /// Callers guarantee a non zero argument, so debug builds assert on it.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn test_gcd_zero() {
        gcd8(0, 6);
    }

    /// The assertions above are compiled out in release builds, where the loop wouldn't terminate
    /// on a zero argument.
    #[cfg(not(debug_assertions))]
    #[test]
    fn test_gcd_zero() {
        assert_eq!(gcd8(0, 6), 6);
        assert_eq!(gcd8(6, 0), 6);
        assert_eq!(gcd64(0, 0), 0);
    }
}
