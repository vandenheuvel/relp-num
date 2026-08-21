use std::cmp::min;
use std::cmp::Ordering;
use std::mem;

pub enum SignChange {
    None,
    Flip,
    Zero,
}

// TODO(CORRECTNESS): The intermediate values below overflow for results that are representable.
//
// Bringing two fractions to a common denominator scales both numerators and the denominator up,
// and each of those products is computed in the same narrow type that stores the result. The
// result of `R8!(255, 2) + R8!(255, 2)` is `255`, which a `Rational8` represents without trouble,
// but `255 * 2` does not fit in a `u8`: debug builds panic, release builds wrap and return `127`.
// The same holds for the numerator products in `$sub_name` and for the denominator product that
// follows them.
//
// Fixing this is a design decision that has to be made for the type as a whole: either every
// intermediate is computed in a wider type (with no wider type available for the widest one), or
// these functions report failure and the operators become checked. Until then, an operation whose
// intermediates leave the range of the type is only correct by accident.
macro_rules! rational {
    (
        $add_name:ident, $sub_name:ident, $sub_direction_name:ident, $mul_name: ident,
        $uty:ty, $gcd_name:ident, $simplify_name:ident
    ) => {
        #[inline]
        pub fn $add_name(
            left_numerator: &mut $uty, left_denominator: &mut $uty, 
            right_numerator: $uty, right_denominator: $uty,
        ) {
            if *left_denominator == right_denominator {
                *left_numerator += right_numerator;

                // Numerator can't be zero

                if left_numerator == left_denominator {
                    *left_numerator = 1;
                    *left_denominator = 1;
                } else if *left_denominator != 1 {
                    // numerator can't be 1 because two positive things were added
                    let gcd = $gcd_name(*left_numerator, *left_denominator);
                    *left_numerator /= gcd;
                    *left_denominator /= gcd;
                }
            } else {
                if *left_denominator == 1 {
                    *left_numerator *= right_denominator;
                    *left_numerator += right_numerator;
                    *left_denominator = right_denominator;
                } else if right_denominator == 1 {
                    *left_numerator += right_numerator * *left_denominator;
                } else {
                    // Neither denominator is 1
                    let gcd = $gcd_name(*left_denominator, right_denominator);

                    *left_numerator *= right_denominator / gcd;
                    *left_denominator /= gcd;

                    *left_numerator += right_numerator * *left_denominator;
                    *left_denominator *= right_denominator;

                    let (n, d) = $simplify_name(*left_numerator, *left_denominator);
                    *left_numerator = n;
                    *left_denominator = d;
                }
            }
        }
        #[inline]
        pub fn $sub_name(
            left_numerator: &mut $uty, left_denominator: &mut $uty, 
            right_numerator: $uty, right_denominator: $uty,
        ) -> SignChange {
            if *left_denominator == right_denominator {
                let flip_sign = $sub_direction_name(left_numerator, left_denominator, right_numerator);

                if left_numerator == left_denominator {
                    *left_numerator = 1;
                    *left_denominator = 1;
                } else if *left_denominator != 1 && *left_numerator != 1 {
                    let gcd = $gcd_name(*left_numerator, *left_denominator);
                    *left_numerator /= gcd;
                    *left_denominator /= gcd;
                }

                flip_sign
            } else {
                if *left_denominator == 1 {
                    *left_numerator *= right_denominator;
                    *left_denominator = right_denominator;
                    $sub_direction_name(left_numerator, left_denominator, right_numerator)
                } else if right_denominator == 1 {
                    $sub_direction_name(left_numerator, left_denominator, right_numerator * *left_denominator)
                } else {
                    // Neither denominator is 1
                    let gcd = $gcd_name(*left_denominator, right_denominator);

                    *left_numerator *= right_denominator / gcd;
                    *left_denominator /= gcd;

                    let rhs_numerator = right_numerator * *left_denominator;
                    let sign_change = if *left_numerator < rhs_numerator {
                        *left_numerator = rhs_numerator - *left_numerator;
                        SignChange::Flip
                    } else {
                        // larger than, not zero
                        *left_numerator -= rhs_numerator;
                        SignChange::None
                    };
                    *left_denominator *= right_denominator;

                    let (n, d) = $simplify_name(*left_numerator, *left_denominator);
                    *left_numerator = n;
                    *left_denominator = d;

                    sign_change
                }
            }
        }
        #[inline]
        fn $sub_direction_name(
            left_numerator: &mut $uty, left_denominator: &mut $uty,
            rhs_numerator: $uty,
        ) -> SignChange {
            match (*left_numerator).cmp(&rhs_numerator) {
                Ordering::Less => {
                    *left_numerator = rhs_numerator - *left_numerator;
                    SignChange::Flip
                }
                Ordering::Equal => {
                    *left_numerator = 0;
                    *left_denominator = 1;
                    SignChange::Zero
                }
                Ordering::Greater => {
                    *left_numerator -= rhs_numerator;
                    SignChange::None
                }
            }
        }
        
        #[inline]
        pub fn $mul_name(
            left_numerator: &mut $uty, left_denominator: &mut $uty,
            mut rhs_numerator: $uty, mut rhs_denominator: $uty,
        ) {
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

            *left_numerator *= rhs_numerator;
            *left_denominator *= rhs_denominator;
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
rational!(add8, sub8, sub_direction8, mul8, u8, gcd8, simplify8);
rational!(add16, sub16, direction16, mul16, u16, gcd16, simplify16);
rational!(add32, sub32, sub_direction32, mul32, u32, gcd32, simplify32);
rational!(add64, sub64, sub_direction64, mul64, u64, gcd64, simplify64);
rational!(add128, sub128, sub_direction128, mul128, u128, gcd128, simplify128);
rational!(add_usize, sub_usize, sub_direction_usize, mul_usize, usize, gcd_usize, simplify_usize);

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
