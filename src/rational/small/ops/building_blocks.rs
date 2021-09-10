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
