use std::cmp::min;
use std::cmp::Ordering;
use std::mem;
use paste::paste;

pub enum SignChange {
    None,
    Flip,
    Zero,
}

macro_rules! implement {
    [$($size:expr,)*] => {
        $(
            paste! {
                #[inline]
                pub fn [<add_ $size>](
                    left_numerator: &mut [<u $size>], left_denominator: &mut [<u $size>],
                    right_numerator: [<u $size>], right_denominator: [<u $size>],
                ) {
                    if *left_denominator == right_denominator {
                        *left_numerator += right_numerator;

                        // Numerator can't be zero

                        if left_numerator == left_denominator {
                            *left_numerator = 1;
                            *left_denominator = 1;
                        } else if *left_denominator != 1 {
                            // numerator can't be 1 because two positive things were added
                            let gcd = [<gcd_ $size>](*left_numerator, *left_denominator);
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
                            let gcd = [<gcd_ $size>](*left_denominator, right_denominator);

                            *left_numerator *= right_denominator / gcd;
                            *left_denominator /= gcd;

                            *left_numerator += right_numerator * *left_denominator;
                            *left_denominator *= right_denominator;

                            let (n, d) = [<simplify_ $size>](*left_numerator, *left_denominator);
                            *left_numerator = n;
                            *left_denominator = d;
                        }
                    }
                }
                #[inline]
                pub fn [<sub_ $size>](
                    left_numerator: &mut [<u $size>], left_denominator: &mut [<u $size>],
                    right_numerator: [<u $size>], right_denominator: [<u $size>],
                ) -> SignChange {
                    if *left_denominator == right_denominator {
                        let flip_sign = [<sub_direction_ $size>](left_numerator, left_denominator, right_numerator);

                        if left_numerator == left_denominator {
                            *left_numerator = 1;
                            *left_denominator = 1;
                        } else if *left_denominator != 1 && *left_numerator != 1 {
                            let gcd = [<gcd_ $size>](*left_numerator, *left_denominator);
                            *left_numerator /= gcd;
                            *left_denominator /= gcd;
                        }

                        flip_sign
                    } else {
                        if *left_denominator == 1 {
                            *left_numerator *= right_denominator;
                            *left_denominator = right_denominator;
                            [<sub_direction_ $size>](left_numerator, left_denominator, right_numerator)
                        } else if right_denominator == 1 {
                            [<sub_direction_ $size>](left_numerator, left_denominator, right_numerator * *left_denominator)
                        } else {
                            // Neither denominator is 1
                            let gcd = [<gcd_ $size>](*left_denominator, right_denominator);

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

                            let (n, d) = [<simplify_ $size>](*left_numerator, *left_denominator);
                            *left_numerator = n;
                            *left_denominator = d;

                            sign_change
                        }
                    }
                }
                #[inline]
                fn [<sub_direction_ $size>](
                    left_numerator: &mut [<u $size>], left_denominator: &mut [<u $size>],
                    rhs_numerator: [<u $size>],
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
                pub fn [<mul_ $size>](
                    left_numerator: &mut [<u $size>], left_denominator: &mut [<u $size>],
                    mut rhs_numerator: [<u $size>], mut rhs_denominator: [<u $size>],
                ) {
                    if *left_numerator != 1 && rhs_denominator != 1 {
                        if *left_numerator == rhs_denominator {
                            *left_numerator = rhs_numerator;
                            let (n, d) = [<simplify_ $size>](*left_numerator, *left_denominator);
                            *left_numerator = n;
                            *left_denominator = d;
                            return
                        }

                        let gcd_ad = [<gcd_ $size>](*left_numerator, rhs_denominator);
                        debug_assert!(gcd_ad > 0);
                        *left_numerator /= gcd_ad;
                        rhs_denominator /= gcd_ad;
                    }

                    if rhs_numerator != 1 && *left_denominator != 1 {
                        if rhs_numerator == *left_denominator {
                            *left_denominator = rhs_denominator;
                            let (n, d) = [<simplify_ $size>](*left_numerator, *left_denominator);
                            *left_numerator = n;
                            *left_denominator = d;
                            return
                        }

                        let gcd_bc = [<gcd_ $size>](*left_denominator, rhs_numerator);
                        debug_assert!(gcd_bc > 0);
                        rhs_numerator /= gcd_bc;
                        *left_denominator /= gcd_bc;
                    }

                    *left_numerator *= rhs_numerator;
                    *left_denominator *= rhs_denominator;
                }

                #[inline]
                pub fn [<simplify_ $size>](numerator: [<u $size>], denominator: [<u $size>]) -> ([<u $size>], [<u $size>]) {
                    debug_assert_ne!(numerator, 0);
                    debug_assert_ne!(denominator, 0);

                    if numerator == 1 || denominator == 1 {
                        (numerator, denominator)
                    } else {
                        let gcd = [<gcd_ $size>](numerator, denominator);
                        (numerator / gcd, denominator / gcd)
                    }
                }

                #[inline]
                pub fn [<gcd_ $size>](mut left: [<u $size>], mut right: [<u $size>]) -> [<u $size>] {
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
        )*
    }
}
implement![8, 16, 32, 64, 128, "size",];
