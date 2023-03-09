use paste::paste;

use std::num::{NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroIsize};
use std::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize};

use crate::rational::small::ops::building_block::{simplify_8, simplify_16, simplify_32, simplify_64, simplify_128, simplify_size};
use crate::rational::small::ops::building_block::{gcd_8, gcd_16, gcd_32, gcd_64, gcd_128, gcd_size};


macro_rules! implement {
    [$($size:expr,)*] => {
        $(
            paste! {
                #[inline]
                pub fn [<mul_ $size>](
                    left_numerator: &mut [<i $size>], left_denominator: &mut [<NonZeroU $size>],
                    right_numerator: [<i $size>], right_denominator: [<NonZeroU $size>],
                ) {
                    let output_sign = (left_numerator * right_numerator).signum();
                    match [<NonZeroI $size>]::new(*left_numerator).zip([<NonZeroI $size>]::new(right_numerator)) {
                        // TODO: Indicate that the first branch is likely
                        Some((left_numerator, right_numerator)) => {
                            // Simplify a and d in (a / b) * (c / d)
                            let (left_numerator, rhs_denominator) = [<simplify_ $size>](left_numerator.unsigned_abs(), right_denominator);
                            // Simplify c and b in (a / b) * (c / d)
                            let (right_numerator, left_denominator) = [<simplify_ $size>](right_numerator.unsigned_abs(), *left_denominator);

                            let numerator = left_numerator.get() as [<i $size>] * right_numerator.get() as [<i $size>] * output_sign;
                            let denominator = left_denominator.checked_mul(rhs_denominator)
                                .expect("attempt to multiply with underflow");

                            // Numerator and denominator are coprime already:
                            //   A, B, C, D sets of prime factors or a, b, c, d
                            //   A ∩ B = empty (initially coprime)
                            //   C ∩ D = empty (initially coprime)
                            //   A ∩ D = empty (simplify 1)
                            //   B ∩ C = empty (simplify 2)
                            //   (A ∪ C) ∩ (B ∪ D) =?= empty
                            //   <=> (A ∩ B) ∪ (A ∩ D) ∪ (C ∩ B) ∪ (C ∩ D) =?= empty (distributivity)
                            // ∎
                            debug_assert_eq!(
                                (numerator, denominator),
                                [<simplify_ $size>](numerator, denominator),
                            );
                        }
                        None => {
                            *left_numerator = 0;
                            *left_denominator = [<NonZeroI $size>]::new(1).unwrap();
                        }
                    }
                }
                
                #[inline]
                pub fn [<add_sub_ $size>](
                    numerator: &mut [<i $size>], denominator: &mut [<NonZeroU $size>],
                    rhs_numerator: &[<i $size>], rhs_denominator: &[<NonZeroU $size>],
                    add_sub_assign: impl Fn(&mut [<i $size>], &[<i $size>]),
                ) {
                    // TODO: Indicate that these first two branches are unlikely
                    if rhs_denominator.get() == 1 {
                        // deals with rhs_numerator == 0
                        numerator += rhs_numerator * denominator.get();
                    } else if denominator.get() == 1 {
                        // deals with numerator == 0
                        denominator = rhs_denominator;
                        numerator *= rhs_denominator.get();
                        add_sub_assign(numerator, rhs_numerator);
                    } else {
                        let gcd = [<gcd_ $size>](denominator, rhs_denominator);
                        let self_scaling = unsafe {
                            // SAFETY: the gcd is built from denominator
                            [<compute_scale_ $size>](denominator, gcd)
                        };
                        let other_scaling = unsafe {
                            // SAFETY: the gcd is built from rhs_denominator
                            [<compute_scale_ $size>](rhs_denominator, gcd)
                        };

                        denominator = denominator
                            .checked_mul(self_scaling)
                            .expect("attempt to add with overflow");
                        numerator *= self_scaling;
                        add_sub_assign(numerator, rhs_numerator * other_scaling);
                    }
                }

                /// SAFETY: The gcd divides the number from which it was built
                unsafe fn [<compute_scale_ $size>](denominator: [<NonZeroU $size>], gcd: [<NonZeroU $size>]) -> [<NonZeroI $size>] {
                    debug_assert!(gcd.get() <= denominator.get());
                    debug_assert_eq!(denominator % gcd, 0);

                    let result = denominator.get() / gcd.get();

                    [<NonZeroU $size>]::new_unchecked(result)
                }
            }
        )*
    }
}

implement![8, 16, 32, 64, 128, "size",];
