use std::cmp::min;
use std::cmp::Ordering;
use std::mem;
use paste::paste;

use std::num::{NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroIsize};
use std::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize};


macro_rules! implement {
    [$($size:expr,)*] => {
        $(
            paste! {
                #[inline]
                pub fn [<simplify_ $size>](numerator: [<NonZeroU $size>], denominator: [<NonZeroU $size>]) -> ([<NonZeroU $size>], [<NonZeroU $size>]) {
                    if numerator == 1 || denominator == 1 {
                        (numerator, denominator)
                    } else {
                        let gcd = [<gcd_ $size>](numerator, denominator);
                        (numerator / gcd, denominator / gcd)
                    }
                }

                #[inline]
                pub fn [<gcd_ $size>](left_input: [<NonZeroU $size>], right_input: [<NonZeroU $size>]) -> [<NonZeroU $size>] {
                    let mut left = left_input.get();
                    let mut right = right_input.get();

                    debug_assert_ne!(left, 1, "has poor performance, check separately");
                    debug_assert_ne!(right, 1, "has poor performance, check separately");

                    let left_trailing = left.trailing_zeros();
                    let right_trailing = right.trailing_zeros();
                    let min_trailing = min(left_trailing, right_trailing);

                    left >>= left_trailing;
                    right >>= right_trailing;

                    loop {
                        debug_assert_eq!(left % 2, 1);
                        debug_assert_eq!(right % 2, 1);

                        if left == right {
                            let result = left << min_trailing;
                            debug_assert_ne!(
                                result, 0,
                                "should be non-zero due to the properties of the algorithm",
                            );
                            break unsafe { [<NonZeroU $size>]::new_unchecked(result) };
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
