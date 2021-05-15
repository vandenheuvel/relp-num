//! # NonZero signs of integers
use std::cmp::Ordering;

use num_traits;

use crate::non_zero::NonZeroSign;
use crate::non_zero::NonZeroSigned;

impl NonZeroSigned for i32 {
    fn signum(&self) -> NonZeroSign {
        match self.cmp(&<i32 as num_traits::Zero>::zero()) {
            Ordering::Less => NonZeroSign::Negative,
            Ordering::Equal => panic!(),
            Ordering::Greater => NonZeroSign::Positive,
        }
    }
}
