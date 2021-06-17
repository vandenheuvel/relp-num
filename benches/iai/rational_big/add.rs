use std::str::FromStr;

use iai::black_box;

use relp_num::RationalBig;
use relp_num::RB;

pub fn small_with_small_same_denominator() -> RationalBig {
    let x = black_box(RB!(3, 16));
    let y = black_box(RB!(2, 16));
    x + y
}

pub fn small_with_small_other_denominator() -> RationalBig {
    let x = black_box(RB!(3, 16));
    let y = black_box(RB!(2, 17));
    x + y
}

pub fn large_with_large_other_denominator() -> RationalBig {
    let x = black_box(RationalBig::from_str("6168468435984654684986468468465846854869699989985/5648654685465465464684846546846856725").unwrap());
    let y = black_box(RationalBig::from_str("616846843598465468438574687768468765846854869699989985/564846898987498778846546846856725").unwrap());
    x + y
}
