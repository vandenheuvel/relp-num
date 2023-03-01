use std::mem;
use std::num::NonZeroU64;

/// See also the `std::num::FpCategory`.
pub enum FloatKind {
    Zero,
    Subnormal(FloatAsRatio),
    Infinity,
    NaN,
    Normal(FloatAsRatio),
}


pub struct FloatAsRatio {
    pub sign: u64,
    pub exponent: i32,
    pub fraction: NonZeroU64,
}

pub fn f32_kind(n: f32) -> FloatKind {
    let n = n.to_bits();
    let sign = (n & 0b1000_0000_0000_0000_0000_0000_0000_0000) >> (32 - 1);
    let exponent = (n & 0b0111_1111_1000_0000_0000_0000_0000_0000) >> (32 - 1 - 8);
    let fraction = n & 0b0000_0000_0111_1111_1111_1111_1111_1111;

    match (exponent, fraction) {
        (0, 0) => FloatKind::Zero,
        (0, _) => FloatKind::Subnormal(FloatAsRatio {
            sign: sign as u64,
            exponent: 1 - 127 - 23,
            fraction: unsafe {
                // SAFETY: Zero would have matched earlier branch
                NonZeroU64::new_unchecked(fraction as u64)
            },
        }),
        (ONES_32, 0) => FloatKind::Infinity,
        (ONES_32, _) => FloatKind::NaN,
        _ => FloatKind::Normal(FloatAsRatio {
            sign: sign as u64,
            exponent: exponent as i32 - 127 - 23,
            fraction: unsafe {
                // SAFETY: A constant is always added
                NonZeroU64::new_unchecked((fraction + (1 << 23)) as u64)
                // SAFETY: A constant is always added
            },
        }),
    }
}

pub fn f64_kind(n: f64) -> FloatKind {
    let n = n.to_bits();
    let sign = (n & 0b1000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000) >> (64 - 1);
    let exponent = (n & 0b0111_1111_1111_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000) >> (64 - 1 - 11);
    let fraction = n & 0b0000_0000_0000_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111_1111;

    assert_eq!(mem::size_of::<usize>(), mem::size_of::<u64>());

    match (exponent, fraction) {
        (0, 0) => FloatKind::Zero,
        (0, _) => FloatKind::Subnormal(FloatAsRatio {
            sign,
            exponent: 1 - 1023 - 52,
            fraction: unsafe {
                // SAFETY: Zero would have matched earlier branch
                NonZeroU64::new_unchecked(fraction)
            },
        }),
        (ONES_64, 0) => FloatKind::Infinity,
        (ONES_64, _) => FloatKind::NaN,
        _ => FloatKind::Normal(FloatAsRatio {
            sign,
            exponent: exponent as i32 - 1023 - 52,
            fraction: unsafe {
                // SAFETY: A constant is always added
                NonZeroU64::new_unchecked(fraction + (1 << 52))
            },
        }),
    }
}
