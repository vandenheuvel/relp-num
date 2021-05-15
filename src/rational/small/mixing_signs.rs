pub trait AddDifferentlySigned<Rhs> {
    type Output;

    #[must_use]
    fn add_differently_signed(self, rhs: Rhs) -> Self::Output;
}

pub trait MulDifferentlySigned<Rhs> {
    type Output;

    #[must_use]
    fn mul_differently_signed(self, rhs: Rhs) -> Self::Output;
}

macro_rules! impl_signed_unsigned {
    ($signed:ty, $unsigned:ty) => {
        impl AddDifferentlySigned<$unsigned> for $signed {
            type Output = Self;

            fn add_differently_signed(self, rhs: $unsigned) -> Self::Output {
                debug_assert!(if self > 0 {
                    rhs <= (<$signed>::MAX - self) as $unsigned
                } else if self == 0 {
                    rhs <= <$signed>::MAX as $unsigned
                } else {
                    // self < 0
                    rhs - (-self as $unsigned) <= <$signed>::MAX as $unsigned
                });

                self.wrapping_add(rhs as $signed)
            }
        }

        impl MulDifferentlySigned<$unsigned> for $signed {
            type Output = Self;

            fn mul_differently_signed(self, rhs: $unsigned) -> Self::Output {
                self * rhs as $signed
            }
        }
    }
}

impl_signed_unsigned!(i8, u8);
impl_signed_unsigned!(i16, u16);
impl_signed_unsigned!(i32, u32);
impl_signed_unsigned!(i64, u64);
impl_signed_unsigned!(i128, u128);

// impl AddDifferentlySigned<u8> for i8 {
//     type Output = Self;
//
//     fn add_differently_signed(self, rhs: u8) -> Self::Output {
//         debug_assert!(if self > 0 {
//             rhs <= (i8::MAX - self) as u8
//         } else if self == 0 {
//             rhs <= i8::MAX as u8
//         } else {
//             // self < 0
//             rhs - (-self as u8) <= i8::MAX as u8
//         });
//
//         self.wrapping_add(rhs as i8)
//     }
// }
//
// impl MulDifferentlySigned<u8> for i8 {
//     type Output = Self;
//
//     fn mul_differently_signed(self, rhs: u8) -> Self::Output {
//         self * rhs as i8
//     }
// }


#[cfg(test)]
#[allow(unused_must_use)]
mod test {
    use crate::rational::small::mixing_signs::{AddDifferentlySigned, MulDifferentlySigned};

    #[test]
    fn test_add() {
        assert_eq!(0_i8.add_differently_signed(0), 0);

        assert_eq!((-1_i8).add_differently_signed(128), 127);
        assert_eq!(0_i8.add_differently_signed(127), 127);
        assert_eq!(1_i8.add_differently_signed(126), 127);

        assert_eq!(4_i8.add_differently_signed(5), 9);
        assert_eq!((-4_i8).add_differently_signed(5), 1);
        assert_eq!((-10_i8).add_differently_signed(137), 127);
    }

    #[test]
    #[should_panic]
    fn test_add_negative_1() {
        -1_i8.add_differently_signed(129);
    }

    #[test]
    #[should_panic]
    fn test_add_negative_2() {
        0_i8.add_differently_signed(128);
    }

    #[test]
    #[should_panic]
    fn test_add_negative_3() {
        1_i8.add_differently_signed(127);
    }

    #[test]
    fn test_mul() {
        assert_eq!(0_i8.mul_differently_signed(0), 0);
        assert_eq!(0.mul_differently_signed(u8::MAX), 0);

        assert_eq!((-1_i8).mul_differently_signed(127), -127);
        assert_eq!(0_i8.mul_differently_signed(127), 0);
        assert_eq!(1_i8.mul_differently_signed(127), 127);

        assert_eq!(4_i8.mul_differently_signed(5), 20);
        assert_eq!((-4_i8).mul_differently_signed(5), -20);
    }

    #[test]
    #[should_panic]
    fn test_mul_negative_1() {
        -1_i8.mul_differently_signed(128);
    }

    #[test]
    #[should_panic]
    fn test_mul_negative_2() {
        2_i8.mul_differently_signed(i8::MAX as u8 / 2 + 1);
    }
}
