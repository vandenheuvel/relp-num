use smallvec::smallvec;

use crate::rational::big::Big8;
use crate::rational::big::ops::BITS_PER_WORD;
use crate::rational::Rational64;
use crate::{RB, NonZero};
use crate::sign::Sign;
use crate::traits::Abs;
use crate::RationalBig;

#[test]
fn eq() {
    // with Self
    let x = Big8::new(1, 1);
    let y = Big8::new(2, 2);
    assert_eq!(x, y);

    let x = Big8::new(2, 1);
    let y = Big8::new(2, 2);
    assert_ne!(x, y);

    let x = Big8::new(-1, 1);
    let y = Big8::new(-2, 2);
    assert_eq!(x, y);

    let x = Big8::new(0, 1);
    let y = Big8::new(-0, 2);
    assert_eq!(x, y);

    // with Rational64
    let x = Big8::new(1, 1);
    let y = Rational64::new(2, 2);
    assert_eq!(x, y);

    let x = Big8::new(2, 1);
    let y = Rational64::new(2, 2);
    assert_ne!(x, y);

    let x = Big8::new(-1, 1);
    let y = Rational64::new(-2, 2);
    assert_eq!(x, y);

    let x = Big8::new(0, 1);
    let y = Rational64::new(-0, 2);
    assert_eq!(x, y);
}

#[test]
fn from() {
    let x = Rational64::new(4, 3);
    let y = Big8::from(x);
    let z = Big8::new(4, 3);
    assert_eq!(y, z);

    let x = <Big8 as num_traits::FromPrimitive>::from_f64(0_f64).unwrap();
    assert_eq!(x, Big8::new(0, 1));

    let x = <Big8 as num_traits::FromPrimitive>::from_f64(1_f64).unwrap();
    assert_eq!(x, Big8::new(1, 1));

    let x = <Big8 as num_traits::FromPrimitive>::from_f64(0.5).unwrap();
    assert_eq!(x, Big8::new(1, 2));

    let x = <Big8 as num_traits::FromPrimitive>::from_f64(2_f64).unwrap();
    assert_eq!(x, Big8::new(2, 1));

    let x = <Big8 as num_traits::FromPrimitive>::from_f64(1.5_f64).unwrap();
    assert_eq!(x, Big8::new(3, 2));

    let x = <Big8 as num_traits::FromPrimitive>::from_f64(f64::MIN_POSITIVE).unwrap();
    let (words, bits) = (1022 / BITS_PER_WORD, 1022 % BITS_PER_WORD);
    let mut denominator = smallvec![0; words];
    denominator.push(1 << bits);
    let expected = Big8 {
        sign: Sign::Positive,
        numerator: smallvec![1],
        denominator,
    };
    assert_eq!(x, expected);

    let x = <Big8 as num_traits::FromPrimitive>::from_f64(f64::MAX).unwrap();
    let total_shift = (1 << (11 - 1)) - 1 - 52;
    let (words, bits) = (total_shift / BITS_PER_WORD, total_shift % BITS_PER_WORD);
    let mut numerator= smallvec![0; words];
    numerator.push(((1 << (52 + 1)) - 1) << bits); // Doesn't overflow, fits exactly in this last word
    let expected = Big8 {
        sign: Sign::Positive,
        numerator,
        denominator: smallvec![1],
    };
    assert_eq!(x, expected);

    let y = <Big8 as num_traits::FromPrimitive>::from_f64(4f64 / 3f64).unwrap();
    let z = Big8::new(4, 3);
    assert!((y - z).abs() < Big8::new(1, 2 << 10));

    // 2 ** 543
    assert_eq!(
        RB!(28793048285076456849987446449190283896766061557132266451844835664715760516297522370041860391064901485759493828054533728788532902755163518009654497157537048672862208_f64),
        RationalBig {
            sign: Sign::Positive,
            numerator: smallvec![0, 0, 0, 0, 0, 0, 0, 0, 1 << 31],
            denominator: smallvec![1],
        }
    )
}

#[test]
fn ord() {
    assert!(RB!(1) > RB!(0));
    assert!(RB!(0) >= RB!(0));
    assert_eq!(RB!(45), RB!(45));
    assert!(RB!(-1) < RB!(1));
    assert!(RB!(1, 2) < RB!(2, 3));
    assert!(RB!(232, 8448) < RB!(94899, 6846));
    assert_eq!(RB!(49684, 49684), RB!(2, 2));
}

#[test]
fn zero() {
    assert!(!RB!(0).is_not_zero());
    assert_eq!(RB!(0), <RationalBig as num_traits::Zero>::zero());
    assert!(!<RationalBig as num_traits::Zero>::zero().is_not_zero());
}

#[test]
fn add() {
    // with Self
    let x = Big8::new(1, 1);
    let y = Big8::new(2, 2);
    assert_eq!(x + y, Big8::new(2, 1));

    let x = Big8::new(2, 1);
    let y = Big8::new(2, 2);
    assert_eq!(x + &y, Big8::new(3, 1));

    let x = Big8::new(-1, 1);
    let y = Big8::new(-2, 2);
    assert_eq!(x + y, Big8::new(-2, 1));

    let x = Big8::new(0, 1);
    let y = &Big8::new(-0, 2);
    assert_eq!(x + y, Big8::new(0, 1));

    // with Rational64
    let mut x = Big8::new(1, 1);
    let y = Big8::new(2, 2);
    x += y;
    assert_eq!(x, Big8::new(2, 1));

    let mut x = Big8::new(2, 1);
    let y = Big8::new(2, 2);
    x += &y;
    assert_eq!(x, Big8::new(3, 1));

    let mut x = Big8::new(1, 1);
    let y = Rational64::new(2, 2);
    x += y;
    assert_eq!(x, Big8::new(2, 1));

    let mut x = Big8::new(2, 1);
    let y = Rational64::new(2, 2);
    x += &y;
    assert_eq!(x, Big8::new(3, 1));
}

#[test]
fn mul() {
    let x = Big8::new(1, 2);
    let y = Big8::new(3, 4);
    assert_eq!(x * y, Big8::new(3, 8));

    let x = Big8::new(5, 6);
    let y = Big8::new(7, 8);
    assert_eq!(x * &y, Big8::new(35, 48));

    let x = Big8::new(-11, 12);
    let y = Rational64::new(-13, 14);
    assert_eq!(x * &y, Big8::new(11 * 13, 12 * 14));

    let x = Big8::new(0, 1);
    let y = &Rational64::new(-0, 2);
    assert_eq!(x * y, Big8::new(0, 1));

    let mut x = Big8::new(1, 1);
    let y = Big8::new(2, 2);
    x *= y;
    assert_eq!(x, Big8::new(1, 1));

    let mut x = Big8::new(2, 1);
    let y = Big8::new(2, 2);
    x *= y;
    assert_eq!(x, Big8::new(8, 4));
}

#[test]
fn test_display() {
    assert_eq!(RB!(0).to_string(), "0");
    assert_eq!(RB!(1).to_string(), "1");
    assert_eq!(RB!(-1).to_string(), "-1");
    assert_eq!(RB!(1, 2).to_string(), "1/2");
    assert_eq!(RB!(-1, 2).to_string(), "-1/2");
}
