use crate::{NonZero, RB};
use crate::rational::big::{Big8};
use crate::rational::Rational64;
use crate::RationalBig;
use std::str::FromStr;

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

    let mut x = Big8::from_str("68498984987984986896468746354684684684968/68468465468464168545346854646").unwrap();
    let y = Big8::from_str("9876519684989849849849847").unwrap();
    let expected = Big8::from_str("676230147000402641135208532975102322580080121519024130/68468465468464168545346854646").unwrap();
    x += y;
    assert_eq!(x, expected);

    let x = Big8::from_str("68498984987984986896468746354684684684968/68468465468464168545346854646").unwrap();
    let y = Big8::from_str("9876519684989849849849847").unwrap();
    let expected = Big8::from_str("676230147000402641135208532975102322580080121519024130/68468465468464168545346854646").unwrap();
    let z = x + y;
    assert_eq!(z, expected);

    let x = Big8::from_str("68498984987984986896468746354684684684968/68468465468464168545346854646").unwrap();
    let y = Big8::from_str("9876519684989849849849847/3").unwrap();
    let z = Big8::from_str("676230147000539639105184502948895260072789490888394066/205405396405392505636040563938").unwrap();
    assert_eq!(x + y, z);
}

#[test]
fn test_sub() {
    // with Self
    let x = Big8::new(1, 1);
    let y = Big8::new(2, 2);
    assert_eq!(x - y, Big8::new(0, 1));

    let x = Big8::new(2, 1);
    let y = Big8::new(2, 2);
    assert_eq!(x - &y, Big8::new(1, 1));

    let x = Big8::new(-1, 1);
    let y = Big8::new(-2, 2);
    assert_eq!(x - y, Big8::new(0, 1));

    let x = Big8::new(0, 1);
    let y = &Big8::new(-0, 2);
    assert_eq!(x - y, Big8::new(0, 1));

    // with Rational64
    let mut x = Big8::new(1, 1);
    let y = Big8::new(2, 2);
    x -= y;
    assert_eq!(x, Big8::new(0, 1));

    let mut x = Big8::new(2, 1);
    let y = Big8::new(2, 2);
    x -= &y;
    assert_eq!(x, Big8::new(1, 1));

    let mut x = Big8::new(1, 1);
    let y = Rational64::new(2, 2);
    x -= y;
    assert_eq!(x, Big8::new(0, 1));

    let mut x = Big8::new(2, 1);
    let y = Rational64::new(2, 2);
    x -= &y;
    assert_eq!(x, Big8::new(1, 1));

    let mut x = Big8::from_str("68498984987984986896468746354684684684968/68468465468464168545346854646").unwrap();
    let y = Big8::from_str("9876519684989849849849847").unwrap();
    let expected = Big8::from_str("-676230147000265643165232563001309385087370752149654194/68468465468464168545346854646").unwrap();
    x -= y;
    assert_eq!(x, expected);

    let x = Big8::from_str("68498984987984986896468746354684684684968/68468465468464168545346854646").unwrap();
    let y = Big8::from_str("9876519684989849849849847").unwrap();
    let expected = Big8::from_str("-676230147000265643165232563001309385087370752149654194/68468465468464168545346854646").unwrap();
    let z = x - y;
    assert_eq!(z, expected);

    let x = Big8::from_str("68498984987984986896468746354684684684968/68468465468464168545346854646").unwrap();
    let y = Big8::from_str("9876519684989849849849847").unwrap();
    let expected = Big8::from_str("676230147000265643165232563001309385087370752149654194/68468465468464168545346854646").unwrap();
    let z = y - x;
    assert_eq!(z, expected);

    let x = Big8::from_str("68498984987984986896468746354684684684968/68468465468464168545346854646").unwrap();
    let y = Big8::from_str("9876519684989849849849847/3").unwrap();
    let z = Big8::from_str("-676230147000128645195256593027516447594661382780284258/205405396405392505636040563938").unwrap();
    assert_eq!(x - y, z);
}

#[test]
fn test_mul() {
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

#[test]
fn test_sum() {
    assert_eq!((0..50001).map(Big8::from).sum::<Big8>(), RB!(1250025000));
    assert_eq!(
        (0..1).map(|i| Big8::new(i, (i + 1) as u64)).sum::<Big8>(),
        RB!(0),
    );
    assert_eq!(
        (0..43).map(|i| Big8::new(i, (i + 1) as u64)).sum::<Big8>(),
        RB!(4728144095208782983, 122332313750680800),
    );
}
