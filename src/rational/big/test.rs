use std::str::FromStr;

use crate::{NonZero, RB, Sign};
use crate::rational::big::Big8;
use crate::rational::Rational64;
use crate::RationalBig;
use smallvec::smallvec;
use crate::rational::big::ops::normalize::simplify_fraction_gcd;
use num_traits::Zero;

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

    let x = Big8::from_str("1236568906498545539/62234083721250000").unwrap();
    let y = Big8::from_str("546838705131439769/1711437302334375000").unwrap();
    let z = x / y;
    assert_eq!(z, Big8::from_str("68011289857420004645/1093677410262879538").unwrap());

    let a = Big8::from_str("112390368016523/11063837106000").unwrap();
    let b = Big8::from_str("55462879519/442553484240").unwrap();
    let c = a / b;
    assert_eq!(c, Big8::from_str("112390368016523/1386571987975").unwrap());

    assert!(z < c);
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

    assert_eq!(RB!(1, 2) + RB!(1, 2), RB!(1));
    assert_eq!(RB!(1, 2) + RB!(3, 2), RB!(2));
    assert_eq!(RB!(3, 1) + RB!(4, 1), RB!(7, 1));

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

    let x = Big8::from_str("3146383673420971972032023490593198871229613539715389096610302560000000/3302432073363697202172148890923583722241").unwrap();
    let y = Big8::from_str("-19040000000/24371529219").unwrap();
    let expected = Big8::from_str("23219911849044943287036970642552000000000/24371529219").unwrap();
    assert_eq!(&x + y, expected);

    let x = Big8::from_str("3146383673420971972032023490593198871229613539715389096610302560000000/3302432073363697202172148890923583722241").unwrap();
    let y = Big8::from_str("-1190934288550035983230200000000/1219533185348999122218328290051").unwrap();
    let expected = Big8::from_str("3837119303577162935033943051362177961413830001188396008105921274746403631342765081863784952360000000/4027425505827929207130173913061266698153904666032123020587815267724291").unwrap();
    assert_eq!(&x + y, expected);

    let x = Big8::from_str("3146383673420971972032023490593198871229613539715389096610302560000000/3302432073363697202172148890923583722241").unwrap();
    let y = Big8::from_str("-23800000000/24371529219").unwrap();
    let expected = Big8::from_str("76682181630963772103758511304607920049504288847839925168388021404881164840000000/80485319769746097976607076963162564582789311659779").unwrap();
    assert_eq!(&x + y, expected);

    let mut x = Big8 {
        sign: Sign::Positive,
        numerator: smallvec![13284626917187606528, 14353657804625640860, 11366567065457835548, 501247837944],
        denominator: smallvec![10945929334190035713, 13004504757950498814, 9],
    };
    simplify_fraction_gcd(&mut x.numerator, &mut x.denominator);
    let mut y = Big8 {
        sign: Sign::Positive,
        numerator: smallvec![12384794773201432064, 64560677146],
        denominator: smallvec![12499693862731150083, 66111026448],
    };
    simplify_fraction_gcd(&mut y.numerator, &mut y.denominator);
    let z = Big8 {
        sign: Sign::Negative,
        numerator: smallvec![4],
        denominator: smallvec![5],
    };
    let xx = &y * z;
    x += xx;
    let expected = Big8::from_str("23219911849044943287036970642552000000000/24371529219").unwrap();
    assert_eq!(x, expected);

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

    assert_eq!(
        Big8::from_str("1190934288550035983230200000000/1219533185348999122218328290051").unwrap() * RB!(-4, 5),
        Big8::from_str("-4763737154200143932920800000000/6097665926744995611091641450255").unwrap(),
    );
    assert_eq!(
        (&Big8::from_str("1190934288550035983230200000000/1219533185348999122218328290051").unwrap()) * RB!(-4, 5),
        Big8::from_str("-4763737154200143932920800000000/6097665926744995611091641450255").unwrap(),
    );
}

#[test]
fn test_mul_add() {
    let mut x = Big8::from_str("1588989165000/32460463963").unwrap();
    let y = Big8::from_str("808953992679657007631484461470500000/1609760080345859697668056906889135691").unwrap();
    let z = Big8::from_str("-9741/100").unwrap();

    let yz = y * z;
    assert_eq!(
        yz,
        Big8::from_str("-7880020842692538911338290139184140500000/160976008034585969766805690688913569100").unwrap(),
    );
    x += yz;
    assert!(x.is_zero());

    let mut x = Big8::from_str("0").unwrap();
    let y = Big8::from_str("9381074085307/3795475922420").unwrap();
    let z = Big8::from_str("-1").unwrap();

    let yz = y * z;
    assert_eq!(yz, Big8::from_str("-9381074085307/3795475922420").unwrap());
    x += yz;
    assert_eq!(x, Big8::from_str("-9381074085307/3795475922420").unwrap());

    // 26219000000/81331626909 + 20591406422593/18977379612100 * &2587354000000/28143222255921
    let x = Big8::from_str("26219000000/81331626909").unwrap();
    let y = Big8::from_str("20591406422593/18977379612100").unwrap();
    let z = Big8::from_str("2587354000000/28143222255921").unwrap();

    let yz = y * &z;
    assert_eq!(yz, Big8::from_str("53277257773121688922000000/534084612258314153908244100").unwrap());
    let result = x + yz;
    let expected = Big8::from_str("18336290500738892172980314459998000000/43437970422031134698979313360500486900").unwrap();
    assert_eq!(result, expected);


    let x = Big8::from_str("340282366920938463504022243945446072289/6512495130518689119600").unwrap();
    let y = Big8::from_str("27940143/20272744325").unwrap();
    let z = Big8::from_str("-22581710000/20077742763").unwrap();

    let yz = y * z;
    assert_eq!(yz, Big8::from_str("-630936206584530000/407030945657418069975").unwrap());
    assert_eq!(x - yz, Big8::from_str("138505453598374099998687302319741407818269762728358498422775/2650787051564352351939188343674463944010000").unwrap());


    let x = Big8::from_str("60425219813/8031097105200").unwrap();
    let y = Big8::from_str("22581710000/20077742763").unwrap();
    let z = Big8::from_str("55880286/55771507675").unwrap();

    let yz = y * z;
    assert_eq!(yz, Big8::from_str("1261872413169060000/1119765984603330206025").unwrap());
    assert_eq!(x + yz, Big8::from_str("77796325643310377435088313973325/8992949357449232987887097098830000").unwrap());


    let x = Big8::from_str("60425219813/8031097105200").unwrap();
    let y = Big8::from_str("22581710000/20077742763").unwrap();
    let z = Big8::from_str("27940143/20272744325").unwrap();

    let yz = y * &z;
    assert_eq!(yz, Big8::from_str("630936206584530000/407030945657418069975").unwrap());
    assert_eq!(x + yz, Big8::from_str("29662044304309632734380146414675/3268905049396108772682393536370000").unwrap());


    let x = Big8::from_str("1236568906498545539/62234083721250000").unwrap();
    let y = Big8::from_str("546838705131439769/1711437302334375000").unwrap();
    let z = Big8::from_str("49738748960728111540097520/613632264427919632014000").unwrap();

    let yz = y * &z;
    assert_eq!(yz, Big8::from_str("27199073076542306045429576463148252266272880/1050193147257852636904958613182681250000000").unwrap());
    assert_eq!(x - yz, Big8::from_str("-394073199269021840118251854401557581848776632371910950000000/65357808249928230866638271812077278833052601562500000000000").unwrap());


    let mut x = Big8::from_str("1236568906498545539/62234083721250000").unwrap();
    let y = Big8::from_str("546838705131439769/1711437302334375000").unwrap();
    let z = Big8::from_str("112390368016523/1386571987975").unwrap();

    let yz = y * &z;
    assert_eq!(yz, Big8::from_str("27199073076542306045429576463148252266272880/1050193147257852636904958613182681250000000").unwrap());
    x -= yz;
    assert_eq!(x, Big8::from_str("-394073199269021840118251854401557581848776632371910950000000/65357808249928230866638271812077278833052601562500000000000").unwrap());
}

#[test]
fn test_div() {
    assert_eq!(RB!(100) / RB!(2), RB!(50));
    assert_eq!(RB!(200) / RB!(2), RB!(100));
    assert_eq!((RB!(200) - RB!(0)) / RB!(2), RB!(100));
    assert_eq!((&RB!(200) - RB!(0)) / RB!(2), RB!(100));
}

#[test]
fn test_display() {
    assert_eq!(RB!(0).to_string(), "0");
    assert_eq!(RB!(1).to_string(), "1");
    assert_eq!(RB!(-1).to_string(), "-1");
    assert_eq!(RB!(1, 2).to_string(), "1/2");
    assert_eq!(RB!(-1, 2).to_string(), "-1/2");

    let x = Big8 {
        sign: Sign::Positive,
        numerator: smallvec![13284626917187606528, 14353657804625640860, 11366567065457835548, 501247837944],
        denominator: smallvec![10945929334190035713, 13004504757950498814, 9],
    };
    assert_eq!(x.to_string(), "3146383673420971972032023490593198871229613539715389096610302560000000/3302432073363697202172148890923583722241");
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

#[test]
fn test_cmp() {
    assert!(RB!(-3) < RB!(-2));
    assert!(RB!(-3) < RB!(0));
    assert!(RB!(-3) < RB!(2));
    assert!(RB!(-3) < RB!(3));

    assert!(Big8::from_str("46684684849681687468684984876848674687485146").unwrap() > RB!(4));
    assert!(Big8::from_str("-46684684849681687468684984876848674687485146466846848496816874686849848768486746874851464668468484968168746868498487684867468748514646684684849681687468684984876848674687485146").unwrap() < RB!(-1));
    assert!(RB!(-2) < RB!(-1));
    assert_eq!(
        Big8::from_str("-46684684849681687468684984876848674687485146466846848496816874686849848768486746874851464668468484968168746868498487684867468748514646684684849681687468684984876848674687485146").unwrap(),
        Big8::from_str("-46684684849681687468684984876848674687485146466846848496816874686849848768486746874851464668468484968168746868498487684867468748514646684684849681687468684984876848674687485146").unwrap(),
    );
    assert_eq!(
        Big8::from_str("46684684849681687468684984876848674687485146466846848496816874686849848768486746874851464668468484968168746868498487684867468748514646684684849681687468684984876848674687485146").unwrap(),
        Big8::from_str("46684684849681687468684984876848674687485146466846848496816874686849848768486746874851464668468484968168746868498487684867468748514646684684849681687468684984876848674687485146").unwrap(),
    );
    assert!(RB!(5) > RB!(4));
    assert!(RB!(5) > RB!(0));
    assert!(RB!(5) >= RB!(0));
    assert!(RB!(-5) <= RB!(-5));
    assert!(RB!(-5) <= RB!(5));
    assert!(RB!(200) - RB!(0) > RB!(0));

    let x = Big8::from_str("-583826928791700523/521249090962500").unwrap();
    let y = Big8::from_str("-1267844014078631957/1042498181925000").unwrap();
    assert!(x > y);
    assert!(!(x < y));
}

#[test]
fn test_eq() {
    assert_eq!(RB!(3), RB!(3));
    assert_eq!(RB!(0), RB!(0));
    assert_eq!(RB!(-1), RB!(-1));
    assert_ne!(RB!(-1), RB!(0));
    assert_ne!(RB!(-1), RB!(1));
    assert_ne!(RB!(0), RB!(1));
}

#[test]
fn test_consistent() {
    assert!(Big8 {
        sign: Sign::Zero,
        numerator: smallvec![],
        denominator: smallvec![1],
    }.is_consistent());
    assert!(Big8 {
        sign: Sign::Positive,
        numerator: smallvec![1],
        denominator: smallvec![1],
    }.is_consistent());
    assert!(!Big8 {
        sign: Sign::Positive,
        numerator: smallvec![1],
        denominator: smallvec![0],
    }.is_consistent());
    assert!(Big8 {
        sign: Sign::Positive,
        numerator: smallvec![1],
        denominator: smallvec![1],
    }.is_consistent());
    assert!(!Big8 {
        sign: Sign::Positive,
        numerator: smallvec![2],
        denominator: smallvec![2],
    }.is_consistent());
    assert!(!Big8 {
        sign: Sign::Positive,
        numerator: smallvec![4],
        denominator: smallvec![6],
    }.is_consistent());
    assert!(!Big8 {
        sign: Sign::Positive,
        numerator: smallvec![4, 4],
        denominator: smallvec![6, 9684, 4],
    }.is_consistent());
    assert!(Big8 {
        sign: Sign::Negative,
        numerator: smallvec![3, 684684685487],
        denominator: smallvec![2],
    }.is_consistent());

    assert!(Big8 {
        sign: Sign::Negative,
        numerator: smallvec![9381074085307],
        denominator: smallvec![3795475922420],
    }.is_consistent());
}
