use std::cmp::Ordering;
use std::convert::TryFrom;

use num_traits::Zero;
use smallvec::{smallvec, SmallVec};

use crate::{RB, Sign};
use crate::integer::big::creation::from_str_radix;
use crate::integer::big::ops::non_zero::{add_assign, add_assign_single_non_zero, mul_assign_single_non_zero, mul_non_zero, sub, sub_assign_result_positive, subtracting_cmp};
use crate::rational::big::Big8;

#[test]
fn test_ord() {
    let x = RB!(2, 3);
    assert_eq!(x, RB!(2, 3));
    let neg_x = RB!(-2, 3);
    assert!(neg_x < x);
    assert!(x > neg_x);
    assert!(neg_x <= x);
    assert!(x >= neg_x);

    let x = Big8::try_from((Sign::Positive, [1, 1], [1])).unwrap();
    let y = RB!(2);
    assert!(x > y);

    let x = Big8::try_from((Sign::Positive, [1, 1], [23])).unwrap();
    let y = Big8::try_from((Sign::Positive, [2], [23])).unwrap();
    assert!(x > y);

    let x = Big8::try_from((Sign::Positive, [1, 1], [1])).unwrap();
    let y = Big8::try_from((Sign::Positive, [2, 1], [1])).unwrap();
    assert!(x < y);

    let x = Big8::try_from((Sign::Positive, [1, 1], [19])).unwrap();
    let y = Big8::try_from((Sign::Positive, [2, 1], [19])).unwrap();
    assert!(x < y);

    let x = Big8::try_from((Sign::Positive, [0, 0, 1], [19])).unwrap();
    let y = Big8::try_from((Sign::Positive, [2, 2], [19])).unwrap();
    assert!(y <= x);
    assert!(x > y);

    let x = Big8::try_from((Sign::Negative, [0, 0, 1], [19])).unwrap();
    let y = Big8::try_from((Sign::Positive, [2, 2], [19])).unwrap();
    assert!(x < y);

    let x = Big8::try_from((Sign::Negative, [0, 0, 1], [19])).unwrap();
    let y = Big8::try_from((Sign::Negative, [0, 0, 1], [19])).unwrap();
    assert_eq!(x, y);

    let x = Big8::try_from((Sign::Negative, [0, 0, 1], [19])).unwrap();
    let y = Big8::zero();
    assert!(x < y);
    assert!(y >= x);

    let x = Big8::try_from((Sign::Positive, [0, 0, 1], [19])).unwrap();
    let y = Big8::zero();
    assert!(x > y);
    assert!(y <= x);

    assert!(RB!(2, 3) < RB!(3, 4));
}

#[test]
fn test_mul_assign() {
    let mut x = RB!(1, 2);
    let y = RB!(1, 2);
    x *= y;
    assert_eq!(x, RB!(1, 4));

    let mut x = RB!(1, 2);
    let y = RB!(1, 3);
    x *= y;
    assert_eq!(x, RB!(1, 6));

    let mut x = RB!(1, 2);
    let y = RB!(0, 1);
    x *= y;
    assert_eq!(x, RB!(0, 1));

    let mut x = RB!(-1, 2);
    let y = RB!(0, 1);
    x *= y;
    assert_eq!(x, RB!(0, 1));

    let mut x = RB!(-1, 2);
    let y = RB!(-1, 1);
    x *= y;
    assert_eq!(x, RB!(1, 2));

    let mut x = RB!(1, 2);
    let y = RB!(-1, 3);
    x *= y;
    assert_eq!(x, RB!(-1, 6));

    assert_eq!(RB!(3, 1) / RB!(6, 1), RB!(1, 2));

    let limit = 5;
    for a in -limit..limit {
        for b in 1..limit {
            for c in -limit..limit {
                for d in 1..limit {
                    assert_eq!(RB!(a, b as u64) * RB!(c, d as u64), RB!(a * c, (b * d) as u64), "{} / {} * {} / {}", a, b, c, d);
                }
            }
        }
    }
}

#[test]
fn test_add_assign() {
    let mut x = RB!(1, 2);
    let y = RB!(1, 2);
    x += &y;
    assert_eq!(x, RB!(1, 1));

    let mut x = RB!(1, 2);
    let y = RB!(1, 3);
    x += &y;
    assert_eq!(x, RB!(5, 6));

    let mut x = RB!(1, 2);
    let y = RB!(0, 1);
    x += &y;
    assert_eq!(x, RB!(1, 2));

    let mut x = RB!(-1, 2);
    let y = RB!(0, 1);
    x += &y;
    assert_eq!(x, RB!(-1, 2));

    let mut x = RB!(-1, 2);
    let y = RB!(-1, 1);
    x += &y;
    assert_eq!(x, RB!(-3, 2));

    let mut x = RB!(1, 2);
    let y = RB!(-1, 3);
    x += &y;
    assert_eq!(x, RB!(1, 6));

    assert_eq!(RB!(1) + RB!(-2), RB!(-1));
    assert_eq!(RB!(6, 5) + RB!(1, 5), RB!(7, 5));
    assert_eq!(RB!(7, 5) + RB!(3, 5), RB!(2));
    assert_eq!(RB!(8, 5) + RB!(3, 5), RB!(11, 5));
    assert_eq!(RB!(8) + RB!(1, 4), RB!(33, 4));
    assert_eq!(RB!(4, 7) + RB!(5, 6), RB!(4 * 6 + 7 * 5, 7 * 6));
    assert_eq!(RB!(4, 8) + RB!(5, 6), RB!(4 * 6 + 8 * 5, 8 * 6));
    assert_eq!(RB!(8, 15) + RB!(11, 18), RB!(8 * 18 + 11 * 15, 15 * 18));

    assert_eq!(RB!(-5, 3) + RB!(-4, 3), RB!(-3));
    assert_eq!(RB!(-5) + RB!(-5), RB!(-10));
    assert_eq!(RB!(-5, 4) + RB!(-5, 2), RB!(-15, 4));
    assert_eq!(RB!(-5, 4) + RB!(1, 2), RB!(-3, 4));

    let limit = 10;
    for a in -limit..limit {
        for b in 1..limit {
            for c in -limit..limit {
                for d in 1..limit {
                    assert_eq!(RB!(a, b as u64) + RB!(c, d as u64), RB!(a * d + c * b, b as u64 * d as u64), "{} / {} + {} / {}", a, b, c, d);
                }
            }
        }
    }
}

#[test]
fn test_sub_assign() {
    let mut x = RB!(1, 2);
    let y = RB!(1, 2);
    x -= &y;
    assert_eq!(x, RB!(0, 1));

    let mut x = RB!(1, 2);
    let y = RB!(1, 3);
    x -= &y;
    assert_eq!(x, RB!(1, 6));

    let mut x = RB!(1, 2);
    let y = RB!(0, 1);
    x -= &y;
    assert_eq!(x, RB!(1, 2));

    let mut x = RB!(-1, 2);
    let y = RB!(0, 1);
    x -= &y;
    assert_eq!(x, RB!(-1, 2));

    let mut x = RB!(-1, 2);
    let y = RB!(-1, 1);
    x -= &y;
    assert_eq!(x, RB!(1, 2));

    let mut x = RB!(1, 2);
    let y = RB!(-1, 3);
    x -= &y;
    assert_eq!(x, RB!(5, 6));

    assert_eq!((&RB!(200) - RB!(0)), RB!(200));

    assert_eq!(RB!(1, 6) - RB!(5, 12), RB!(-1, 4));
    assert_eq!(RB!(4, 7) - RB!(5, 6), RB!(4 * 6 - 7 * 5, 7 * 6));
    assert_eq!(RB!(4, 8) - RB!(5, 6), RB!(4 * 6 - 8 * 5, 8 * 6));
    assert_eq!(RB!(8) - RB!(17, 2), RB!(-1, 2));
    assert_eq!(RB!(6, 5) - RB!(1, 5), RB!(1));
    assert_eq!(RB!(7, 5) - RB!(1, 5), RB!(6, 5));
    assert_eq!(RB!(8, 5) - RB!(3, 5), RB!(1));
    assert_eq!(RB!(8, 15) - RB!(11, 18), RB!(8 * 18 - 11 * 15, 15 * 18));

    let limit = 10;
    for a in -limit..limit {
        for b in 1..limit {
            for c in -limit..limit {
                for d in 1..limit {
                    assert_eq!(RB!(a, b as u64) - RB!(c, d as u64), RB!(a * d - c * b, b as u64 * d as u64), "{} / {} - {} / {}", a, b, c, d);
                }
            }
        }
    }
}

#[test]
fn test_bigint_add_assign() {
    type SV = SmallVec<[usize; 8]>;

    // Same length, no overflow
    let mut x: SV = smallvec![1];
    let y: SV = smallvec![1];
    add_assign(&mut x, &y);
    let expected: SV = smallvec![2];
    assert_eq!(x, expected);

    // Same length, overflow
    let mut x: SV = smallvec![usize::MAX];
    let y: SV = smallvec![1];
    add_assign(&mut x, &y);
    let expected: SV = smallvec![0, 1];
    assert_eq!(x, expected);

    // First shorter
    let mut x: SV = smallvec![usize::MAX];
    let y: SV = smallvec![0, 1];
    add_assign(&mut x, &y);
    let expected: SV = smallvec![usize::MAX, 1];
    assert_eq!(x, expected);

    // First longer
    let mut x: SV = smallvec![0, 1];
    let y: SV = smallvec![usize::MAX];
    add_assign(&mut x, &y);
    let expected: SV = smallvec![usize::MAX, 1];
    assert_eq!(x, expected);

    // First shorter, second repeated carry and end with carry
    let mut x: SV = smallvec![1];
    let y: SV = smallvec![usize::MAX, usize::MAX, usize::MAX];
    add_assign(&mut x, &y);
    let expected: SV = smallvec![0, 0, 0, 1];
    assert_eq!(x, expected);

    // First shorter, second repeated carry and end without carry
    let mut x: SV = smallvec![1];
    let y: SV = smallvec![usize::MAX, usize::MAX, usize::MAX, 1];
    add_assign(&mut x, &y);
    let expected: SV = smallvec![0, 0, 0, 2];
    assert_eq!(x, expected);

    let mut x = from_str_radix::<10, 3>("68498984987984986896468746354684684684968").unwrap();
    let y = from_str_radix::<10, 3>("676230147000334142150220547988205853833725436834339162").unwrap();
    add_assign(&mut x, &y);
    let expected = from_str_radix::<10, 3>("676230147000402641135208532975102322580080121519024130").unwrap();
    assert_eq!(x, expected);

    let mut x = from_str_radix::<10, 3>("68498984987984986896468746354684684684968").unwrap();
    let y = from_str_radix::<10, 3>("676230147000334142150220547988205853833725436834339162").unwrap();
    add_assign(&mut x, &y);
    let expected = from_str_radix::<10, 3>("676230147000402641135208532975102322580080121519024130").unwrap();
    assert_eq!(x, expected);

    let mut x = from_str_radix::<10, 3>("13282457576090002999724080439382126039670578699984818946692017256202044898307").unwrap();
    let y = from_str_radix::<10, 3>("52138404881359597776641425341642690746162654701917220048397413248229209595444").unwrap();
    add_assign(&mut x, &y);
    let expected = from_str_radix::<10, 3>("65420862457449600776365505781024816785833233401902038995089430504431254493751").unwrap();
    assert_eq!(x, expected);

    let mut x = from_str_radix::<10, 3>("92599469589222131768757076514696607382155504523751371565834361998764652118557").unwrap();
    let y = from_str_radix::<10, 3>("80627506337117343961599775375716501347124738605551411762759133617725727360716").unwrap();
    add_assign(&mut x, &y);
    let expected = from_str_radix::<10, 3>("173226975926339475730356851890413108729280243129302783328593495616490379479273").unwrap();
    assert_eq!(x, expected);

    let mut x: SV = smallvec![12105913134615829217, 2];
    let y: SV = smallvec![10094979305352480000];
    add_assign(&mut x, &y);
    let expected: SV = smallvec![3754148366258757601, 3];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![9471424444590689296, 27735644];
    let y: SV = smallvec![10094979305352480000];
    add_assign(&mut x, &y);
    let expected: SV = smallvec![1119659676233617680, 27735645];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![0, 0, 0, 0, 1];
    let y: SV = smallvec![1];
    add_assign(&mut x, &y);
    let expected: SV = smallvec![1, 0, 0, 0, 1];
    assert_eq!(x, expected);
}

#[test]
fn test_bigint_sub_assign() {
    type SV = SmallVec<[usize; 8]>;

    // Same length, no overflow
    let mut x: SV = smallvec![2];
    let y: SV = smallvec![1];
    unsafe { sub_assign_result_positive(&mut x, &y); }
    let expected: SV = smallvec![1];
    assert_eq!(x, expected);

    // First longer, overflow
    let mut x: SV = smallvec![0, 0, 1];
    let y: SV = smallvec![1];
    unsafe { sub_assign_result_positive(&mut x, &y); }
    let expected: SV = smallvec![usize::MAX, usize::MAX];
    assert_eq!(x, expected);

    // First longer, overflow
    let mut x: SV = smallvec![0, 1, 1];
    let y: SV = smallvec![1, 1];
    unsafe { sub_assign_result_positive(&mut x, &y); }
    let expected: SV = smallvec![usize::MAX, usize::MAX];
    assert_eq!(x, expected);

    // First longer
    let mut x: SV = smallvec![0, 2];
    let y: SV = smallvec![1];
    unsafe { sub_assign_result_positive(&mut x, &y); }
    let expected: SV = smallvec![usize::MAX, 1];
    assert_eq!(x, expected);

    // First longer
    let mut x: SV = smallvec![0, 1];
    let y: SV = smallvec![usize::MAX];
    unsafe { sub_assign_result_positive(&mut x, &y); }
    let expected: SV = smallvec![1];
    assert_eq!(x, expected);

    let mut x = from_str_radix::<10, 3>("676230147000334142150220547988205853833725436834339162").unwrap();
    let y = from_str_radix::<10, 3>("68498984987984986896468746354684684684968").unwrap();
    unsafe { sub_assign_result_positive(&mut x, &y); }
    let expected = from_str_radix::<10, 3>("676230147000265643165232563001309385087370752149654194").unwrap();
    assert_eq!(x, expected);

    let mut x = from_str_radix::<10, 3>("676230147000334142150220547988205853833725436834339162").unwrap();
    let y = from_str_radix::<10, 3>("68498984987984986896468746354684684684968").unwrap();
    unsafe { sub_assign_result_positive(&mut x, &y); }
    let expected = from_str_radix::<10, 3>("676230147000265643165232563001309385087370752149654194").unwrap();
    assert_eq!(x, expected);

    let mut x = from_str_radix::<10, 3>("52138404881359597776641425341642690746162654701917220048397413248229209595444").unwrap();
    let y = from_str_radix::<10, 3>("13282457576090002999724080439382126039670578699984818946692017256202044898307").unwrap();
    unsafe { sub_assign_result_positive(&mut x, &y); }
    let expected = from_str_radix::<10, 3>("38855947305269594776917344902260564706492076001932401101705395992027164697137").unwrap();
    assert_eq!(x, expected);

    let mut x = from_str_radix::<10, 3>("92599469589222131768757076514696607382155504523751371565834361998764652118557").unwrap();
    let y = from_str_radix::<10, 3>("80627506337117343961599775375716501347124738605551411762759133617725727360716").unwrap();
    unsafe { sub_assign_result_positive(&mut x, &y); }
    let expected = from_str_radix::<10, 3>("11971963252104787807157301138980106035030765918199959803075228381038924757841").unwrap();
    assert_eq!(x, expected);
}

#[test]
fn test_sub() {
    type SV = SmallVec<[usize; 8]>;

    let x: SV = smallvec![11];
    let y: SV = smallvec![5];
    let result = unsafe { sub(&x, &y) };
    let expected: SV = smallvec![6];
    assert_eq!(result, expected);

    let x: SV = smallvec![1, 1];
    let y: SV = smallvec![2];
    let result = unsafe { sub(&x, &y) };
    let expected: SV = smallvec![usize::MAX];
    assert_eq!(result, expected);
}

#[test]
fn test_mul() {
    type SV = SmallVec<[usize; 8]>;

    unsafe {
        let x: SV = smallvec![1];
        let y = mul_non_zero::<8>(&x, &x);
        let expected: SV = smallvec![1];
        assert_eq!(y, expected);

        let x: SV = smallvec![1, 1];
        let y: SV = smallvec![1];
        let z = mul_non_zero::<8>(&x, &y);
        let expected: SV = smallvec![1, 1];
        assert_eq!(z, expected);

        let x: SV = smallvec![1, 1];
        let y: SV = smallvec![1, 1];
        let z = mul_non_zero::<8>(&x, &y);
        let expected: SV = smallvec![1, 2, 1];
        assert_eq!(z, expected);

        let x: SV = smallvec![1, 1, 1, 1, 1];
        let y: SV = smallvec![1];
        let z = mul_non_zero::<8>(&x, &y);
        let expected: SV = smallvec![1, 1, 1, 1, 1];
        assert_eq!(z, expected);

        let x: SV = smallvec![1, 1, 1];
        let y: SV = smallvec![1, 1];
        let z = mul_non_zero::<8>(&x, &y);
        let expected: SV = smallvec![1, 2, 2, 1];
        assert_eq!(z, expected);

        let x: SV = smallvec![616865135358];
        let y: SV = smallvec![318864];
        let z = mul_non_zero::<8>(&x, &y);
        let expected: SV = smallvec![196696084520793312];
        assert_eq!(z, expected);

        let x: SV = smallvec![6168651349984645358];
        let y: SV = smallvec![31884648664];
        let z = mul_non_zero::<8>(&x, &y);
        let expected: SV = smallvec![2946066457054546128, 10662330449];
        assert_eq!(z, expected);

        let x = from_str_radix::<10, 8>("68468468498498987982211").unwrap();
        let y = from_str_radix::<10, 8>("6546845498498498766994984941").unwrap();
        let z = mul_non_zero::<8>(&x, &y);
        let expected = from_str_radix::<10, 8>("448252484778484366353430902886798387597665920884551").unwrap();
        assert_eq!(z, expected);

        let x = from_str_radix::<10, 8>("6846846598498849754611315531318498498987982211").unwrap();
        let y = from_str_radix::<10, 8>("65468454984984984989846544418766994984941").unwrap();
        let z = mul_non_zero::<8>(&x, &y);
        let expected = from_str_radix::<10, 8>("448252468322919508262853593995316625918253404600786790378945516838911366717665920884551").unwrap();
        assert_eq!(z, expected);

        let x = from_str_radix::<10, 8>("68468465984988497546416161698149845311616811315531318498498987982211").unwrap();
        let y = from_str_radix::<10, 8>("654684549849849849898465444187669985648546168541168443544984941").unwrap();
        let z = mul_non_zero::<8>(&x, &y);
        let expected = from_str_radix::<10, 8>("44825246832291950826483732998274014934302316363445684381827995526563290241044825692328446158571230923548759376413518121517970884551").unwrap();
        assert_eq!(z, expected);

        let x = from_str_radix::<10, 8>("684684659849886161698149845311616811315531318498498987982211").unwrap();
        let y = from_str_radix::<10, 8>("654684549849849865444187669985648546168541168443544984941").unwrap();
        let z = mul_non_zero::<8>(&x, &y);
        let expected = from_str_radix::<10, 8>("448252468322920295517819464130433697009775835506250832016384806318621662991558571230923548759376413518121517970884551").unwrap();
        assert_eq!(z, expected);

        let x = from_str_radix::<10, 8>("1237940039285380274899124191").unwrap();
        let y = from_str_radix::<10, 8>("2475880078570760549798248403").unwrap();
        let z = mul_non_zero::<8>(&x, &y);
        let expected = from_str_radix::<10, 8>("3064991081731777716716693916889274006560267730564416973").unwrap();
        assert_eq!(z, expected);

        let mut x: SV = smallvec![
            0x7146b08a5e154,
            0xec91987b2f52425e,
            0x1ebf6edad66a22f9,
            0xd77eaaba0c9edebb,
            0xf7110260b98b2714,
            0x426c694a49d8e6e8,
        ];
        x.reverse();
        let mut y: SV = smallvec![0x2cd0de4066, 0xd14fd230f03d41d8, 0x2090b6d374079b2f];
        y.reverse();
        let z = mul_non_zero::<8>(&x, &y);
        let expected: SV = smallvec![
            0x5494de2152f8dc98,
            0xaa45e7c3cd025cf6,
            0xda234e5e081bc853,
            0x07be6f417d03787e,
            0x3a21f12680711212,
            0xbc462415317db996,
            0xb39a7d94c9beea07,
            0xf04db0367a800873,
            0x13d4921,
        ];
        assert_eq!(z, expected);

        let x = from_str_radix::<10, 3>("68468465468464168545346854646").unwrap();
        let y = from_str_radix::<10, 3>("9876519684989849849849847").unwrap();
        let z = from_str_radix::<10, 3>("676230147000334142150220547988205853833725436834339162").unwrap();
        assert_eq!(mul_non_zero::<8>(&x, &y), z);

        let x = from_str_radix::<10, 3>("9876519684989849849849847").unwrap();
        let y = from_str_radix::<10, 3>("68468465468464168545346854646").unwrap();
        let z = from_str_radix::<10, 3>("676230147000334142150220547988205853833725436834339162").unwrap();
        assert_eq!(mul_non_zero::<8>(&x, &y), z);
    }
}

#[test]
fn test_mul_assign_single() {
    type SV = SmallVec<[usize; 8]>;

    let mut x: SV = smallvec![1];
    mul_assign_single_non_zero(&mut x, 1);
    let expected: SV = smallvec![1];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![1, 1];
    mul_assign_single_non_zero(&mut x, 1);
    let expected: SV = smallvec![1, 1];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![1, 1, 1, 1, 1];
    mul_assign_single_non_zero(&mut x, 3);
    let expected: SV = smallvec![3, 3, 3, 3, 3];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![1 << 63];
    mul_assign_single_non_zero(&mut x, 1 << 63);
    let expected: SV = smallvec![0, 1 << (126 - 64)];
    assert_eq!(x, expected);

    let mut x = from_str_radix::<10, 4>("684684659849886161698149845311616811315531318498498987982211").unwrap();
    mul_assign_single_non_zero(&mut x, 646846844846);
    let expected = from_str_radix::<10, 4>("442886111938355599686725600875542300070422743926852384563217257325034506").unwrap();
    assert_eq!(x, expected);

    // (2 ** 64 - 1) % 6700417 == 0
    // ((2 ** 64 - 1) / 6700417) * 2 ** 64
    let mut x = from_str_radix::<10, 8>("50785252159819077446213849579520").unwrap();
    mul_assign_single_non_zero(&mut x, 6700417);
    // (2 ** 64 - 1) * 2 ** 64
    let expected: SV = smallvec![0, usize::MAX];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![274177];
    mul_assign_single_non_zero(&mut x, 67280421310721);
    let expected: SV = smallvec![1, 1];
    assert_eq!(x, expected);
}

#[test]
fn test_add_assign_single() {
    let mut x = from_str_radix::<10, 4>("684684659849886161698149845311616811315531318498498987982211").unwrap();
    add_assign_single_non_zero(&mut x, 646846844846);
    let expected = from_str_radix::<10, 4>("684684659849886161698149845311616811315531318499145834827057").unwrap();
    assert_eq!(x, expected);
}

#[test]
fn test_subtracting_cmp_ne() {
    type SV = SmallVec<[usize; 8]>;

    let mut x: SV = smallvec![0, 1];
    let y: SV = smallvec![1];
    assert_eq!(subtracting_cmp(&mut x, &y), Ordering::Greater);
    let expected: SV = smallvec![usize::MAX];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![1, 1];
    let y: SV = smallvec![1];
    assert_eq!(subtracting_cmp(&mut x, &y), Ordering::Greater);
    let expected: SV = smallvec![0, 1];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![0, 0, 1];
    let y: SV = smallvec![1];
    assert_eq!(subtracting_cmp(&mut x, &y), Ordering::Greater);
    let expected: SV = smallvec![usize::MAX, usize::MAX];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![1];
    let y: SV = smallvec![2];
    assert_eq!(subtracting_cmp(&mut x, &y), Ordering::Less);
    let expected: SV = smallvec![1];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![1, 0, 0, 1];
    let y: SV = smallvec![2, 0, 0, 1];
    assert_eq!(subtracting_cmp(&mut x, &y), Ordering::Less);
    let expected: SV = smallvec![1];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![0, 0, 0, 2];
    let y: SV = smallvec![1];
    assert_eq!(subtracting_cmp(&mut x, &y), Ordering::Greater);
    let expected: SV = smallvec![usize::MAX, usize::MAX, usize::MAX, 1];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![0, 0, 0, 1];
    let y: SV = smallvec![usize::MAX, usize::MAX, usize::MAX];
    assert_eq!(subtracting_cmp(&mut x, &y), Ordering::Greater);
    let expected: SV = smallvec![1];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![1, 0, 0, 2];
    let y: SV = smallvec![2, 0, 0, 1];
    assert_eq!(subtracting_cmp(&mut x, &y), Ordering::Greater);
    let expected: SV = smallvec![usize::MAX, usize::MAX, usize::MAX];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![1];
    let y: SV = smallvec![0, 1];
    assert_eq!(subtracting_cmp(&mut x, &y), Ordering::Less);
    let expected: SV = smallvec![usize::MAX];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![1];
    let y: SV = smallvec![1, 1];
    assert_eq!(subtracting_cmp(&mut x, &y), Ordering::Less);
    let expected: SV = smallvec![0, 1];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![1];
    let y: SV = smallvec![1, 0, 0, 1];
    assert_eq!(subtracting_cmp(&mut x, &y), Ordering::Less);
    let expected: SV = smallvec![0, 0, 0, 1];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![1];
    let y: SV = smallvec![2, 0, 0, 1];
    assert_eq!(subtracting_cmp(&mut x, &y), Ordering::Less);
    let expected: SV = smallvec![1, 0, 0, 1];
    assert_eq!(x, expected);

    let mut x: SV = smallvec![1];
    let y: SV = smallvec![0, 0, 0, 1];
    assert_eq!(subtracting_cmp(&mut x, &y), Ordering::Less);
    let expected: SV = smallvec![usize::MAX, usize::MAX, usize::MAX];
    assert_eq!(x, expected);
}

#[test]
fn test_neg() {
    assert_eq!(-RB!(1), RB!(-1));
    assert_eq!(-RB!(0), RB!(0));
    assert_eq!(-&RB!(0), RB!(0));
    assert_eq!(-&RB!(1), RB!(-1));
}
