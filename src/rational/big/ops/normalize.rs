use std::cmp::{min, Ordering};
use std::mem;

use smallvec::SmallVec;

use crate::rational::big::ops::{BITS_PER_WORD, cmp, is_well_formed, sub, sub_assign_result_positive, sub_assign_single_result_positive};
use crate::rational::big::ops::building_blocks::{shl_mut, shr, shr_mut};
use crate::rational::big::ops::div::{div_assign_by_odd, div_assign_double, div_assign_one_word};

#[inline]
pub fn gcd<const S: usize>(left: &SmallVec<[usize; S]>, right: &SmallVec<[usize; S]>) -> SmallVec<[usize; S]> {
    debug_assert!(is_well_formed(left));
    debug_assert!(is_well_formed(right));
    debug_assert!(!left.is_empty());
    debug_assert!(!right.is_empty());
    debug_assert!(left[0] != 1 || left.len() > 1);
    debug_assert!(right[0] != 1 || right.len() > 1);
    debug_assert_ne!(left, right);

    let (left_zero_words, left_zero_bits) = unsafe { trailing_zeros(left) };
    let (right_zero_words, right_zero_bits) = unsafe { trailing_zeros(right) };
    let left = shr(left, left_zero_words, left_zero_bits);
    let right = shr(right, right_zero_words, right_zero_bits);

    let (words, bits) = min((left_zero_words, left_zero_bits), (right_zero_words, right_zero_bits));

    let mut odd_gcd = binary_gcd(left, right);
    shl_mut(&mut odd_gcd, words, bits);

    odd_gcd
}

#[inline]
pub fn prepare_gcd_single<const S: usize>(
    left: &SmallVec<[usize; S]>, mut right: usize,
) -> (SmallVec<[usize; S]>, usize, u32) {
    let left_zero_bits = left[0].trailing_zeros();
    let right_zero_bits = right.trailing_zeros();

    let zero_bits = min(left_zero_bits, right_zero_bits);
    let large_shifted = shr(left,0, left_zero_bits);
    right >>= right_zero_bits;

    return (large_shifted, right, zero_bits)
}

#[inline]
pub fn prepare_gcd_single_mut<const S: usize>(
    left: &mut SmallVec<[usize; S]>, mut right: usize,
) -> (usize, u32, u32, u32) {
    let left_zero_bits = left[0].trailing_zeros();
    let right_zero_bits = right.trailing_zeros();

    let zero_bits = min(left_zero_bits, right_zero_bits);
    shr_mut(left,0, zero_bits);
    right >>= zero_bits;

    return (right, left_zero_bits - zero_bits, right_zero_bits - zero_bits, zero_bits)
}

#[inline]
pub fn gcd_single<const S: usize>(
    mut large: SmallVec<[usize; S]>, small: usize, bits: u32,
) -> usize {
    debug_assert_eq!(small % 2, 1);
    while large.len() > 1 {
        debug_assert_eq!(large[0] % 2, 1);

        sub_assign_single_result_positive(&mut large, small);
        let (zero_words, zero_bits) = unsafe { trailing_zeros(&large) };
        shr_mut(&mut large, zero_words, zero_bits);
    }

    let mut left = large[0];
    let mut right = small;

    loop {
        debug_assert_eq!(left % 2, 1);
        debug_assert_eq!(right % 2, 1);

        if right == left {
            break right << bits;
        }

        if left > right {
            mem::swap(&mut left, &mut right);
        }

        right -= left;

        right >>= right.trailing_zeros();
    }
}

#[inline]
pub fn gcd_scalar(mut left: usize, mut right: usize) -> usize {
    debug_assert_ne!(left, 0);
    debug_assert_ne!(right, 0);
    debug_assert_ne!(left, right);

    let left_zeros = left.trailing_zeros();
    let right_zeros = right.trailing_zeros();
    let zeros = min(left_zeros, right_zeros);

    left >>= left_zeros;
    right >>= right_zeros;

    loop {
        if left == right {
            break right << zeros;
        }

        if left > right {
            mem::swap(&mut left, &mut right);
        }

        right -= left;

        right >>= right.trailing_zeros();
    }
}

#[inline]
pub fn simplify_fraction_gcd_single<const S: usize>(left: &mut SmallVec<[usize; S]>, right: usize) -> usize {
    debug_assert!(is_well_formed(left));
    debug_assert!(!left.is_empty());
    debug_assert_ne!(right, 0);
    debug_assert_ne!(right, 1);
    debug_assert!(left[0] != 1 || left.len() > 1);

    let (mut right, left_to_shift, right_to_shift, _) = prepare_gcd_single_mut(left, right);
    let right_shifted = right >> right_to_shift;

    if right_shifted > 1 {
        let other = shr(left, 0, left_to_shift);
        // TODO(PERFORMANCE): If no left_to_shift, do the first allocation after subtraction?
        if other[0] != 1 || other.len() > 1 {
            debug_assert_eq!(other[0] % 2, 1);
            debug_assert_eq!(right_shifted % 2, 1);
            // TODO(ARCHITECTURE): Don't pass that bit count through the function to cancel it again after
            let gcd = gcd_single(other, right_shifted, 0);

            if gcd > 1 {
                right /= gcd;
                div_assign_one_word(left, gcd);
            }
        }
    }

    right
}

#[inline]
pub fn simplify_fraction_without_info<const S: usize>(numerator: &mut SmallVec<[usize; S]>, denominator: &mut SmallVec<[usize; S]>) {
    debug_assert!(is_well_formed(numerator));
    debug_assert!(is_well_formed(denominator));
    debug_assert!(!numerator.is_empty());
    debug_assert!(!denominator.is_empty());

    if numerator[0] == 1 && numerator.len() == 1 || denominator[0] == 1 && denominator.len() == 1 {
        return;
    }

    match cmp(numerator, denominator) {
        Ordering::Equal => {
            numerator.truncate(1); numerator[0] = 1;
            denominator.truncate(1); denominator[0] = 1;
        }
        Ordering::Less | Ordering::Greater => simplify_fraction_gcd(numerator, denominator),
    }
}

#[inline]
pub fn simplify_fraction_gcd<const S: usize>(left: &mut SmallVec<[usize; S]>, right: &mut SmallVec<[usize; S]>) {
    debug_assert!(is_well_formed(left));
    debug_assert!(is_well_formed(right));
    debug_assert!(!left.is_empty());
    debug_assert!(!right.is_empty());
    debug_assert!(left[0] != 1 || left.len() > 1);
    debug_assert!(right[0] != 1 || right.len() > 1);
    // This restriction could be relaxed, but it might cost an allocation if this is not checked
    // beforehand. So we leave it to the caller to ensure that they are not equal before entering
    // the method.
    debug_assert_ne!(right, left);

    let which_odd = remove_shared_two_factors_mut(left, right);
    let (start_left, start_right) = match which_odd {
        WhichOdd::Left(words_to_shift, bits_to_shift) => {
            match prepare_side(left, right, words_to_shift, bits_to_shift) {
                PreparationResult::StartValues(values) => values,
                PreparationResult::EqualAfterShift => {
                    left.truncate(1);
                    left[0] = 1;
                    right.truncate(words_to_shift + 1);
                    for i in 0..words_to_shift {
                        right[i] = 0;
                    }
                    right[words_to_shift] = 1 << bits_to_shift;
                    return;
                }
            }
        }
        WhichOdd::Right(words_to_shift, bits_to_shift) => {
            match prepare_side(right, left, words_to_shift, bits_to_shift) {
                PreparationResult::StartValues(values) => values,
                PreparationResult::EqualAfterShift => {
                    right.truncate(1);
                    right[0] = 1;
                    // TODO(PERFORMANCE): Reuse allocation?
                    left.truncate(words_to_shift + 1);
                    for i in 0..words_to_shift {
                        left[i] = 0;
                    }
                    left[words_to_shift] = 1 << bits_to_shift;
                    return;
                }
            }
        }
        WhichOdd::Both => (left.clone(), right.clone()),
    };

    if !(start_left[0] == 1 && start_left.len() == 1) && !(start_right[0] == 1 && start_right.len() == 1) {
        let gcd = binary_gcd(start_left, start_right);
        debug_assert!(is_well_formed(&gcd));
        debug_assert!(!gcd.is_empty());
        debug_assert_eq!(gcd[0] % 2, 1);

        if gcd[0] != 1 || gcd.len() > 1 {
            match (cmp(left, &gcd), cmp(right, &gcd)) {
                (Ordering::Equal, _) => {
                    left[0] = 1; left.truncate(1);
                    div_assign_by_odd(right, &gcd);
                }
                (_, Ordering::Equal) => {
                    div_assign_by_odd(left, &gcd);
                    right[0] = 1; right.truncate(1);
                }
                (_, _) => div_assign_double(left, right, gcd),
            }
        }
    }
}

#[inline]
pub fn remove_shared_two_factors_mut<const S: usize>(left: &mut SmallVec<[usize; S]>, right: &mut SmallVec<[usize; S]>) -> WhichOdd {
    let (left_zero_words, left_zero_bits) = unsafe { trailing_zeros(left) };
    let (right_zero_words, right_zero_bits) = unsafe { trailing_zeros(right) };

    let (zero_words, zero_bits) = min((left_zero_words, left_zero_bits), (right_zero_words, right_zero_bits));
    shr_mut(left, zero_words, zero_bits);
    shr_mut(right, zero_words, zero_bits);

    match (left_zero_words, left_zero_bits).cmp(&(right_zero_words, right_zero_bits)) {
        Ordering::Less => {
            let (words, bits) = shift_difference(right_zero_words, right_zero_bits, left_zero_words, left_zero_bits);
            WhichOdd::Left(words, bits)
        },
        Ordering::Equal => WhichOdd::Both,
        Ordering::Greater => {
            let (words, bits) = shift_difference(left_zero_words, left_zero_bits, right_zero_words, right_zero_bits);
            WhichOdd::Right(words, bits)
        },
    }
}

fn shift_difference(left_words: usize, left_bits: u32, right_words: usize, right_bits: u32) -> (usize, u32) {
    debug_assert!(left_words >= right_words);

    if left_bits >= right_bits {
        (left_words - right_words, left_bits - right_bits)
    } else {
        debug_assert!(left_words > right_words);
        (left_words - right_words - 1, BITS_PER_WORD + left_bits - right_bits)
    }
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum WhichOdd {
    Left(usize, u32),
    Right(usize, u32),
    Both,
}

#[inline]
fn prepare_side<const S: usize>(
    already_odd: &SmallVec<[usize; S]>,
    even: &SmallVec<[usize; S]>, words_to_shift: usize, bits_to_shift: u32,
) -> PreparationResult<S> {
    let oddified = shr(even, words_to_shift, bits_to_shift);
    let mut other = match cmp(already_odd, &oddified) {
        Ordering::Less => {
            // left is smallest, subtract it from even_right

            // second start value is known to be positive
            sub(&oddified, already_odd)
        }
        Ordering::Equal => {
            // even = already_odd * 2 ** k with k = words_to_shift * BITS_PER_WORD + bits_to_shift
            return PreparationResult::EqualAfterShift;
        }
        Ordering::Greater => {
            // even_right is smallest, subtract it from left

            // second start value is known to be positive
            sub(already_odd, &oddified)
        }
    };

    // other is now even:
    let (zero_words, zero_bits) = unsafe { trailing_zeros(&other) };
    shr_mut(&mut other, zero_words, zero_bits);

    // now both `other` and `oddified` are odd, it is unknown which one is larger
    PreparationResult::StartValues((other, oddified))
}

enum PreparationResult<const S: usize> {
    StartValues((SmallVec<[usize; S]>, SmallVec<[usize; S]>)),
    EqualAfterShift,
}

#[inline]
fn binary_gcd<const S: usize>(mut left: SmallVec<[usize; S]>, mut right: SmallVec<[usize; S]>) -> SmallVec<[usize; S]> {
    debug_assert!(!left.is_empty() && is_well_formed(&left));
    debug_assert!(!right.is_empty() && is_well_formed(&right));

    loop {
        debug_assert_eq!(left[0] % 2, 1);
        debug_assert_eq!(right[0] % 2, 1);

        unsafe {
            match cmp_and_remove(&mut left, &mut right) {
                Ordering::Less => {
                    sub_assign_result_positive(&mut right, &left);
                    let (zero_words, zero_bits) = trailing_zeros(&right);
                    shr_mut(&mut right, zero_words, zero_bits);
                }
                Ordering::Equal => break left,
                Ordering::Greater => {
                    sub_assign_result_positive(&mut left, &right);
                    let (zero_words, zero_bits) = trailing_zeros(&left);
                    shr_mut(&mut left, zero_words, zero_bits);
                }
            }
        }
    }
}

#[inline]
fn cmp_and_remove<const S: usize>(left: &mut SmallVec<[usize; S]>, right: &mut SmallVec<[usize; S]>) -> Ordering {
    debug_assert!(is_well_formed(left));
    debug_assert!(is_well_formed(right));

    match left.len().cmp(&right.len()) {
        Ordering::Less => Ordering::Less,
        Ordering::Equal => {
            let length = left.len();
            debug_assert_eq!(right.len(), length);

            let mut nr_equal = 0;
            for (left_word, right_word) in left.iter().zip(right.iter()).rev() {
                match left_word.cmp(right_word) {
                    Ordering::Less => {
                        right.truncate(length - nr_equal);
                        return Ordering::Less
                    },
                    Ordering::Equal => {
                        nr_equal += 1;
                    }
                    Ordering::Greater => {
                        left.truncate(length - nr_equal);
                        return Ordering::Greater
                    },
                }
            }

            Ordering::Equal
        }
        Ordering::Greater => Ordering::Greater,
    }
}

/// Count the number of trailing zeros.
///
/// Alternatively phrased, what is the highest power of 2 that divides the input value?
///
/// This method should not be called on a zero value.
///
/// # Returns
///
/// A tuple where the first item indicates the number of (least significant) words that are zero and
/// the second item indicates the number of trailing bits that are zero in the first value that is
/// not zero.
#[inline]
pub unsafe fn trailing_zeros<const S: usize>(values: &SmallVec<[usize; S]>) -> (usize, u32) {
    debug_assert!(!values.is_empty() && is_well_formed(values));

    let mut zero_words = 0;
    while values.get_unchecked(zero_words) == &0 {
        // At least the last value is not allowed to be zero, so we don't have to check bounds
        zero_words += 1;
    }

    (zero_words, values.get_unchecked(zero_words).trailing_zeros())
}

#[cfg(test)]
mod test {
    use smallvec::smallvec;

    use crate::rational::big::creation::int_from_str;
    use crate::rational::big::ops::gcd;
    use crate::rational::big::ops::normalize::{binary_gcd, gcd_scalar, gcd_single, remove_shared_two_factors_mut, simplify_fraction_gcd, simplify_fraction_gcd_single, simplify_fraction_without_info, trailing_zeros, WhichOdd};
    use crate::rational::big::ops::test::SV;

    #[test]
    fn test_binary_gcd() {
        let x: SV = smallvec![7];
        let y: SV = smallvec![15];
        let expected: SV = smallvec![1];
        assert_eq!(binary_gcd(x, y), expected);

        let x: SV = smallvec![35];
        let y: SV = smallvec![125];
        let expected: SV = smallvec![5];
        assert_eq!(binary_gcd(x, y), expected);

        let x: SV = smallvec![6851533845];
        let y: SV = smallvec![6468684843];
        let expected: SV = smallvec![3];
        assert_eq!(binary_gcd(x, y), expected);

        let x: SV = smallvec![2_usize.pow(59) - 55]; // prime
        let y: SV = smallvec![964684684643];
        let expected: SV = smallvec![1];
        assert_eq!(binary_gcd(x, y), expected);

        let x: SV = smallvec![1, 1];
        let y: SV = smallvec![3, 0, 1];
        let expected: SV = smallvec![1];
        assert_eq!(binary_gcd(x, y), expected);

        let x: SV = smallvec![1, 1];
        let y: SV = smallvec![1, 1];
        let expected: SV = smallvec![1, 1];
        assert_eq!(binary_gcd(x, y), expected);

        // [17182455669393173089, 8195493687874724080, 2236847494119194494]
        // [17628647896610972437, 18063123016434192470, 1524534684235201587]
        let x = int_from_str::<8>("761159759740049482819703824192566027846076086339694209633", 10).unwrap();
        let y = int_from_str::<8>("518772270804619926440708190306636065541232071485957284629", 10).unwrap();
        let expected: SV = smallvec![3];
        assert_eq!(binary_gcd(x, y), expected);

        let x = int_from_str::<8>("13315363230513411010491282670607898860050786975267763235425", 10).unwrap();
        let y = int_from_str::<8>("518772270804619926440708190306636065541232071485957284629", 10).unwrap();
        let expected: SV = smallvec![1];
        assert_eq!(binary_gcd(x, y), expected);

        // [17182455669393173089, 8195493687874724080, 2236847494119194494, 2]
        // [15546263315196014731, 7428251573324005790, 5285916862589597670, 2]
        let x = int_from_str::<8>("13315363230513411010491282670607898860050786975267763235425", 10).unwrap();
        let y = int_from_str::<8>("14352907772122650863372699051221170991133251118239677804683", 10).unwrap();
        let expected: SV = smallvec![1];
        assert_eq!(binary_gcd(x, y), expected);

        let x = int_from_str::<8>("2537510112612432421162161736760954813703561240667558277280326395321829260829", 10).unwrap();
        let y = int_from_str::<8>("28066955534242121399724313080842652291012276578744271510348498026737179911481", 10).unwrap();
        let expected: SV = smallvec![1];
        assert_eq!(binary_gcd(x, y), expected);
    }

    #[test]
    fn test_gcd() {
        let x: SV = smallvec![6];
        let y: SV = smallvec![12];
        assert_eq!(gcd(&x, &y), x);

        let x: SV = smallvec![131522304505784511, 2433];
        let y: SV = smallvec![15588921427233345156];
        let expected: SV = smallvec![3];
        assert_eq!(gcd(&x, &y), expected);

        let x: SV = smallvec![15588921427233345156, 28952784];
        let y: SV = smallvec![81331626909];
        let expected: SV = smallvec![81331626909];
        assert_eq!(gcd(&x, &y), expected);

        let x: SV = smallvec![1202576035807934423, 22];
        let y: SV = smallvec![8031097105200];
        let expected: SV = smallvec![501943569075];
        assert_eq!(gcd(&x, &y), expected);

        let x: SV = smallvec![5427079275432240933];
        let y: SV = smallvec![8031097105200];
        let expected: SV = smallvec![6692580921];
        assert_eq!(gcd(&x, &y), expected);

        let x: SV = smallvec![16256560833088857922, 16549708957000594284, 7174888939365837514];
        let y: SV = smallvec![12764522021006322602, 13940785908623865679, 16353990074255549379, 2111485];
        let expected: SV = int_from_str("2441488190682268924480702310120250331237912178039550781250", 10).unwrap();
        assert_eq!(gcd(&x, &y), expected);

        let x: SV = smallvec![0, 16256560833088857922, 16549708957000594284, 7174888939365837514];
        let y: SV = smallvec![0, 12764522021006322602, 13940785908623865679, 16353990074255549379, 2111485];
        let expected: SV = int_from_str("45037507812500000000000000000000000000000000000000000000000000000000000000000", 10).unwrap();
        assert_eq!(gcd(&x, &y), expected);
    }

    #[test]
    fn test_zeros() {
        let x: SV = smallvec![1];
        assert_eq!(unsafe { trailing_zeros(&x) }, (0, 0));

        let x: SV = smallvec![0, 1];
        assert_eq!(unsafe { trailing_zeros(&x) }, (1, 0));

        let x: SV = smallvec![2];
        assert_eq!(unsafe { trailing_zeros(&x) }, (0, 1));

        let x: SV = smallvec![0, 2];
        assert_eq!(unsafe { trailing_zeros(&x) }, (1, 1));

        let x: SV = smallvec![0, 0, 0, 14, 6];
        assert_eq!(unsafe { trailing_zeros(&x) }, (3, 1));
    }

    #[test]
    fn test_simplify_fraction_gcd_single() {
        let mut x: SV = smallvec![990];
        assert_eq!(simplify_fraction_gcd_single(&mut x, 141), 47);
        let expected: SV = smallvec![330];
        assert_eq!(x, expected);
    }

    #[test]
    fn test_simplify_without_info() {
        let x = int_from_str::<8>("1208925819614629174706176", 10).unwrap();
        let y = int_from_str::<8>("10301051460877537453973547267843", 10).unwrap();

        let mut xx = x.clone();
        let mut yy = y.clone();
        simplify_fraction_without_info(&mut xx, &mut yy);
        assert_eq!(xx, x);
        assert_eq!(yy, y);


        let mut x: SV = smallvec![12384794773201432064, 64560677146];
        let mut y: SV = smallvec![12499693862731150083, 66111026448];
        simplify_fraction_without_info(&mut x, &mut y);
        let xx: SV = smallvec![23800000000];
        let yy: SV = smallvec![24371529219];
        assert_eq!(x, xx);
        assert_eq!(y, yy);
    }

    #[test]
    fn test_simplify_fraction_gcd() {
        let mut left: SV = smallvec![3];
        let mut right: SV = smallvec![6];
        simplify_fraction_gcd(&mut left, &mut right);
        let expected_left: SV = smallvec![1];
        let expected_right: SV = smallvec![2];
        assert_eq!(left, expected_left);
        assert_eq!(right, expected_right);

        let mut left: SV = smallvec![18];
        let mut right: SV = smallvec![9];
        simplify_fraction_gcd(&mut left, &mut right);
        let expected_left: SV = smallvec![2];
        let expected_right: SV = smallvec![1];
        assert_eq!(left, expected_left);
        assert_eq!(right, expected_right);

        let mut left: SV = smallvec![10];
        let mut right: SV = smallvec![44];
        simplify_fraction_gcd(&mut left, &mut right);
        let expected_left: SV = smallvec![5];
        let expected_right: SV = smallvec![22];
        assert_eq!(left, expected_left);
        assert_eq!(right, expected_right);

        let mut left = int_from_str::<4>("92599469589222131768757076514696607382155504523751371565834361998764652118557", 10).unwrap();
        let mut right = int_from_str::<4>("80627506337117343961599775375716501347124738605551411762759133617725727360716", 10).unwrap();
        simplify_fraction_gcd(&mut left, &mut right);
        let expected_left = int_from_str::<4>("92599469589222131768757076514696607382155504523751371565834361998764652118557", 10).unwrap();
        let expected_right = int_from_str::<4>("80627506337117343961599775375716501347124738605551411762759133617725727360716", 10).unwrap();
        assert_eq!(left, expected_left);
        assert_eq!(right, expected_right);

        let mut left = int_from_str::<4>("56133911068484242799448626161685304582024553157488543020696996053474359822962", 10).unwrap();
        let mut right = int_from_str::<4>("38216995984691851084372960027886471545826521541414504619469803608024496954797", 10).unwrap();
        let mut x = left.clone(); let mut y = right.clone();
        remove_shared_two_factors_mut(&mut x, &mut y);
        assert_eq!(x, left); assert_eq!(y, right);
        simplify_fraction_gcd(&mut left, &mut right);
        let expected_left = int_from_str::<4>("56133911068484242799448626161685304582024553157488543020696996053474359822962", 10).unwrap();
        let expected_right = int_from_str::<4>("38216995984691851084372960027886471545826521541414504619469803608024496954797", 10).unwrap();
        assert_eq!(left, expected_left);
        assert_eq!(right, expected_right);

        let mut left = int_from_str::<4>("96149135622564868513332764767713630331755573676701733681721499377985831780603", 10).unwrap();
        let mut right = int_from_str::<4>("99939187751827453177194542570098438266282603262618044779272964070464092694778", 10).unwrap();
        simplify_fraction_gcd(&mut left, &mut right);
        let expected_left = int_from_str::<4>("32049711874188289504444254922571210110585191225567244560573833125995277260201", 10).unwrap();
        let expected_right = int_from_str::<4>("33313062583942484392398180856699479422094201087539348259757654690154697564926", 10).unwrap();
        assert_eq!(left, expected_left);
        assert_eq!(right, expected_right);
    }

    #[test]
    fn test_remove_shared_two_factors_mut() {
        let mut left: SV = smallvec![3];
        let mut right: SV = smallvec![6];
        let which_odd = remove_shared_two_factors_mut(&mut left, &mut right);
        assert_eq!(which_odd, WhichOdd::Left(0, 1));
        let expected_left: SV = smallvec![3];
        let expected_right: SV = smallvec![6];
        assert_eq!(left, expected_left);
        assert_eq!(right, expected_right);

        let mut left: SV = smallvec![0, 16256560833088857922, 16549708957000594284, 7174888939365837514];
        let mut right: SV = smallvec![0, 16549708957000594284, 16549708957000594284, 7174888939365837514];
        remove_shared_two_factors_mut(&mut left, &mut right);
        let expected_left: SV = int_from_str("1220744095341134462240351155060125165618956089019775390625", 10).unwrap();
        let expected_right: SV = int_from_str("1220744095341134462240351155060125165619102663081731258806", 10).unwrap();
        assert_eq!(left, expected_left);
        assert_eq!(right, expected_right);

        let mut left: SV = smallvec![0, 12511854210725346487, 1932217123071064976, 10302437120704275430, 18852552];
        let mut right: SV = smallvec![0, 6021696704607738643, 14862474386500622791, 14562584587638410510, 8871];
        remove_shared_two_factors_mut(&mut left, &mut right);
        let expected_left: SV = smallvec![12511854210725346487, 1932217123071064976, 10302437120704275430, 18852552];
        let expected_right: SV = smallvec![6021696704607738643, 14862474386500622791, 14562584587638410510, 8871];
        assert_eq!(left, expected_left);
        assert_eq!(right, expected_right);
    }

    #[test]
    fn test_gcd_scalar() {
        assert_eq!(gcd_scalar(2, 3), 1);
        assert_eq!(gcd_scalar(990, 141), 3);
        assert_eq!(gcd_scalar(4, 2), 2);
        assert_eq!(gcd_scalar(7, 11), 1);
        assert_eq!(gcd_scalar(9889, 11), 11);
        assert_eq!(gcd_scalar(3 * 129, 98540), 1);
        assert_eq!(gcd_scalar(3 * 127, 3 * 98987), 3);
        assert_eq!(gcd_scalar(789 * 987, 789 * 6188988), 2367);
    }

    #[test]
    fn test_gcd_single() {
        assert_eq!(gcd_single::<2>(smallvec![1, 1], 3, 0), 1);
        assert_eq!(gcd_single::<2>(smallvec![1, 2], 3, 0), 3);
        assert_eq!(gcd_single::<2>(smallvec![13835058055282163747, 1 << 3], (1 << 62) + 1, 0), (1 << 62) + 1);
        assert_eq!(gcd_single::<2>(
                smallvec![4611686018427388777, (1 << 7) + (1 << 6) + (1 << 4) + (1 << 3) + (1 << 1)],
                (1 << 62) + 1,
                0,
            ),
            (1 << 62) + 1,
        );
        assert_eq!(gcd_single::<2>(
                smallvec![4611686018427388777, (1 << 7) + (1 << 6) + (1 << 4) + (1 << 3) + (1 << 1)],
                873,
                0,
            ),
            873,
        );
        assert_eq!(gcd_single::<1>(smallvec![7], 3, 0), 1);
    }
}
