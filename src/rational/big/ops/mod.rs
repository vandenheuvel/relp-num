use std::cmp::Ordering;
use std::iter::Sum;
use std::mem;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use num_traits::Zero;
use smallvec::SmallVec;

use crate::rational::big::Big;
use crate::rational::big::ops::building_blocks::{addmul_1, carrying_add_mut, carrying_sub, carrying_sub_mut, mul_1, sub_assign_slice, sub_n, to_twos_complement};
use crate::rational::big::ops::div::div as div_by_odd_or_even;
use crate::rational::big::ops::normalize::{lcm, simplify_fraction_gcd, simplify_fraction_without_info};
use crate::sign::Sign;

pub mod building_blocks;
pub mod div;
pub mod normalize;

// TODO(PERFORMANCE): Save the constant as usize or as u32?
pub const BITS_PER_WORD: usize = mem::size_of::<usize>() * 8;

impl<const S: usize> Add<Big<S>> for Big<S> {
    type Output = Self;

    fn add(mut self, rhs: Big<S>) -> Self::Output {
        // TODO(PERFORMANCE): Can The ownership of rhs be utilized?
        self += &rhs;
        self
    }
}

impl<const S: usize> Add<Big<S>> for &Big<S> {
    type Output = Big<S>;

    fn add(self, rhs: Big<S>) -> Self::Output {
        Add::add(rhs, self)
    }
}

impl<const S: usize> Add<&Big<S>> for Big<S> {
    type Output = Self;

    fn add(mut self, rhs: &Big<S>) -> Self::Output {
        self += rhs;
        self
    }
}

impl<const S: usize> Add for &Big<S> {
    type Output = Big<S>;

    fn add(self, rhs: Self) -> Self::Output {
        // TODO(PERFORMANCE): Which one should be cloned?
        let x = self.clone();
        x + rhs
    }
}

impl<const S: usize> AddAssign<Big<S>> for Big<S> {
    fn add_assign(&mut self, rhs: Big<S>) {
        AddAssign::add_assign(self, &rhs);
    }
}

impl<const S: usize> AddAssign<&Big<S>> for Big<S> {
    fn add_assign(&mut self, rhs: &Big<S>) {
        match (self.sign, rhs.sign) {
            (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => self.add(rhs),
            (Sign::Positive, Sign::Negative) | (Sign::Negative, Sign::Positive) => self.sub(rhs),
            (_, Sign::Zero) => {},
            (Sign::Zero, _) => {
                *self = Self {
                    sign: rhs.sign,
                    numerator: rhs.numerator.clone(),
                    denominator: rhs.denominator.clone(),
                };
            },
        }
    }
}

impl<const S: usize> Sub<Big<S>> for Big<S> {
    type Output = Self;

    fn sub(self, rhs: Big<S>) -> Self::Output {
        Sub::sub(self, &rhs)
    }
}

impl<const S: usize> Sub<&Big<S>> for Big<S> {
    type Output = Self;

    fn sub(mut self, rhs: &Big<S>) -> Self::Output {
        SubAssign::sub_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Sub<Big<S>> for &Big<S> {
    type Output = Big<S>;

    fn sub(self, rhs: Big<S>) -> Self::Output {
        Sub::sub(rhs, self)
    }
}

impl<const S: usize> Sub for &Big<S> {
    type Output = Big<S>;

    fn sub(self, rhs: Self) -> Self::Output {
        // TODO(PERFORMANCE): Which one should be cloned?
        Sub::sub(self.clone(), rhs)
    }
}

impl<const S: usize> SubAssign<Big<S>> for Big<S> {
    fn sub_assign(&mut self, rhs: Big<S>) {
        SubAssign::sub_assign(self, &rhs);
    }
}

impl<const S: usize> SubAssign<&Big<S>> for Big<S> {
    fn sub_assign(&mut self, rhs: &Big<S>) {
        match (self.sign, rhs.sign) {
            (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => self.sub(rhs),
            (Sign::Positive, Sign::Negative) | (Sign::Negative, Sign::Positive) => self.add(rhs),
            (_, Sign::Zero) => {},
            (Sign::Zero, _) => {
                *self = Self {
                    sign: !rhs.sign,
                    numerator: rhs.numerator.clone(),
                    denominator: rhs.denominator.clone(),
                };
            },
        }
    }
}

impl<const S: usize> Sum for Big<S> {
    fn sum<I: Iterator<Item=Self>>(mut iter: I) -> Self {
        let first = iter.next();
        match first {
            None => <Self as num_traits::Zero>::zero(),
            Some(mut total) => {
                while let Some(next_value) = iter.next() {
                    total += next_value;
                }

                total
            }
        }
    }
}

impl<const S: usize> Big<S> {
    fn add(&mut self, rhs: &Self) {
        if self.denominator == rhs.denominator {
            add_assign(&mut self.numerator, &rhs.numerator);

            // Numerator can't be zero

            if self.numerator == self.denominator {
                self.numerator[0] = 1;
                self.numerator.truncate(1);
                self.denominator[0] = 1;
                self.denominator.truncate(1);
            } else if self.denominator[0] != 1 || self.denominator.len() > 1 {
                simplify_fraction_gcd(&mut self.numerator, &mut self.denominator);
            }
        } else {
            if self.denominator[0] == 1 && self.denominator.len() == 1 { // denominator == 1
                self.numerator = mul(&self.numerator, &rhs.denominator);
                add_assign(&mut self.numerator, &rhs.numerator);
                self.denominator = rhs.denominator.clone();
            } else if rhs.denominator[0] == 1 && rhs.denominator.len() == 1 { // denominator == 1
                let numerator = mul(&rhs.numerator, &self.denominator);
                add_assign(&mut self.numerator, &numerator);
            } else {
                // Neither denominator is 1

                let lcm = lcm(&self.denominator, &rhs.denominator);

                let left_numerator = div_by_odd_or_even(&lcm, &self.denominator);
                self.numerator = mul(&self.numerator, &left_numerator);
                let right_numerator = div_by_odd_or_even(&lcm, &rhs.denominator);
                let right_numerator = mul(&right_numerator, &rhs.numerator);

                add_assign(&mut self.numerator, &right_numerator);
                self.denominator = lcm;
            }
        }
    }
    fn sub(&mut self, rhs: &Self) {
        if self.denominator == rhs.denominator {
            match subtracting_cmp(&mut self.numerator, &rhs.numerator) {
                Ordering::Less => {
                    self.sign = !self.sign;
                }
                Ordering::Equal => {
                    self.sign = Sign::Zero;
                    self.denominator[0] = 1;
                    self.denominator.truncate(1);
                }
                Ordering::Greater => {}
            }
        } else {
            if self.denominator[0] == 1 && self.denominator.len() == 1 { // denominator == 1
                self.numerator = mul(&self.numerator, &rhs.denominator);

                if subtracting_cmp_ne(&mut self.numerator, &rhs.numerator) == UnequalOrdering::Less {
                    self.sign = !self.sign;
                }
                self.denominator = rhs.denominator.clone();
            } else if rhs.denominator[0] == 1 && rhs.denominator.len() == 1 { // denominator == 1
                let numerator = mul(&rhs.numerator, &self.denominator);

                if subtracting_cmp_ne(&mut self.numerator, &numerator) == UnequalOrdering::Less {
                    self.sign = !self.sign;
                }
            } else {
                // Neither denominator is 1

                let lcm = lcm(&self.denominator, &rhs.denominator);

                let left_numerator = div_by_odd_or_even(&lcm, &self.denominator);
                self.numerator = mul(&self.numerator, &left_numerator);
                let right_numerator = div_by_odd_or_even(&lcm, &rhs.denominator);
                let right_numerator = mul(&right_numerator, &rhs.numerator);

                if subtracting_cmp_ne(&mut self.numerator, &right_numerator) == UnequalOrdering::Less {
                    self.sign = !self.sign;
                }
                self.denominator = lcm;
            }
        }
    }
}

fn cmp(left: &[usize], right: &[usize]) -> Ordering {
    // debug_assert!(is_well_formed(left));
    // debug_assert!(is_well_formed(right));

    match left.len().cmp(&right.len()) {
        Ordering::Less => Ordering::Less,
        Ordering::Equal => {
            for (left_word, right_word) in left.iter().zip(right.iter()).rev() {
                match left_word.cmp(right_word) {
                    Ordering::Less => return Ordering::Less,
                    Ordering::Equal => {}
                    Ordering::Greater => return Ordering::Greater,
                }
            }

            Ordering::Equal
        }
        Ordering::Greater => Ordering::Greater,
    }
}

pub fn subtracting_cmp<const S: usize>(left: &mut SmallVec<[usize; S]>, right: &SmallVec<[usize; S]>) -> Ordering {
    debug_assert!(is_well_formed(left));
    debug_assert!(is_well_formed(right));

    if left.len() > right.len() {
        let carry = unsafe { sub_assign_slice(&mut left[..right.len()], right) };
        debug_assert!(!carry);
        Ordering::Greater
    } else {
        // left.len() <= right.len()
        let mut last_non_zero_index = None;
        let mut carry = false;
        // TODO(PERFORMANCE): Is assembler faster?
        for i in 0..left.len() {
            carry = carrying_sub_mut(&mut left[i], right[i], carry);
            if left[i] != 0 {
                last_non_zero_index = Some(i);
            }
        }
        if carry {
            to_twos_complement(left);
            Ordering::Less
        } else {
            match last_non_zero_index {
                None => {
                    left.clear();
                    Ordering::Equal
                }
                Some(index) => {
                    left.truncate(index);
                    Ordering::Greater
                }
            }
        }
    }
}

impl<const S: usize> Mul for Big<S> {
    type Output = Self;

    fn mul(mut self, rhs: Self) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Mul<&Big<S>> for Big<S> {
    type Output = Self;

    fn mul(mut self, rhs: &Big<S>) -> Self::Output {
        // TODO(PERFORMANCE): Should cloning be avoided?
        MulAssign::mul_assign(&mut self, rhs.clone());
        self
    }
}

impl<const S: usize> Mul<Big<S>> for &Big<S> {
    type Output = Big<S>;

    fn mul(self, rhs: Big<S>) -> Self::Output {
        Mul::mul(rhs, self)
    }
}

impl<const S: usize> Mul<&Big<S>> for &Big<S> {
    type Output = Big<S>;

    fn mul(self, rhs: &Big<S>) -> Self::Output {
        let mut x = self.clone();
        // TODO(PERFORMANCE): Should cloning be avoided?
        MulAssign::mul_assign(&mut x, rhs.clone());
        x
    }
}

impl<const S: usize> MulAssign for Big<S> {
    fn mul_assign(&mut self, rhs: Self) {
        match (self.sign, rhs.sign) {
            (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                self.sign *= rhs.sign;
                self.mul(rhs.numerator, rhs.denominator);
            }
            (Sign::Positive | Sign::Negative, Sign::Zero) => {
                self.set_zero();
            }
            (Sign::Zero, _) => {}
        }
    }
}

impl<const S: usize> MulAssign<&Big<S>> for Big<S> {
    fn mul_assign(&mut self, rhs: &Self) {
        match (self.sign, rhs.sign) {
            (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                self.sign *= rhs.sign;
                self.mul(rhs.numerator.clone(), rhs.denominator.clone());
            }
            (Sign::Positive | Sign::Negative, Sign::Zero) => {
                self.set_zero();
            }
            (Sign::Zero, _) => {}
        }
    }
}

impl<const S: usize> Div<Big<S>> for Big<S> {
    type Output = Big<S>;

    fn div(mut self, rhs: Big<S>) -> Self::Output {
        DivAssign::div_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Div<&Big<S>> for Big<S> {
    type Output = Big<S>;

    fn div(mut self, rhs: &Big<S>) -> Self::Output {
        DivAssign::div_assign(&mut self, rhs);
        self
    }
}

impl<const S: usize> Div<Big<S>> for &Big<S> {
    type Output = Big<S>;

    fn div(self, rhs: Big<S>) -> Self::Output {
        let mut x = self.clone();
        DivAssign::div_assign(&mut x, rhs);
        x
    }
}

impl<const S: usize> Div<&Big<S>> for &Big<S> {
    type Output = Big<S>;

    fn div(self, rhs: &Big<S>) -> Self::Output {
        let mut x = self.clone();
        // TODO(PERFORMANCE): Should cloning be avoided?
        DivAssign::div_assign(&mut x, rhs.clone());
        x
    }
}

impl<const S: usize> DivAssign for Big<S> {
    fn div_assign(&mut self, rhs: Self) {
        match (self.sign, rhs.sign) {
            (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                self.sign *= rhs.sign;
                self.mul(rhs.denominator, rhs.numerator);
            }
            (Sign::Positive | Sign::Negative, Sign::Zero) => panic!(),
            (Sign::Zero, _) => {}
        }
    }
}

impl<const S: usize> DivAssign<&Big<S>> for Big<S> {
    fn div_assign(&mut self, rhs: &Self) {
        match (self.sign, rhs.sign) {
            (Sign::Positive | Sign::Negative, Sign::Positive | Sign::Negative) => {
                self.sign *= rhs.sign;
                self.mul(rhs.denominator.clone(), rhs.numerator.clone());
            }
            (Sign::Positive | Sign::Negative, Sign::Zero) => panic!(),
            (Sign::Zero, _) => {}
        }
    }
}

impl<const S: usize> Big<S> {
    fn mul(&mut self, mut rhs_numerator: SmallVec<[usize; S]>, mut rhs_denominator: SmallVec<[usize; S]>) {
        if (rhs_denominator[0] != 1 || rhs_denominator.len() > 1) && (self.numerator.len() != 1 || self.numerator[0] != 1) {
            if cmp(&rhs_denominator, &self.numerator) == Ordering::Equal {
                self.numerator = rhs_numerator;
                simplify_fraction_without_info(&mut self.numerator, &mut self.denominator);
                return;
            } else {
                simplify_fraction_gcd(&mut self.numerator, &mut rhs_denominator);
            }
        }
        if (self.denominator[0] != 1 || self.denominator.len() > 1) && (rhs_numerator.len() != 1 || rhs_numerator[0] != 1) {
            if cmp(&rhs_numerator, &self.denominator) == Ordering::Equal {
                self.denominator = rhs_denominator;
                simplify_fraction_without_info(&mut self.numerator, &mut self.denominator);
                return;
            }
            simplify_fraction_gcd(&mut rhs_numerator, &mut self.denominator);
        }
        self.numerator = mul(&self.numerator, &rhs_numerator);
        self.denominator = mul(&self.denominator, &rhs_denominator);
    }
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub(crate) enum UnequalOrdering {
    Less,
    Greater,
}

#[inline]
pub(crate) fn subtracting_cmp_ne_single<const S: usize>(left: &mut SmallVec<[usize; S]>, right: usize) -> UnequalOrdering {
    debug_assert!(is_well_formed(left));
    debug_assert_ne!(right, 0);
    debug_assert!(left.len() > 1 || left[0] != right);

    if left.len() > 1 {
        // result won't be negative
        let mut carry = carrying_sub_mut(&mut left[0], right, false);

        let mut i = 1;
        while carry {
            carry = carrying_sub_mut(&mut left[i], 0, true);
            i += 1;
        }

        while let Some(0) = left.last() {
            left.pop();
        }

        UnequalOrdering::Greater
    } else {
        // result might be negative
        if left[0] < right {
            left[0] = right - left[0];
            UnequalOrdering::Less
        } else {
            // left[0] > right
            left[0] -= right;
            UnequalOrdering::Greater
        }
    }
}

#[inline]
pub(crate) fn subtracting_cmp_ne<const S: usize>(left: &mut SmallVec<[usize; S]>, right: &SmallVec<[usize; S]>) -> UnequalOrdering {
    debug_assert!(is_well_formed(left));
    debug_assert!(is_well_formed(right));
    debug_assert_ne!(left, right);

    if left.len() > right.len() {
        let carry = unsafe { sub_assign_slice(&mut left[..right.len()], right) };
        debug_assert!(!carry);
        UnequalOrdering::Greater
    } else {
        // left.len() <= right.len()
        let mut last_non_zero_index = None;
        let mut carry = false;
        // TODO(PERFORMANCE): Is assembler faster?
        for i in 0..left.len() {
            carry = carrying_sub_mut(&mut left[i], right[i], carry);
            if left[i] != 0 {
                last_non_zero_index = Some(i);
            }
        }
        if carry {
            to_twos_complement(left);
            UnequalOrdering::Less
        } else {
            left.truncate(1 + last_non_zero_index.unwrap());
            UnequalOrdering::Greater
        }
    }
}

#[inline]
pub fn add_assign_single<const S: usize>(
    values: &mut SmallVec<[usize; S]>,
    rhs: usize,
) {
    let mut carry = carrying_add_mut(&mut values[0], rhs, false);
    let mut i = 1;
    while carry && i < values.len() {
        carry = carrying_add_mut(&mut values[i], 0, true);
        i += 1;
    }
    if carry {
        values.push(1);
    }
}

#[inline]
pub fn add_assign<const S: usize>(
    values: &mut SmallVec<[usize; S]>,
    rhs: &SmallVec<[usize; S]>,
) {
    debug_assert!(is_well_formed(values));
    debug_assert!(is_well_formed(rhs));

    let mut left_index = 0;
    let mut right_index = 0;

    let mut carry = false;
    while left_index < values.len() && right_index < rhs.len() {
        carry = carrying_add_mut(&mut values[left_index], rhs[right_index], carry);
        left_index += 1; right_index += 1;
    }

    while carry && right_index < rhs.len() {
        let (new_value, new_carry) = rhs[right_index].overflowing_add(carry as usize);
        values.push(new_value);
        carry = new_carry;
        right_index += 1;
    }

    // TODO(PERFORMANCE): Check that this separate loop is worth it
    while right_index < rhs.len() {
        values.push(rhs[right_index]);
        right_index += 1;
    }

    if carry {
        values.push(1)
    }
}

#[inline]
fn sub<const S: usize>(
    values: &SmallVec<[usize; S]>,
    rhs: &SmallVec<[usize; S]>,
) -> SmallVec<[usize; S]> {
    debug_assert!(is_well_formed(values));
    debug_assert!(is_well_formed(rhs));
    debug_assert_eq!(cmp(values, rhs), Ordering::Greater);

    let mut result = SmallVec::with_capacity(values.len());

    unsafe {
        let mut carry = {
            sub_n(&mut result, values, rhs, rhs.len() as i32) > 0
        };

        while carry {
            debug_assert!(values.len() > rhs.len());
            let (value, new_carry) = carrying_sub(values[result.len()], 0, carry);
            carry = new_carry;
            result.push(value);
        }

        result.extend_from_slice(&values[result.len()..]);
    }

    result
}

#[inline]
fn sub_single_result_positive<const S: usize>(
    values: &SmallVec<[usize; S]>,
    rhs: usize,
) -> SmallVec<[usize; S]> {
    debug_assert!(!values.is_empty() && (values.len() > 1 || values[0] > rhs));

    let mut result = SmallVec::with_capacity(values.len());
    let (value, mut carry) = carrying_sub(values[0], rhs as usize, false);
    result.push(value);

    let mut i = 1;
    while carry {
        let (value, new_carry) = carrying_sub(values[i], 0, true);
        result.push(value);
        carry = new_carry;
        i += 1;
    }

    debug_assert!(!carry);

    result
}

#[inline]
fn sub_assign_result_positive<const S: usize>(
    values: &mut SmallVec<[usize; S]>,
    rhs: &SmallVec<[usize; S]>,
) {
    debug_assert!(is_well_formed(values));
    debug_assert_eq!(cmp(values, rhs), Ordering::Greater);

    let mut carry = unsafe { // Value is larger and as such still valid after subtraction
        sub_assign_slice(&mut values[..rhs.len()], rhs)
    };

    debug_assert!(is_well_formed(values));

    let mut index = 0;
    while carry {
        debug_assert!(values.len() > rhs.len());
        carry = carrying_sub_mut(&mut values[rhs.len() + index], 0, carry);
        index += 1;
    }

    while let Some(0) = values.last() {
        values.pop();
    }

    debug_assert!(is_well_formed(values));
}

#[inline]
pub fn cmp_single<const S: usize>(large: &SmallVec<[usize; S]>, small: usize) -> Ordering {
    debug_assert!(!large.is_empty());

    if large.len() > 1 {
        Ordering::Greater
    } else {
        large[0].cmp(&small)
    }
}

#[inline]
fn sub_assign_single_result_positive<const S: usize>(
    values: &mut SmallVec<[usize; S]>, rhs: usize,
) {
    debug_assert!(is_well_formed(values));
    debug_assert_eq!(cmp_single(values, rhs), Ordering::Greater);

    let mut carry = carrying_sub_mut(&mut values[0], rhs, false);

    debug_assert!(is_well_formed(values));

    let mut index = 0;
    while carry {
        debug_assert!(values.len() > 1);
        carry = carrying_sub_mut(&mut values[1 + index], 0, carry);
        index += 1;
    }

    while let Some(0) = values.last() {
        values.pop();
    }

    debug_assert!(is_well_formed(values));
}

#[inline]
pub fn mul_assign_single<const S: usize>(
    values: &mut SmallVec<[usize; S]>,
    rhs: usize,
) {
    let (mut high, low) = building_blocks::mul(values[0], rhs);
    values[0] = low;
    for i in 1..values.len() {
        let (high_new, low) = building_blocks::mul(values[i], rhs);
        values[i] = high + low;
        high = high_new;
    }
    if high > 0 {
        values.push(high);
    }
}

#[inline]
pub fn mul<const S: usize>(
    values: &SmallVec<[usize; S]>,
    rhs: &SmallVec<[usize; S]>,
) -> SmallVec<[usize; S]> {
    debug_assert!(is_well_formed(values));
    debug_assert!(is_well_formed(rhs));
    debug_assert!(!values.is_empty());
    debug_assert!(!rhs.is_empty());

    let mut result = SmallVec::with_capacity(values.len() + rhs.len());

    let (large, small) = if rhs.len() > values.len() {
        (rhs, values)
    } else {
        (values, rhs)
    };

    unsafe {
        let carry = mul_1(&mut result, large, small[0]);
        result.set_len(large.len());
        result.push(carry);
    }

    unsafe {
        for i in 1..small.len() {
            let carry = addmul_1(&mut result[i..], large, large.len() as i32, small[i]);
            result.push(carry);
        }

        if *result.last().unwrap() == 0 {
            result.pop();
        }
    }

    debug_assert!(is_well_formed(&result));

    result
}

impl<const S: usize> Ord for Big<S> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<const S: usize> PartialOrd for Big<S> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let by_sign = self.sign.partial_cmp(&other.sign);

        let by_length = by_sign.or_else(|| {
            match (self.numerator.len() + other.denominator.len()).cmp(&(other.numerator.len() + self.denominator.len())) {
                Ordering::Less => Some(Ordering::Less),
                Ordering::Equal => None,
                Ordering::Greater => Some(Ordering::Greater),
            }
        });

        let by_product = by_length.unwrap_or_else(|| {
            if self.numerator == other.numerator && self.denominator == other.denominator {
                Ordering::Equal
            } else {
                let ad = mul(&self.numerator, &other.denominator);
                let bc = mul(&other.numerator, &self.denominator);

                cmp(&ad, &bc)
            }
        });

        Some(by_product)
    }
}

impl<const S: usize> Neg for Big<S> {
    type Output = Self;

    #[inline]
    fn neg(mut self) -> Self::Output {
        self.sign = !self.sign;
        self
    }
}

impl<const S: usize> Neg for &Big<S> {
    type Output = Big<S>;

    #[inline]
    fn neg(self) -> Self::Output {
        Self::Output {
            sign: !self.sign,
            numerator: self.numerator.clone(),
            denominator: self.denominator.clone(),
        }
    }
}

#[inline]
fn is_well_formed<const S: usize>(values: &SmallVec<[usize; S]>) -> bool {
    match values.last() {
        None => true,
        Some(&value) => value != 0,
    }
}

#[cfg(test)]
mod test {
    use smallvec::{smallvec, SmallVec};

    use crate::rational::big::ops::{add_assign, is_well_formed, mul, mul_assign_single, sub_assign_result_positive};
    use crate::RB;

    pub type SV = SmallVec<[usize; 8]>;

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

        assert_eq!(RB!(1) + RB!(-2), RB!(-1));
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
    }

    #[test]
    fn test_bigint_add_assign() {
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
    }

    #[test]
    fn test_bigint_sub_assign() {
        // Same length, no overflow
        let mut x: SV = smallvec![2];
        let y: SV = smallvec![1];
        sub_assign_result_positive(&mut x, &y);
        let expected: SV = smallvec![1];
        assert_eq!(x, expected);

        // First longer, overflow
        let mut x: SV = smallvec![0, 0, 1];
        let y: SV = smallvec![1];
        sub_assign_result_positive(&mut x, &y);
        let expected: SV = smallvec![usize::MAX, usize::MAX];
        assert_eq!(x, expected);

        // First longer, overflow
        let mut x: SV = smallvec![0, 1, 1];
        let y: SV = smallvec![1, 1];
        sub_assign_result_positive(&mut x, &y);
        let expected: SV = smallvec![usize::MAX, usize::MAX];
        assert_eq!(x, expected);

        // First longer
        let mut x: SV = smallvec![0, 2];
        let y: SV = smallvec![1];
        sub_assign_result_positive(&mut x, &y);
        let expected: SV = smallvec![usize::MAX, 1];
        assert_eq!(x, expected);

        // First longer
        let mut x: SV = smallvec![0, 1];
        let y: SV = smallvec![usize::MAX];
        sub_assign_result_positive(&mut x, &y);
        let expected: SV = smallvec![1];
        assert_eq!(x, expected);
    }

    #[test]
    fn test_mul() {
        let x: SV = smallvec![1];
        let y = mul(&x, &x);
        let expected: SV = smallvec![1];
        assert_eq!(y, expected);

        let x: SV = smallvec![1, 1];
        let y: SV = smallvec![1];
        let z = mul(&x, &y);
        let expected: SV = smallvec![1, 1];
        assert_eq!(z, expected);

        let x: SV = smallvec![1, 1];
        let y: SV = smallvec![1, 1];
        let z = mul(&x, &y);
        let expected: SV = smallvec![1, 2, 1];
        assert_eq!(z, expected);

        let x: SV = smallvec![1, 1, 1, 1, 1];
        let y: SV = smallvec![1];
        let z = mul(&x, &y);
        let expected: SV = smallvec![1, 1, 1, 1, 1];
        assert_eq!(z, expected);

        let x: SV = smallvec![1, 1, 1];
        let y: SV = smallvec![1, 1];
        let z = mul(&x, &y);
        let expected: SV = smallvec![1, 2, 2, 1];
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
        let z = mul(&x, &y);
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
    }

    #[test]
    fn test_mul_assign_single() {
        let mut x: SV = smallvec![1];
        mul_assign_single(&mut x, 1);
        let expected: SV = smallvec![1];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![1, 1];
        mul_assign_single(&mut x, 1);
        let expected: SV = smallvec![1, 1];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![1, 1, 1, 1, 1];
        mul_assign_single(&mut x, 3);
        let expected: SV = smallvec![3, 3, 3, 3, 3];
        assert_eq!(x, expected);

        let mut x: SV = smallvec![1 << 63];
        mul_assign_single(&mut x, 1 << 63);
        let expected: SV = smallvec![0, 1 << (126 - 64)];
        assert_eq!(x, expected);
    }

    #[test]
    fn test_is_well_formed() {
        // Empty values are allowed, they represent zero. In many methods, that is invalid input,
        // however.
        let x: SV = smallvec![];
        assert!(is_well_formed(&x));

        let x: SV = smallvec![0, 1];
        assert!(is_well_formed(&x));

        let x: SV = smallvec![648, 64884, 1];
        assert!(is_well_formed(&x));

        // Ends with zero

        let x: SV = smallvec![564, 6448, 84, 0];
        assert!(!is_well_formed(&x));

        let x: SV = smallvec![0];
        assert!(!is_well_formed(&x));

        let x: SV = smallvec![0, 0, 0, 0];
        assert!(!is_well_formed(&x));
    }
}
