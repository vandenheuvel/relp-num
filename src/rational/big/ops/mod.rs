use std::cmp::{min, Ordering};
use std::iter::repeat;
use std::iter::Sum;
use std::mem;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use num_traits::{One, Zero};
use smallvec::SmallVec;

use crate::rational::big::Big;
use crate::rational::big::ops::building_blocks::{addmul_1, carrying_add_mut, carrying_sub, carrying_sub_mut, mul_1, sub_assign_slice, sub_n, to_twos_complement};
use crate::rational::big::ops::div::{div as div_by_odd_or_even, div_assign_by_odd};
use crate::rational::big::ops::normalize::{gcd, remove_shared_two_factors_mut, simplify_fraction_gcd, simplify_fraction_without_info};
use crate::sign::Sign;

pub mod building_blocks;
pub mod div;
pub mod normalize;

pub const BITS_PER_WORD: u32 = (mem::size_of::<usize>() * 8) as u32;

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
        -Sub::sub(rhs, self)
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
        debug_assert!(self.is_consistent());
        debug_assert!(!self.is_zero());
        debug_assert!(!rhs.is_zero());

        if self.denominator == rhs.denominator {
            add_assign(&mut self.numerator, &rhs.numerator);

            // Numerator can't be zero

            match cmp(&self.numerator, &self.denominator) {
                Ordering::Equal => self.set_one(),
                Ordering::Less | Ordering::Greater => {
                    if (self.numerator[0] != 1 || self.numerator.len() > 1) && (self.denominator[0] != 1 || self.denominator.len() > 1) {
                        simplify_fraction_gcd(&mut self.numerator, &mut self.denominator);
                    }
                }
            }
        } else {
            if self.denominator[0] == 1 && self.denominator.len() == 1 { // denominator == 1
                self.numerator = mul(&self.numerator, &rhs.denominator);
                add_assign(&mut self.numerator, &rhs.numerator);
                self.denominator = rhs.denominator.clone();

                if self.numerator[0] != 1 || self.numerator.len() > 1 {
                    simplify_fraction_gcd(&mut self.numerator, &mut self.denominator);
                }
            } else if rhs.denominator[0] == 1 && rhs.denominator.len() == 1 { // denominator == 1
                let numerator = mul(&rhs.numerator, &self.denominator);
                add_assign(&mut self.numerator, &numerator);
                if self.numerator[0] != 1 || self.numerator.len() > 1 {
                    simplify_fraction_gcd(&mut self.numerator, &mut self.denominator);
                }
            } else {
                // Neither denominator is 1
                let mut gcd = gcd(&self.denominator, &rhs.denominator);

                if gcd[0] != 1 || gcd.len() > 1 {
                    if cmp(&rhs.denominator, &gcd) == Ordering::Equal {
                        // No need to modify numerator
                    } else {
                        let left = div_by_odd_or_even(&rhs.denominator, &gcd);
                        self.numerator = mul(&self.numerator, &left);
                    }

                    remove_shared_two_factors_mut(&mut self.denominator, &mut gcd);
                    if cmp(&self.denominator, &gcd) == Ordering::Equal {
                        self.denominator.truncate(1);
                        self.denominator[0] = 1;
                        add_assign(&mut self.numerator, &rhs.numerator);
                        self.denominator = rhs.denominator.clone();
                    } else {
                        if gcd[0] != 1 || gcd.len() > 1 {
                            div_assign_by_odd(&mut self.denominator, &gcd);
                        }
                        let right = mul(&rhs.numerator, &self.denominator);
                        add_assign(&mut self.numerator, &right);
                        self.denominator = mul(&rhs.denominator, &self.denominator);
                    }
                    simplify_fraction_gcd(&mut self.numerator, &mut self.denominator);
                } else {
                    self.numerator = mul(&self.numerator, &rhs.denominator);
                    let right = mul(&rhs.numerator, &self.denominator);
                    add_assign(&mut self.numerator, &right);
                    self.denominator = mul(&self.denominator, &rhs.denominator);
                }
            }
        }

        debug_assert!(self.is_consistent());
    }
    fn sub(&mut self, rhs: &Self) {
        debug_assert!(self.is_consistent());
        debug_assert!(!self.is_zero());
        debug_assert!(!rhs.is_zero());

        if self.denominator == rhs.denominator {
            match subtracting_cmp(&mut self.numerator, &rhs.numerator) {
                Ordering::Less => self.sign = !self.sign,
                Ordering::Equal => {
                    self.sign = Sign::Zero;
                    self.denominator[0] = 1;
                    self.denominator.truncate(1);
                    return;
                }
                Ordering::Greater => {}
            }
            match cmp(&self.numerator, &self.denominator) {
                Ordering::Equal => self.set_one(),
                Ordering::Less | Ordering::Greater => {
                    if (self.numerator[0] != 1 || self.numerator.len() > 1) && (self.denominator[0] != 1 || self.denominator.len() > 1) {
                        simplify_fraction_gcd(&mut self.numerator, &mut self.denominator);
                    }
                }
            }
        } else {
            if self.denominator[0] == 1 && self.denominator.len() == 1 { // denominator == 1
                self.numerator = mul(&self.numerator, &rhs.denominator);

                match subtracting_cmp(&mut self.numerator, &rhs.numerator) {
                    Ordering::Less => self.sign = !self.sign,
                    Ordering::Greater => {},
                    Ordering::Equal => panic!(),
                }
                self.denominator = rhs.denominator.clone();
                if self.numerator[0] != 1 || self.numerator.len() > 1 {
                    simplify_fraction_gcd(&mut self.numerator, &mut self.denominator);
                }
            } else if rhs.denominator[0] == 1 && rhs.denominator.len() == 1 { // denominator == 1
                let numerator = mul(&rhs.numerator, &self.denominator);

                match subtracting_cmp(&mut self.numerator, &numerator) {
                    Ordering::Less => self.sign = !self.sign,
                    Ordering::Greater => {},
                    Ordering::Equal => panic!(),
                }
                if self.numerator[0] != 1 || self.numerator.len() > 1 {
                    simplify_fraction_gcd(&mut self.numerator, &mut self.denominator);
                }
            } else {
                // Neither denominator is 1
                let mut gcd = gcd(&self.denominator, &rhs.denominator);

                if gcd[0] != 1 || gcd.len() > 1 {
                    if cmp(&rhs.denominator, &gcd) == Ordering::Equal {
                        // No need to modify numerator
                    } else {
                        let left = div_by_odd_or_even(&rhs.denominator, &gcd);
                        self.numerator = mul(&self.numerator, &left);
                    }

                    remove_shared_two_factors_mut(&mut self.denominator, &mut gcd);
                    if cmp(&self.denominator, &gcd) == Ordering::Equal {
                        self.denominator.truncate(1);
                        self.denominator[0] = 1;
                        match subtracting_cmp(&mut self.numerator, &rhs.numerator) {
                            Ordering::Less => self.sign = !self.sign,
                            Ordering::Greater => {}
                            Ordering::Equal => panic!(),
                        }
                        self.denominator = rhs.denominator.clone();
                    } else {
                        if gcd[0] != 1 || gcd.len() > 1 {
                            div_assign_by_odd(&mut self.denominator, &gcd);
                        }
                        let right = mul(&rhs.numerator, &self.denominator);
                        match subtracting_cmp(&mut self.numerator, &right) {
                            Ordering::Less => self.sign = !self.sign,
                            Ordering::Greater => {}
                            Ordering::Equal => panic!(),
                        };
                        self.denominator = mul(&rhs.denominator, &self.denominator);
                    }
                    if self.numerator[0] != 1 || self.numerator.len() > 1 {
                        simplify_fraction_gcd(&mut self.numerator, &mut self.denominator);
                    }
                } else {
                    self.numerator = mul(&self.numerator, &rhs.denominator);
                    let right = mul(&rhs.numerator, &self.denominator);
                    match subtracting_cmp(&mut self.numerator, &right) {
                        Ordering::Less => self.sign = !self.sign,
                        Ordering::Greater => {}
                        Ordering::Equal => panic!(),
                    }
                    self.denominator = mul(&self.denominator, &rhs.denominator);
                }
            }
        }

        debug_assert!(self.is_consistent());
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
        // TODO(PERFORMANCE): Should cloning be avoided?
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
        debug_assert!(self.is_consistent());
        debug_assert!(!self.is_zero());
        debug_assert!(is_well_formed(&rhs_numerator));
        debug_assert!(!rhs_numerator.is_empty());
        debug_assert!(is_well_formed(&rhs_denominator));
        debug_assert!(!rhs_denominator.is_empty());

        if (rhs_denominator[0] != 1 || rhs_denominator.len() > 1) && (self.numerator.len() != 1 || self.numerator[0] != 1) {
            // TODO(PERFORMANCE): Check for equality here as a special case, or not?

            match cmp(&rhs_denominator, &self.numerator) {
                Ordering::Equal => {
                    self.numerator = rhs_numerator;
                    simplify_fraction_without_info(&mut self.numerator, &mut self.denominator);
                    return;
                }
                Ordering::Less | Ordering::Greater => {
                    simplify_fraction_gcd(&mut self.numerator, &mut rhs_denominator);
                }
            }
        }

        if (self.denominator[0] != 1 || self.denominator.len() > 1) && (rhs_numerator.len() != 1 || rhs_numerator[0] != 1) {
            // TODO(PERFORMANCE): Check for equality here as a special case, or not?
            match cmp(&rhs_numerator, &self.denominator) {
                Ordering::Equal => {
                    self.denominator = rhs_denominator;
                    simplify_fraction_without_info(&mut self.numerator, &mut self.denominator);
                    return;
                }
                Ordering::Less | Ordering::Greater => {
                    simplify_fraction_gcd(&mut rhs_numerator, &mut self.denominator);
                }
            }
        }

        self.numerator = mul(&self.numerator, &rhs_numerator);
        self.denominator = mul(&self.denominator, &rhs_denominator);

        debug_assert!(self.is_consistent());
    }
}

#[inline]
pub(crate) fn subtracting_cmp_ne_single<const S: usize>(left: &mut SmallVec<[usize; S]>, right: usize) -> Ordering {
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

        Ordering::Greater
    } else {
        // result might be negative
        if left[0] < right {
            left[0] = right - left[0];
            Ordering::Less
        } else {
            // left[0] > right
            left[0] -= right;
            Ordering::Greater
        }
    }
}

#[inline]
pub(crate) fn subtracting_cmp<const S: usize>(left: &mut SmallVec<[usize; S]>, right: &SmallVec<[usize; S]>) -> Ordering {
    debug_assert!(is_well_formed(left));
    debug_assert!(is_well_formed(right));

    match left.len().cmp(&right.len()) {
        Ordering::Less => {
            let mut carry = false;
            let mut i = 0;
            while i < left.len() {
                // TODO(PERFORMANCE): Is assembler faster?
                let (new_value, new_carry) = carrying_sub(right[i], left[i], carry);
                left[i] = new_value;
                carry = new_carry;
                i += 1;
            }

            while carry {
                let (new_value, new_carry) = carrying_sub(right[i], 0, true);
                left.push(new_value);
                carry = new_carry;
                i += 1;
            }

            left.extend_from_slice(&right[i..]);

            while *left.last().unwrap() == 0 {
                left.pop();
            }

            Ordering::Less
        }
        Ordering::Equal => {
            let mut carry = false;
            for i in 0..left.len() {
                // TODO(PERFORMANCE): Is assembler faster?
                carry = carrying_sub_mut(&mut left[i], right[i], carry);
            }

            if carry {
                // result is negative
                to_twos_complement(left);
                while *left.last().unwrap() == 0 {
                    left.pop();
                }
                Ordering::Less
            } else {
                // result is zero or positive

                while let Some(0) = left.last() {
                    left.pop();
                }

                // TODO(PERFORMANCE): This test is often not necessary, as it is known in advance
                //  whether the result can be zero or not.
                if left.is_empty() {
                    Ordering::Equal
                } else {
                    Ordering::Greater
                }
            }
        }
        Ordering::Greater => {
            let mut carry = unsafe { sub_assign_slice(&mut left[..right.len()], right) };
            let mut i = 0;
            while carry && i + right.len() < left.len() {
                carry = carrying_sub_mut(&mut left[i + right.len()], 0, true);
                i += 1;
            }
            debug_assert!(!carry);
            while *left.last().unwrap() == 0 {
                left.pop();
            }

            Ordering::Greater
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

    let mut i = 0;

    let mut carry = false;
    while i < values.len() && i < rhs.len() {
        carry = carrying_add_mut(&mut values[i], rhs[i], carry);
        i += 1;
    }

    while carry && i < rhs.len() {
        let (new_value, new_carry) = rhs[i].overflowing_add(carry as usize);
        values.push(new_value);
        carry = new_carry;
        i += 1;
    }

    // TODO(PERFORMANCE): Check that this separate loop is worth it
    while i < rhs.len() {
        values.push(rhs[i]);
        i += 1;
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
    // Will be overwritten in the unsafe block, but this is safe and extends the length
    result.extend(repeat(0).take(rhs.len()));

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

        if result.len() < values.len() {
            result.extend_from_slice(&values[result.len()..]);
        } else {
            while let Some(0) = result.last() {
                result.pop();
            }
        }
    }

    result
}

/// Subassign from a value.
///
/// # Arguments
///
/// * `values`: is larger than `rhs` but might have the most significant word(s) already removed, if
/// they were equal to `rhs`. It is as such not necessarily well formed and can't be easily compared
/// to `rhs`.
/// * `rhs`: value to subtract.
#[inline]
unsafe fn sub_assign_result_positive<const S: usize>(
    values: &mut SmallVec<[usize; S]>,
    rhs: &SmallVec<[usize; S]>,
) {
    let smallest = min(values.len(), rhs.len());
    let mut carry = sub_assign_slice(&mut values[..smallest], &rhs[..smallest]);

    let mut index = 0;
    while carry {
        debug_assert!(values.len() > rhs.len());
        carry = carrying_sub_mut(&mut values[rhs.len() + index], 0, true);
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

impl<const S: usize> PartialEq for Big<S> {
    fn eq(&self, other: &Self) -> bool {
        match (self.sign, other.sign) {
            (Sign::Positive, Sign::Negative) |
            (Sign::Negative, Sign::Positive) => false,
            (Sign::Zero, Sign::Zero) => true,
            (Sign::Positive, Sign::Positive) | (Sign::Negative, Sign::Negative) => {
                self.numerator == other.numerator && self.denominator == other.denominator
            }
            (Sign::Zero, Sign::Positive | Sign::Negative) |
            (Sign::Positive | Sign::Negative, Sign::Zero) => false,
        }
    }
}
impl<const S: usize> Eq for Big<S> {}

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
            debug_assert_eq!(self.sign, other.sign);
            debug_assert_ne!(self.sign, Sign::Zero);

            let size_comparison = (self.numerator.len() + other.denominator.len()).cmp(&(other.numerator.len() + self.denominator.len()));
            match (size_comparison, self.sign) {
                (Ordering::Less, Sign::Positive) | (Ordering::Greater, Sign::Negative) => Some(Ordering::Less),
                (Ordering::Equal, _) => None,
                (Ordering::Greater, Sign::Positive) | (Ordering::Less, Sign::Negative) => Some(Ordering::Greater),
                (_, Sign::Zero) => panic!(),
            }
        });

        let by_product = by_length.unwrap_or_else(|| {
            if self.numerator == other.numerator && self.denominator == other.denominator {
                Ordering::Equal
            } else {
                debug_assert_eq!(self.sign, other.sign);
                debug_assert_ne!(self.sign, Sign::Zero);

                let ad = mul(&self.numerator, &other.denominator);
                let bc = mul(&other.numerator, &self.denominator);

                match (cmp(&ad, &bc), self.sign) {
                    (Ordering::Less, Sign::Positive) | (Ordering::Greater, Sign::Negative) => Ordering::Less,
                    (Ordering::Equal, _) => Ordering::Equal,
                    (Ordering::Greater, Sign::Positive) | (Ordering::Less, Sign::Negative) => Ordering::Greater,
                    (_, Sign::Zero) => panic!(),
                }
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
pub fn is_well_formed<const S: usize>(values: &SmallVec<[usize; S]>) -> bool {
    match values.last() {
        None => true,
        Some(&value) => value != 0,
    }
}

#[cfg(test)]
mod test {
    use smallvec::{smallvec, SmallVec};

    use crate::{RB, Sign};
    use crate::rational::big::Big8;
    use crate::rational::big::creation::int_from_str;
    use crate::rational::big::ops::{add_assign, add_assign_single, is_well_formed, mul, mul_assign_single, sub, sub_assign_result_positive, subtracting_cmp, Ordering};

    pub type SV = SmallVec<[usize; 8]>;

    #[test]
    fn test_ord() {
        let x = Big8 {
            sign: Sign::Positive,
            numerator: smallvec![2],
            denominator: smallvec![3],
        };
        let y = Big8 {
            sign: Sign::Positive,
            numerator: smallvec![2],
            denominator: smallvec![3],
        };
        assert_eq!(x, y);

        let neg_x = Big8 {
            sign: Sign::Negative,
            numerator: smallvec![2],
            denominator: smallvec![3],
        };
        assert!(neg_x < x);
        assert!(x > neg_x);
        assert!(neg_x <= x);
        assert!(x >= neg_x);

        let x = Big8 {
            sign: Sign::Positive,
            numerator: smallvec![1, 1],
            denominator: smallvec![1],
        };
        let y = Big8 {
            sign: Sign::Positive,
            numerator: smallvec![2],
            denominator: smallvec![1],
        };
        assert!(x > y);

        let x = Big8 {
            sign: Sign::Positive,
            numerator: smallvec![1, 1],
            denominator: smallvec![23],
        };
        let y = Big8 {
            sign: Sign::Positive,
            numerator: smallvec![2],
            denominator: smallvec![23],
        };
        assert!(x > y);

        let x = Big8 {
            sign: Sign::Positive,
            numerator: smallvec![1, 1],
            denominator: smallvec![1],
        };
        let y = Big8 {
            sign: Sign::Positive,
            numerator: smallvec![2, 1],
            denominator: smallvec![1],
        };
        assert!(x < y);

        let x = Big8 {
            sign: Sign::Positive,
            numerator: smallvec![1, 1],
            denominator: smallvec![19],
        };
        let y = Big8 {
            sign: Sign::Positive,
            numerator: smallvec![2, 1],
            denominator: smallvec![19],
        };
        assert!(x < y);

        let x = Big8 {
            sign: Sign::Positive,
            numerator: smallvec![0, 0, 1],
            denominator: smallvec![19],
        };
        let y = Big8 {
            sign: Sign::Positive,
            numerator: smallvec![2, 2],
            denominator: smallvec![19],
        };
        assert!(y <= x);
        assert!(x > y);

        let x = Big8 {
            sign: Sign::Negative,
            numerator: smallvec![0, 0, 1],
            denominator: smallvec![19],
        };
        let y = Big8 {
            sign: Sign::Positive,
            numerator: smallvec![2, 2],
            denominator: smallvec![19],
        };
        assert!(x < y);

        let x = Big8 {
            sign: Sign::Negative,
            numerator: smallvec![0, 0, 1],
            denominator: smallvec![19],
        };
        let y = Big8 {
            sign: Sign::Negative,
            numerator: smallvec![0, 0, 1],
            denominator: smallvec![19],
        };
        assert_eq!(x, y);

        let x = Big8 {
            sign: Sign::Negative,
            numerator: smallvec![0, 0, 1],
            denominator: smallvec![19],
        };
        let y = <Big8 as num_traits::Zero>::zero();
        assert!(x < y);
        assert!(y >= x);

        let x = Big8 {
            sign: Sign::Positive,
            numerator: smallvec![0, 0, 1],
            denominator: smallvec![19],
        };
        let y = <Big8 as num_traits::Zero>::zero();
        assert!(x > y);
        assert!(y <= x);

        let x = Big8 {
            sign: Sign::Positive,
            numerator: smallvec![2],
            denominator: smallvec![3],
        };
        let y = Big8 {
            sign: Sign::Positive,
            numerator: smallvec![3],
            denominator: smallvec![4],
        };
        assert!(x < y);
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

        let mut x = int_from_str::<3>("68498984987984986896468746354684684684968", 10).unwrap();
        let y = int_from_str::<3>("676230147000334142150220547988205853833725436834339162", 10).unwrap();
        add_assign(&mut x, &y);
        let expected = int_from_str::<3>("676230147000402641135208532975102322580080121519024130", 10).unwrap();
        assert_eq!(x, expected);

        let mut x = int_from_str::<3>("68498984987984986896468746354684684684968", 10).unwrap();
        let y = int_from_str::<3>("676230147000334142150220547988205853833725436834339162", 10).unwrap();
        add_assign(&mut x, &y);
        let expected = int_from_str::<3>("676230147000402641135208532975102322580080121519024130", 10).unwrap();
        assert_eq!(x, expected);

        let mut x = int_from_str::<3>("13282457576090002999724080439382126039670578699984818946692017256202044898307", 10).unwrap();
        let y = int_from_str::<3>("52138404881359597776641425341642690746162654701917220048397413248229209595444", 10).unwrap();
        add_assign(&mut x, &y);
        let expected = int_from_str::<3>("65420862457449600776365505781024816785833233401902038995089430504431254493751", 10).unwrap();
        assert_eq!(x, expected);

        let mut x = int_from_str::<3>("92599469589222131768757076514696607382155504523751371565834361998764652118557", 10).unwrap();
        let y = int_from_str::<3>("80627506337117343961599775375716501347124738605551411762759133617725727360716", 10).unwrap();
        add_assign(&mut x, &y);
        let expected = int_from_str::<3>("173226975926339475730356851890413108729280243129302783328593495616490379479273", 10).unwrap();
        assert_eq!(x, expected);
    }

    #[test]
    fn test_bigint_sub_assign() {
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

        let mut x = int_from_str::<3>("676230147000334142150220547988205853833725436834339162", 10).unwrap();
        let y = int_from_str::<3>("68498984987984986896468746354684684684968", 10).unwrap();
        unsafe { sub_assign_result_positive(&mut x, &y); }
        let expected = int_from_str::<3>("676230147000265643165232563001309385087370752149654194", 10).unwrap();
        assert_eq!(x, expected);

        let mut x = int_from_str::<3>("676230147000334142150220547988205853833725436834339162", 10).unwrap();
        let y = int_from_str::<3>("68498984987984986896468746354684684684968", 10).unwrap();
        unsafe { sub_assign_result_positive(&mut x, &y); }
        let expected = int_from_str::<3>("676230147000265643165232563001309385087370752149654194", 10).unwrap();
        assert_eq!(x, expected);

        let mut x = int_from_str::<3>("52138404881359597776641425341642690746162654701917220048397413248229209595444", 10).unwrap();
        let y = int_from_str::<3>("13282457576090002999724080439382126039670578699984818946692017256202044898307", 10).unwrap();
        unsafe { sub_assign_result_positive(&mut x, &y); }
        let expected = int_from_str::<3>("38855947305269594776917344902260564706492076001932401101705395992027164697137", 10).unwrap();
        assert_eq!(x, expected);

        let mut x = int_from_str::<3>("92599469589222131768757076514696607382155504523751371565834361998764652118557", 10).unwrap();
        let y = int_from_str::<3>("80627506337117343961599775375716501347124738605551411762759133617725727360716", 10).unwrap();
        unsafe { sub_assign_result_positive(&mut x, &y); }
        let expected = int_from_str::<3>("11971963252104787807157301138980106035030765918199959803075228381038924757841", 10).unwrap();
        assert_eq!(x, expected);
    }

    #[test]
    fn test_sub() {
        let x: SV = smallvec![11];
        let y: SV = smallvec![5];
        let result = sub(&x, &y);
        let expected: SV = smallvec![6];
        assert_eq!(result, expected);

        let x: SV = smallvec![1, 1];
        let y: SV = smallvec![2];
        let result = sub(&x, &y);
        let expected: SV = smallvec![usize::MAX];
        assert_eq!(result, expected);
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

        let x: SV = smallvec![616865135358];
        let y: SV = smallvec![318864];
        let z = mul(&x, &y);
        let expected: SV = smallvec![196696084520793312];
        assert_eq!(z, expected);

        let x: SV = smallvec![6168651349984645358];
        let y: SV = smallvec![31884648664];
        let z = mul(&x, &y);
        let expected: SV = smallvec![2946066457054546128, 10662330449];
        assert_eq!(z, expected);

        let x: SV = int_from_str("68468468498498987982211", 10).unwrap();
        let y: SV = int_from_str("6546845498498498766994984941", 10).unwrap();
        let z = mul(&x, &y);
        let expected: SV = int_from_str("448252484778484366353430902886798387597665920884551", 10).unwrap();
        assert_eq!(z, expected);

        let x: SV = int_from_str("6846846598498849754611315531318498498987982211", 10).unwrap();
        let y: SV = int_from_str("65468454984984984989846544418766994984941", 10).unwrap();
        let z = mul(&x, &y);
        let expected: SV = int_from_str("448252468322919508262853593995316625918253404600786790378945516838911366717665920884551", 10).unwrap();
        assert_eq!(z, expected);

        let x: SV = int_from_str("68468465984988497546416161698149845311616811315531318498498987982211", 10).unwrap();
        let y: SV = int_from_str("654684549849849849898465444187669985648546168541168443544984941", 10).unwrap();
        let z = mul(&x, &y);
        let expected: SV = int_from_str("44825246832291950826483732998274014934302316363445684381827995526563290241044825692328446158571230923548759376413518121517970884551", 10).unwrap();
        assert_eq!(z, expected);

        let x: SV = int_from_str("684684659849886161698149845311616811315531318498498987982211", 10).unwrap();
        let y: SV = int_from_str("654684549849849865444187669985648546168541168443544984941", 10).unwrap();
        let z = mul(&x, &y);
        let expected: SV = int_from_str("448252468322920295517819464130433697009775835506250832016384806318621662991558571230923548759376413518121517970884551", 10).unwrap();
        assert_eq!(z, expected);

        let x: SV = int_from_str("1237940039285380274899124191", 10).unwrap();
        let y: SV = int_from_str("2475880078570760549798248403", 10).unwrap();
        let z = mul(&x, &y);
        let expected: SV = int_from_str("3064991081731777716716693916889274006560267730564416973", 10).unwrap();
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

        let x = int_from_str::<3>("68468465468464168545346854646", 10).unwrap();
        let y = int_from_str::<3>("9876519684989849849849847", 10).unwrap();
        let z = int_from_str::<3>("676230147000334142150220547988205853833725436834339162", 10).unwrap();
        assert_eq!(mul(&x, &y), z);

        let x = int_from_str::<3>("9876519684989849849849847", 10).unwrap();
        let y = int_from_str::<3>("68468465468464168545346854646", 10).unwrap();
        let z = int_from_str::<3>("676230147000334142150220547988205853833725436834339162", 10).unwrap();
        assert_eq!(mul(&x, &y), z);
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

        let mut x = int_from_str::<4>("684684659849886161698149845311616811315531318498498987982211", 10).unwrap();
        mul_assign_single(&mut x, 646846844846);
        let expected = int_from_str::<4>("442886111938355599686725600875542300070422743926852384563217257325034506", 10).unwrap();
        assert_eq!(x, expected);
    }

    #[test]
    fn test_add_assign_single() {
        let mut x = int_from_str::<4>("684684659849886161698149845311616811315531318498498987982211", 10).unwrap();
        add_assign_single(&mut x, 646846844846);
        let expected = int_from_str::<4>("684684659849886161698149845311616811315531318499145834827057", 10).unwrap();
        assert_eq!(x, expected);
    }

    #[test]
    fn test_subtracting_cmp_ne() {
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
