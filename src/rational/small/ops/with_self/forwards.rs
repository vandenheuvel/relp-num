use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};
use crate::NonZero;
use crate::rational::small::Ratio;

impl<'a, N: 'a, D: NonZero + 'a> Add<Self> for &'a Ratio<N, D> where Ratio<N, D>: Add {
    type Output = Ratio<N, D>;

    #[must_use]
    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Add::add(self.clone(), rhs)
    }
}

impl<'a, N: 'a, D: NonZero + 'a> Add for Ratio<N, D> where Self: AddAssign {
    type Output = Self;

    #[must_use]
    #[inline]
    fn add(mut self, rhs: Self) -> Self::Output {
        AddAssign::add_assign(&mut self, rhs);
        self
    }
}

impl<'a, N: 'a, D: NonZero + 'a> Add<&Self> for Ratio<N, D> where Self: AddAssign<&'a Self> {
    type Output = Self;

    #[must_use]
    #[inline]
    fn add(mut self, rhs: &Self) -> Self::Output {
        AddAssign::add_assign(&mut self, rhs);
        self
    }
}

impl<N, D: NonZero> Add<Ratio<N, D>> for &Ratio<N, D> where Self:  {
    type Output = Ratio<N, D>;

    #[must_use]
    #[inline]
    fn add(self, rhs: Ratio<N, D>) -> Self::Output {
        Add::add(rhs, self)
    }
}

impl<'a, N: 'a, D: NonZero + 'a> AddAssign for Ratio<N, D> where Self: AddAssign<&'a Self> {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        AddAssign::add_assign(self, &rhs);
    }
}


impl<N, D: NonZero> Sub for Ratio<N, D> where Self: SubAssign {
    type Output = Self;
    
    #[must_use]
    #[inline]
    fn sub(mut self, rhs: Self) -> Self::Output {
        SubAssign::sub_assign(&mut self, rhs);
        self
    }
}

impl<'a, N: 'a, D: NonZero + 'a> Sub<Self> for &'a Ratio<N, D> {
    type Output = Ratio<N, D>;
    
    #[must_use]
    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Sub::sub(self.clone(), rhs)
    }
}

impl<'a, N: 'a, D: NonZero + 'a> Sub<&Self> for Ratio<N, D> where Self: SubAssign<&'a Self> {
    type Output = Self;
    
    #[must_use]
    #[inline]
    fn sub(mut self, rhs: &Self) -> Self::Output {
        SubAssign::sub_assign(&mut self, rhs);
        self
    }
}

impl<N, D: NonZero> Sub<Ratio<N, D>> for &Ratio<N, D> where Ratio<N, D>: Sub<Self> {
    type Output = Ratio<N, D>;
    
    #[must_use]
    #[inline]
    fn sub(self, rhs: Ratio<N, D>) -> Self::Output {
        -Sub::sub(rhs, self)
    }
}

impl<'a, N: 'a, D: NonZero + 'a> SubAssign for Ratio<N, D> where Self: SubAssign<&'a Self> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        SubAssign::sub_assign(self, &rhs)
    }
}

impl<'a, N: 'a, D: NonZero + 'a> Mul<&Self> for Ratio<N, D> where Self: MulAssign<&'a Self> {
    type Output = Self;
    
    #[must_use]
    #[inline]
    fn mul(mut self, rhs: &Self) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl<'a, N: 'a, D: NonZero + 'a> Mul<Self> for &'a Ratio<N, D> {
    type Output = Ratio<N, D>;
    
    #[must_use]
    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        Mul::mul(self.clone(), rhs)
    }
}

impl<N, D: NonZero> Mul for Ratio<N, D> {
    type Output = Self;
    
    #[must_use]
    #[inline]
    fn mul(mut self, rhs: Self) -> Self::Output {
        MulAssign::mul_assign(&mut self, rhs);
        self
    }
}

impl<'a, N: 'a, D: NonZero + 'a> MulAssign for Ratio<N, D> where Self: MulAssign<&'a Self> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        MulAssign::mul_assign(self, &rhs);
    }
}

impl<N, D: NonZero> Mul<Ratio<N, D>> for &Ratio<N, D> where Ratio<N, D>: Mul<Self> {
    type Output = Ratio<N, D>;
    
    #[must_use]
    #[inline]
    fn mul(self, rhs: Ratio<N, D>) -> Self::Output {
        Mul::mul(rhs, self)
    }
}

impl<N, D: NonZero> Div for Ratio<N, D> where Self: DivAssign<Self> {
    type Output = Self;
    
    #[must_use]
    #[inline]
    fn div(mut self, rhs: Self) -> Self::Output {
        DivAssign::div_assign(&mut self, rhs);
        self
    }
}

impl<'a, N: 'a, D: NonZero + 'a> Div<&Self> for Ratio<N, D> where Self: DivAssign<&'a Self> {
    type Output = Self;
    
    #[must_use]
    #[inline]
    fn div(mut self, rhs: &Self) -> Self::Output {
        DivAssign::div_assign(&mut self, rhs);
        self
    }
}

impl<'a, N: 'a, D: NonZero + 'a> Div<Self> for &'a Ratio<N, D> {
    type Output = Ratio<N, D>;
    
    #[must_use]
    #[inline]
    fn div(self, rhs: Self) -> Self::Output {
        Div::div(self.clone(), rhs)
    }
}

impl<'a, N: 'a, D: NonZero + 'a> DivAssign for Ratio<N, D> where Self: DivAssign<&'a Self> {
    #[inline]
    fn div_assign(&mut self, rhs: Self) {
        DivAssign::div_assign(self, &rhs);
    }
}
