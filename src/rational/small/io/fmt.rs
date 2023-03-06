use std::fmt;
use num_traits::One;
use crate::rational::small::Ratio;
use crate::{NonZero, Sign, Signed};
use crate::sign::{NonNegativelySigned, NonNegativeSign, PositivelySigned};

impl<
    N: fmt::Display,
    D: fmt::Display + NonZero,
> fmt::Display for Ratio<N, D> {
    default fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.numerator.fmt(f)?;
        f.write_str("/")?;
        self.denominator.fmt(f)
    }
}

trait TestSkipDenom = One<Output=Self> + PartialEq;
impl<
    N: Signed + fmt::Display,
    D: TestSkipDenom + fmt::Display + NonZero,
> fmt::Display for Ratio<N, D> {
    default fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.numerator.signum() {
            Sign::Positive => {}
            Sign::Zero => return f.write_str("0"),
            Sign::Negative => {
                f.write_str("-")?;
            }
        }

        write_values(&self.numerator, &self.denominator, f)
    }
}

impl<
    N: NonNegativelySigned + Signed + fmt::Display,
    D: TestSkipDenom + fmt::Display + NonZero,
> fmt::Display for Ratio<N, D> {
    default fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match NonNegativelySigned::signum(&self.numerator) {
            NonNegativeSign::Zero => f.write_str("0"),
            NonNegativeSign::Positive => write_values(&self.numerator, &self.denominator, f),
        }
    }
}

impl<
    N: PositivelySigned + NonNegativelySigned + Signed + fmt::Display,
    D: TestSkipDenom + fmt::Display + NonZero,
> fmt::Display for Ratio<N, D> {
    default fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write_values(&self.numerator, &self.denominator, f)
    }
}

fn write_values<
    N: fmt::Display,
    D: TestSkipDenom + fmt::Display,
>(
    numerator: &N,
    denominator: &D,
    f: &mut fmt::Formatter,
) -> fmt::Result {
    numerator.fmt(f)?;
    if !denominator.is_one() {
        f.write_str("/")?;
        denominator.fmt(f)?;
    }

    Ok(())
}

impl<N, D: NonZero> fmt::Debug for Ratio<N, D> where Self: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self, f)
    }
}
