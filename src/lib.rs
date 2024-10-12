use std::ops;
use core::fmt;
use gcd::Gcd;

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Fraction {
    neg_sign: bool,
    numerator: u64,
    denominator: u64,
}

impl Fraction {
    /// Equivalent to `(+) u64::MAX / 1`.
    pub const MAX: Fraction = Fraction {
        neg_sign: false, numerator: u64::MAX, denominator: 1
    };
    /// Equivalent to `(+) 1 / u64::MAX`.
    pub const MIN_POSITIVE: Fraction = Fraction {
        neg_sign: false, numerator: 1, denominator: u64::MAX
    };
    /// Equivalent to `(-) u64::MAX / 1`.
    pub const MAX_NEGATIVE: Fraction = Fraction {
        neg_sign: true, numerator: u64::MAX, denominator: 1
    };
    /// Equivalent to `(-) 1 / u64::MAX`
    /// or `-1 / u64::MAX`.
    pub const MIN: Fraction = Fraction {
        neg_sign: true, numerator: 1, denominator: u64::MAX
    };
    /// Defined as `(+) 0 / 0`.
    pub const UNDEFINED: Fraction = Fraction {
        neg_sign: false, numerator: 0, denominator: 0
    };
    /// Using the principle that as a denominator approaches 0 from the right,
    /// a rational approaches a value closer and closer to infinity:
    /// 
    /// `INFINITY` is defined as `(+) 1 / 0`.
    pub const INFINITY: Fraction = Fraction {
        neg_sign: false, numerator: 1, denominator: 0
    };
    /// Using the principle that as a denominator approaches 0 from the left,
    /// a rational approaches a value closer and closer to negative infinity:
    /// 
    /// `NEG_INFINITY` is defined as `(-) 1 / 0`.
    pub const NEG_INFINITY: Fraction = Fraction {
        neg_sign: true, numerator: 1, denominator: 0
    };
    /// Defined as `(+) 0 / 1`.
    pub const ZERO: Fraction = Fraction {
        neg_sign: false, numerator: 0, denominator: 1
    };
    /// Defined as `(+) 1 / 1`.
    pub const ONE: Fraction = Fraction {
        neg_sign: false, numerator: 1, denominator: 1
    };
    /// Defined as `(-) 1 / 1` or `-1 / 1`.
    pub const NEG_ONE: Fraction = Fraction {
        neg_sign: true, numerator: 1, denominator: 1
    };

    pub fn new() -> Self { Fraction::ONE }

    pub fn from(neg_sign: bool, numerator: u64, denominator: u64) -> Self {
        Fraction {
            neg_sign,
            numerator,
            denominator,
        }
    }

    pub fn negate(&mut self) { self.neg_sign = !self.neg_sign }

    pub fn negated(self) -> Self {
        Fraction::from(
            !self.neg_sign,
            self.numerator,
            self.denominator
        )
    }

    pub fn reciprocal(self) -> Self {
        Fraction::from(self.neg_sign, self.denominator, self.numerator)
    }

    pub fn simplify(&mut self) {
        let common_divisor = self.numerator.gcd(self.denominator);
        self.numerator /= common_divisor;
        self.denominator /= common_divisor;
    }

    pub fn simplifed(self) -> Self {
        if self.numerator == 0 && self.denominator != 0 {
            return Fraction::ZERO;
        }
        if self.numerator != 0 && self.denominator == 0 {
            return match self.neg_sign {
                true => Fraction::NEG_INFINITY,
                false => Fraction::INFINITY
            }
        }
        if self.numerator == 0 && self.denominator == 0 {
            return Fraction::UNDEFINED;
        }
        if self.numerator == self.denominator {
            return match self.neg_sign {
                true => Fraction::NEG_ONE,
                false => Fraction::ONE
            }
        }
        let gcd = self.numerator.gcd(self.denominator);
        Fraction::from(
            self.neg_sign,
            self.numerator / gcd,
            self.denominator / gcd
        )
    }

    pub fn as_f64(self) -> f64 {
        let negate = match self.neg_sign {
            true => -1.0,
            false => 1.0,
        };

        match self.denominator {
            0 => f64::NAN,
            _ => negate * self.numerator as f64 / self.denominator as f64,
        }
    }

    pub fn from_f64(fp: f64) -> Self {
        if !fp.is_finite() {
            return match fp {
                f64::INFINITY => Fraction::INFINITY,
                f64::NEG_INFINITY => Fraction::NEG_INFINITY,
                _ => Fraction::UNDEFINED
            }
        }
        if fp.abs() == 0.0f64 {
            return Fraction::ZERO
        }

        let u_int_pow_of_ten = 10u64.pow(15);
        let float_pow_of_ten = 1e15;

        let near_int_fp = (fp.abs() * float_pow_of_ten).round();
        // Floating Point Integer Representation
        let fp_int_rep = unsafe { near_int_fp.to_int_unchecked::<u64>() };

        Fraction { // no need to check for -0.0 due to guard clause
            neg_sign: fp.is_sign_negative(),
            numerator: (fp_int_rep / fp_int_rep.gcd(u_int_pow_of_ten)),
            denominator: (u_int_pow_of_ten / fp_int_rep.gcd(u_int_pow_of_ten)),
        }
    }
    
    pub fn cap_to_finite(self) -> Self {
        match self {
            Fraction::INFINITY => Fraction::MAX,
            Fraction::NEG_INFINITY => Fraction::MIN,
            Fraction::UNDEFINED => Fraction::ZERO,
            _ => self
        }
    }
}

impl ops::Mul for Fraction {
    // The multiplication of rational numbers is a closed operation.
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let neg_sign = self.neg_sign ^ rhs.neg_sign;
        let numerator = self.numerator * rhs.numerator;
        let denominator = self.denominator * rhs.denominator;
        Self::from(neg_sign, numerator, denominator)
    }
}

impl ops::Div for Fraction {
    // The multiplication of rational numbers is a closed operation.
    type Output = Self;

    fn div(self, rhs: Self) -> Self {
        let neg_sign = self.neg_sign ^ rhs.neg_sign;
        let numerator = self.numerator * rhs.denominator;
        let denominator = self.denominator * rhs.numerator;
        Self::from(neg_sign, numerator, denominator)
    }
}

impl fmt::Display for Fraction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}/{}",
            match self.neg_sign {
                true => "-",
                false => "",
            },
            self.numerator,
            self.denominator
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identities() {
        assert_eq!(Fraction::MAX, Fraction::MIN_POSITIVE.reciprocal());
        assert_eq!(Fraction::MAX_NEGATIVE, Fraction::MIN.reciprocal());
        assert_eq!(Fraction::INFINITY, Fraction::NEG_INFINITY.negated());
        assert_eq!(Fraction::ZERO, Fraction::from(false, 0, 1000).simplifed());
        assert_eq!(Fraction::UNDEFINED, Fraction::from(true, 0, 0).simplifed());
        assert_eq!(
            (Fraction::MAX * Fraction::MIN_POSITIVE).simplifed(),
            Fraction::ONE
        );
    }

    #[test]
    fn float_evaluations() {
        assert_eq!(Fraction::from_f64(f64::INFINITY), Fraction::INFINITY);
        assert_eq!(Fraction::from_f64(f64::NEG_INFINITY), Fraction::NEG_INFINITY);
        assert_eq!(Fraction::from_f64(f64::NAN), Fraction::UNDEFINED);
        assert_eq!(Fraction::from_f64(-0.0f64), Fraction::ZERO);
    }

    #[test]
    fn capping() {
        assert_eq!(Fraction::INFINITY.cap_to_finite(), Fraction::MAX);
        assert_eq!(Fraction::MAX.cap_to_finite(), Fraction::MAX);
    }
}
