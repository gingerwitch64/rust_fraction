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
    pub const POS_MAX: Fraction = Fraction {
        neg_sign: false, numerator: u64::MAX, denominator: 1
    };
    /// Equivalent to `(+) 1 / u64::MAX`.
    pub const POS_MIN: Fraction = Fraction {
        neg_sign: false, numerator: 1, denominator: u64::MAX
    };
    /// Equivalent to `(-) u64::MAX / 1`.
    pub const NEG_MAX: Fraction = Fraction {
        neg_sign: true, numerator: u64::MAX, denominator: 1
    };
    /// Equivalent to `(-) 1 / u64::MAX`
    /// or `-1 / u64::MAX`.
    pub const NEG_MIN: Fraction = Fraction {
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

    /// Returns `Fraction::ONE`.
    pub fn new() -> Self { Fraction::ONE }

    /// Returns a new fraction from a `bool` sign and two `u64`s.
    pub fn from(neg_sign: bool, numerator: u64, denominator: u64) -> Self {
        Fraction {
            neg_sign,
            numerator,
            denominator,
        }
    }

    /// Mutates a fraction's `neg_sign`.
    pub fn negate(&mut self) { self.neg_sign = !self.neg_sign }

    /// Returns a negated version of the fraction.
    pub fn negated(self) -> Self {
        Fraction::from(
            !self.neg_sign,
            self.numerator,
            self.denominator
        )
    }

    /// Returns a fraction with a swapped `numerator` and `denominator`.
    pub fn reciprocal(self) -> Self {
        Fraction::from(self.neg_sign, self.denominator, self.numerator)
    }

    /// NOT RECCOMENDED: USE `Fraction::simplified()` INSTEAD
    /// 
    /// This function does not support/will behave unusually
    /// with any fractions containing a value of `0`.
    /// 
    /// Mutates a fraction into a proportionate one.
    pub fn simplify(&mut self) {
        let common_divisor = self.numerator.gcd(self.denominator);
        self.numerator /= common_divisor;
        self.denominator /= common_divisor;
    }

    /// Returns a simplified version of the fraction.
    /// 
    /// Fractions with denominators of `0` will be simplified to
    /// `Fraction::NEG_INFINITY` or `Fraction::INFINITY` based on
    /// their negation sign, and either variant of `0/0` will be
    /// simplified to `Fraction::UNDEFINED`.
    pub fn simplified(self) -> Self {
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

    /// Potentially lossily converts a fraction into a 64 bit floating point.
    pub fn as_f64(self) -> f64 {
        let negate = match self.neg_sign {
            true => -1.0,
            false => 1.0,
        };

        match self.denominator {
            0 => f64::NAN,
            1 => negate * self.numerator as f64,
            _ => negate * self.numerator as f64 / self.denominator as f64,
        }
    }

    /// Losslessly converts a floating point to a `Fraction`.
    /// 
    /// This function uses the IEEE 754 double precision floating
    /// point standard to extract the sign, exponent and fraction from
    /// an f64, then using those numbers to construct a completely
    /// equivalent fraction.
    /// 
    /// _Nola's Note:
    /// Only tested thus far on Little Endian hardware._
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

        let two_pow_52: u64 = 0x10000000000000;
        let float: f64 = fp;
        let float_as_bits = float.to_bits().to_le();
        let ieee_754_fraction: u64 = 0x000FFFFFFFFFFFFF;
        let ieee_754_exponent: u64 = 0x7FF0000000000000;
        let ieee_754_sign:     u64 = 0x8000000000000000;
        let inv_two_pow_52: Fraction = Fraction::from(false, 0x1, two_pow_52);

        assert_eq!(ieee_754_exponent ^ ieee_754_fraction ^ ieee_754_sign, 0xFFFFFFFFFFFFFFFF);

        let sign: bool = ieee_754_sign & float_as_bits == ieee_754_sign;
        let fraction: u64 = ieee_754_fraction & float_as_bits;

        let le_exponent = (float_as_bits & ieee_754_exponent).to_le() >> 52;
        let halved_exponent_bytes =
        le_exponent
        .to_le_bytes()
        .split_at(8 / 2)
        .0
        .iter()
        .map(|&x| {x} )
        .collect::<Vec<u8>>();
        let signed_exponent: i16 = i16::from_le_bytes([
            halved_exponent_bytes[0],
            halved_exponent_bytes[1],
        ]);
        let final_exponent: i16 = match signed_exponent {
            0x7FF => panic!("Infinite/NAN Value Requested"),
            0 => -1022,
            _ => signed_exponent - 1023
        };
        let two_power_biased_exp: u64 = 2u64.pow(final_exponent.abs().try_into().unwrap());
        let frac_twopow: Fraction = match final_exponent.is_negative() {
            true => Fraction::from(false, 1, two_power_biased_exp),
            false => Fraction::from(false, two_power_biased_exp, 1),
        };
        let frac_fraction: Fraction = match signed_exponent {
            0 => Fraction::from(false, fraction, 1),
            _ => Fraction::from(false, two_pow_52 | fraction, 1),
        };
        let negator: Fraction = match sign {
            true => Fraction::NEG_ONE,
            false => Fraction::ONE
        };
        let final_frac: Fraction = negator * frac_twopow * frac_fraction * inv_two_pow_52;
        final_frac.simplified()
    }
    
    /// Clamps infinite values to extreme, but absolute Fractions.
    /// 
    /// Finite values remain untouched.
    pub fn cap_to_finite(self) -> Self {
        match self {
            Fraction::INFINITY => Fraction::POS_MAX,
            Fraction::NEG_INFINITY => Fraction::NEG_MAX,
            Fraction::UNDEFINED => Fraction::ZERO,
            _ => self
        }
    }
}

impl ops::Add for Fraction {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let lcm = self.denominator * rhs.denominator
                / self.denominator.gcd(rhs.denominator);
        let lhs_num = self.numerator * rhs.denominator;
        let rhs_num = rhs.numerator * self.denominator;
        let neg_sign = match self.neg_sign ^ rhs.neg_sign {
            false => self.neg_sign,
            true => (lhs_num > rhs_num) ^ rhs.neg_sign
        };
        let numerator = match self.neg_sign ^ rhs.neg_sign {
            true => lhs_num.abs_diff(rhs_num),
            false => lhs_num + rhs_num
        };
        let denominator: u64 = lcm;
        Self::from(neg_sign, numerator, denominator).simplified()
    }
}

impl ops::Mul for Fraction {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let neg_sign = self.neg_sign ^ rhs.neg_sign;
        let numerator = self.numerator * rhs.numerator;
        let denominator = self.denominator * rhs.denominator;
        Self::from(neg_sign, numerator, denominator)
    }
}

impl ops::Div for Fraction {
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
        assert_eq!(Fraction::POS_MAX, Fraction::POS_MIN.reciprocal());
        assert_eq!(Fraction::NEG_MAX, Fraction::NEG_MIN.reciprocal());
        assert_eq!(Fraction::INFINITY, Fraction::NEG_INFINITY.negated());
        assert_eq!(Fraction::ZERO, Fraction::from(false, 0, 1000).simplified());
        assert_eq!(Fraction::UNDEFINED, Fraction::from(true, 0, 0).simplified());
        assert_eq!(
            (Fraction::POS_MAX * Fraction::POS_MIN).simplified(),
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
        assert_eq!(Fraction::INFINITY.cap_to_finite(), Fraction::POS_MAX);
        assert_eq!(Fraction::POS_MAX.cap_to_finite(), Fraction::POS_MAX);
    }

    #[test]
    fn operations() {
        assert_eq!(Fraction::ONE + Fraction::from(false, 1, 2), Fraction::from(false, 3, 2));
        assert_eq!(Fraction::NEG_ONE + Fraction::from(false, 1, 2), Fraction::from(true, 1, 2));
        assert_eq!(Fraction::ONE + Fraction::NEG_ONE, Fraction::ZERO);
        assert_eq!(Fraction::NEG_ONE + Fraction::ONE, Fraction::ZERO);
    }
}
