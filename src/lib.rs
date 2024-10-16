use core::fmt;
use gcd::Gcd;
use std::ops;

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Fraction {
    neg_sign: bool,
    numerator: u64,
    denominator: u64,
}

impl Fraction {
    /// Equivalent to `(+) u64::MAX / 1`.
    pub const POS_MAX: Fraction = Fraction {
        neg_sign: false,
        numerator: u64::MAX,
        denominator: 1,
    };
    /// Equivalent to `(+) 1 / u64::MAX`.
    pub const POS_MIN: Fraction = Fraction {
        neg_sign: false,
        numerator: 1,
        denominator: u64::MAX,
    };
    /// Equivalent to `(-) u64::MAX / 1`.
    pub const NEG_MAX: Fraction = Fraction {
        neg_sign: true,
        numerator: u64::MAX,
        denominator: 1,
    };
    /// Equivalent to `(-) 1 / u64::MAX`
    /// or `-1 / u64::MAX`.
    pub const NEG_MIN: Fraction = Fraction {
        neg_sign: true,
        numerator: 1,
        denominator: u64::MAX,
    };
    /// Defined as `(+) 0 / 0`.
    pub const UNDEFINED: Fraction = Fraction {
        neg_sign: false,
        numerator: 0,
        denominator: 0,
    };
    /// Using the principle that as a denominator approaches 0 from the right,
    /// a rational approaches a value closer and closer to infinity:
    ///
    /// `INFINITY` is defined as `(+) 1 / 0`.
    pub const INFINITY: Fraction = Fraction {
        neg_sign: false,
        numerator: 1,
        denominator: 0,
    };
    /// Using the principle that as a denominator approaches 0 from the left,
    /// a rational approaches a value closer and closer to negative infinity:
    ///
    /// `NEG_INFINITY` is defined as `(-) 1 / 0`.
    pub const NEG_INFINITY: Fraction = Fraction {
        neg_sign: true,
        numerator: 1,
        denominator: 0,
    };
    /// Defined as `(+) 0 / 1`.
    pub const ZERO: Fraction = Fraction {
        neg_sign: false,
        numerator: 0,
        denominator: 1,
    };
    /// Defined as `(-) 0 / 1`.
    pub const NEG_ZERO: Fraction = Fraction {
        neg_sign: true,
        numerator: 0,
        denominator: 1,
    };
    /// Defined as `(+) 1 / 1`.
    pub const ONE: Fraction = Fraction {
        neg_sign: false,
        numerator: 1,
        denominator: 1,
    };
    /// Defined as `(-) 1 / 1` or `-1 / 1`.
    pub const NEG_ONE: Fraction = Fraction {
        neg_sign: true,
        numerator: 1,
        denominator: 1,
    };
    /// A fractional representation of Pi (π), accurate to 15 digits
    /// (when using Fraction::as_f64).
    pub const PI: Fraction = Fraction {
        neg_sign: false,
        numerator: 884279719003555,
        denominator: 281474976710656,
    };
    /// A selector for an IEEE 754 compliant f64's fraction.
    /// 
    /// Equivalent to `0x000FFFFFFFFFFFFF`.
    const IEEE_754_DOUBLE_FRACTION: u64 = 0x000FFFFFFFFFFFFF;
    /// A selector for an IEEE 754 compliant f64's exponent.
    /// 
    /// Equivalent to `0x7FF0000000000000`.
    const IEEE_754_DOUBLE_EXPONENT: u64 = 0x7FF0000000000000;
    /// A selector for an IEEE 754 compliant f64's sign bit.
    /// 
    /// Equivalent to `0x8000000000000000` and `f64::to_bits(-0.0).to_le()`.
    const IEEE_754_DOUBLE_SIGN_BIT: u64 = 0x8000000000000000;

    /// Returns `Fraction::ONE`.
    pub fn new() -> Self {
        Fraction::ONE
    }

    /// Returns a new fraction from a `bool` sign and two `u64`s.
    pub fn from(neg_sign: bool, numerator: u64, denominator: u64) -> Self {
        Fraction {
            neg_sign,
            numerator,
            denominator,
        }
    }

    /// Mutates a fraction's `neg_sign`.
    pub fn negate(&mut self) {
        self.neg_sign = !self.neg_sign
    }

    /// Returns a negated version of the fraction.
    pub fn negated(self) -> Self {
        Fraction::from(!self.neg_sign, self.numerator, self.denominator)
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
                false => Fraction::INFINITY,
            };
        }
        if self.numerator == 0 && self.denominator == 0 {
            return Fraction::UNDEFINED;
        }
        if self.numerator == self.denominator {
            return match self.neg_sign {
                true => Fraction::NEG_ONE,
                false => Fraction::ONE,
            };
        }
        let gcd = self.numerator.gcd(self.denominator);
        Fraction::from(self.neg_sign, self.numerator / gcd, self.denominator / gcd)
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
    /// # THIS WILL CRASH!!!
    /// If the exponent of the floating point is too large, Rust will
    /// state that a (u64) value has overflowed.
    /// This is because the exponent can be anywhere from 2<sup>-1022</sup>
    /// to 2<sup>1023</sup>, which far exceeds the u64's maximum value of
    /// (2<sup>64</sup> - 1).
    ///
    /// _Nola's Note:
    /// Only tested thus far on Little Endian hardware._
    pub fn from_f64(fp: f64) -> Self {
        match fp {
            f64::INFINITY => return Fraction::INFINITY,
            f64::NEG_INFINITY => return Fraction::NEG_INFINITY,
            _ => {},
        }

        let float_as_bits: u64 = fp.to_bits().to_le();
        match float_as_bits {
            Fraction::IEEE_754_DOUBLE_SIGN_BIT => return Fraction::NEG_ZERO,
            0 => return Fraction::ZERO,
            _ => {},
        }

        let sign: bool = Fraction::IEEE_754_DOUBLE_SIGN_BIT & float_as_bits == Fraction::IEEE_754_DOUBLE_SIGN_BIT;
        let fraction: u64 = Fraction::IEEE_754_DOUBLE_FRACTION & float_as_bits;

        let le_exponent: u64 = (float_as_bits & Fraction::IEEE_754_DOUBLE_EXPONENT).to_le() >> Fraction::IEEE_754_DOUBLE_FRACTION.count_ones();
        let halved_exponent_bytes: Vec<u8> = le_exponent
            .to_le_bytes() // convert to an array of `u8`s
            .split_at(8 / 2) // split the array in half
            .0 // take the first array
            .iter() // iterate over it
            .map(|&x| x) // mapping the borrowed u8s to owned u8s
            .collect(); // put them into the final Vector

        // because the exponent is 11 bits, we only need two bytes to
        // contain it, and storing it as an i16 allows for various type
        // conversions and negative representations
        let exponent: i16 = i16::from_le_bytes([halved_exponent_bytes[0], halved_exponent_bytes[1]]);

        Fraction::UNDEFINED
    }

    /// Clamps infinite values to extreme, but absolute Fractions.
    ///
    /// Finite values remain untouched.
    pub fn cap_to_finite(self) -> Self {
        match self {
            Fraction::INFINITY => Fraction::POS_MAX,
            Fraction::NEG_INFINITY => Fraction::NEG_MAX,
            Fraction::UNDEFINED => Fraction::ZERO,
            _ => self,
        }
    }
}

impl ops::Add for Fraction {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let lcm = self.denominator * rhs.denominator / self.denominator.gcd(rhs.denominator);
        let lhs_num = self.numerator * rhs.denominator;
        let rhs_num = rhs.numerator * self.denominator;
        let neg_sign = match self.neg_sign ^ rhs.neg_sign {
            false => self.neg_sign,
            true => (lhs_num > rhs_num) ^ rhs.neg_sign,
        };
        let numerator = match self.neg_sign ^ rhs.neg_sign {
            true => lhs_num.abs_diff(rhs_num),
            false => lhs_num + rhs_num,
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
        Self::from(neg_sign, numerator, denominator).simplified()
    }
}

impl ops::Div for Fraction {
    type Output = Self;

    fn div(self, rhs: Self) -> Self {
        let neg_sign = self.neg_sign ^ rhs.neg_sign;
        let numerator = self.numerator * rhs.denominator;
        let denominator = self.denominator * rhs.numerator;
        Self::from(neg_sign, numerator, denominator).simplified()
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
        assert_eq!(
            Fraction::from_f64(f64::NEG_INFINITY),
            Fraction::NEG_INFINITY
        );
        assert_eq!(Fraction::from_f64(f64::NAN), Fraction::UNDEFINED);
        assert_eq!(Fraction::from_f64(-0.0f64), Fraction::ZERO);
        assert_eq!(Fraction::from_f64(0.5), Fraction::from(false, 1, 2));
        assert!(
            (Fraction::from_f64(0.3333333333333333) + Fraction::from(true, 1, 3)).as_f64()
            < 1e10
        );
    }

    #[test]
    fn ieee_consts() {
        assert_eq!(
            0xFFFFFFFFFFFFFFFFu64,
            u64::MAX
        );
        assert_eq!(
            Fraction::IEEE_754_DOUBLE_SIGN_BIT ^
            Fraction::IEEE_754_DOUBLE_EXPONENT ^
            Fraction::IEEE_754_DOUBLE_FRACTION,
            u64::MAX
        );
    }

    #[test]
    #[should_panic]
    fn extreme_fp_conversions() {
        let float: f64 = 2.0;
        let mut i: i32 = 0;
        loop {
            println!("Converting {}.powi({})...", float, i);
            Fraction::from_f64(float.powi(i));
            i += 1;
        }
    }

    #[test]
    fn capping() {
        assert_eq!(Fraction::INFINITY.cap_to_finite(), Fraction::POS_MAX);
        assert_eq!(Fraction::POS_MAX.cap_to_finite(), Fraction::POS_MAX);
    }

    #[test]
    fn operations() {
        assert_eq!(
            Fraction::ONE + Fraction::from(false, 1, 2),
            Fraction::from(false, 3, 2)
        );
        assert_eq!(
            Fraction::NEG_ONE + Fraction::from(false, 1, 2),
            Fraction::from(true, 1, 2)
        );
        assert_eq!(Fraction::ONE + Fraction::NEG_ONE, Fraction::ZERO);
        assert_eq!(Fraction::NEG_ONE + Fraction::ONE, Fraction::ZERO);
    }
}
