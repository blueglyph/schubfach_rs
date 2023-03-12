// Copyright 2022 Redglyph

use std::fmt::LowerExp;
use std::str::FromStr;
use ibig::{ibig, IBig};
use num::{Float, Zero};
use crate::*;

#[derive(Debug)]
struct FloatChecker<T> {
    v: T,
    s: String,
    options: FmtOptions
}

impl<T: Copy + FormatInterface> FloatChecker<T> {
    fn new(v: T, options: Option<FmtOptions>) -> Self {
        let options = options.unwrap_or(FmtOptions::simple());
        FloatChecker {
            v,
            s: v.format_opt(&options), //v.ftoa(),
            options
        }
    }
}

trait FloatConst where Self: Sized {
    const P: i32;
    const W: i32;
    const Q_MIN: i32;
    const Q_MAX: i32;
    const C_MIN: i64;
    const C_MAX: i64;
    const K_MIN: i32;
    const K_MAX: i32;
    const H: i32;
    const MIN_VALUE: Self;
    const MIN_NORMAL: Self;
    const MAX_VALUE: Self;
    const E_MIN: i32;
    const E_MAX: i32;
    const C_TINY: i64;
    const MIN_FIXED_DECIMAL_POINT: isize;
    const MAX_FIXED_DECIMAL_POINT: isize;

    fn max_len10() -> i32 {
        Self::MAX_FIXED_DECIMAL_POINT as i32
    }

    fn max_significant_digits() -> i32 {
        Self::H
    }
}

#[derive(Debug, Clone)]
struct ParseResult {
    c: i64,
    q: i32,
    len10: i32,
}

trait FloatTester {
    fn parse(&self, string: String) -> Result<ParseResult, &str>;
    fn recovers(&self, big: IBig) -> bool;
    fn is_ok(&self) -> Result<(), String>;
}

impl<T> FloatTester for FloatChecker<T>
    where T: Zero + Float + FormatInterface + FloatConst + From<f64> + FromStr
{
    fn parse(&self, mut string: String) -> Result<ParseResult, &str> {
        let mut result = ParseResult { c: 0, q: 0, len10: 0 };
        string.push('*'); // end delimiter
        unsafe {
            let ptr = string.as_ptr();
            let mut s = ptr;
            while *s == b'0' {
                s = s.add(1);
            }
            // => s is on the first non-zero integer digit (if any)
            if s.offset_from(ptr) > 1 {
                return Err("more than one leading zero in integer part");
            }
            let mut p = s;
            let mut overflow = false;
            while (*p).is_ascii_digit() {
                if !overflow {
                    let c = result.c.wrapping_mul(10).wrapping_add((*p - b'0') as i64);
                    if c < 0 {
                        overflow = true;
                    } else {
                        result.c = c;
                    }
                }
                if overflow {
                    if *p != b'0' {
                        return Err("too many digits in integer part");
                    }
                    result.q += 1;
                }
                p = p.add(1);
            }
            // => p is on the first character after the integer part
            result.len10 = p.offset_from(ptr) as i32;
            if result.len10 == 0 {
                return Err("integer part missing");
            }
            let mut fz = p;
            if *fz == b'.' {
                fz = fz.add(1);
            } else {
                return Err("decimal mark '.' missing")
            }
            // => fz is after '.' (if any)
            let mut f = fz;
            while *f == b'0' {
                if !overflow {
                    let c = result.c.wrapping_mul(10);
                    if c < 0 {
                        overflow = true;
                    } else {
                        result.c = c;
                    }
                }
                if overflow {
                    result.q += 1;
                }
                f = f.add(1);
            }
            // => f is on the first non-zero fraction digit (if any)
            result.len10 = if result.c == 0 {
                0
            } else {
                f.offset_from(ptr) as i32 - 1
            };

            let mut x = f;

            while (*x).is_ascii_digit() {
                if !overflow {
                    let c = result.c.wrapping_mul(10).wrapping_add((*x - b'0') as i64);
                    if c < 0 {
                        overflow = true;
                    } else {
                        result.c = c;
                    }
                }
                if overflow {
                    if *x != b'0' {
                        return Err("too many digits in integer + fractional parts");
                    }
                    result.q += 1;
                }
                x = x.add(1);
            }
            // => x is after the last fraction digit
            if f.offset_from(fz) > 1 && x == f {
                return Err("several zeros only in fractional part");
            }
            if x == fz {
                return Err("fractional part missing")
            }
            result.len10 += x.offset_from(f) as i32;
            let mut g = x;
            if *g == b'e' || *g == b'E' {
                g = g.add(1);
            }
            // => g is after the exponent 'e' indicator (if any)
            let mut ez = g;
            if *ez == b'-' {
                ez = ez.add(1);
            }
            // => ez is after the exponent sign (if any)
            let mut e = ez;
            while *e == b'0' {
                e = e.add(1);
            }
            // => e is on the first non-zero exponent digit (if any)
            let mut z = e;
            while (*z).is_ascii_digit() {
                result.q = result.q.wrapping_mul(10).wrapping_add((*z - b'0') as i32);
                if result.q < 0 {
                    return Err("exponent too big");
                }
                z = z.add(1);
            }
            // => z is after the last exponent digit

            // check for the end of the string
            if z.offset_from(ptr) as usize != string.len() - 1 {
                return Err("trailing characters");
            }

            if x == z { // no exponent
                if *s == b'.' {
                    // check -MIN_FIXED_DECIMAL_POINT when abs(v) < 1
                    let min_dec = -T::MIN_FIXED_DECIMAL_POINT;
                    if f.offset_from(p) > min_dec {
                        return Err("too small, should have been exponent notation");
                    }
                } else {
                    // check MAX_FIXED_DECIMAL_POINT when abs(v) >= 1
                    let max_dec = T::MAX_FIXED_DECIMAL_POINT;
                    if p.offset_from(s) > max_dec {
                        return Err("too big, should have been exponent notation");
                    }
                }
                result.q -= x.offset_from(fz) as i32;
                Ok(result)
            } else { // exponent
                if x == g {
                    return Err("missing exponent mark 'e'/'E'");
                }
                if ez == z {
                    return Err("missing exponent");
                }
                if e == z {
                    return Err("null exponent");
                }
                if ez != e {
                    return Err("'0' digit(s) in front of exponent");
                }
                if s == p {
                    return Err("exponent notation with '0' integer digit");
                }
                if p.offset_from(s) > 1 {
                    return Err("exponent notation with more than one integer digit")
                }
                if g != ez {
                    // negative exponent
                    result.q = -result.q;
                }
                // => result.q is the exponent
                if T::MIN_FIXED_DECIMAL_POINT as i32 <= result.q && result.q < T::MAX_FIXED_DECIMAL_POINT as i32 {
                    return Err("should not have been exponent notation");
                }
                result.q -= x.offset_from(fz) as i32;
                // => result.q is the "exponent of the last digit", if there were no decimal point
                Ok(result)
            }
        }
    }

    fn recovers(&self, big: IBig) -> bool {
        let value: T = big.to_f64().into();
        value == self.v
    }


    fn is_ok(&self) -> Result<(), String> {
        // tests that parsing the generated string yields the original value
        match self.s.parse::<T>() {
            Ok(recovered) => if recovered != self.v {
                return Err(format!("string '{}' does not recover original value", self.s));
            }
            Err(_) => return Err(format!("Error when parsing string to float")),
        }

        // parses the string to verify its format
        let mut s = self.s.clone();
        let mut v = self.v;
        if v.is_nan() {
            if self.s != "NaN" {
                return Err("expected 'NaN'".to_string());
            }
            return Ok(())
        }
        if v.is_sign_negative() && (!v.is_zero() || self.options.negative_zero) {
            if s.is_empty() || !s.starts_with('-') {
                return Err("empty or not starting with '-'".to_string());
            }
            v = -self.v;
            s.remove(0);
        }
        if v.is_infinite() {
            if s != "inf" {
                return Err("expected 'inf' (or '-inf')".to_string());
            }
            return Ok(())
        }
        if v.is_zero() {
            return match self.options.trailing_dot_zero {
                true  if s != "0.0" => { Err("expected '0.0' (or '-0.0')".to_string()) },
                false if s != "0" => { Err("expected '0' (or '-0')".to_string()) },
                _ => Ok(())
            }
        }

        let mut parsed = self.parse(s)?;
        while parsed.len10 > T::max_significant_digits() {
            if parsed.c % 10 != 0 {
                return Err(format!("expected multiple of 10 for a value with more than {} integer digits ({} -> {} * 10^{})",
                                   T::max_significant_digits(), self.s, parsed.c, parsed.q));
            }
            parsed.c /= 10;
            parsed.q += 1;
            parsed.len10 -= 1;
        }
        if parsed.len10 < 2 {
            parsed.c *= 10;
            parsed.q -= 1;
            parsed.len10 += 1;
        }

        // println!("parsed: {:?}", parsed);

        if parsed.len10 < 2 || T::max_len10() < parsed.len10 {
            return Err(format!("parsed.len10 = {} out of boundaries (2 .. {})", parsed.len10, T::max_len10()));
        }

        if parsed.len10 > 2 {
            let mut p = parsed.clone();
            while p.c % 10 == 0 {
                p.c /= 10;
                p.q += 1;
                p.len10 -= 1;
            }
            let low = ibig_scale(p.c as u64 / 10, -p.q - 1);
            // println!("ibig_scale({}, {})", p.c as u64 / 10, -p.q - 1);
            if self.recovers(low.clone()) {
                return Err(format!("recovers with shorter, lower value ({})", &low));
            }
            let high = ibig_scale(p.c as u64 / 10 + 1, -p.q - 1);
            if self.recovers(high.clone()) {
                return Err(format!("recovers with shorter, higher value ({})", &high));
            }
        }
/*
        // Try with the decimal predecessor...
        BigDecimal dp = c == 10 ?
                BigDecimal.valueOf(99, -q + 1) :
                BigDecimal.valueOf(c - 1, -q);
        if (recovers(dp)) {
            BigDecimal bv = toBigDecimal();
            BigDecimal deltav = bv.subtract(BigDecimal.valueOf(c, -q));
            if (deltav.signum() >= 0) {
                return true;
            }
            BigDecimal delta = dp.subtract(bv);
            if (delta.signum() >= 0) {
                return false;
            }
            int cmp = deltav.compareTo(delta);
            return cmp > 0 || cmp == 0 && (c & 0x1) == 0;
        }

        // ... and with the decimal successor
        BigDecimal ds = BigDecimal.valueOf(c + 1, -q);
        if (recovers(ds)) {
            BigDecimal bv = toBigDecimal();
            BigDecimal deltav = bv.subtract(BigDecimal.valueOf(c, -q));
            if (deltav.signum() <= 0) {
                return true;
            }
            BigDecimal delta = ds.subtract(bv);
            if (delta.signum() <= 0) {
                return false;
            }
            int cmp = deltav.compareTo(delta);
            return cmp < 0 || cmp == 0 && (c & 0x1) == 0;
        }

*/
        Ok(())
    }
}

fn ibig_scale(unscaled: u64, scale: i32) -> IBig {
    let unscaled_b = IBig::from(unscaled);
    let scale_b = ibig!(10).pow(scale.abs() as usize);
    if scale > 0 {
        unscaled_b / scale_b
    } else {
        unscaled_b * scale_b
    }
}

// ---------------------------------------------------------------------------------------------

impl FloatConst for f64 {
    // Pre-calculated constants because most functions are unstable as const:
    const P: i32 = 53;
    const W: i32 = 11;
    const Q_MIN: i32 = -1074;
    const Q_MAX: i32 = 971;
    const C_MIN: i64 = 4503599627370496;
    const C_MAX: i64 = 9007199254740991;
    const K_MIN: i32 = -324;
    const K_MAX: i32 = 292;
    const H: i32 = 17; // maximum number of significant digits
    const MIN_VALUE: f64 = 4.9E-324;    // replace with f64::from_bits(0x0000000000000001) when const stable
    const MIN_NORMAL: f64 = 2.2250738585072014E-308;
    const MAX_VALUE: f64 = 1.7976931348623157E308;
    const E_MIN: i32 = -323;
    const E_MAX: i32 = 309;
    const C_TINY: i64 = 3;
    const MIN_FIXED_DECIMAL_POINT: isize = <NumFmtBuffer as NumFormat<f64, u64>>::MIN_FIXED_DECIMAL_POINT as isize;
    const MAX_FIXED_DECIMAL_POINT: isize = <NumFmtBuffer as NumFormat<f64, u64>>::MAX_FIXED_DECIMAL_POINT as isize;
}

#[test]
fn test_checker() {
    let values: &[(i64, i32, &str)] = &[
        (1000000000000000000, 1, "10000000000000000000.0"),
        (10, 21, "1.0e22"),
        (125, -24, "1.25e-22"),
        (10, -1, "1.0"),
        (100010, -1, "10001.0"),
    ];
    for (id, (c, q, s)) in values.iter().enumerate() {
        let chk = FloatChecker { v: 0.0, s: s.to_string(), options: FmtOptions::default() };
        match chk.parse(s.to_string()) {
            Ok(result) => {
                // println!("{:?}", result);
                assert_eq!(*c, result.c, "wrong value of c in test {}", id);
                assert_eq!(*q, result.q, "wrong value of q in test {}", id);
            }
            Err(e) => panic!("{}", format!("cannot parse value {}: {}", s, e.to_string()))
        }
    }
}
// ---------------------------------------------------------------------------------------------

fn test_dec<T>(x: T)
    where T: Zero + Float + FormatInterface + FloatConst + Display + LowerExp + From<f64> + FromStr
{
    let mut options = FmtOptions::simple();
    options.trailing_dot_zero = true;
    let checker = FloatChecker::new(x, Some(options));
    println!("{x:e} => {}", checker.s);
    if let Err(msg) = checker.is_ok() {
        panic!("'{x:e}' didn't pass the test. Result: '{}', error:'{msg}'", checker.s);
    }
}

#[test]
fn test_extreme_values() {
    assert_eq!(f64::MIN_VALUE, f64::from_bits(0x0000000000000001));

    test_dec(f64::NEG_INFINITY);
    test_dec(-f64::MAX_VALUE);
    test_dec(-f64::MIN_NORMAL);
    test_dec(-f64::MIN_VALUE);
    test_dec(-0.0);
    test_dec(0.0);
    test_dec(f64::MIN_VALUE);
    test_dec(f64::MIN_NORMAL);
    test_dec(f64::MAX_VALUE);
    test_dec(f64::INFINITY);
    test_dec(f64::NAN);
}

/// There are tons of doubles that are rendered incorrectly by the JDK.
/// While the renderings correctly round back to the original value,
/// they are longer than needed or are not the closest decimal to the double.
/// Here are just a very few examples.
const ANOMALIES: &[&str] = &[
        // JDK renders these, and others, with 18 digits!
        "2.82879384806159E17", "1.387364135037754E18",
        "1.45800632428665E17",

        // JDK renders these longer than needed.
        "1.6E-322", "6.3E-322",
        "7.3879E20", "2.0E23", "7.0E22", "9.2E22",
        "9.5E21", "3.1E22", "5.63E21", "8.41E21",

        // JDK does not render these, and many others, as the closest.
        "9.9E-324", "9.9E-323",
        "1.9400994884341945E25", "3.6131332396758635E25",
        "2.5138990223946153E25",
];

#[test]
fn test_some_anomalies() {
    for dec in ANOMALIES {
        test_dec(dec.parse::<f64>().unwrap());
    }
}
