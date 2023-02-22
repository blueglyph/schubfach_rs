// Copyright 2022 Redglyph

use num::{Float, Zero};
use crate::*;

#[derive(Debug)]
struct FloatChecker<T> {
    v: T,
    s: String,
}

impl<T: Copy + FormatInterface> FloatChecker<T> {
    fn new(v: T) -> Self {
        FloatChecker {
            v,
            s: v.ftoa(),
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
}

struct ParseResult {
    c: i64,
    q: i32,
    len10: i32,
}

trait FloatTester {
    fn is_ok(&self) -> Result<ParseResult, &str>;
    fn parse(&self, string: String) -> Result<ParseResult, &str>;
}

impl<T: Zero + Float + FormatInterface + FloatConst> FloatTester for FloatChecker<T> {
    fn is_ok(&self) -> Result<ParseResult, &str> {
        let mut s = self.s.clone();
        let mut v = self.v;
        if v.is_nan() {
            if self.s != "NaN" {
                return Err("expected 'NaN'");
            }
        }
        if v.is_sign_negative() {
            if s.is_empty() || !s.starts_with('-') {
                return Err("empty or not starting with '-'");
            }
            v = -self.v;
            s.remove(0);
        }
        if v.is_infinite() {
            if s != "inf" {
                return Err("expected 'inf' (or '-inf')");
            }
        }
        if v.is_zero() {
            if s != "0" {
                return Err("expected '0' (or '-0')");
            }
        }
        let parsed = self.parse(s)?;

        Ok(parsed)
    }

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
            while (*p).is_ascii_digit() {
                result.c = result.c.wrapping_mul(10).wrapping_add((*p - b'0') as i64);
                if result.c < 0 {
                    return Err("integer part too big");
                }
                p = p.add(1);
            }
            // => p is on the first character after the integer part
            result.len10 = p.offset_from(s) as i32;
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
                result.c = result.c.wrapping_mul(10);
                if result.c < 0 {
                    return Err("fractional part too big");
                }
                f = f.add(1);
            }
            // => f is on the first non-zero fraction digit (if any)
            if result.c == 0 {
                result.len10 = 0;
            }
            let mut x = f;
            while (*x).is_ascii_digit() {
                result.c = result.c.wrapping_mul(10).wrapping_add((*x - b'0') as i64);
                if result.c < 0 {
                    return Err("fractional part too big");
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
            let mut g = x;
            if *g == b'e' || *g == b'E' {
                g = g.add(1);
            }
            // => g is after the exponent 'e' indicator (if any)
            let mut ez = x;
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
                result.q = fz.offset_from(x) as i32;
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
    const H: i32 = 17;
    const MIN_VALUE: f64 = 4.9E-324;
    const MIN_NORMAL: f64 = 2.2250738585072014E-308;
    const MAX_VALUE: f64 = 1.7976931348623157E308;
    const E_MIN: i32 = -323;
    const E_MAX: i32 = 309;
    const C_TINY: i64 = 3;
    const MIN_FIXED_DECIMAL_POINT: isize = <NumFmtBuffer as NumFormat<f64, u64>>::MIN_FIXED_DECIMAL_POINT as isize;
    const MAX_FIXED_DECIMAL_POINT: isize = <NumFmtBuffer as NumFormat<f64, u64>>::MAX_FIXED_DECIMAL_POINT as isize;
}

// ---------------------------------------------------------------------------------------------

fn test_dec<T: Zero + Float + FormatInterface + FloatConst + Display>(x: T) {
    let mut checker = FloatChecker::new(x);
    if let Err(msg) = checker.is_ok() {
        panic!("{x} didn't pass the test. Result: '{}', error:'{msg}'", checker.s);
    }
}

#[test]
fn test_build() {
    test_dec(-0.0);
    test_dec(f64::NAN);
    test_dec(f64::INFINITY);
    test_dec(f64::NEG_INFINITY);
    test_dec(0.0);
    test_dec(-0.0);
}

#[test]
fn test_2() {
    for i in 0..10 {
        print!("{i} ");
        match () {
            _ if i < 3 => println!("< 3"),
            _ if i < 7 => println!("< 7"),
            _ if i < 9 => println!("< 9"),
            _ => {}
        }
    }
}