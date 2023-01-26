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
}

struct ParseResult {
    c: i64,
    q: i32,
    len10: i32,
}

trait FloatTester {
    fn is_ok(&mut self) -> bool;
    fn parse(&self) -> Option<ParseResult>;
}

impl<T: Zero + Float + FormatInterface + FloatConst> FloatTester for FloatChecker<T> {
    fn is_ok(&mut self) -> bool {
        if self.v.is_nan() {
            return self.s == "NaN";
        }
        if self.v.is_sign_negative() {
            if self.s.is_empty() || !self.s.starts_with('-') {
                return false;
            }
            self.v = -self.v;
            self.s.remove(0);
        }
        if self.v.is_infinite() {
            return self.s == "inf";
        }
        if self.v.is_zero() {
            return self.s == "0"
        }
        if self.v < T::MIN_VALUE {  // TODO: fake, remove
            return false;
        }
        true
    }

    fn parse(&self) -> Option<ParseResult> {
        None
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
}

// ---------------------------------------------------------------------------------------------

fn test_dec<T: Zero + Float + FormatInterface + FloatConst + Display>(x: T) {
    let mut checker = FloatChecker::new(x);
    assert!(checker.is_ok(), "{x} didn't pass the test");
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
