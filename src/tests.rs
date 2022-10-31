// Copyright 2022 Redglyph
//
// Unit tests

#![cfg(test)]

use std::cmp::min;
use std::str::FromStr;
use std::time::Instant;
use num::{Float, ToPrimitive, Zero};
use crate::*;

#[test]
fn test_double() {
    // constants for double-precision encoding
    assert_eq!(SIGNIFICAND_SIZE, 53);
    assert_eq!(EXPONENT_BIAS, 1075);
    assert_eq!(MAX_IEEE_EXPONENT, 2047);
    assert_eq!(HIDDEN_BIT, 0x0010000000000000);
    assert_eq!(FRACTION_MASK, 0x000fffffffffffff);
    assert_eq!(EXPONENT_MASK, 0x7ff0000000000000);
    assert_eq!(SIGN_MASK, 0x8000000000000000);

    // base methods
    for f in vec![1.0, -1.0, f64::NAN, f64::INFINITY, f64::NEG_INFINITY, 0.0, 1e10, -1.5e-8] {
        let x = Double::from(f);
        let report = format!("test failed for f = {f}");
        assert_eq!(x.is_nan(), f.is_nan(), "{report}");
        assert_eq!(x.is_inf(), f.is_infinite(), "{report}");
        assert_eq!(x.is_zero(), f.is_zero(), "{report}");
        if x.is_finite() {
            let (significand, exponent, sign) = f.integer_decode();
            assert_eq!(significand & !HIDDEN_BIT, x.physical_fraction(), "{report}");
            assert_eq!(exponent + EXPONENT_BIAS as i16, (x.physical_exponent() as i16), "{report}");
            assert_eq!((1 - sign) / 2, x.sign_bit() as i8, "{report}");
        }
    }
}

#[test]
fn visual_dtoa() {
    let values = vec![
        1.0,
        0.5,
        0.35,
        0.125,
        0.123,
        0.1234,
        0.12345,
        0.123456,
        0.1234567,
        0.12345678,
        0.123456789,
        0.1234567890,
        0.12345678901,
        0.123456789012,
        0.1234567890123,
        0.12345678901234,
        0.123456789012345,
        0.1234567890123456,
        1.2345678901234567,
        12.345678901234567,
        1.2345e-190,
        -1.2345e-190,
        1.2345e190,
        -1.2345e190,
        f64::NAN,
        f64::NEG_INFINITY,
        f64::INFINITY
    ];
    let mut error = false;
    for value in values {
        let exp = if value.is_finite() && value.abs() > 1e-3 && value.abs() < 1e3 {
            value.to_string()
        } else {
            format!("{value:e}")
        };
        let res = dtoa(value);
        if exp != res {
            error = true;
            println!("{exp} -> {res} ## ERROR");
        }
    }
    assert!(!error);
}

#[test]
fn random_dtoa() {
    // we cannot simply compare all values to Grisu3/Dragon4 because some roundings will be different,
    // here we check that the parsed string yields the same original value:
    let mut rng = oorandom::Rand64::new(0);
    let timer = Instant::now();
    for i in 0..10_000_000 {
        let mut f;
        loop {
            let ieee = rng.rand_u64();
            f = unsafe { mem::transmute::<u64, f64>(ieee) };
            if f.is_finite() {
                break;
            }
        }
        let res = dtoa(f);
        let f2 = f64::from_str(&res).expect(&format!("test #{i}: could not convert {f} -> '{res}' -> f64"));
        assert_eq!(f, f2);
    }
    let elapsed = timer.elapsed();
    println!("elapsed time: {:.3} s", elapsed.as_secs_f64());
}

#[test]
fn digits_dtoa() {
    const MAX_TESTS: u64 = 1_000_000;
    const MAX_VALUE: f64 = ((1_u64 << 54) - 1) as f64;

    let mut rng = oorandom::Rand64::new(0);
    let mut low = 1.0;
    let mut high = 10.0;
    let timer = Instant::now();
    for digit in 1..=17 {
        let nbr_tests = min(MAX_TESTS, high.to_u64().unwrap() * 2 / 5);
        for _ in 0..nbr_tests {
            let value = (rng.rand_float() * (high - low) + low).trunc();
            let res = dtoa(value);
            let exp = value.to_string();
            assert_eq!(res, exp, "incorrect string");
        }
        low = high;
        high = if digit < 16 { high * 10.0 } else { MAX_VALUE };
    }
    let elapsed = timer.elapsed();
    println!("elapsed time: {:.3} s", elapsed.as_secs_f64());
}
