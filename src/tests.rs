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
fn test_zero_fill() {
    let values = vec![
        1.0,
        -1.0,
        0.1,
        -0.1,
        1.0e100,
        -1.0e-100,
        1.125,
        1.0625,
        1.005,
        0.02,
        0.003,
        0.0004,
        0.00005,
        0.000025,
        0.0000000000000006,
        1000000020.0,
        1234567891.0,
        10.0,
        200.0,
        3000.0,
        40000.0,
        500000.0,
        6000000.0,
        70000000.0,
        800000000.0,
        90000000000.0,
        100000000000.0,
        2000000000000.0,
        30000000000000.0,
        400000000000000.0,
        5000000000000000.0,
        60000000000000000.0,
        700000000000000000.0,
        8000000000000000000.0,
        4.9130000005651315e250,
        60000000000000000.0,
        -43559580779681430.0,
    ];
    for value in values {
        let res = dtoa(value);
        let exp = {
            if res.contains('e') {
                format!("{value:e}")
            } else {
                value.to_string()
            }
        };
        assert_eq!(exp, res);
    }
}

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

    // constants used in FPFormatter
    assert!(FPFormatter::MIN_FIXED_DECIMAL_POINT <= -1, "internal error");
    assert!(FPFormatter::MIN_FIXED_DECIMAL_POINT >= -30, "internal error");
    assert!(FPFormatter::MAX_FIXED_DECIMAL_POINT >= 1, "internal error");
    assert!(FPFormatter::MAX_FIXED_DECIMAL_POINT <= 32, "internal error");

    // base methods
    for f in vec![1.0, -1.0, f64::NAN, f64::INFINITY, f64::NEG_INFINITY, 0.0, 1e10, -1.5e-8] {
        let x = Double::from(f);
        let report = format!("test failed for f = {f}");
        match x.encoding() {
            Encoding::NaN => assert!(f.is_nan(), "{report}"),
            Encoding::Inf => assert!(f.is_infinite(), "{report}"),
            Encoding::Zero => assert!(f.is_zero(), "{report}"),
            Encoding::Digits => assert!(f.is_finite() && !f.is_zero(), "{report}"),
        }
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
fn limits_dtoa() {
    let tests: &[(f64, &str)] = &[
        // those tests depend on the value of FPFormatter::MIN_FIXED_DECIMAL_POINT
        (0.0000002, "0.0000002"),
        (0.00000002, "2e-8"),
        // those tests depend on the value of FPFormatter::MAX_FIXED_DECIMAL_POINT
        (12345678901234562.0, "12345678901234562"),
        (123456789012345620.0, "1.2345678901234562e17"),
    ];
    for (idx, (value, exp)) in tests.into_iter().enumerate() {
        let res = dtoa(*value);
        assert_eq!(res, *exp, "failed in test #{idx}");
    }
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
    const MAX_TESTS: u64 = 2_000_000;
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

#[test]
fn visual_dtoa_width() {
    let values = vec![
        (1.0,       Some(10),   Some(4),    "1.0000"),  // d-d
        (1.5,       Some(10),   Some(4),    "1.5000"),  // d-d.d-d
        (100.0,     Some(10),   Some(2),    "100.00"),  // d-d(0-0)
        (30.125,    Some(10),   Some(4),    "30.1250"), // d-d.d-d(0-0)
        (0.5,       Some(10),   Some(2),    "0.50"),    // 0.d-d(0-0)
        (0.05,      Some(10),   Some(4),    "0.0500"),  // 0.(0-0)d-d
        (10.125,    Some(10),   Some(2),    "10.12"),   // rounding
        (20.375,    Some(10),   Some(2),    "20.38"),   // rounding

        (99.9953,   Some(5),    Some(3),    "100.0"),   // rounding => prec -> 2 => one more digit => prec -> 1

        (99.9535,   Some(5),    Some(3),    "99.96"),   // len > 5 => precision -> 2
        (99.9996,   Some(6),    Some(2),    "100.00"),  // rounding -> one more digit
        (99.9996,   Some(5),    Some(2),    "100.0"),   // len > 5 => precision -> 1
        (999.9,     Some(3),    Some(0),    "1e3"),     // "1000".len > 3 => sci
        (999.9,     Some(3),    Some(1),    "1e3"),     // "1000".len > 3 => sci
        (999.9,     Some(4),    Some(1),    "1000"),    // precision -> 0, one more digit because prec had to be adjusted
        (0.000526,  Some(6),    Some(4),    "5.2e-4"),  // "0.0005".len > 6 => sci, with one more digit
    ];
    let mut error = false;
    for (value, width, precision, exp) in values {
        let res = dtoa_width(value, width, precision);
        if exp != res {
            error = true;
            println!("{exp} -> {res} ## ERROR");
        }
    }
    assert!(!error);
}

#[test]
fn test_width() {
    let values = vec![
        (0.000526,  Some(5),    Some(5),   false, 1,  "5.2e-4"),  // "0.0005".len > 6 => sci, with one more digit
        /*
        (1.0,       Some(10),   Some(4),   true,  4,  "1.0000"),  // d-d
        (1.5,       Some(10),   Some(4),   true,  4,  "1.5000"),  // d-d.d-d
        (100.0,     Some(10),   Some(2),   true,  2,  "100.00"),  // d-d(0-0)
        (30.125,    Some(10),   Some(4),   true,  4,  "30.1250"), // d-d.d-d(0-0)
        (0.5,       Some(10),   Some(2),   true,  2,  "0.50"),    // 0.d-d(0-0)
        (0.05,      Some(10),   Some(4),   true,  4,  "0.0500"),  // 0.(0-0)d-d
        (10.125,    Some(10),   Some(2),   true,  2,  "10.12"),   // rounding
        (20.375,    Some(10),   Some(2),   true,  2,  "20.38"),   // rounding
        */
        (99.9535,   Some(5),    Some(3),   true,  2,  "99.96"),   // len > 5 => precision -> 2
        (99.9953,   Some(5),    Some(3),   true,  1,  "100.0"),   // rounding => prec -> 2 => one more digit => prec -> 1
        (99.9996,   Some(6),    Some(2),   true,  2,  "100.00"),  // rounding -> one more digit
        (99.9996,   Some(5),    Some(2),   true,  1,  "100.0"),   // len > 5 => precision -> 1
        (999.9,     Some(3),    Some(0),   false, 0,  "1e3"),     // "1000".len > 3 => sci
        (999.9,     Some(4),    Some(1),   true,  0,  "1000"),    // precision -> 0, one more digit because prec had to be adjusted
        (0.000526,  Some(5),    Some(5),   false, 1,  "5.2e-4"),  // "0.0005".len > 6 => sci, with one more digit
    ];
    let mut error = false;
    for (idx, (value, width, precision, exp_fixed, exp_prec, _)) in values.into_iter().enumerate() {
        let (fixed, prec) = check_width(value, width, precision);
        if exp_fixed != fixed || (fixed && exp_prec != prec) {
            error = true;
            println!("test #{idx}: expecting {exp_fixed}, {exp_prec}, but got {fixed}, {prec}");
        } else {
            println!("test #{idx} OK");
        }
    }
    assert!(!error);
}
