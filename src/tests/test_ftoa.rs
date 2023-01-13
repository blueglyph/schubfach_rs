// Copyright 2022 Redglyph

use std::cmp::min;
use std::mem;
use std::str::FromStr;
use std::time::Instant;
use num::ToPrimitive;
use crate::FormatInterface;

#[test]
fn limits_ftoa() {
    let tests: &[(f64, &str)] = &[
        // those tests depend on the value of FPFormatter::MIN_FIXED_DECIMAL_POINT
        (0.0000002, "0.0000002"),
        (0.00000002, "2e-8"),
        // those tests depend on the value of FPFormatter::MAX_FIXED_DECIMAL_POINT
        (18014398509481984000000.0, "18014398509481984000000"), // = (1 << 54) * 1E6
        (180143985094819840000000.0, "1.8014398509481984e23"),  // = (1 << 54) * 1E7
    ];
    for (idx, (value, exp)) in tests.into_iter().enumerate() {
        let res = value.ftoa();
        assert_eq!(res, *exp, "failed in test #{idx}");
    }
}

/// Timing test, launch with
///
/// ```cargo test -r timing_random_ftoa -- --ignored --test-threads=1 --show-output```
#[test]
#[ignore]
fn timing_random_ftoa() {
    // we cannot simply compare all values to Grisu3/Dragon4 because some roundings will be different,
    // here we check that the parsed string yields the same original value:
    let mut rng = oorandom::Rand64::new(0);
    let timer = Instant::now();
    for i in 0..10_000_000 {
        let mut f;
        loop {
            let ieee = rng.rand_u64();
            f = unsafe { mem::transmute::<u64, f64>(ieee) };
            if f.is_normal() {
                break;
            }
        }
        let res = f.ftoa();
        let f2 = f64::from_str(&res).expect(&format!("test #{i}: could not convert {f} -> '{res}' -> f64"));
        assert_eq!(f, f2);
    }
    let elapsed = timer.elapsed();
    println!("elapsed time: {:.3} s", elapsed.as_secs_f64());
}

/// Timing test, launch with
///
/// ```cargo test -r timing_digits_ftoa -- --ignored --test-threads=1 --show-output```
#[test]
#[ignore]
fn timing_digits_ftoa() {
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
            let res = value.ftoa();
            let exp = value.to_string();
            assert_eq!(res, exp, "incorrect string");
        }
        low = high;
        high = if digit < 16 { high * 10.0 } else { MAX_VALUE };
    }
    let elapsed = timer.elapsed();
    println!("elapsed time: {:.3} s", elapsed.as_secs_f64());
}
