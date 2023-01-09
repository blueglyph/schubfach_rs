// Copyright 2022 Redglyph

use crate::*;
use crate::FmtMode::{Fix, Sci};
use crate::NumFmtBuffer;

fn test_format_opt(values: Vec<(f64, Option<u32>, Option<u32>, FmtMode, bool, &str)>) {
    let mut error = false;
    for (idx, (value, width, precision, mode, trailing_dot_zero, exp_string)) in values.into_iter().enumerate() {
        let options = FmtOptions {
            width,
            precision,
            trailing_dot_zero,
            mode,
            ..FmtOptions::default()
        };
        let string = format_opt(value, &options);
        if string != exp_string {
            error = true;
            println!("test #{idx}: expecting '{exp_string}' but got '{string}'");
        } else {
            // println!("test #{idx} OK: '{string}'");
        }
    }
    assert!(!error);
}

#[test]
fn fixed() {
    let values = vec![
        // 1) d-d[.0] or d-d(0-0)[.0]: trailing / scientific
        // value        width       prec        mode    trail   expected
        (1.0,           None,       None,       Fix,    true,   "1.0"),
        (1.0,           None,       None,       Fix,    false,  "1"),
        (10.0,          None,       None,       Fix,    true,   "10.0"),
        (10.0,          None,       None,       Fix,    false,  "10"),
        (1.0,           Some(10),   Some(2),    Fix,    false,  "1.00"),
        (10.0,          Some(10),   Some(2),    Fix,    false,  "10.00"),
        (2.0,           None,       Some(0),    Fix,    false,  "2"),
        (2.0,           None,       Some(0),    Fix,    true,   "2"),
        // - adjust precision
        (100000.0,      Some(5),    None,       Fix,    false,  "1e5"),
        (100000.0,      Some(5),    None,       Fix,    true,   "1.0e5"),
        (1200.0,        Some(4),    Some(2),    Fix,    false,  "1200"),
        (1234.0,        Some(4),    Some(2),    Fix,    false,  "1234"),
        (1200.0,        Some(3),    Some(2),    Fix,    false,  "1e3"),
        (1234.0,        Some(3),    Some(2),    Fix,    false,  "1e3"),
        (1500.0,        Some(3),    Some(2),    Fix,    false,  "2e3"),
        (2500.0,        Some(3),    Some(2),    Fix,    false,  "2e3"),
        (120000.0,      Some(5),    Some(2),    Fix,    false,  "1.2e5"),
        (125000.0,      Some(5),    Some(2),    Fix,    false,  "1.2e5"),
        (115000.0,      Some(5),    Some(2),    Fix,    false,  "1.2e5"),
        (120000.0,      Some(4),    None,       Fix,    false,  "1e5"),
        (150000.0,      Some(4),    None,       Fix,    false,  "2e5"),
        (120000.0,      Some(5),    None,       Fix,    false,  "1.2e5"),
        (1150000000.0,  Some(5),    Some(1),    Fix,    false,  "1.2e9"),
        (9950000000.0,  Some(5),    Some(1),    Fix,    false,  "1e10"),

        // 2) d-d.d-d(0-0)
        // value        width       prec        mode    trail   expected
        (10.25,         Some(10),   Some(2),    Fix,    false,  "10.25"),
        (10.95,         Some(10),   None,       Fix,    false,  "10.95"),
        (10.95,         Some(4),    None,       Fix,    false,  "11.0"),
        (10.95,         Some(4),    Some(3),    Fix,    false,  "11.0"),
        (10.95,         Some(4),    Some(0),    Fix,    false,  "11"),
        (9.95,          Some(3),    Some(3),    Fix,    false,  "10"),
        (9.95,          Some(4),    Some(1),    Fix,    false,  "10.0"),
        (2222.25,       Some(3),    None,       Fix,    false,  "2e3"),
        (9999.95,       Some(3),    None,       Fix,    false,  "1e4"),
        (9999.95,       Some(3),    Some(1),    Fix,    false,  "1e4"),
        (1.5,           None,       Some(4),    Fix,    true,   "1.5000"),
        (1.5,           Some(10),   Some(4),    Fix,    true,   "1.5000"),
        (1.5,           Some(4),    Some(4),    Fix,    true,   "1.50"),
        (1.5,           None,       Some(0),    Fix,    false,  "2"),
        (1.5,           None,       Some(0),    Fix,    true,   "2"),
        (1.5,           None,       None,       Fix,    true,   "1.5"),
        (99999.95,      Some(5),    Some(1),    Fix,    false,  "1.0e5"),
        (12000.0,       None,       Some(1),    Fix,    true,   "12000.0"),
        (12000.0,       None,       None,       Fix,    true,   "12000.0"),
        (12000.0,       None,       None,       Fix,    false,  "12000"),
        (12000.0,       None,       Some(4),    Fix,    true,   "12000.0000"),
        (1.0,           None,       Some(4),    Fix,    true,   "1.0000"),
        (1.0,           None,       Some(0),    Fix,    true,   "1"),
        (12000.0,       Some(10),   Some(1),    Fix,    true,   "12000.0"),
        (12000.0,       Some(10),   None,       Fix,    true,   "12000.0"),
        (12000.0,       Some(10),   None,       Fix,    false,  "12000"),
        (12000.0,       Some(10),   Some(4),    Fix,    true,   "12000.0000"),
        (1.0,           Some(10),   Some(4),    Fix,    true,   "1.0000"),
        (1.0,           Some(10),   Some(0),    Fix,    true,   "1"),
        (12000.0,       Some(8),    Some(4),    Fix,    true,   "12000.00"),
        (1.0,           Some(4),    Some(4),    Fix,    true,   "1.00"),

        // 3) 0.d-d or 0.(0-0)d-d
        // value        width       prec        mode    trail   expected
        (0.5,           None,       Some(0),    Fix,    false,  "0"),
        (0.5,           None,       Some(0),    Fix,    true,   "0"),
        (0.5,           None,       None,       Fix,    false,  "0.5"),
        (0.1234,        None,       None,       Fix,    true,   "0.1234"),
        (0.1234,        Some(10),   None,       Fix,    true,   "0.1234"),
        (0.0123,        Some(4),    None,       Fix,    true,   "0.01"),
        (0.0995,        Some(5),    None,       Fix,    true,   "0.100"),
        (0.9995,        Some(5),    None,       Fix,    true,   "1.000"),
        (0.0001,        Some(4),    None,       Fix,    true,   "1e-4"),
        (0.1234,        Some(8),    Some(2),    Fix,    true,   "0.12"),
        (0.00001234,    Some(6),    Some(2),    Fix,    true,   "1.2e-5"),
        (0.0000995,     Some(6),    Some(2),    Fix,    true,   "1.0e-4"),
        (0.0005,        None,       Some(4),    Fix,    true,   "0.0005"),
        (0.0005,        None,       Some(6),    Fix,    true,   "0.000500"),

        // 4) d-d.d-d(0-0) or 0.d-d or 0.(0-0)d-d: rounding
        // value        width       prec        mode    trail   expected
        (0.099,         Some(4),    Some(2),    Fix,    false,  "0.10"),
        (0.00099,       Some(6),    Some(4),    Fix,    false,  "0.0010"),
        (99.999,        Some(6),    Some(2),    Fix,    false,  "100.00"),
        (99.999,        None,       Some(2),    Fix,    false,  "100.00"),
        (99.995,        None,       Some(2),    Fix,    false,  "100.00"),
        (99.989,        None,       Some(2),    Fix,    false,  "99.99"),
    ];
    test_format_opt(values);
}

#[test]
fn sci() {
    let values = vec![
        // value        width       prec        mode    trail   expected
        (1.0,           None,       None,       Sci,    false,  "1e0"),
        (-1.0,          None,       None,       Sci,    false,  "-1e0"),
        (1.0,           None,       None,       Sci,    true,   "1.0e0"),
        (1.0,           None,       Some(2),    Sci,    true,   "1.00e0"),
        (10.0,          None,       None,       Sci,    false,  "1e1"),
        (10.0,          None,       None,       Sci,    true,   "1.0e1"),
        (10.0,          None,       Some(2),    Sci,    true,   "1.00e1"),
        // exponents
        (1.0e5,         None,       None,       Sci,    false,  "1e5"),
        (1.0e10,        None,       None,       Sci,    false,  "1e10"),
        (1.0e15,        None,       None,       Sci,    false,  "1e15"),
        (1.0e100,       None,       None,       Sci,    false,  "1e100"),
        (1.0e150,       None,       None,       Sci,    false,  "1e150"),
        (1.0e125,       None,       None,       Sci,    false,  "1e125"),
        (1.0e-5,        None,       None,       Sci,    false,  "1e-5"),
        (1.0e-10,       None,       None,       Sci,    false,  "1e-10"),
        (1.0e-15,       None,       None,       Sci,    false,  "1e-15"),
        (1.0e-100,      None,       None,       Sci,    false,  "1e-100"),
        (1.0e-150,      None,       None,       Sci,    false,  "1e-150"),
        (1.0e-125,      None,       None,       Sci,    false,  "1e-125"),
        (9.995e-10,     Some(7),    Some(3),    Sci,    false,  "1.00e-9"),
        (9.295e-10,     Some(7),    Some(3),    Sci,    false,  "9.3e-10"),
        (9.295e-9,      Some(7),    Some(3),    Sci,    false,  "9.30e-9"),
        (9.295e-9,      Some(9),    Some(3),    Sci,    false,  "9.295e-9"),
        // width and exponent carry
        (9.999e9,       Some(4),    None,       Sci,    false,   "1e10"),
        (9.999e99,      Some(5),    None,       Sci,    false,   "1e100"),
        (9.999e9,       Some(5),    None,       Sci,    true,    "1e10"),
        (9.999e99,      Some(6),    None,       Sci,    true,    "1e100"),
        (9.999e9,       Some(6),    None,       Sci,    true,    "1.0e10"),
        (9.999e99,      Some(7),    None,       Sci,    true,    "1.0e100"),
        (-9.999e9,      Some(5),    None,       Sci,    true,    "-1e10"),
        (-9.999e99,     Some(6),    None,       Sci,    true,    "-1e100"),
        (-9.999e9,      Some(6),    None,       Sci,    true,    "-1e10"),
        (-9.999e99,     Some(7),    None,       Sci,    true,    "-1e100"),
    ];
    test_format_opt(values);
}

#[test]
fn special() {
    let values = vec![
        // 1) special values
        // value            width       prec        mode    trail   expected
        (f64::NAN,          None,       None,       Fix,    false,  "NaN"),
        (f64::NEG_INFINITY, None,       None,       Fix,    false,  "-inf"),
        (f64::INFINITY,     None,       None,       Fix,    false,  "inf"),
        (-0.0,              None,       None,       Fix,    true,   "0.0"),
        (0.0,               None,       None,       Fix,    false,  "0"),
        (0.0,               None,       None,       Fix,    true,   "0.0"),
        (f64::EPSILON,      None,       None,       Sci,    true,   "2.220446049250313e-16"),
        (f64::MIN,          None,       None,       Sci,    true,   "-1.7976931348623157e308"),
        (f64::MIN_POSITIVE, None,       None,       Sci,    true,   "2.2250738585072014e-308"),
        (f64::MAX,          None,       None,       Sci,    true,   "1.7976931348623157e308"),
        (1.0e-307,          None,       None,       Sci,    true,   "1.0e-307"),
        (1.0e308,           None,       None,       Sci,    true,   "1.0e308"),

        // 2) abuse
        // value        width       prec        mode    trail   expected
        (1234.1234,     Some(0),    None,       Fix,    true,   "1e3"),
        (1234.1234,     Some(0),    Some(4),    Fix,    true,   "1e3"),
        (999.999,       Some(0),    Some(5),    Fix,    true,   "1e3"),
    ];
    test_format_opt(values);
}

#[test]
fn digits() {
    let values = vec![
        // value                width       prec        mode    trail   expected
        (1.0,                   None,       None,       Fix,    false,  "1"),
        (12.0,                  None,       None,       Fix,    false,  "12"),
        (123.0,                 None,       None,       Fix,    false,  "123"),
        (1234.0,                None,       None,       Fix,    false,  "1234"),
        (12345.0,               None,       None,       Fix,    false,  "12345"),
        (123456.0,              None,       None,       Fix,    false,  "123456"),
        (1234567.0,             None,       None,       Fix,    false,  "1234567"),
        (12345678.0,            None,       None,       Fix,    false,  "12345678"),
        (123456789.0,           None,       None,       Fix,    false,  "123456789"),
        (1234567890.0,          None,       None,       Fix,    false,  "1234567890"),
        (12345678901.0,         None,       None,       Fix,    false,  "12345678901"),
        (123456789012.0,        None,       None,       Fix,    false,  "123456789012"),
        (1234567890123.0,       None,       None,       Fix,    false,  "1234567890123"),
        (12345678901234.0,      None,       None,       Fix,    false,  "12345678901234"),
        (123456789012345.0,     None,       None,       Fix,    false,  "123456789012345"),
        (1234567890123456.0,    None,       None,       Fix,    false,  "1234567890123456"),
        (12345678901234568.0,   None,       None,       Fix,    false,  "12345678901234568"),
        (10.0,                  None,       None,       Fix,    false,  "10"),
        (100.0,                 None,       None,       Fix,    false,  "100"),
        (1000.0,                None,       None,       Fix,    false,  "1000"),
        (10000.0,               None,       None,       Fix,    false,  "10000"),
        (100000.0,              None,       None,       Fix,    false,  "100000"),
        (1000000.0,             None,       None,       Fix,    false,  "1000000"),
        (10000000.0,            None,       None,       Fix,    false,  "10000000"),
        (100000000.0,           None,       None,       Fix,    false,  "100000000"),
        (1000000000.0,          None,       None,       Fix,    false,  "1000000000"),
        (10000000000.0,         None,       None,       Fix,    false,  "10000000000"),
        (100000000000.0,        None,       None,       Fix,    false,  "100000000000"),
        (1000000000000.0,       None,       None,       Fix,    false,  "1000000000000"),
        (10000000000000.0,      None,       None,       Fix,    false,  "10000000000000"),
        (100000000000000.0,     None,       None,       Fix,    false,  "100000000000000"),
        (1000000000000000.0,    None,       None,       Fix,    false,  "1000000000000000"),
        (1000000010000.0,       None,       None,       Fix,    false,  "1000000010000"),
        //
        (1e1,                   None,       None,       Sci,    false,  "1e1"),
        (1e2,                   None,       None,       Sci,    false,  "1e2"),
        (1e4,                   None,       None,       Sci,    false,  "1e4"),
        (1e8,                   None,       None,       Sci,    false,  "1e8"),
        (1e9,                   None,       None,       Sci,    false,  "1e9"),
        (1e10,                  None,       None,       Sci,    false,  "1e10"),
        (1e11,                  None,       None,       Sci,    false,  "1e11"),
        (1e100,                 None,       None,       Sci,    false,  "1e100"),
        (1e110,                 None,       None,       Sci,    false,  "1e110"),
        (1e101,                 None,       None,       Sci,    false,  "1e101"),
    ];
    test_format_opt(values);
}

#[test]
fn rounding_even() {
    let values = vec![
        // value                width       prec        mode    trail   expected
        (0.4,                   None,       Some(0),    Fix,    false,  "0"),
        (0.5,                   None,       Some(0),    Fix,    false,  "0"),
        (1.4,                   None,       Some(0),    Fix,    false,  "1"),
        (1.5,                   None,       Some(0),    Fix,    false,  "2"),
        (2.4,                   None,       Some(0),    Fix,    false,  "2"),
        (2.5,                   None,       Some(0),    Fix,    false,  "2"),

        (0.4,                   None,       None,       Fix,    false,  "0.4"),
        (0.5,                   None,       None,       Fix,    false,  "0.5"),
        (1.4,                   None,       None,       Fix,    false,  "1.4"),
        (1.5,                   None,       None,       Fix,    false,  "1.5"),
        (2.4,                   None,       None,       Fix,    false,  "2.4"),
        (2.5,                   None,       None,       Fix,    false,  "2.5"),
    ];
    test_format_opt(values);
}

#[test]
fn round() {
    // round(start_ptr: *mut u8, removed_digit_ptr: *mut u8, potential_tie: bool, can_eat_left: bool)
    let values = vec![
        // buf          start   prev    can_eat result      left    right
        ("#04#",        1,      2,      false,  "#04#",     false,  false),     // tie to even, down
        ("#4#",         1,      1,      true,   "04#",      true,   false),     // tie to even, down
        ("#5#",         1,      1,      true,   "05#",      true,   false),     // tie to even, down
        ("#6#",         1,      1,      true,   "16#",      true,   false),     // tie to even, down
        ("#05#",        1,      2,      false,  "#05#",     false,  false),     // tie to even, down
        ("#15#",        1,      2,      false,  "#25#",     false,  false),     // tie to even, up
        ("#25#",        1,      2,      false,  "#25#",     false,  false),     // tie to even, down
        ("#35#",        1,      2,      false,  "#45#",     false,  false),     // tie to even, up
        ("#45#",        1,      2,      false,  "#45#",     false,  false),     // tie to even, down
        ("#55#",        1,      2,      false,  "#65#",     false,  false),     // tie to even, up
        ("#65#",        1,      2,      false,  "#65#",     false,  false),     // tie to even, down
        ("#75#",        1,      2,      false,  "#85#",     false,  false),     // tie to even, up
        ("#85#",        1,      2,      false,  "#85#",     false,  false),     // tie to even, down
        ("#95#",        1,      2,      false,  "#10#",     false,  true),      // tie to even, up
        ("#149#",       1,      2,      false,  "#149#",    false,  false),     // down
        ("#151#",       1,      2,      false,  "#251#",    false,  false),     // up
        ("#251#",       1,      2,      false,  "#351#",    false,  false),     // up
        ("#95#",        1,      2,      false,  "#10#",     false,  true),      // carry & eat right
        ("##95#",       2,      3,      true,   "#105#",    true,   false),     // carry & eat left
        ("##9999#",     2,      5,      true,   "#10009#",  true,   false),
        ("##9989#",     2,      5,      true,   "##9999#",  false,  false),
        ("##9899#",     2,      5,      true,   "##9909#",  false,  false),
        ("##8999#",     2,      5,      true,   "##9009#",  false,  false),
    ];
    for (idx, (buffer, start, prev, can_eat_left, exp_buffer, exp_left, exp_right)) in values.into_iter().enumerate() {
        unsafe {
            let mut buf = buffer.as_bytes().to_owned();
            let start_ptr = buf.as_mut_ptr().add(start);
            let prev_ptr  = buf.as_mut_ptr().add(prev);
            let potential_tie = *prev_ptr.add(1) == b'#';
            let (left, right) = NumFmtBuffer::round(start_ptr, prev_ptr, potential_tie, can_eat_left);
            let msg = format!("test #{idx}: ");
            let res_buf = String::from_utf8(buf).unwrap();
            assert_eq!(left, exp_left, "{}left", msg);
            assert_eq!(right, exp_right, "{}right", msg);
            assert_eq!(res_buf, exp_buffer, "{}buffer", msg);
        }
    }
}
