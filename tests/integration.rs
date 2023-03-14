// Copyright 2022 Redglyph
//
// Integration tests: tests that all the functionalities are accessible and work as expected.

#![cfg(test)]

use schubfach::*;
use schubfach::test_values::StdFixValues;

#[test]
fn format_options() {
    let options = FmtOptions {
        width: None,
        precision: None,
        mode: FmtMode::Std,
        ..FmtOptions::default()
    };
    assert_eq!(1.0.format_opt(&options), "1.0");
}

#[test]
fn display_f64() {
    let limit = StdFixValues::new();

    let val1: f64 = 0.5;
    let val2: f64 = 1.5;
    let val3 = limit.min_fix;
    let val4 = limit.low_fix;
    let str3_fix = limit.min_fix_str;
    let str4_fix = limit.low_fix_str;
    let str4_sci = limit.low_sci_str;
    assert_eq!(format!("{}",    val1.to_std()), "0.5",       "test with std, '{{}}'");
    assert_eq!(format!("{:+}",  val1.to_std()), "+0.5",      "test with std, '{{:+}}'");
    assert_eq!(format!("{:5}",  val1.to_std()), "  0.5",     "test with std, '{{:5}}'");
    assert_eq!(format!("{:>5}", val1.to_std()), "  0.5",     "test with std, '{{:>5}}'");
    assert_eq!(format!("{:<5}", val1.to_std()), "0.5  ",     "test with std, '{{:<5}}'");
    assert_eq!(format!("{:^5}", val1.to_std()), " 0.5 ",     "test with std, '{{:^5}}'");
    assert_eq!(format!("{:.5}", val1.to_std()), "0.50000",   "test with std, '{{:.5}}'");
    assert_eq!(format!("{:.0}", val1.to_std()), "0",         "test with std, '{{:.0}}'");
    assert_eq!(format!("{:.0}", val2.to_std()), "2",         "test with std, '{{:.0}}'");
    assert_eq!(format!("{}",    val3.to_std()), str3_fix,    "test with std on val3");
    assert_eq!(format!("{}",    val4.to_std()), str4_sci,    "test with std on val4");

    assert_eq!(format!("{}",    val1.to_fix()), "0.5",       "test with fix, '{{}}'");
    assert_eq!(format!("{:+}",  val1.to_fix()), "+0.5",      "test with fix, '{{:+}}'");
    assert_eq!(format!("{:5}",  val1.to_fix()), "  0.5",     "test with fix, '{{:5}}'");
    assert_eq!(format!("{:>5}", val1.to_fix()), "  0.5",     "test with fix, '{{:>5}}'");
    assert_eq!(format!("{:<5}", val1.to_fix()), "0.5  ",     "test with fix, '{{:<5}}'");
    assert_eq!(format!("{:^5}", val1.to_fix()), " 0.5 ",     "test with fix, '{{:^5}}'");
    assert_eq!(format!("{:.5}", val1.to_fix()), "0.50000",   "test with fix, '{{:.5}}'");
    assert_eq!(format!("{:.0}", val1.to_fix()), "0",         "test with fix, '{{:.0}}'");
    assert_eq!(format!("{:.0}", val2.to_fix()), "2",         "test with fix, '{{:.0}}'");
    assert_eq!(format!("{}",    val3.to_fix()), str3_fix,    "test with fix on val3");
    assert_eq!(format!("{}",    val4.to_fix()), str4_fix,    "test with fix on val4");

    let val5: f64 = 1500.0;
    let val6: f64 = -0.03125;
    assert_eq!(format!("{}", val5.to_sci()), "1.5e3", "test with sci, '{{}}'");
    assert_eq!(format!("{}", val6.to_sci()), "-3.125e-2", "test with sci, '{{}}'");
}

#[test]
fn buffer_f64() {
    let values = [
        (0.5,       "0.5"),
        (1.5,       "1.5"),
        (1500.0,    "1500.0"),
        (-0.03125,  "-0.03125"),
    ];
    let mut buffer = NumFmtBuffer::new();
    for (value, exp_string) in values {
        let string: &str = buffer.to_str(value);
        assert_eq!(string, exp_string);
    }
}
