// Copyright 2022 Redglyph
//
// Integration tests: tests that all the functionalities are accessible and work as expected.

#![cfg(test)]

use schubfach::*;

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
    // if MIN_FIXED_DECIMAL_POINT = -3 => 0.000[d] is the limit => 1e-4 is the limit
    // for std as fixed-format
    let min = <NumFmtBuffer as NumFormat<f64, u64>>::MIN_FIXED_DECIMAL_POINT - 1;

    let val1: f64 = 0.5;
    let val2: f64 = 1.5;
    let val3: f64 = 10.0_f64.powi(min);
    let val4 = val3 / 10.0;
    let str3_fix = "0.".to_string() + &"0".repeat(min.abs() as usize - 1) + "1";
    let str4_fix = "0.".to_string() + &"0".repeat(min.abs() as usize) + "1";
    let str4_sci = format!("1.0e{}", min - 1);
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
