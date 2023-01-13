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
        mode: FmtMode::Fix,
        ..FmtOptions::default()
    };
    assert_eq!(1.0.format_opt(&options), "1.0");
}

#[test]
fn display_f64() {
    let val1: f64 = 0.5;
    let val2: f64 = 1.5;
    assert_eq!(format!("{}",    val1.to_fix()), "0.5",       "test with fix, '{{}}'");
    assert_eq!(format!("{:+}",  val1.to_fix()), "+0.5",      "test with fix, '{{:+}}'");
    assert_eq!(format!("{:5}",  val1.to_fix()), "  0.5",     "test with fix, '{{:5}}'");
    assert_eq!(format!("{:>5}", val1.to_fix()), "  0.5",     "test with fix, '{{:>5}}'");
    assert_eq!(format!("{:<5}", val1.to_fix()), "0.5  ",     "test with fix, '{{:<5}}'");
    assert_eq!(format!("{:^5}", val1.to_fix()), " 0.5 ",     "test with fix, '{{:^5}}'");
    assert_eq!(format!("{:.5}", val1.to_fix()), "0.50000",   "test with fix, '{{:.5}}'");
    assert_eq!(format!("{:.0}", val1.to_fix()), "0",         "test with fix, '{{:.0}}'");
    assert_eq!(format!("{:.0}", val2.to_fix()), "2",         "test with fix, '{{:.0}}'");

    let val3: f64 = 1500.0;
    let val4: f64 = -0.03125;
    assert_eq!(format!("{}",    val3.to_sci()), "1.5e3",     "test with sci, '{{}}'");
    assert_eq!(format!("{}",    val4.to_sci()), "-3.125e-2", "test with sci, '{{}}'");
}
