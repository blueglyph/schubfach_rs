// Copyright 2022 Redglyph
//
// Rounding tests

#![cfg(test)]

use std::str::FromStr;
use schubfach::*;

#[test]
fn format_rounding() {
    find_issues(7, false, true, false, &Policy::ToEven);
}

/// Iterates through floating-point values and compares Display::fmt implementation for f64
/// and simple string-based rounding to detect discrepancies.
///
/// * `depth`: maximum number of fractional digits to test
/// * `verbose`: displays all values
/// * `negative`: tests negative values instead of positive ones
///
/// Note: we could also check [Round::round_digit] for comparison but it's not correct all
/// the time anyway.
fn find_issues(depth: usize, verbose: bool, show_error: bool, negative: bool, policy: &Policy) {
    let it = RoundTestIter::new(depth, negative);
    let mut nbr_test = 0;
    let mut nbr_error = 0;
    if verbose {
        println!("'original value' :'precision': 'Display-rounded' <> 'expected'")
    }
    for (sval, pr) in it {
        let val = f64::from_str(&sval).expect(&format!("error converting {} to f64", sval));
        // let display_val = format!("{val:.pr$}");
        let display_val = format(val, None, Some(pr as u32), FmtMode::Fix);
        let sround_val = str_sround(&sval, pr, policy);
        let comp = if display_val == sround_val {
            "=="
        } else {
            nbr_error += 1;
            "<>"
        };
        nbr_test += 1;
        if verbose || show_error && display_val != sround_val {
            println!("{sval:<8}:{pr}: {display_val} {comp} {sround_val}");
        }
    }
    println!("\n=> {nbr_error} / {nbr_test} error(s) for depth 0-{depth}");
}

//==============================================================================
// Iteration through floating-point values (string representation)
//------------------------------------------------------------------------------

const INIT_STEP: u8 = b'a';
const LAST_STEP: u8 = b'9';

const INIT_DIGIT: u8 = b'4';    // to test 0.*4 .. values
// const INIT_DIGIT: u8 = b'5';    // to test 0.*5 .. values
// const STOP_DIGIT: u8 = b'5';    // to test .. 0.*5 values
const STOP_DIGIT: u8 = b'6';    // to test .. 0.*6 values

struct RoundTestIter {
    base: Vec<u8>,
    precision: usize,
    max: usize
}

impl RoundTestIter {
    pub fn new(max: usize, negative: bool) -> RoundTestIter {
        RoundTestIter {
            base: if negative { b"-0.a".to_vec() } else { b"0.a".to_vec() },
            precision: 1,
            max,
        }
    }
}

/// step[pr]:
/// 'a' : checks base + 4*10^-pr, then jumps to 'b'
/// 'b' : checks base + 5*10^-pr, then tries pr+1, otherwise increases base digits and jumps to 'a'
/// '0'-'9': base digits
impl Iterator for RoundTestIter {
    type Item = (String, usize);

    fn next(&mut self) -> Option<Self::Item> {
        match self.base.pop() {
            Some(step) if step >= b'a' => {
                let mut value = self.base.clone();
                value.push(step as u8 - INIT_STEP + INIT_DIGIT);
                // 'value' only contains ASCII characters:
                let result = Some((unsafe { String::from_utf8_unchecked(value) }, self.precision - 1));
                if step as u8 - INIT_STEP + INIT_DIGIT == STOP_DIGIT {
                    if self.precision < self.max {
                        self.base.push(b'0');
                        self.base.push(INIT_STEP);
                        self.precision += 1;
                    } else {
                        self.precision -= 1;
                        loop {
                            match self.base.pop() {
                                Some(digit) if digit == LAST_STEP => {
                                    self.precision -= 1;
                                }
                                Some(digit) if digit != b'.' => {
                                    self.base.push(1 + digit as u8);
                                    self.base.push(INIT_STEP);
                                    self.precision += 1;
                                    break;
                                }
                                _ => break
                            }
                        }
                    }
                } else {
                    self.base.push(step + 1);
                }
                result
            }
            _ => None
        }
    }
}

//==============================================================================
// String-based rounding (for comparison)
//------------------------------------------------------------------------------

#[derive(Debug, PartialEq)]
pub enum Policy {
    ToEven,
    AwayFromZero
}

/// Rounds the fractional part of `n` to `pr` digits, using `str_sround()` to perform
/// a rounding to the nearest (on the absolute value). The rounding is made by processing the
/// string, using the "away from zero" method.
///
/// * `n`: string representation of the floating-point value to round, it must contain more than
/// `pr` digits in the fractional part.
/// * `pr`: number of digits to keep in the fractional part
///
/// ```
/// assert_eq!(str_sround("2.95", 1, Policy::ToEven), "3.0");
/// assert_eq!(str_sround("-2.95", 1, Policy::ToEven), "-3.0");
/// ```
pub fn str_sround(n: &str, pr: usize, policy: &Policy) -> String {
    let mut s = n.to_string().into_bytes();
    match s.iter().position(|&x| x == b'.') {
        None => {
            s.push(b'.');
            for _ in 0..pr {
                s.push(b'0');
            }
            unsafe { String::from_utf8_unchecked(s) }
        }
        Some(mut pos) => {
            let prec = s.len() - pos - 1;
            if prec < pr {
                for _ in prec..pr {
                    s.push(b'0')
                }
            } else if prec > pr {
                let ch = *s.iter().nth(pos + pr + 1).unwrap();
                s.truncate(pos + pr + 1);
                if ch >= b'5' {
                    // increment s
                    let mut frac = 0;
                    let mut int = 0;
                    let mut is_frac = true;
                    loop {
                        match s.pop() {
                            Some(b'9') if is_frac => {
                                frac += 1;
                            }
                            Some(b'.') => is_frac = false,
                            Some(b'9') if !is_frac => {
                                int += 1;
                            }
                            Some(b'-') => {
                                s.push(b'-');
                                s.push(b'1');
                                break;
                            }
                            Some(ch2) => {
                                match policy {
                                    Policy::ToEven => {
                                        if ch > b'5' || ch2 & 1 != 0 || frac != 0 || int != 0 {
                                            s.push(ch2 + 1)
                                        } else {
                                            s.push(ch2)
                                        }
                                    }
                                    Policy::AwayFromZero => s.push(ch2 + 1),
                                }
                                break;
                            }
                            None => {
                                s.push(b'1');
                                break;
                            },
                        }
                    }
                    if !is_frac {
                        for _ in 0..int {
                            s.push(b'0');
                        }
                        pos += int;
                        s.push(b'.');
                    }
                    for _ in 0..frac {
                        s.push(b'0');
                    }
                }
            }
            // removes '.' if no digit after:
            if s.len() == pos + 1 {
                s.pop();
            }
            // 's' only contains ASCII characters:
            unsafe { String::from_utf8_unchecked(s) }
        }
    }
}
