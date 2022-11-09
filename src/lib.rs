// Copyright 2022 Redglyph
//
// Implementation of the Schufbach algorithm for IEEE-754 double-precision floating-point values,
// as described in the following article:
//
//     Raffaello Giulietti, "The Schubfach way to render doubles", March 16, 2020,
//     https://drive.google.com/file/d/1luHhyQF9zKlM8yJ1nebU0OgVYhfC6CBN
//
// Translated from Alexander Bolz's C++ implementation, found at
//
//     https://github.com/abolz/Drachennest
//     (rev. e6714a39ad331b4489d0b6aaf3968635bff4eb5e, May 15, 2021)
//
// with the following licence:
//
//     Copyright 2020 Alexander Bolz
//
//     Distributed under the Boost Software License, Version 1.0.
//      (See accompanying file LICENSE_1_0.txt or copy at https://www.boost.org/LICENSE_1_0.txt)

#![allow(dead_code)]

mod tests;
mod maths;

extern crate core;

use std::{mem, ptr};
use std::cmp::{max, min};
use crate::maths::*;

// ---------------------------------------------------------------------------------------------
// IEEE-754 double precision:
//
// - bit 63: sign, 0 = positive, 1 = negative
// - bits 62-52: exponent (11 bits),
// - bits 51-00: fraction (52 bits) of 53-bit normalized significand (MSB "hidden" since always '1')
//
// finite value = -1 ^ sign * (1.fraction) * 2 ^ (e - 1023)

type BitsType = u64;

const MAX_DIGITS_10: i32 = 53;
const MAX_EXPONENT: i32 = 1024;

const SIGNIFICAND_SIZE: i32 = MAX_DIGITS_10;
const EXPONENT_BIAS: i32 = MAX_EXPONENT - 1 + (SIGNIFICAND_SIZE - 1);
const MAX_IEEE_EXPONENT: BitsType = (2 * MAX_EXPONENT - 1) as BitsType;
const HIDDEN_BIT: BitsType = (1 as BitsType) << (SIGNIFICAND_SIZE - 1);
const FRACTION_MASK: BitsType = HIDDEN_BIT - 1;
const EXPONENT_MASK: BitsType = MAX_IEEE_EXPONENT << (SIGNIFICAND_SIZE - 1);
const SIGN_MASK: BitsType = (1 as BitsType) << 63;

#[derive(PartialEq)]
enum Encoding {
    NaN,    // not a number
    Inf,    // +infinity or -infinity number
    Zero,   // zero finite number
    Digits  // non-zero finite number
}

#[derive(Debug)]
/// IEEE-754 double-precision floating-point value
struct Double {
    bits: BitsType
}

impl Double {
    /// Creates a new [Double] value from the IEEE-754 binary encoding
    fn new(bits: BitsType) -> Self {
        Double { bits }
    }

    /// Fraction component (significand without its hidden MSB)
    fn physical_fraction(&self) -> BitsType {
        self.bits & FRACTION_MASK
    }

    /// Exponent component
    fn physical_exponent(&self) -> BitsType {
        (self.bits & EXPONENT_MASK) >> (SIGNIFICAND_SIZE - 1)
    }

    /// Encoding class (zero, finite, inf or nan)
    fn encoding(&self) -> Encoding {
        if self.bits & !SIGN_MASK == 0 {
            Encoding::Zero
        } else if self.bits & EXPONENT_MASK != EXPONENT_MASK {
            Encoding::Digits
        } else if self.bits & FRACTION_MASK == 0 {
            Encoding::Inf
        } else {
            Encoding::NaN
        }
    }

    /// Whether the value is finite in the form `-1 ^ sign * (1.fraction) * 2 ^ (e - 1023)`
    fn is_finite(&self) -> bool {
        self.bits & EXPONENT_MASK != EXPONENT_MASK
    }

    /// Whether the value is positive / negative infinity
    fn is_inf(&self) -> bool {
        self.bits & EXPONENT_MASK == EXPONENT_MASK && self.bits & FRACTION_MASK == 0
    }

    /// Whether the value is not a number (neither finite or infinite)
    fn is_nan(&self) -> bool {
        self.bits & EXPONENT_MASK == EXPONENT_MASK && self.bits  & FRACTION_MASK != 0
    }

    /// Whether the value is null
    fn is_zero(&self) -> bool {
        self.bits & !SIGN_MASK == 0
    }

    /// Sign: 0 = positive, 1 = negative
    fn sign_bit(&self) -> usize {
        usize::from(self.bits & SIGN_MASK != 0)
    }
}

impl From<f64> for Double {
    fn from(f: f64) -> Self {
        let bits = f.to_bits();
        Double::new(bits)
    }
}

// ---------------------------------------------------------------------------------------------

/// Decimal exponent representation `digits` * 10^`exponent`
struct FloatingDecimal64 {
    digits: u64,    // num_digits <= 17
    exponent: i32,
    sign: usize
}

impl From<Double> for FloatingDecimal64 {
    /// Builds the decimal representation from extracted IEEE-754 fraction and exponent
    fn from(double: Double) -> Self {
        let ieee_fraction = double.physical_fraction();
        let ieee_exponent = double.physical_exponent();
        let sign = double.sign_bit();
        let c: u64;
        let q: i32;
        if ieee_exponent != 0 {
            c = HIDDEN_BIT | ieee_fraction;
            q = ieee_exponent as i32 - EXPONENT_BIAS;
            if 0 <= -q && -q < SIGNIFICAND_SIZE && multiple_of_pow2(c, -q) {
                return FloatingDecimal64 { digits: c >> -q, exponent: 0, sign };
            }
        } else {
            c = ieee_fraction;
            q = 1 - EXPONENT_BIAS;
        }

        let is_even: bool = c % 2 == 0;
        let accept_lower = is_even;
        let accept_upper = is_even;

        let lower_boundary_is_closer: bool = ieee_fraction == 0 && ieee_exponent > 1;

        let cbl: u64 = 4 * c - 2 + u64::from(lower_boundary_is_closer);
        let cb: u64  = 4 * c;
        let cbr: u64 = 4 * c + 2;

        // (q * 1262611         ) >> 22 == floor(log_10(    2^q))
        // (q * 1262611 - 524031) >> 22 == floor(log_10(3/4 2^q))
        debug_assert!(-1500 <= q && q <= 1500);
        let k: i32 = floor_div_pow2(q * 1262611 - if lower_boundary_is_closer { 524031 } else { 0 }, 22);
        let h: i32 = q + floor_log2_pow10(-k) + 1;
        debug_assert!(1 <= h && h <= 4);

        let pow10: U64x2 = compute_pow10_double(-k);
        let vbl: u64 = round_to_odd(pow10, cbl << h);
        let vb: u64  = round_to_odd(pow10, cb  << h);
        let vbr: u64 = round_to_odd(pow10, cbr << h);

        let lower: u64 = vbl + u64::from(!accept_lower);
        let upper: u64 = vbr - u64::from(!accept_upper);

        // See Figure 4 in [1].
        // And the modifications in Figure 6.

        let s: u64 = vb / 4; // NB: 4 * s == vb & ~3 == vb & -4

        if s >= 10 { // vb >= 40
            let sp: u64 = s / 10; // = vb / 40
            let up_inside: bool = lower <= 40 * sp;
            let wp_inside: bool =          40 * sp + 40 <= upper;
            if up_inside != wp_inside {
                return FloatingDecimal64 { digits: sp + u64::from(wp_inside), exponent: k + 1, sign };
            }
        }

        let u_inside: bool = lower <= 4 * s;
        let w_inside: bool =          4 * s + 4 <= upper;
        if u_inside != w_inside {
            return FloatingDecimal64 { digits: s + u64::from(w_inside), exponent: k, sign };
        }

        // NB: s & 1 == vb & 0x4
        let mid: u64 = 4 * s + 2; // = 2(s + t)
        let round_up: bool = vb > mid || (vb == mid && (s & 1) != 0);

        FloatingDecimal64 { digits: s + u64::from(round_up), exponent: k, sign }
    }
}

// ---------------------------------------------------------------------------------------------

/// Formatting options for [FPFormatter] methods
struct FmtOptions {
    /// maximum string length
    width: Option<u32>,
    /// number of fractional digits
    precision: Option<u32>,
    /// true: includes ".0" for integer values, false: only includes the integer part
    trailing_dot_zero: bool
}

impl Default for FmtOptions {
    fn default() -> Self {
        FmtOptions { width: None, precision: None, trailing_dot_zero: false }
    }
}

/// Floating-point formatter
struct FPFormatter {
    /// buffer holding the floating-point value decimal representation
    buffer: *mut u8,
    /// current pointer into the buffer
    ptr: *mut u8,
}

impl FPFormatter {
    const BUFFER_LEN: usize = 64;
    const MIN_FIXED_DECIMAL_POINT: i32 = -6; // 0.000000[digits] -> fixed, more zeros -> scientific
    const MAX_FIXED_DECIMAL_POINT: i32 = 17; // [17 digits].0    -> fixed, more digits -> scientific

    pub fn new() -> Self {
        let bytes = Vec::<u8>::with_capacity(Self::BUFFER_LEN);
        let mut bytes = mem::ManuallyDrop::new(bytes);
        let buffer = bytes.as_mut_ptr() as *mut u8;
        FPFormatter { buffer, ptr: buffer }
    }

    // -----------------------------------------------------------------------------------------

    /// Converts `value` into 2 decimal ASCII digits.
    ///
    /// Parameters:
    /// * `buf`: destination buffer
    /// * `offset`: destination offset using self.ptr
    /// * `value`: integer, 0 <= value <= 99
    fn write_2digits(&mut self, offset: usize, value: u32) {
        const DIGITS100: &[u8; 200] = &[
            b'0', b'0', b'0', b'1', b'0', b'2', b'0', b'3', b'0', b'4', b'0', b'5', b'0', b'6', b'0', b'7', b'0', b'8', b'0', b'9',
            b'1', b'0', b'1', b'1', b'1', b'2', b'1', b'3', b'1', b'4', b'1', b'5', b'1', b'6', b'1', b'7', b'1', b'8', b'1', b'9',
            b'2', b'0', b'2', b'1', b'2', b'2', b'2', b'3', b'2', b'4', b'2', b'5', b'2', b'6', b'2', b'7', b'2', b'8', b'2', b'9',
            b'3', b'0', b'3', b'1', b'3', b'2', b'3', b'3', b'3', b'4', b'3', b'5', b'3', b'6', b'3', b'7', b'3', b'8', b'3', b'9',
            b'4', b'0', b'4', b'1', b'4', b'2', b'4', b'3', b'4', b'4', b'4', b'5', b'4', b'6', b'4', b'7', b'4', b'8', b'4', b'9',
            b'5', b'0', b'5', b'1', b'5', b'2', b'5', b'3', b'5', b'4', b'5', b'5', b'5', b'6', b'5', b'7', b'5', b'8', b'5', b'9',
            b'6', b'0', b'6', b'1', b'6', b'2', b'6', b'3', b'6', b'4', b'6', b'5', b'6', b'6', b'6', b'7', b'6', b'8', b'6', b'9',
            b'7', b'0', b'7', b'1', b'7', b'2', b'7', b'3', b'7', b'4', b'7', b'5', b'7', b'6', b'7', b'7', b'7', b'8', b'7', b'9',
            b'8', b'0', b'8', b'1', b'8', b'2', b'8', b'3', b'8', b'4', b'8', b'5', b'8', b'6', b'8', b'7', b'8', b'8', b'8', b'9',
            b'9', b'0', b'9', b'1', b'9', b'2', b'9', b'3', b'9', b'4', b'9', b'5', b'9', b'6', b'9', b'7', b'9', b'8', b'9', b'9',
        ];

        debug_assert!(value <= 99);
        unsafe {
            // code is optimized to a single movw:
            ptr::copy_nonoverlapping(DIGITS100.as_ptr().add(2 * value as usize), self.ptr.add(offset), 2);
        }
    }

    /// Number of trailing zeros for `value`, with 0 <= `value` <= 99.
    fn trailing_zeros_2digits(value: u32) -> usize {
        const TRAILING_ZEROS100: &[u8; 100] = &[
            2, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ];

        debug_assert!(value <= 99);
        TRAILING_ZEROS100[value as usize] as usize
    }

    /// Converts the `value` integer into 8 decimal ASCII digits, skipping all the trailing zeros.
    ///
    /// Parameters:
    /// * `offset`: destination offset using self.ptr
    /// * `value`: integer, 0 <= value <= 99,999,999
    ///
    /// Returns the number of trailing zeros.
    fn write_8digits_skip_trailing_zeros(&mut self, offset: usize, value: u32) -> usize {
        debug_assert!(1 <= value && value <= 99999999);

        let q: u32 = value / 10000;
        let r: u32 = value % 10000;
        let qh: u32 = q / 100;
        let ql: u32 = q % 100;

        self.write_2digits(offset + 0, qh);
        self.write_2digits(offset + 2, ql);

        if r == 0 {
            Self::trailing_zeros_2digits(if ql == 0 { qh } else { ql }) + if ql == 0 { 6 } else { 4 }
        } else {
            let rh: u32 = r / 100;
            let rl: u32 = r % 100;
            self.write_2digits(offset + 4, rh);
            self.write_2digits(offset + 6, rl);
            Self::trailing_zeros_2digits(if rl == 0 { rh } else { rl }) + if rl == 0 { 2 } else { 0 }
        }
    }

    /// Converts the `value` integer into 17 decimal ASCII digits.
    ///
    /// Parameters:
    /// * `offset`: destination offset to self.ptr
    /// * `value`: integer, 0 <= digits <= 99,999,999
    ///
    /// Returns the number of trailing zeros.
    fn write_decimal_digits_backwards(&mut self, mut offset: usize, mut value: u64) -> usize {
        let mut tz: usize = 0; // number of trailing zeros removed.
        let mut nd: usize = 0; // number of decimal digits processed.

        // At most 17 digits remaining
        if value >= 100000000 {
            let q = value / 100000000;
            let r = (value % 100000000) as u32;
            value = q;
            offset -= 8;
            if r != 0 {
                tz = self.write_8digits_skip_trailing_zeros(offset, r);
                debug_assert!(tz <= 7);
            } else {
                tz = 8;
            }
            nd = 8;
        }

        // At most 9 digits remaining
        debug_assert!(value <= u32::MAX as u64);
        let mut output = value as u32;
        if output >= 10000 {
            let q = output / 10000;
            let r = output % 10000;
            output = q;
            offset -= 4;
            if r != 0 {
                let rh = r / 100;
                let rl = r % 100;
                self.write_2digits(offset + 0, rh);
                self.write_2digits(offset + 2, rl);
                if tz == nd {
                    tz += Self::trailing_zeros_2digits(if rl == 0 { rh } else { rl });
                    tz +=                              if rl == 0 {  2 } else {  0 };
                }
            } else {
                if tz == nd {
                    tz += 4;
                } else {
                    unsafe { ptr::write_bytes(self.ptr.add(offset), b'0', 4); }
                }
            }
            nd += 4;
        }

        // At most 5 digits remaining
        if output >= 100 {
            let q = output / 100;
            let r = output % 100;
            output = q;
            offset -= 2;
            self.write_2digits(offset, r);
            if tz == nd {
                tz += Self::trailing_zeros_2digits(r);
            }
            nd += 2;
            if output >= 100 {
                let q2 = output / 100;
                let r2 = output % 100;
                output = q2;
                offset -= 2;
                self.write_2digits(offset, r2);
                if tz == nd {
                    tz += Self::trailing_zeros_2digits(r2);
                }
                nd += 2;
            }
        }

        // At most 2 digits remaining
        debug_assert!(1 <= output && output <= 99, "output: {output}");
        if output >= 10 {
            let q = output;
            offset -= 2;
            self.write_2digits(offset, q);
            if tz == nd {
                tz += Self::trailing_zeros_2digits(q);
            }
            // nd += 2;
        } else {
            let q = output;
            debug_assert!(1 <= q && q <= 9);
            unsafe {
                *self.ptr.add(offset - 1) = b'0' + q as u8;
            }
        }
        tz
    }

    /// Converts the positive, finite double-precision number into decimal form and stores the result into
    /// `buffer`. The number is given as `digits` * 10 ^ `decimal_exponent`.
    ///
    /// Parameters:
    /// * `buffer`: destination buffer
    /// * `digits`: positive integer
    /// * `decimal_exponent`: base 10 exponent
    /// * `force_trailing_dot_zero`: includes the trailing ".0" for integer values
    ///
    /// Returns the length of the string written into the buffer.
    unsafe fn format_digits(&mut self, value: &FloatingDecimal64, options: &FmtOptions) -> usize {
        let digits = value.digits;
        let exponent = value.exponent;
        debug_assert!(digits >= 1);
        debug_assert!(digits <= 99_999_999_999_999_999_u64);
        debug_assert!(exponent >= -999);
        debug_assert!(exponent <= 999);

        self.write_sign(value.sign);

        // width and precision, subtract 1 from width if option given and sign consumed
        let width = options.width.and_then(|width| Some(width - value.sign as u32));
        let mut precision = options.precision;

        // extracts the raw digits
        let mut num_digits = decimal_length(digits);
        let decimal_point = num_digits as i32 + exponent;
        let mut use_fixed = Self::MIN_FIXED_DECIMAL_POINT <= decimal_point && decimal_point <= Self::MAX_FIXED_DECIMAL_POINT;
        let decimal_digits_position: usize =
            if use_fixed {
                if decimal_point <= 0 {
                    // 0.d-d or 0.(0-0)d-d
                    (2 - decimal_point) as usize
                } else {
                    // d-d.d-d or d-d(0-0)[.0]
                    0
                }
            } else {
                // dE[-]eee or d.d-dE[-]eee
                1
            };

        let offset = decimal_digits_position + num_digits;
        let tz = self.write_decimal_digits_backwards(offset, digits);
        let ptr_end = self.ptr.add(offset - tz);
        num_digits -= tz;
        //    | num_digits    = # digits in buffer (not counting the possible '-' sign)
        // -> | tz            = # trailing zeros not written in the buffer
        //    | decimal_point = # digits to skip before inserting '.'

        // check width and precision
        if let Some(w) = width {
            match () {
                _ if exponent >= 0 => {
                    // d-d[.0] or d-d(0-0)[.0]
                    if num_digits + tz > w as usize {
                        use_fixed = false;
                    }
                }
                _ if 0 < decimal_point && decimal_point < num_digits as i32 => {
                    // d-d.d-d(0-0)
                    // complicated case since rounding could generate an extra int digit -> Ed-d.d-d
                    // (for ex. 9.99, precision = 1 -> 10.0)
                    let decimal_point = decimal_point as u32;
                    let mut extra = 0;
                    let mut leading9 = 0;
                    if let Some(p) = precision {
                        if p <= num_digits as u32 - decimal_point - 1 {
                            // rounding tie to even, so if the digit right before the rounding is > '5' or a tie,
                            // and if all other digits are '9', an extra digit will appear
                            let offset = (decimal_point + p) as usize;
                            let previous_digit = *self.ptr.add(offset);
                            leading9 = (0..offset).take_while(|ofs| *self.ptr.add(*ofs) == b'9').count();
                            if previous_digit >= b'5' && leading9 >= offset {
                                extra = 1;
                            };
                        }
                    }
                    if decimal_point + extra > w {
                        // does not fit, even without decimals
                        use_fixed = false;
                    } else {
                        // reduces precision if necessary
                        if let Some(p) = precision {
                            let pmax = w - decimal_point - extra - 1;
                            if pmax < p {
                                precision = Some(pmax);
                                // we may have to re-evaluate extra and prec once more if prec had to be adjusted,
                                // because another digit is now involved for the rounding
                                let offset = (decimal_point + pmax) as usize;
                                let previous_digit = *self.ptr.add(offset);
                                if previous_digit >= b'5' && leading9 >= offset {
                                    extra = 1;
                                    if decimal_point + extra > w {
                                        use_fixed = false;
                                    }
                                };
                            }
                        }
                    }
                }
                _ => {
                    // 0.d-d or 0.(0-0)d-d
                    debug_assert!(exponent < 0);
                    if let Some(p) = precision {
                        precision = Some(min(p, w - 2))
                    }
                }
            }
        }
        println!("[v={v},width={},prec={}]",
                 if width.is_some() { width.unwrap().to_string() } else { "-".to_string() },
                 if precision.is_some() { precision.unwrap().to_string() } else { "-".to_string() });
        if use_fixed {
            if decimal_point <= 0 {
                // 0.[000]digits
                ptr::copy(b"0." as *const u8, self.ptr, 2);
                if decimal_point < 0 {
                    self.ptr.add(2).write_bytes(b'0', -decimal_point as usize);
                }
                self.ptr = ptr_end;
            } else {
                let fill = tz as i32 + exponent;
                if fill > 0 {
                    ptr_end.write_bytes(b'0', fill as usize);
                }
                let decimal_ptr = self.ptr.add(decimal_point as usize);
                if decimal_point < num_digits as i32 {
                    // dig.its
                    ptr::copy(decimal_ptr, decimal_ptr.add(1), num_digits - decimal_point as usize);
                    *decimal_ptr = b'.';
                    self.ptr = ptr_end.add(1);
                } else {
                    // digits[000]
                    self.ptr = decimal_ptr;
                    if options.trailing_dot_zero {
                        ptr::copy(b".0" as *const u8, self.ptr, 2);
                        self.ptr = self.ptr.add(2);
                    }
                }
            }
        } else {
            // Copy the first digit one place to the left.
            *self.ptr = *self.ptr.add(1);
            if num_digits == 1 {
                // dE+123
                self.ptr = self.ptr.add(1);
            } else {
                // d.igitsE+123
                *self.ptr.add(1) = b'.';
                self.ptr = ptr_end;
            }

            let scientific_exponent = decimal_point - 1;
            if scientific_exponent < 0 {
                ptr::copy(b"e-" as *const u8, self.ptr, 2);
                self.ptr = self.ptr.add(2);
            } else {
                *self.ptr = b'e';
                self.ptr = self.ptr.add(1);
            }
            let k = scientific_exponent.abs() as u32;
            if k < 10 {
                *self.ptr = b'0' + k as u8;
                self.ptr = self.ptr.add(1);
            } else if k < 100 {
                self.write_2digits(0, k);
                self.ptr = self.ptr.add(2);
            } else {
                let q = k / 100;
                let r = k % 100;
                *self.ptr = b'0' + q as u8;
                self.write_2digits(1, r);
                self.ptr = self.ptr.add(3);
            }
        }
        self.ptr.offset_from(self.buffer) as usize
    }

    unsafe fn write_sign(&mut self, sign: usize) {
        *self.ptr = b'-';
        self.ptr = self.ptr.add(sign);
    }

    /// Converts the given double-precision number into decimal form and stores the result in the given
    /// buffer.
    ///
    /// The output format is similar to `{f}` except when the position of the decimal point is out of
    /// the boundaries (MIN_FIXED_DECIMAL_POINT and MAX_FIXED_DECIMAL_POINT), in which case the format
    /// is similar to `{e}`.
    ///
    /// The output is optimal, i.e. the output string
    ///  1. rounds back to the input number when read in (using round-to-nearest-even)
    ///  2. is as short as possible,
    ///  3. is as close to the input number as possible.
    ///
    /// Note:
    /// This function may temporarily write up to TO_CHARS_MIN_BUFFER_LEN characters into the buffer.
    pub fn to_fix(&mut self, value: f64, options: &FmtOptions) -> String {
        let v = Double::from(value);
        unsafe {
            self.ptr = self.buffer;
            let length = match v.encoding() {
                Encoding::NaN => {
                    ptr::copy(b"NaN " as *const u8, self.ptr, 4);
                    3
                }
                Encoding::Inf => {
                    self.write_sign(v.sign_bit());
                    ptr::copy(b"inf " as *const u8, self.ptr, 4);
                    3 + v.sign_bit()
                }
                Encoding::Zero => {
                    ptr::copy(b"0.0 " as *const u8, self.ptr, 4);
                    if options.trailing_dot_zero { 3 } else { 1 }
                }
                Encoding::Digits => {
                    let dec = FloatingDecimal64::from(v);
                    self.format_digits(&dec, options, value)
                }
            };
            String::from_raw_parts(self.buffer, length, Self::BUFFER_LEN)
        }
    }


    pub fn check_width(&mut self, x:f64, options: &FmtOptions) -> (bool, u32) {
        let v = Double::from(x);
        self.ptr = self.buffer;
        if v.encoding() != Encoding::Digits {
            panic!("not a Digits value")
        }
        let dec = FloatingDecimal64::from(v);
        let value: &FloatingDecimal64 = &dec;

        unsafe {
            let digits = value.digits;
            let exponent = value.exponent;
            debug_assert!(digits >= 1);
            debug_assert!(digits <= 99_999_999_999_999_999_u64);
            debug_assert!(exponent >= -999);
            debug_assert!(exponent <= 999);

            self.write_sign(value.sign);

            // width and precision, subtract 1 from width if option given and sign consumed
            let width = options.width.and_then(|width| Some(width - value.sign as u32));
            let mut precision = options.precision;

            // extracts the raw digits
            let mut num_digits = decimal_length(digits);
            let decimal_point = num_digits as i32 + exponent;
            let mut use_fixed = Self::MIN_FIXED_DECIMAL_POINT <= decimal_point && decimal_point <= Self::MAX_FIXED_DECIMAL_POINT;
            let decimal_digits_position: usize =
                if use_fixed {
                    if decimal_point <= 0 {
                        // 0.d-d or 0.(0-0)d-d
                        (2 - decimal_point) as usize
                    } else {
                        // d-d.d-d or d-d(0-0)[.0]
                        0
                    }
                } else {
                    // dE[-]eee or d.d-dE[-]eee
                    1
                };

            let offset = decimal_digits_position + num_digits;
            let tz = self.write_decimal_digits_backwards(offset, digits);
            // let ptr_end = self.ptr.add(offset - tz);
            num_digits -= tz;
            //    | num_digits    = # digits in buffer (not counting the possible '-' sign)
            // -> | tz            = # trailing zeros not written in the buffer
            //    | decimal_point = # digits to skip before inserting '.'

            // check width and precision
            if let Some(w) = width {
                match () {
                    _ if exponent >= 0 => {
                        // d-d[.0] or d-d(0-0)[.0]
                        if num_digits + tz > w as usize {
                            use_fixed = false;
                        }
                    }
                    _ if 0 < decimal_point && decimal_point < num_digits as i32 => {
                        // d-d.d-d(0-0)
                        // complicated case since rounding could generate an extra int digit -> Ed-d.d-d
                        // (for ex. 9.99, precision = 1 -> 10.0)
                        let decimal_point = decimal_point as u32;
                        let mut extra = 0;
                        let mut leading9 = 0;
                        if let Some(p) = precision {
                            if p <= num_digits as u32 - decimal_point - 1 {
                                // rounding tie to even, so if the digit right before the rounding is > '5' or a tie,
                                // and if all other digits are '9', an extra digit will appear
                                let offset = (decimal_point + p) as usize;
                                let previous_digit = *self.ptr.add(offset);
                                leading9 = (0..offset).take_while(|ofs| *self.ptr.add(*ofs) == b'9').count();
                                if previous_digit >= b'5' && leading9 >= offset {
                                    extra = 1;
                                };
                            }
                        }
                        if decimal_point + extra > w {
                            // does not fit, even without decimals
                            use_fixed = false;
                        } else {
                            // reduces precision if necessary
                            if let Some(p) = precision {
                                let pmax = max(0, w as i32 - (decimal_point + extra + 1) as i32) as u32;
                                if pmax < p {
                                    precision = Some(pmax);
                                    // we may have to re-evaluate extra and prec once more if prec had to be adjusted,
                                    // because another digit is now involved for the rounding
                                    let offset = (decimal_point + pmax) as usize;
                                    let previous_digit = *self.ptr.add(offset);
                                    if previous_digit >= b'5' && leading9 >= offset {
                                        extra = 1;
                                        if decimal_point + extra > w {
                                            use_fixed = false;
                                        }
                                    };
                                }
                            }
                        }
                    }
                    _ => {
                        // 0.d-d or 0.(0-0)d-d
                        debug_assert!(exponent < 0);
                        if let Some(p) = precision {
                            let pmax = max(0, w as i32 - 2);
                            if pmax > -decimal_point {
                                precision = Some(min(p, w - 2))
                            } else {
                                // 0.000526 w=5 => pmax=3, -decimal_point=3, no digit to show!
                                use_fixed = false;
                            }
                        }
                    }
                }
            }
            return (use_fixed, precision.unwrap())
        }
    }
}

// ---------------------------------------------------------------------------------------------

/// Converts the given double-precision number into decimal form.
///
/// ```
/// use schubfach::dtoa;
///
/// assert_eq!(dtoa(12.3456789), "12.3456789");
/// assert_eq!(dtoa(1.5e-300), "1.5e-300");
/// assert_eq!(dtoa(-1.5e300), "-1.5e300");
/// ```
///
/// The output format is similar to `{f}` except when the position of the decimal point is out of
/// the boundaries (MIN_FIXED_DECIMAL_POINT and MAX_FIXED_DECIMAL_POINT), in which case the format
/// is similar to `{e}`.
///
/// The output is optimal, i.e. the output string
///  1. rounds back to the input number when read in (using round-to-nearest-even)
///  2. is as short as possible,
///  3. is as close to the input number as possible.
pub fn dtoa(value: f64) -> String {
    dtoa_width(value, None, None)
}

pub fn dtoa_width(value: f64, width: Option<u32>, precision: Option<u32>) -> String {
    let mut fmt = FPFormatter::new();
    fmt.to_fix(value, &FmtOptions { width, precision, ..FmtOptions::default() })
}


pub fn check_width(value: f64, width: Option<u32>, precision: Option<u32>) -> (bool, u32) {
    let mut fmt = FPFormatter::new();
    fmt.check_width(value, &FmtOptions { width, precision, ..FmtOptions::default() })
}