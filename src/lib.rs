// Copyright 2022 Redglyph
//
// Implementation of the Schufbach algorithm for IEEE-754 double-precision floating-point values,
// as described in the following article:
//
//     Raffaello Giulietti, "The Schubfach way to render doubles", March 16, 2020,
//     https://drive.google.com/file/d/1luHhyQF9zKlM8yJ1nebU0OgVYhfC6CBN
//
// The algorithm has a Java implementation by the author:
//
//     https://github.com/c4f7fcce9cb06515/Schubfach
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

extern crate core;

mod tests;
mod maths;

use std::{alloc, ptr};
use std::alloc::Layout;
use std::cmp::{max, min};
use std::fmt::{Display, Formatter};
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

#[derive(PartialEq)]
pub enum Encoding {
    NaN,    // not a number
    Inf,    // +infinity or -infinity number
    Zero,   // zero finite number
    Digits  // non-zero finite number
}

#[derive(Debug)]
/// IEEE-754 double-precision floating-point value
pub struct Decoded<T> {
    bits: T
}

impl<T> Decoded<T> {
    /// Creates a new [Decoded] value from the IEEE-754 binary encoding
    pub fn new(bits: T) -> Self {
        Decoded { bits }
    }
}

pub trait FPDecoded {
    type Item;

    const MAX_DIGITS_10: i32 = 53;
    const MAX_EXPONENT: i32 = 1024;
    const SIGNIFICAND_SIZE: i32 = Self::MAX_DIGITS_10;
    const EXPONENT_BIAS: i32 = Self::MAX_EXPONENT - 1 + (Self::SIGNIFICAND_SIZE - 1);
    const MAX_IEEE_EXPONENT: Self::Item;
    const HIDDEN_BIT: Self::Item;
    const FRACTION_MASK: Self::Item;
    const EXPONENT_MASK: Self::Item;
    const SIGN_MASK: Self::Item;
    /// Fraction component (significand without its hidden MSB)
    fn get_fraction(&self) -> Self::Item;
    /// Exponent component
    fn get_exponent(&self) -> Self::Item;
    /// Encoding class (zero, finite, inf or nan)
    fn encoding(&self) -> Encoding;
    /// Whether the value is finite in the form `-1 ^ sign * (1.fraction) * 2 ^ (e - 1023)`
    fn is_finite(&self) -> bool;
    /// Whether the value is positive / negative infinity
    fn is_inf(&self) -> bool;
    /// Whether the value is not a number (neither finite or infinite)
    fn is_nan(&self) -> bool;
    /// Whether the value is null
    fn is_zero(&self) -> bool;
    /// Sign: 0 = positive, 1 = negative
    fn sign_bit(&self) -> usize;
}

impl FPDecoded for Decoded<BitsType> {
    type Item = BitsType;

    const MAX_IEEE_EXPONENT: Self::Item = (2 * Self::MAX_EXPONENT - 1) as Self::Item;
    const HIDDEN_BIT: Self::Item = (1 as Self::Item) << (Self::SIGNIFICAND_SIZE - 1);
    const FRACTION_MASK: Self::Item = Self::HIDDEN_BIT - 1;
    const EXPONENT_MASK: Self::Item = Self::MAX_IEEE_EXPONENT << (Self::SIGNIFICAND_SIZE - 1);
    const SIGN_MASK: Self::Item = (1 as Self::Item) << 63;

    /// Fraction component (significand without its hidden MSB)
    fn get_fraction(&self) -> Self::Item {
        self.bits & Self::FRACTION_MASK
    }

    /// Exponent component
    fn get_exponent(&self) -> Self::Item {
        (self.bits & Self::EXPONENT_MASK) >> (Self::SIGNIFICAND_SIZE - 1)
    }

    /// Encoding class (zero, finite, inf or nan)
    fn encoding(&self) -> Encoding {
        if self.bits & !Self::SIGN_MASK == 0 {
            Encoding::Zero
        } else if self.bits & Self::EXPONENT_MASK != Self::EXPONENT_MASK {
            Encoding::Digits
        } else if self.bits & Self::FRACTION_MASK == 0 {
            Encoding::Inf
        } else {
            Encoding::NaN
        }
    }

    fn is_finite(&self) -> bool {
        self.bits & Self::EXPONENT_MASK != Self::EXPONENT_MASK
    }

    fn is_inf(&self) -> bool {
        self.bits & Self::EXPONENT_MASK == Self::EXPONENT_MASK && self.bits & Self::FRACTION_MASK == 0
    }

    fn is_nan(&self) -> bool {
        self.bits & Self::EXPONENT_MASK == Self::EXPONENT_MASK && self.bits  & Self::FRACTION_MASK != 0
    }

    fn is_zero(&self) -> bool {
        self.bits & !Self::SIGN_MASK == 0
    }

    fn sign_bit(&self) -> usize {
        usize::from(self.bits & Self::SIGN_MASK != 0)
    }
}

impl From<f64> for Decoded<BitsType> {
    fn from(f: f64) -> Self {
        let bits = f.to_bits();
        Decoded::new(bits)
    }
}

// ---------------------------------------------------------------------------------------------

/// Decimal exponent representation `digits` * 10^`exponent`
struct FloatingDecimal<T> {
    digits: T,    // num_digits <= 17
    exponent: i32,
    /// 1 = negative, 0 = positive
    sign: usize
}

impl From<Decoded<u64>> for FloatingDecimal<u64> {
    /// Builds the decimal representation from extracted IEEE-754 fraction and exponent
    fn from(double: Decoded<u64>) -> Self {
        let ieee_fraction = double.get_fraction();
        let ieee_exponent = double.get_exponent();
        let sign = double.sign_bit();
        let c: u64;
        let q: i32;
        if ieee_exponent != 0 {
            c = Decoded::<u64>::HIDDEN_BIT | ieee_fraction;
            q = ieee_exponent as i32 - Decoded::<u64>::EXPONENT_BIAS;
            if 0 <= -q && -q < Decoded::<u64>::SIGNIFICAND_SIZE && multiple_of_pow2(c, -q) {
                return FloatingDecimal { digits: c >> -q, exponent: 0, sign };
            }
        } else {
            c = ieee_fraction;
            q = 1 - Decoded::<u64>::EXPONENT_BIAS;
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
                return FloatingDecimal { digits: sp + u64::from(wp_inside), exponent: k + 1, sign };
            }
        }

        let u_inside: bool = lower <= 4 * s;
        let w_inside: bool =          4 * s + 4 <= upper;
        if u_inside != w_inside {
            return FloatingDecimal { digits: s + u64::from(w_inside), exponent: k, sign };
        }

        // NB: s & 1 == vb & 0x4
        let mid: u64 = 4 * s + 2; // = 2(s + t)
        let round_up: bool = vb > mid || (vb == mid && (s & 1) != 0);

        FloatingDecimal { digits: s + u64::from(round_up), exponent: k, sign }
    }
}

// ---------------------------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum FmtMode {
    Fix,
    Sci,
    Simple
}

#[derive(Debug, Clone)]
/// Formatting options for [NumFmtBuffer] methods
pub struct FmtOptions {
    /// maximum string length
    pub width: Option<u32>,
    /// number of fractional digits
    pub precision: Option<u32>,
    /// true: includes ".0" for integer values, false: only includes the integer part
    pub trailing_dot_zero: bool,
    /// true: negative sign for "-0", false: negative sign only for non-null values
    pub negative_zero: bool,
    /// true: panics when cannot render value, false: does not panic, may return out-of-spec strings
    pub panic_on_issue: bool,
    /// mode: Fix = fixed, Sci = scientific, Simple: simple format without width/precision
    pub mode: FmtMode
}

impl FmtOptions {
    fn simple() -> Self {
        FmtOptions {
            width: None,
            precision: None,
            trailing_dot_zero: false,
            negative_zero: true,
            panic_on_issue: false,
            mode: FmtMode::Simple,
        }
    }
}

impl Default for FmtOptions {
    fn default() -> Self {
        FmtOptions {
            width: None,
            precision: None,
            trailing_dot_zero: true,
            negative_zero: true,
            panic_on_issue: false,
            mode: FmtMode::Fix
        }
    }
}

/// Floating-point formatter
pub struct NumFmtBuffer {
    /// buffer holding the floating-point value decimal representation
    buffer: *mut u8,
    /// current pointer into the buffer
    pub ptr: *mut u8,
    size: usize,
    options: FmtOptions
}

impl NumFmtBuffer {
    const BUFFER_LEN: usize = 48;   // see conditions in implemented traits (e.g. NumFormat)

    pub fn new() -> Self {
        let size = Self::BUFFER_LEN;
        let layout = Layout::array::<u8>(size).expect("cannot create layout");
        let buffer = unsafe { alloc::alloc(layout) };
        if cfg!(test) {
            unsafe { buffer.write_bytes(b'#', size); }
        }
        NumFmtBuffer { buffer, ptr: buffer, size, options: FmtOptions::default() }
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

        // this is well optimized:
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
            // this is well optimized (automatically changed to a multiplication/shr):
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

    /// Writes the mantissa '-' sign at `self.ptr` and advances the pointer if the sign was required.
    unsafe fn write_sign(&mut self, sign: usize) {
        *self.ptr = b'-';
        self.ptr = self.ptr.add(sign);
    }

    /// Rounds the digits in the buffer that start at position `start_ptr`. The digit that
    /// follows the last precision digit to keep is pointed by `removed_digit_ptr`. If this
    /// digit is the last one, `potential_tie` is true.
    /// In case the rounding generates a new digit because of carry (9.99|9 -> 10.00),
    /// - if `can_eat_left=true`, the character at `start_ptr.sub(1)` can be used
    /// - if `can_eat_left=false`, the digits must be moved to the right
    ///
    /// The method is rounding to tie even.
    ///
    /// Returns a tuple of booleans (`left`, `right`) where
    /// * `left || right` = true if the rounding generated one extra digit because of a carry
    /// * `left` = true if the extra digit ate up one digit to the left
    /// * `right` = true if the extra digit made the buffer shift one position to the right
    /// * `left` and `right` are mutually exclusive.
    unsafe fn round(start_ptr: *mut u8, removed_digit_ptr: *mut u8, potential_tie: bool, can_eat_left: bool) -> (bool, bool) {
        debug_assert!(start_ptr <= removed_digit_ptr);
        let digits = removed_digit_ptr.offset_from(start_ptr) as usize;
        let mut tie = potential_tie && *removed_digit_ptr == b'5';
        let mut carry = *removed_digit_ptr >= b'5';
        let mut ptr = removed_digit_ptr;
        while carry && start_ptr < ptr {
            ptr = ptr.sub(1);
            if !tie || (tie && *ptr & 1 != 0) {
                // rounds up
                if *ptr == b'9' {
                    *ptr = b'0';
                } else {
                    *ptr += 1;
                    carry = false;
                }
            } else {
                // rounds down
                carry = false;
            }
            tie = false;
        }
        if carry || digits == 0 {
            // one more digit to place on the left, either because of a carry or because we
            // removed the last digit.
            let new_digit = if tie || !carry { b'0' } else { b'1' };
            if can_eat_left {
                *ptr.sub(1) = new_digit;
                (true, false)
            } else {
                ptr::copy(ptr, ptr.add(1), digits);
                *ptr = new_digit;
                (false, true)
            }
        } else {
            (false, false)
        }
    }
}

pub trait NumFormat<F, U> {
    const MIN_FIXED_DECIMAL_POINT: i32 = -6; // 0.000000[17 digits] -> fixed, more zeros -> scientific
    const MAX_FIXED_DECIMAL_POINT: i32 = 23; // [17 digits]000000.0 -> fixed, more digits -> scientific

    unsafe fn simple_format(&mut self, decoded: Decoded<U>) -> usize;
    fn format(&mut self, decoded: Decoded<U>) -> usize;
    fn fp_format(&mut self, value: f64) -> usize;
    fn to_string(self, value: F) -> String;
    fn to_str(&mut self, value: F) -> &str;
}

impl NumFormat<f64, u64> for NumFmtBuffer {

    // -----------------------------------------------------------------------------------------

    // Maximum buffer footprint for format():
    // a) fixed:
    //   a.1) if decimal_point < 0 "0.(0-0)d-d"
    //     - 1: "-" or "+" sign
    //     - 17: digits
    //     - 2: "0."
    //     - dpn: decimal_point.abs() <= Self::MIN_FIXED_DECIMAL_POINT.abs()
    //     - remaining precision if specified
    //     => size = max(20 + Self::MIN_FIXED_DECIMAL_POINT.abs(), 3 + precision)
    //   a.2) if 0 < dpp = decimal_point < num_digits0: "d-d.d-d"
    //     - 1: sign
    //     - 1: "."
    //     - 17: digits
    //     - remaining precision if specified: max "-" + 16 + "." + 1 + (precision - 1)
    //     => size = max(19, 18 + precision)
    //   a.3) if num_digits0 <= dpp: "d-d(0-0).0"
    //     - 1: sign
    //     - max(17, dpp): digits <= max(17, Self::MAX_FIXED_DECIMAL_POINT)
    //     - 2: ".0"
    //     - remaining precision if specified
    //     => size = max(3 + max(17, Self::MAX_FIXED_DECIMAL_POINT), 2 + precision)
    // b) scientific:
    //   - 1:  "-" or "+" sign
    //   - 17: digits
    //   - 1:  "."
    //   - 2:  "e-"
    //   - 3:  exponent digits
    //   - remaining precision if specified: "-" + 1 + "." + precision + "e-" + 3
    //   => size = max(24, 8 + precision)
    // c) engineer: same as scientific but rem. precision: "-" + 3 + "." + precision + "e-" + 3
    //   => size = max(24, 10 + precision)
    //
    // Maximum buffer footprint for format_simple(): same but no precision and engineering mode
    //   => same max size without precision
    //
    // size = max(24,                                       = 24
    //            20 + Self::MIN_FIXED_DECIMAL_POINT.abs(), = 26
    //             3 + Self::MAX_FIXED_DECIMAL_POINT,       = 26
    //            18 + precision)                           => max precision = 6
    // We would like max precision = at least 17 + Self::MIN_FIXED_DECIMAL_POINT.abs() = 23
    // => min size = 18 + precision = 41

    // -----------------------------------------------------------------------------------------

    /// Converts the finite double-precision number into decimal form and stores the result into
    /// `self.buffer`.
    ///
    /// Parameters:
    /// * `value`: decimal exponent representation `digits` * 10^`exponent` of the value.
    /// * `options`, only uses `force_trailing_dot_zero`: includes the trailing ".0" for integer values
    ///
    /// Returns the length of the string written into the buffer.
    unsafe fn simple_format(&mut self, decoded: Decoded<BitsType>) -> usize {
        assert!(self.size >= max(
            max(24, 20 + Self::MIN_FIXED_DECIMAL_POINT.abs() as usize),
            3 + Self::MAX_FIXED_DECIMAL_POINT as usize),
            "buffer size is too small for simple_format()");

        let decimal = FloatingDecimal::from(decoded);
        let digits = decimal.digits;
        let exponent = decimal.exponent;
        debug_assert!(digits >= 1);
        debug_assert!(digits <= 99_999_999_999_999_999_u64);
        debug_assert!(exponent >= -999);
        debug_assert!(exponent <= 999);

        self.ptr = self.buffer;
        self.write_sign(decimal.sign);

        let mut num_digits = decimal_length(digits);
        let decimal_point = num_digits as i32 + exponent;
        let use_fixed = Self::MIN_FIXED_DECIMAL_POINT <= decimal_point && decimal_point <= Self::MAX_FIXED_DECIMAL_POINT;
        let decimal_digits_position: usize =
            if use_fixed {
                if decimal_point <= 0 {
                    // 0.[000]digits
                    (2 - decimal_point) as usize
                } else {
                    // dig.its
                    // digits[000]
                    0
                }
            } else {
                // dE+123 or d.igitsE+123
                1
            };

        let offset = decimal_digits_position + num_digits;
        let tz = self.write_decimal_digits_backwards(offset, digits);
        let ptr_end = self.ptr.add(offset - tz);
        num_digits -= tz;

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
                    if self.options.trailing_dot_zero {
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

    /// Formats `value` into the buffer according the `options`, returns the total length.
    fn format(&mut self, decoded: Decoded<BitsType>) -> usize {
        assert!(self.size >= max(
            max(24, 20 + Self::MIN_FIXED_DECIMAL_POINT.abs() as usize),
            3 + Self::MAX_FIXED_DECIMAL_POINT as usize),
            "buffer size is too small for format()");

        let forced_fixed = false;   // TODO: from options STD/FIX/...

        let decimal = FloatingDecimal::from(decoded);
        let digits = decimal.digits;
        let exponent = decimal.exponent;
        debug_assert!(digits >= 1);
        debug_assert!(digits <= 99_999_999_999_999_999_u64);
        debug_assert!(exponent >= -999);
        debug_assert!(exponent <= 999);

        self.ptr = self.buffer;
        unsafe {
            // writes the sign and advances ptr if necessary
            self.write_sign(decimal.sign);

            // width and precision, subtract 1 from width if option given and sign consumed, and
            // ensure width and precision are not larger than the buffer size allows
            let width = self.options.width
                .and_then(|width| Some(min(width - decimal.sign as u32, self.size as u32)));
            let mut precision = self.options.precision
                .and_then(|prec| Some(min(prec, self.size as u32 - 18)));

            // extracts the raw digits
            let num_digits0 = decimal_length(digits);
            let mut decimal_point = num_digits0 as i32 + exponent;
            let mut use_fixed = self.options.mode == FmtMode::Fix &&
                Self::MIN_FIXED_DECIMAL_POINT <= decimal_point && decimal_point <= Self::MAX_FIXED_DECIMAL_POINT;
            let decimal_digits_position: usize =
                if use_fixed {
                    if decimal_point <= 0 {
                        // 0.d-d or 0.(0-0)d-d
                        // -------------------
                        //                   |<====| (-/0)  = -decimal_point
                        //                        |<=====>| = num_digits
                        //   memory at ptr: ???????d-----d
                        //                         |||||||
                        //   later:         0.0---0d-----d  (unless rounded or scientific)
                        //                         ^-- decimal_digits_position
                        (2 - decimal_point) as usize
                    } else {
                        // D-D.d-d or D-D(0-0)[.0]
                        // -----------------------
                        //                 |====>| (+)     |========>| (+) = decimal_point
                        //                 |<=======>|     |<===>|         = num_digits
                        //                                 |<=======>|     = num_digits0 (+ exponent)
                        //   memory at ptr: D---Dd--d?  or  D---D??????
                        //                  |||||\\\\       |||||
                        //   later:         D---D.d--d      D---D0--0[.0] (unless rounded or scientific)
                        //                  ^---------------^-- decimal_digits_position
                        0
                    }
                } else {
                    // dE[-]eee or d.d-dE[-]eee
                    // ------------------------
                    //                  |<======>| = num_digits
                    //   memory at ptr: ?Dd-----d?????
                    //                   /|||||||
                    //   later:         D.d-----dE[-]e-e  (unless rounded)
                    //                   ^-- decimal_digits_position
                    1
                };

            let offset = decimal_digits_position + num_digits0;
            let tz = self.write_decimal_digits_backwards(offset, digits);
            let mut start_ptr = self.ptr.add(decimal_digits_position);
            let mut end_ptr = self.ptr.add(offset - tz);
            let mut num_digits = num_digits0 - tz;
            // num_digits    = # digits in buffer (not counting the possible '-' sign)
            // tz            = # trailing zeros not written in the buffer
            // decimal_point = # digits to skip before inserting '.'

            // Check width and precision
            // -------------------------
            if use_fixed {
                // vvvvvv------- max width = 6 (optional)
                // 273.15
                //     ^^------- precision = 2 (optional)
                if let Some(w) = width {
                    // adjust precision for fixed-point notation if fractional part doesn't fit
                    // switches to scientific if integer part doesn't fit (precision to re-evaluate)
                    match () {
                        _ if exponent >= 0 => {
                            // d-d[.0] or d-d(0-0)[.0]
                            if let Some(p) = precision {
                                let pmax = w as i32 - (num_digits + tz + 1) as i32;
                                // 1200.00 w=4, p=2, num_digits=2, tz=2 => pmin=-1, still OK with new p=0
                                if pmax < -1 {
                                    // if pmin < -1, not possible => scientific format
                                    use_fixed = false;
                                } else {
                                    precision = Some(max(0, min(p as i32, pmax)) as u32)
                                }
                            } else {
                                if num_digits + tz > w as usize {
                                    use_fixed = false;
                                }
                            }
                        }
                        _ if 0 < decimal_point && decimal_point < num_digits as i32 => {
                            // d-d.d-d(0-0)
                            // rounding could generate an extra int digit -> Ed-d.d-d
                            // (for ex. 9.99, precision = 1 -> 10.0)
                            let decimal_point = decimal_point as u32;
                            let pmax = max(0, w as i32 - (decimal_point + 1) as i32) as u32;
                            if precision.is_none() {
                                // 12.345 num_digits=5, decimal_point=2, len=6, p=3
                                let p = num_digits as u32 - decimal_point;
                                if p > pmax {
                                    // pretend this is the required precision, it will be adjusted below
                                    precision = Some(p)
                                }
                            }
                            if let Some(mut p) = precision {
                                // adjust the precision to what is possible, disregarding rounding effects for now
                                if pmax < p {
                                    p = pmax;
                                }
                                // adjust the precision if rounding generates an extra digit
                                let mut extra = 0;
                                if p < num_digits as u32 - decimal_point {
                                    // rounding tie to even, so if the digit right before the rounding is > '5' or a tie,
                                    // and if all other digits are '9', an extra digit will appear
                                    let offset = (decimal_point + p) as usize;
                                    let previous_digit = *start_ptr.add(offset);
                                    let leading9 = (0..offset).take_while(|ofs| *start_ptr.add(*ofs) == b'9').count();
                                    if previous_digit >= b'5' && leading9 >= offset {
                                        extra = 1;
                                        let pmax = max(0, w as i32 - (decimal_point + extra + 1) as i32) as u32;
                                        if pmax < p {
                                            p = pmax;
                                        }
                                    };
                                }
                                if decimal_point + extra > w {
                                    // does not fit, even without decimals
                                    use_fixed = false;
                                }
                                if use_fixed {
                                    debug_assert!(p <= max(0, w as i32 - (decimal_point + extra + 1) as i32) as u32); // p <= pmax?
                                    // adjust the precision, unless scientific mode has been selected
                                    precision = Some(p);
                                }
                            }
                        }
                        _ => {
                            // 0.d-d or 0.(0-0)d-d
                            let pmax = max(0, w as i32 - 2);
                            if precision.is_none() {
                                let p = -decimal_point + num_digits as i32;
                                if p > pmax {
                                    // pretend this is the requested precision, it will be adjusted below
                                    precision = Some(p as u32)
                                }
                            }
                            if let Some(p) = precision {
                                let p = min(p as i32, pmax);
                                if forced_fixed || p > -decimal_point {
                                    // forced or at least one remaining digit
                                    precision = Some(p as u32)
                                } else {
                                    // 0.000526 w=5 => pmax=3, -decimal_point=3, no remaining digit in fixed
                                    use_fixed = false;
                                }
                            }
                        }
                    }
                }
            }
            let (mut left, mut right) = (false, false);
            if use_fixed {
                // ---------------------------------------------------------------------------------
                // fixed
                // ---------------------------------------------------------------------------------
                if let Some(p) = precision {
                    if exponent < 0 {
                        // d-d.d-d(0-0) or 0.d-d or 0.(0-0)d-d
                        if (p as i32) < (num_digits as i32) - decimal_point && (p as i32) >= -decimal_point {
                            // precision p requires rounding
                            let prev_digit_ptr = start_ptr.add((p as i32 + decimal_point) as usize);
                            let can_eat_extra = decimal_point <= 0;
                            let potential_tie = (p as i32) == (num_digits as i32) - decimal_point - 1;
                            (left, right) = Self::round(start_ptr, prev_digit_ptr, potential_tie, can_eat_extra);
                        }
                    }
                }
                let length;
                if decimal_point <= 0 {
                    // 0.d-d or 0.(0-0)d-d
                    // -------------------
                    //                   |<====| (-/0)  = -decimal_point
                    //                        |<=====>| = num_digits
                    //   memory at ptr: ???????d-----d??
                    //                         |||||||
                    //   adding 0/.:    0.0---0d-----d??
                    //   if rounded:     |<=======>|XX  = precision (if not None)
                    //   if width <=:  |<=========>|    = width min (if not None)
                    //   if width >:   |<=============//===>| = width max (if not None)
                    if decimal_point == 0 && left {
                        *self.ptr = *self.ptr.add(1);
                        *self.ptr.add(1) = b'.';
                    } else {
                        ptr::copy(b"0." as *const u8, self.ptr, 2);
                        let fill = -decimal_point - i32::from(left);
                        if fill > 0 {
                            self.ptr.add(2).write_bytes(b'0', fill as usize);
                        }
                    }
                    length = if let Some(p) = precision {
                        let missing_tz = p as i32 - num_digits as i32 + decimal_point;
                        if missing_tz > 0 {
                            //                   |<====|        = -decimal_point = -5
                            //                        |<=====>| = num_digits = 7 (tz not included)
                            //   memory at ptr: 0.0---0d-----d????????
                            //                                ^--- end_ptr
                            //                   |<==============>| p = 16 -> add 4 zeros
                            //   after:         0.0---0d-----d0--0????
                            end_ptr.write_bytes(b'0', missing_tz as usize);
                        }
                        if p > 0 { p as usize + 2 } else { 1 }
                    } else {
                        num_digits + -decimal_point as usize + 2
                    } + decimal.sign;
                    debug_assert!(length <= self.options.width.unwrap_or(u32::MAX) as usize,
                              "length ({}) > width ({:?})", length, self.options.width);
                } else {
                    // D-D.d-d or D-D(0-0)[.0]
                    // -----------------------
                    if !right {
                        // no carry:
                        //               |====>| (+)         |========>| (+) = decimal_point
                        //               |<==========>|      |<===>|   |     = num_digits
                        //                                   |<=======>|     = num_digits0 (+ exponent)
                        // memory at ptr: D---Dd-----d??  or  D---D??????
                        //                |||||\\\\\\\        |||||
                        // adding 0/.:    D---D.d-----d?      D---D0--0[.0]
                        // if rounded:   |     |<==>|XX      |         |     = precision (if not None)
                        // if width <=:  |<========>|        |<=======>|     = width min (if not None)
                        let fill = tz as i32 + exponent; // = decimal_point - num_digits
                        if fill > 0 {
                            end_ptr.write_bytes(b'0', fill as usize);
                        }
                        let decimal_ptr = self.ptr.add(decimal_point as usize);
                        length = if decimal_point < num_digits as i32 {
                            // D---D.d-----d
                            ptr::copy(decimal_ptr, decimal_ptr.add(1), num_digits - decimal_point as usize);
                            *decimal_ptr = b'.';
                            end_ptr = end_ptr.add(1);
                            if let Some(p) = precision {
                                let missing_tz = p as i32 - num_digits as i32 + decimal_point;
                                if missing_tz > 0 {
                                    end_ptr.write_bytes(b'0', missing_tz as usize);
                                }
                                decimal_point as usize + if p > 0 { 1 + p as usize } else { 0 }
                            } else {
                                num_digits + 1
                            }
                        } else {
                            // D---D0--0[.0]
                            self.ptr = decimal_ptr;
                            let dot_zero = self.options.trailing_dot_zero // we prefer ".0"
                                && precision.unwrap_or(1) > 0        // if precision is not constrained to 0
                                && num_digits0 + 2 <= width.unwrap_or(u32::MAX) as usize; // and if there is enough space
                            if dot_zero || precision.unwrap_or(0) > 0 {
                                ptr::copy_nonoverlapping(b".0" as *const u8, self.ptr, 2);
                                if let Some(p) = precision {
                                    if p > 1 {
                                        decimal_ptr.add(2).write_bytes(b'0', p as usize - 1);
                                    }
                                }
                                num_digits0 + 1 + precision.unwrap_or(1) as usize
                            } else {
                                num_digits0
                            }
                        } + decimal.sign;
                    } else {
                        // carry in D-D.d-d case, only occurs when precision == Some(prec):
                        //
                        // round + carry (right == true)
                        //               |====>| (+)        = decimal_point
                        //               |<==========>|     = num_digits
                        // memory at ptr: D---Dd-----d???
                        // round.+carry:  1D---Dd-----d??   => decimal_point and num_digits
                        //                1|||||\\\\\\\        are now short of 1 digit
                        // adding .:      1D---D.d-----d?
                        // actual:      = 10---0.0--0
                        //               |      |<==>|XX    = prec
                        // if width <=:  |<=========>|      = width min (if not None)

                        debug_assert!(precision.is_some());
                        // 1)   99.95: "9995??", p=1, decimal_point=2, num_digits=4
                        //    round -> "1000??" -> "100.0?" -> snip -> "100.0"
                        //              ^^^^        ^^^ ^
                        // 2)   99.9953: "999953??", p=1, decimal_point=2, num_digits=6
                        //    round ->   "100053??" -> "100.03??" -> snip -> "100.0"
                        //                ^^^^          ^^^ ^
                        let decimal_ptr = start_ptr.add(1 + decimal_point as usize);
                        let p = precision.unwrap() as usize;
                        length = if p > 0 {
                            ptr::copy(decimal_ptr, decimal_ptr.add(1), p);
                            *decimal_ptr = b'.';
                            1 + p as usize
                        } else {
                            // no trailing '.'
                            0
                        } + 1 + decimal_point as usize;
                    }
                }
                length
            } else {
                // ---------------------------------------------------------------------------------
                // scientific
                // ---------------------------------------------------------------------------------
                // vvvvvvvvvvvv--- max width          = 12 (optional)
                // 1.380649E-23
                //          ^^^--- num_exp_digits     =  3
                //   ^^^^^^------- precision          =  6 (optional)

                // check width and precision
                let sci_exponent = decimal_point - 1;
                let mut num_exp_digits = {
                    let num_exp_digits_abs = match sci_exponent.abs() {
                        0 ..=  9 => 1,
                        10 ..= 99 => 2,
                        _         => 3
                    };
                    num_exp_digits_abs + if sci_exponent < 0 { 1 } else { 0 }
                };
                if let Some(w) = width {
                    if self.options.panic_on_issue && w < 2 + num_exp_digits {   // 2 = first digit + 'E'
                        // TODO: returns an error, panics if options.panic in upper function
                        panic!("cannot format value with width <= {w}, requires at least {} characters", 3 + num_exp_digits);
                    }
                    let mut pmax = max(0, w as i32 - 3 - num_exp_digits as i32) as u32;  // 3 = first digit + '.' + 'E'
                    if precision.is_none() && num_digits - 1 > pmax as usize {
                        // pretend this is the required precision, it will be adjusted below
                        precision = Some(pmax)
                    }
                    if let Some(mut p) = precision {
                        // ex: num_digits = 7:  1 2 3 4 5 6 7
                        //     p = 4:           d.d d d d d d
                        //                       |<--p-->|^-- previous_digit
                        if sci_exponent >= 0 {
                            p = min(p, pmax);
                            if p + 1 < num_digits as u32 && (sci_exponent == 9 || sci_exponent == 99) {
                                // rounding tie to even, so if the digit right before the rounding is > '5' or a tie,
                                // and if all other digits are '9', an extra digit will appear, which *may* induce
                                // an extra exponent digit, for ex. if w=6, p=2, "9.999E9" -> "1.00E10" (len=7)
                                // so precision has to be further reduced to p=1           -> "1.0E10"  (len=6, OK)
                                let offset = (1 + p) as usize;
                                let previous_digit = *start_ptr.add(offset);
                                let leading9 = (0..offset).take_while(|ofs| *start_ptr.add(*ofs) == b'9').count();
                                if previous_digit >= b'5' && leading9 >= offset {
                                    num_exp_digits += 1;
                                    pmax = max(0, w as i32 - 3 - num_exp_digits as i32) as u32;
                                    p = min(p, pmax);
                                };
                            }
                        } else {
                            if pmax < p {
                                if pmax + 1 < num_digits as u32 && (sci_exponent == -10 || sci_exponent == -100) {
                                    // when the exponent is negative, the new '0' digit compensates the disappearing
                                    // exponent digit, so the precision can be kept:
                                    // w=7, p=3: "9.995e-10" (len=9) -> pmax=1 "10.0e-10" -> p=2 "1.00e-9" (len=7)
                                    let offset = (1 + pmax) as usize;
                                    let previous_digit = *start_ptr.add(offset);
                                    let leading9 = (0..offset).take_while(|ofs| *start_ptr.add(*ofs) == b'9').count();
                                    if previous_digit >= b'5' && leading9 >= offset {
                                        num_exp_digits -= 1;
                                        pmax += 1
                                    }
                                }
                                p = pmax;
                            }

                        }
                        precision = Some(p)
                    }
                }

                // Rounding
                // --------
                if let Some(p) = precision {
                    if p + 1 < num_digits as u32 {
                        let prev_digit_ptr = start_ptr.add(1 + p as usize);
                        let can_eat_extra = decimal_digits_position > 1;
                        let potential_tie = (p as i32) == (num_digits as i32) - 2;
                        (left, right) = Self::round(start_ptr, prev_digit_ptr, potential_tie, can_eat_extra);
                        if left {
                            start_ptr = start_ptr.sub(1);
                        }
                        if left || right {
                            //end_ptr = end_ptr.add(1);   // not used later
                            decimal_point += 1;
                            num_digits += 1;
                        }
                    }
                }

                // Mantissa
                // --------
                if self.options.trailing_dot_zero // we prefer ".0"
                    && num_digits == 1 // it is not already there
                    && precision.is_none() // precision is not constrained
                    && 3 + num_exp_digits <= width.unwrap_or(u32::MAX) // there is enough space
                {
                    precision = Some(1); // faking precision requirement to get ".0"
                }
                //   |=>|               decimal_point = -2
                //      |<=====>|       num_digits    =  7
                // [0.00]2480649?????
                //       |\\\\\\
                //       2.480649E-3
                //                ^^--- num_exp_digits     =  2
                //         ^^^^-------- precision          =  4 (optional)
                // Lengths (without the mantissa sign)
                // - precision = None:    m = 1 + num_digits = 8, e = 1 + num_exp_digits = 3
                // - precision = Some(4): m = 2 + precision  = 6, e = 1 + num_exp_digits = 3
                let num_decimals = precision.unwrap_or(num_digits as u32 - 1) as usize;
                let num_bytes = min(num_digits - 1, num_decimals);
                if num_decimals > 0 {
                    match decimal_digits_position {
                        0 => {
                            ptr::copy(start_ptr.add(1), start_ptr.add(2), num_bytes);
                        }
                        1 => {
                            let digit = *start_ptr;
                            *self.ptr = digit;
                        }
                        _ => {
                            *self.ptr = *start_ptr;
                            ptr::copy(start_ptr.add(1), self.ptr.add(2), num_bytes);
                        }
                    }
                    *self.ptr.add(1) = b'.';
                    let fill = num_decimals as i32 - num_digits as i32 + 1;
                    if fill > 0 {
                        ptr::write_bytes(self.ptr.add(2 + num_bytes), b'0', fill as usize);
                    }
                    self.ptr = self.ptr.add(2 + num_decimals);
                } else /* if decimal_digits_position > 0 */ {
                    *self.ptr = *start_ptr;
                    self.ptr = self.ptr.add(1);
                } /*else { // collapsed with previous case
                    self.ptr = self.ptr.add(1);
                }*/
                // start_ptr, end_ptr not up-to-date anymore, not used later

                // Exponent
                // --------
                let scientific_exponent = decimal_point - 1;
                if scientific_exponent < 0 {
                    ptr::copy(b"e-" as *const u8, self.ptr, 2);  // TODO: option e or E
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
                    // this is correctly optimized by LLVM:
                    let q = k / 100;
                    let r = k % 100;
                    *self.ptr = b'0' + q as u8;
                    self.write_2digits(1, r);
                    self.ptr = self.ptr.add(3);
                }
                let length = self.ptr.offset_from(self.buffer) as usize;
                length
            }
        }
    }

    fn fp_format(&mut self, value: f64) -> usize {
        let v = Decoded::from(value);
        unsafe {
            match v.encoding() {
                Encoding::NaN => {
                    ptr::copy(b"NaN " as *const u8, self.buffer, 4);
                    3
                }
                Encoding::Inf => {
                    self.ptr = self.buffer;
                    self.write_sign(v.sign_bit());
                    ptr::copy(b"inf " as *const u8, self.ptr, 4);
                    3 + v.sign_bit()
                }
                Encoding::Zero => {
                    self.ptr = self.buffer;
                    if self.options.negative_zero {
                        self.write_sign(v.sign_bit());
                    }
                    ptr::copy(b"0.0 " as *const u8, self.ptr, 4);
                    v.sign_bit() * usize::from(self.options.negative_zero)  // -
                        + 1                                                 // 0
                        + 2 * usize::from(self.options.trailing_dot_zero)   // .0
                }
                Encoding::Digits => {
                    if self.options.mode == FmtMode::Simple {
                        self.simple_format(v)
                    } else {
                        self.format(v)
                    }
                }
            }
        }
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
    fn to_string(mut self, value: f64) -> String {
        let length = self.fp_format(value);
        unsafe {
            let bufsize = self.size;
            self.size = 0; // prevents de-allocating twice when dropping
            String::from_raw_parts(self.buffer, length, bufsize)
        }
    }

    fn to_str(&mut self, value: f64) -> &str {
        let length = self.fp_format(value);
        unsafe {
            let v = std::slice::from_raw_parts(self.buffer, length);
            std::str::from_utf8_unchecked(v)
        }
    }
}

impl Drop for NumFmtBuffer {
    fn drop(&mut self) {
        if self.size != 0 {
            let layout = Layout::array::<u8>(self.size).expect("could not create layout to deallocate buffer");
            self.size = 0;
            unsafe {
                alloc::dealloc(self.buffer, layout);
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------

pub struct NumWithOptions<F: Sized> {
    value: F,
    mode: FmtMode
}

pub trait FormatInterface
    where Self: Sized
{
    /// FIX interface to Display formatter (fixed decimal place).
    fn to_fix(&self) -> NumWithOptions<Self>;
    /// SCI interface to Display formatter (scientific format).
    fn to_sci(&self) -> NumWithOptions<Self>;

    /// Converts the number into decimal form.
    fn ftoa(&self) -> String;
    /// Converts the number into decimal form.
    fn format(&self, width: Option<u32>, precision: Option<u32>, mode: FmtMode) -> String;
    /// Converts the number into decimal form.
    fn format_opt(&self, options: &FmtOptions) -> String;
}

impl FormatInterface for f64 {
    fn to_fix(&self) -> NumWithOptions<Self> {
        NumWithOptions { value: *self, mode: FmtMode::Fix }
    }

    fn to_sci(&self) -> NumWithOptions<Self> {
        NumWithOptions { value: *self, mode: FmtMode::Sci }
    }

    /// Converts the double-precision number into decimal form.
    ///
    /// ```
    /// use schubfach::FormatInterface;
    ///
    /// assert_eq!(12.3456789.ftoa(), "12.3456789");
    /// assert_eq!(1.5e-300.ftoa(), "1.5e-300");
    /// ```
    ///
    /// The output format is similar to `{}` except when the position of the decimal point is out of
    /// the boundaries (MIN_FIXED_DECIMAL_POINT and MAX_FIXED_DECIMAL_POINT), in which case the format
    /// is similar to `{:e}`.
    ///
    /// The output is optimal, i.e. the output string
    ///  1. rounds back to the input number when read in (using round-to-nearest-even)
    ///  2. is as short as possible,
    ///  3. is as close to the input number as possible.
    fn ftoa(&self) -> String {
        let mut fmt = NumFmtBuffer::new();
        fmt.options.trailing_dot_zero = false;
        fmt.options.mode = FmtMode::Simple;
        fmt.to_string(*self)
    }

    /// Converts the double-precision number into decimal form.
    fn format(&self, width: Option<u32>, precision: Option<u32>, mode: FmtMode) -> String {
        let mut fmt = NumFmtBuffer::new();
        fmt.options.width = width;
        fmt.options.precision = precision;
        fmt.options.mode = mode;
        fmt.to_string(*self)
    }

    /// Converts the double-precision number into decimal form.
    fn format_opt(&self, options: &FmtOptions) -> String {
        let mut fmt = NumFmtBuffer::new();
        fmt.options = options.clone();
        fmt.to_string(*self)
    }
}

impl Display for NumWithOptions<f64> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut fmt = NumFmtBuffer::new();
        fmt.options.width = f.width().and_then(|x| Some(x as u32));
        fmt.options.precision = f.precision().and_then(|x| Some(x as u32));
        fmt.options.mode = self.mode;
        let s = fmt.to_string(self.value);
        f.pad_integral(true, "", &s)
    }
}
