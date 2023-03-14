// Copyright 2022 Redglyph

use std::fmt::LowerExp;
use std::str::FromStr;
use num::{Float, PrimInt, Zero};
use oorandom::Rand64;
use crate::*;

#[derive(Debug)]
struct FloatChecker<T> {
    v: T,
    s: String,
    options: FmtOptions
}

impl<T: Copy + FormatInterface> FloatChecker<T> {
    fn new(v: T, options: Option<FmtOptions>) -> Self {
        let options = options.unwrap_or(FmtOptions::simple());
        FloatChecker {
            v,
            s: v.format_opt(&options), //v.ftoa(),
            options
        }
    }
}

/// Builds a floating-point value from parts (significand, exponent, sign, ...)
trait FloatFromParts {
    type BitsType;
    /// Builds a floating-point value from its significand, exponent, and sign.
    fn from_parts(significand: Self::BitsType, exponent: i32, negative: bool) -> Self;
    fn from_rnd_parts(rng: &mut Rand64) -> Self;
    fn from_rnd_float(rng: &mut Rand64) -> Self;
}

/// Floating-point constants for each type (f64, ...)
trait FloatConst where Self: Sized + 'static + FloatFromParts
{
    const P: i32;
    const W: i32;
    const Q_MIN: i32;
    const Q_MAX: i32;
    const C_MIN: i64;
    const C_MAX: i64;
    const K_MIN: i32;
    const K_MAX: i32;
    const H: i32;
    const MIN_VALUE: Self;
    const MIN_NORMAL: Self;
    const MAX_VALUE: Self;
    const E_MIN: i32;
    const E_MAX: i32;
    const C_TINY: i64;
    const MIN_FIXED_DECIMAL_POINT: isize;
    const MAX_FIXED_DECIMAL_POINT: isize;

    const EXTREMES: &'static [Self];
    const ANOMALIES: &'static [&'static str];
    const SIG_EXP: &'static [(<Self as FloatFromParts>::BitsType, i32)];

    fn max_len10() -> i32 {
        Self::MAX_FIXED_DECIMAL_POINT as i32
    }

    fn max_significant_digits() -> i32 {
        Self::H
    }
}

#[derive(Debug, Clone)]
struct ParseResult {
    c: u64,
    q: i32,
    len10: i32,
}

trait FloatTester {
    type Data;
    fn parse(&self, string: String) -> Result<ParseResult, &str>;
    fn is_ok(&self) -> Result<(), String>;
    fn get_float(string: &str) -> Self::Data;
    fn test_dec(x: Self::Data);
    fn test_extreme_values();
    fn test_some_anomalies();
    fn test_powers2();
    fn test_powers10();
    fn test_paxson();
    fn test_ints();
    fn test_longs();
    fn test_random(random_count: u64);
    fn test_random_units(random_count: u64);
    fn tests(random_count: u64);
}

impl<T> FloatTester for FloatChecker<T>
    where T: Copy + Zero + Float + FormatInterface + FloatConst + From<f64> + FromStr + From<i32> +
             Display + LowerExp + FloatFromParts,
          <T as FloatFromParts>::BitsType: Copy
{
    type Data = T;

    fn parse(&self, mut string: String) -> Result<ParseResult, &str> {
        let mut result = ParseResult { c: 0, q: 0, len10: 0 };
        string.push('*'); // end delimiter
        unsafe {
            let ptr = string.as_ptr();
            let mut s = ptr;
            while *s == b'0' {
                s = s.add(1);
            }
            // => s is on the first non-zero integer digit (if any)
            if s.offset_from(ptr) > 1 {
                return Err("more than one leading zero in integer part");
            }
            let mut p = s;
            let mut overflow = false;
            while (*p).is_ascii_digit() {
                if !overflow {
                    if let Some(c) = result.c.checked_mul(10).and_then(|c| c.checked_add((*p - b'0') as u64)) {
                        result.c = c;
                    } else {
                        overflow = true;
                    }
                }
                if overflow {
                    if *p != b'0' {
                        return Err("too many digits in integer part");
                    }
                    result.q += 1;
                }
                p = p.add(1);
            }
            // => p is on the first character after the integer part
            result.len10 = p.offset_from(ptr) as i32 - result.q;
            if result.len10 == 0 {
                return Err("integer part missing");
            }
            let mut fz = p;
            if *fz == b'.' {
                fz = fz.add(1);
            } else {
                return Err("decimal mark '.' missing")
            }
            // => fz is after '.' (if any)
            let mut f = fz;
            while *f == b'0' {
                if !overflow {
                    if let Some(c) = result.c.checked_mul(10) {
                        result.c = c;
                    } else {
                        overflow = true;
                    }
                }
                if overflow {
                    result.q += 1;
                }
                f = f.add(1);
            }
            // => f is on the first non-zero fraction digit (if any)
            result.len10 = if result.c == 0 {
                0
            } else {
                f.offset_from(ptr) as i32 - 1 - result.q
            };

            let mut x = f;

            while (*x).is_ascii_digit() {
                if !overflow {
                    if let Some(c) = result.c.checked_mul(10).and_then(|c| c.checked_add((*x - b'0') as u64)) {
                        result.c = c;
                        result.len10 += 1;
                    } else {
                        overflow = true;
                    }
                }
                if overflow {
                    if *x != b'0' {
                        return Err("too many digits in integer + fractional parts");
                    }
                    result.q += 1;
                }
                x = x.add(1);
            }
            // => x is after the last fraction digit
            if f.offset_from(fz) > 1 && x == f {
                return Err("several zeros only in fractional part");
            }
            if x == fz {
                return Err("fractional part missing")
            }
            let mut g = x;
            if *g == b'e' || *g == b'E' {
                g = g.add(1);
            }
            // => g is after the exponent 'e' indicator (if any)
            let mut ez = g;
            if *ez == b'-' {
                ez = ez.add(1);
            }
            // => ez is after the exponent sign (if any)
            let mut e = ez;
            while *e == b'0' {
                e = e.add(1);
            }
            // => e is on the first non-zero exponent digit (if any)
            let mut z = e;
            while (*z).is_ascii_digit() {
                result.q = result.q.wrapping_mul(10).wrapping_add((*z - b'0') as i32);
                if result.q < 0 {
                    return Err("exponent too big");
                }
                z = z.add(1);
            }
            // => z is after the last exponent digit

            // check for the end of the string
            if z.offset_from(ptr) as usize != string.len() - 1 {
                return Err("trailing characters");
            }

            if x == z { // no exponent
                if *s == b'.' {
                    // check -MIN_FIXED_DECIMAL_POINT when abs(v) < 1
                    let min_dec = -T::MIN_FIXED_DECIMAL_POINT;
                    if f.offset_from(p) > min_dec + 1 {
                        return Err("too small, should have been exponent notation");
                    }
                } else {
                    // check MAX_FIXED_DECIMAL_POINT when abs(v) >= 1
                    let max_dec = T::MAX_FIXED_DECIMAL_POINT;
                    if p.offset_from(s) > max_dec {
                        return Err("too big, should have been exponent notation");
                    }
                }
                result.q -= x.offset_from(fz) as i32;
                Ok(result)
            } else { // exponent
                if x == g {
                    return Err("missing exponent mark 'e'/'E'");
                }
                if ez == z {
                    return Err("missing exponent");
                }
                if e == z {
                    return Err("null exponent");
                }
                if ez != e {
                    return Err("'0' digit(s) in front of exponent");
                }
                if s == p {
                    return Err("exponent notation with '0' integer digit");
                }
                if p.offset_from(s) > 1 {
                    return Err("exponent notation with more than one integer digit")
                }
                if g != ez {
                    // negative exponent
                    result.q = -result.q;
                }
                // => result.q is the exponent
                if T::MIN_FIXED_DECIMAL_POINT as i32 <= result.q && result.q < T::MAX_FIXED_DECIMAL_POINT as i32 {
                    return Err("should not have been exponent notation");
                }
                result.q -= x.offset_from(fz) as i32;
                // => result.q is the "exponent of the last digit", if there were no decimal point
                Ok(result)
            }
        }
    }

    fn is_ok(&self) -> Result<(), String> {
        // parses the string to verify its format
        let mut s = self.s.clone();
        let mut v = self.v;
        if v.is_nan() {
            if self.s != "NaN" {
                return Err("expected 'NaN'".to_string());
            }
            return Ok(())
        }
        if v.is_sign_negative() && (!v.is_zero() || self.options.negative_zero) {
            if s.is_empty() || !s.starts_with('-') {
                return Err("empty or not starting with '-'".to_string());
            }
            v = -self.v;
            s.remove(0);
        }
        if v.is_infinite() {
            if s != "inf" {
                return Err("expected 'inf' (or '-inf')".to_string());
            }
            return Ok(())
        }
        if v.is_zero() {
            return match self.options.trailing_dot_zero {
                true  if s != "0.0" => { Err("expected '0.0' (or '-0.0')".to_string()) },
                false if s != "0" => { Err("expected '0' (or '-0')".to_string()) },
                _ => Ok(())
            }
        }

        // tests that parsing the generated string yields the original value
        match self.s.parse::<T>() {
            Ok(recovered) => if recovered != self.v {
                return Err(format!("string '{}' does not recover original value", self.s));
            }
            Err(_) => return Err(format!("Error when parsing string to float")),
        }

        let mut parsed = self.parse(s)?;
        while parsed.len10 > T::max_significant_digits() {
            if parsed.c % 10 != 0 {
                println!("{:?}", parsed);
                return Err(format!("expected multiple of 10 for a value with more than {} integer digits ({} -> {} * 10^{})",
                                   T::max_significant_digits(), self.s, parsed.c, parsed.q));
            }
            parsed.c /= 10;
            parsed.q += 1;
            parsed.len10 -= 1;
        }
        // println!("parsed: {:?}", parsed);
        if parsed.len10 < 2 {
            parsed.c *= 10;
            parsed.q -= 1;
            parsed.len10 += 1;
        }
        if parsed.len10 < 2 || T::max_len10() < parsed.len10 {
            return Err(format!("parsed.len10 = {} out of boundaries (2 .. {})", parsed.len10, T::max_len10()));
        }
        // The exponent is bounded
        if parsed.q + parsed.len10 < T::E_MIN || T::E_MAX < parsed.q + parsed.len10 {
            return Err("out of exponent bounds".to_string());
        }
        while parsed.len10 > 2 && parsed.c % 10 == 0 {
            parsed.c /= 10;
            parsed.q += 1;
            parsed.len10 -= 1;
        }
        Ok(())
    }

    fn get_float(string: &str) -> Self::Data {
        match string.parse::<T>() {
            Ok(v) => v,
            Err(_) => panic!("could not parse '{}' to float", string)
        }
    }

    fn test_dec(x: Self::Data) {
        let mut options = FmtOptions::simple();
        options.trailing_dot_zero = true;
        let checker = FloatChecker::new(x, Some(options));
        // println!("{x:e} => {}", checker.s);
        if let Err(msg) = checker.is_ok() {
            panic!("'{x:e}' didn't pass the test. Result: '{}', error:'{msg}'", checker.s);
        }
    }
    
    fn test_extreme_values() {
        for dec in T::EXTREMES {
            Self::test_dec(*dec);
        }
    }

    fn test_some_anomalies() {
        for &dec in T::ANOMALIES {
            Self::test_dec(Self::get_float(dec));
        }
    }

    fn test_powers2() {
        let mut v = T::MIN_VALUE;
        while v < T::MAX_VALUE {
            Self::test_dec(v);
            v = v + v;
        }
    }

    fn test_powers10() {
        for e in T::E_MIN..=T::E_MAX {
            Self::test_dec(Self::get_float(&format!("1e{}", e)));
        }
    }

    fn test_paxson() {
        for (s, e) in T::SIG_EXP {
            Self::test_dec(T::from_parts(*s, *e, false));
        }
    }

    fn test_ints() {
        for i in 0..1_000_000 {
            Self::test_dec(<T as From<i32>>::from(i));
        }
    }

    fn test_longs() {
        for i in 10_000..100_000 {
            Self::test_dec(<T as From<i32>>::from(i) * 1.0e15.into());
        }
    }

    fn test_random(random_count: u64) {
        let mut rng = Rand64::new(0);
        for _ in 0..random_count {
            Self::test_dec(T::from_rnd_parts(&mut rng));
        }
    }

    fn test_random_units(random_count: u64) {
        let mut rng = Rand64::new(1);
        for _ in 0..random_count {
            Self::test_dec(T::from_rnd_float(&mut rng));
        }
    }

    fn tests(random_count: u64) {
        Self::test_some_anomalies();
        Self::test_extreme_values();
        Self::test_powers2();
        Self::test_powers10();
        Self::test_paxson();
        Self::test_ints();
        Self::test_longs();
        Self::test_random(random_count);
        Self::test_random_units(random_count);
    }
}

// ---------------------------------------------------------------------------------------------

impl FloatConst for f64 {
    // Pre-calculated constants because most functions are unstable as const:
    const P: i32 = 53;
    const W: i32 = 11;
    const Q_MIN: i32 = -1074;
    const Q_MAX: i32 = 971;
    const C_MIN: i64 = 4503599627370496;
    const C_MAX: i64 = 9007199254740991;
    const K_MIN: i32 = -324;
    const K_MAX: i32 = 292;
    const H: i32 = 17; // maximum number of significant digits
    const MIN_VALUE: f64 = 4.9E-324;    // replace with f64::from_bits(0x0000000000000001) when const stable
    const MIN_NORMAL: f64 = 2.2250738585072014E-308;
    const MAX_VALUE: f64 = 1.7976931348623157E308;
    const E_MIN: i32 = -323;
    const E_MAX: i32 = 309;
    const C_TINY: i64 = 3;
    const MIN_FIXED_DECIMAL_POINT: isize = <NumFmtBuffer as NumFormat<f64, u64>>::MIN_FIXED_DECIMAL_POINT as isize;
    const MAX_FIXED_DECIMAL_POINT: isize = <NumFmtBuffer as NumFormat<f64, u64>>::MAX_FIXED_DECIMAL_POINT as isize;

    const EXTREMES: &'static [Self] = &[
        f64::NEG_INFINITY,
        -f64::MAX_VALUE,
        -f64::MIN_NORMAL,
        -f64::MIN_VALUE,
        -0.0,
        0.0,
        f64::MIN_VALUE,
        f64::MIN_NORMAL,
        f64::MAX_VALUE,
        f64::INFINITY,
        f64::NAN,
    ];

    /// There are tons of doubles that are rendered incorrectly by the JDK.
    /// While the renderings correctly round back to the original value,
    /// they are longer than needed or are not the closest decimal to the double.
    /// Here are just a very few examples.
    const ANOMALIES: &'static [&'static str] = &[
        "9.9E-324", "9.9E-323",
    ];

    /// Values are from tables 3 and 4 in
    /// Paxson V, "A Program for Testing IEEE Decimal-Binary Conversion"
    const SIG_EXP: &'static [(<Self as FloatFromParts>::BitsType, i32)] = &[
        (8_511_030_020_275_656, -342),
        (5_201_988_407_066_741, -824),
        (6_406_892_948_269_899,  237),
        (8_431_154_198_732_492,   72),
        (6_475_049_196_144_587,   99),
        (8_274_307_542_972_842,  726),
        (5_381_065_484_265_332, -456),
        (6_761_728_585_499_734,  -57),
        (7_976_538_478_610_756,  376),
        (5_982_403_858_958_067,  377),
        (5_536_995_190_630_837,   93),
        (7_225_450_889_282_194,  710),
        (7_225_450_889_282_194,  709),
        (8_703_372_741_147_379,  117),
        (8_944_262_675_275_217,   -1),
        (7_459_803_696_087_692, -707),
        (6_080_469_016_670_379, -381),
        (8_385_515_147_034_757,  721),
        (7_514_216_811_389_786, -828),
        (8_397_297_803_260_511, -345),
        (6_733_459_239_310_543,  202),
        (8_091_450_587_292_794, -473),
        (6_567_258_882_077_402,  952),
        (6_712_731_423_444_934,  535),
        (6_712_731_423_444_934,  534),
        (5_298_405_411_573_037, -957),
        (5_137_311_167_659_507, -144),
        (6_722_280_709_661_868,  363),
        (5_344_436_398_034_927, -169),
        (8_369_123_604_277_281, -853),
        (8_995_822_108_487_663, -780),
        (8_942_832_835_564_782, -383),
        (8_942_832_835_564_782, -384),
        (8_942_832_835_564_782, -385),
        (6_965_949_469_487_146, -249),
        (6_965_949_469_487_146, -250),
        (6_965_949_469_487_146, -251),
        (7_487_252_720_986_826,  548),
        (5_592_117_679_628_511,  164),
        (8_887_055_249_355_788,  665),
        (6_994_187_472_632_449,  690),
        (8_797_576_579_012_143,  588),
        (7_363_326_733_505_337,  272),
        (8_549_497_411_294_502, -448),
    ];
}

impl FloatFromParts for f64 {
    type BitsType = u64;

    /// Builds an f64 from its significand, exponent, and sign.
    ///
    /// The `significand` is masked and its MSB is removed. The `exponent` must be provided
    /// unbiased, as a signed integer.
    fn from_parts(significand: Self::BitsType, exponent: i32, negative: bool) -> Self {
        assert!(significand / 2 <= <Decoded<u64> as FPDecoded>::FRACTION_MASK);
        let exp: u64 = (exponent + <Decoded<u64> as FPDecoded>::EXPONENT_BIAS) as u64;
        assert!(exp <= <Decoded<u64> as FPDecoded>::EXPONENT_MASK);
        let bits: u64 = (significand & <Decoded<u64> as FPDecoded>::FRACTION_MASK)
            | exp.unsigned_shl(<Decoded<u64> as FPDecoded>::SIGNIFICAND_SIZE as u32 - 1)
            | if negative { <Decoded<u64> as FPDecoded>::SIGN_MASK } else { 0 };
        f64::from_bits(bits)
    }

    /// Builds an f64 from random u64 bits, so it can generate normal/subnormal values and inf/NaN.
    fn from_rnd_parts(rng: &mut Rand64) -> Self {
        f64::from_bits(rng.rand_u64())
    }

    /// Builds an f64 from a random value in the range [0 - 2^53[.
    fn from_rnd_float(rng: &mut Rand64) -> Self {
        const HIDDEN_BIT: u64 = <Decoded<u64> as FPDecoded>::HIDDEN_BIT;
        let significand: u64 = rng.rand_range(0..HIDDEN_BIT) | HIDDEN_BIT;
        f64::from_parts(significand, 0, false)
    }
}

#[test]
/// Tests the tester
fn test_checker() {
    let values: &[(u64, i32, &str)] = &[
        (10000000000000000000, 0, "10000000000000000000.0"),
        (10, 21, "1.0e22"),
        (125, -24, "1.25e-22"),
        (10, -1, "1.0"),
        (100010, -1, "10001.0"),
    ];
    for (id, (c, q, s)) in values.iter().enumerate() {
        let chk = FloatChecker { v: 0.0, s: s.to_string(), options: FmtOptions::default() };
        match chk.parse(s.to_string()) {
            Ok(result) => {
                // println!("{:?}", result);
                assert_eq!(*c, result.c, "wrong value of c in test {}", id);
                assert_eq!(*q, result.q, "wrong value of q in test {}", id);
            }
            Err(e) => panic!("{}", format!("cannot parse value {}: {}", s, e.to_string()))
        }
    }
}

// ---------------------------------------------------------------------------------------------

#[test]
fn test_f64() {
    FloatChecker::<f64>::tests(1_000);
}
