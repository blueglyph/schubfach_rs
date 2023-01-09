// Copyright 2022 Redglyph

use num::{Float, Zero};
use crate::*;

#[test]
fn test_constants() {
    // constants for double-precision encoding
    assert_eq!(Decoded::<u64>::SIGNIFICAND_SIZE, 53);
    assert_eq!(Decoded::<u64>::EXPONENT_BIAS, 1075);
    assert_eq!(Decoded::<u64>::MAX_IEEE_EXPONENT, 2047);
    assert_eq!(Decoded::<u64>::HIDDEN_BIT, 0x0010000000000000);
    assert_eq!(Decoded::<u64>::FRACTION_MASK, 0x000fffffffffffff);
    assert_eq!(Decoded::<u64>::EXPONENT_MASK, 0x7ff0000000000000);
    assert_eq!(Decoded::<u64>::SIGN_MASK, 0x8000000000000000);

    // constants used in FPFormatter
    assert!(NumFmtBuffer::MIN_FIXED_DECIMAL_POINT <= -1, "internal error");
    assert!(NumFmtBuffer::MIN_FIXED_DECIMAL_POINT >= -30, "internal error");
    assert!(NumFmtBuffer::MAX_FIXED_DECIMAL_POINT >= 1, "internal error");
    assert!(NumFmtBuffer::MAX_FIXED_DECIMAL_POINT <= 32, "internal error");
}

#[test]
fn test_double() {
    // base methods
    for f in vec![1.0, -1.0, f64::NAN, f64::INFINITY, f64::NEG_INFINITY, 0.0, 1e10, -1.5e-8] {
        let x = Decoded::from(f);
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
            assert_eq!(significand & !Decoded::<u64>::HIDDEN_BIT, x.physical_fraction(), "{report}");
            assert_eq!(exponent + Decoded::<u64>::EXPONENT_BIAS as i16, (x.physical_exponent() as i16), "{report}");
            assert_eq!((1 - sign) / 2, x.sign_bit() as i8, "{report}");
        }
    }
}
