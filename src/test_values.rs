// ---------------------------------------------------------------------------------------------
// Test values

use crate::{NumFmtBuffer, NumFormat};

#[derive(Debug)]
pub struct StdFixValues {
    pub min_exp: i32,
    pub min_fix: f64,           // min for fix format in Std
    pub low_fix: f64,           // too low for fix format in Std
    pub min_fix_str: String,
    pub low_fix_str: String,
    pub low_sci_str: String,
    pub digits: i32,
    pub max_exp: i32,
    pub max_fix: f64,           // max for fix format in Std
    pub high_fix: f64,          // too high for fix format in Std
    pub max_fix_str: String,
    pub high_fix_str: String,
    pub high_sci_str: String,
}

impl StdFixValues {
    pub fn new() -> Self {
        // if MIN_FIXED_DECIMAL_POINT = -3 => 0.000[d-d] is the limit => 1e-4 is the limit
        // for std as fixed-format
        let min_exp = <NumFmtBuffer as NumFormat<f64, u64>>::MIN_FIXED_DECIMAL_POINT - 1;
        let min_fix = 10.0_f64.powi(min_exp);
        let low_fix = min_fix / 10.0;
        let min_fix_str = "0.".to_string() + &"0".repeat(min_exp.abs() as usize - 1) + "1";
        let low_fix_str = "0.".to_string() + &"0".repeat(min_exp.abs() as usize) + "1";
        let low_sci_str = format!("1.0e{}", min_exp - 1);

        // if MAX_FIXED_DECIMAL_POINT = 3 + 17 => [d-d]000.0 is the limit => [d-d]e3 is the limit
        // for std as fixed-format
        let digits = <NumFmtBuffer as NumFormat<f64, u64>>::MAX_DIGITS; // 17 for f64
        let max_exp = <NumFmtBuffer as NumFormat<f64, u64>>::MAX_FIXED_DECIMAL_POINT - 1;
        let max_fix = 2.0 * 10.0_f64.powi(max_exp);
        let high_fix = max_fix * 10.0;
        let max_fix_str = "2".to_string() + &"0".repeat(max_exp.abs() as usize) + ".0";
        let high_fix_str = "2".to_string() + &"0".repeat(max_exp.abs() as usize + 1) + ".0";
        let high_sci_str = format!("2.0e{}", max_exp + 1);

        Self {
            min_exp, min_fix, low_fix, min_fix_str, low_fix_str, low_sci_str,
            digits,
            max_exp, max_fix, high_fix, max_fix_str, high_fix_str, high_sci_str,
        }
    }
}
