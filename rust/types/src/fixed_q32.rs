//! Safe fixed-point wrapper for deterministic fractional arithmetic.

use fixed::types::I32F32;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;

/// Parts-per-million scale for probability-style values.
pub const PPM_SCALE: u32 = 1_000_000;

/// Error type for safe fixed-point construction and conversion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FixedQ32Error {
    /// Conversion or arithmetic exceeded representable range.
    Overflow,
    /// Division by zero was requested.
    DivisionByZero,
}

impl fmt::Display for FixedQ32Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Overflow => write!(f, "fixed-point overflow"),
            Self::DivisionByZero => write!(f, "fixed-point division by zero"),
        }
    }
}

impl std::error::Error for FixedQ32Error {}

/// Signed Q32.32 fixed-point number.
///
/// This wrapper intentionally exposes only checked and explicit operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct FixedQ32(I32F32);

impl FixedQ32 {
    /// Fractional bits in the Q32.32 encoding.
    pub const FRACTIONAL_BITS: u32 = 32;
    /// Raw scaling factor (2^32).
    pub const SCALE: i64 = 1_i64 << Self::FRACTIONAL_BITS;

    /// Construct from raw two's-complement bits.
    #[must_use]
    pub const fn from_bits(bits: i64) -> Self {
        Self(I32F32::from_bits(bits))
    }

    /// Return the raw two's-complement bits.
    #[must_use]
    pub const fn to_bits(self) -> i64 {
        self.0.to_bits()
    }

    /// Zero.
    #[must_use]
    pub const fn zero() -> Self {
        Self::from_bits(0)
    }

    /// One.
    #[must_use]
    pub const fn one() -> Self {
        Self::from_bits(Self::SCALE)
    }

    /// Construct from an integer, returning an error on overflow.
    pub fn try_from_i64(value: i64) -> Result<Self, FixedQ32Error> {
        I32F32::checked_from_num(value)
            .map(Self)
            .ok_or(FixedQ32Error::Overflow)
    }

    /// Construct from an unsigned integer, returning an error on overflow.
    pub fn try_from_u64(value: u64) -> Result<Self, FixedQ32Error> {
        I32F32::checked_from_num(value)
            .map(Self)
            .ok_or(FixedQ32Error::Overflow)
    }

    /// Construct an exact fixed-point ratio `num / den`.
    pub fn from_ratio(num: i64, den: i64) -> Result<Self, FixedQ32Error> {
        if den == 0 {
            return Err(FixedQ32Error::DivisionByZero);
        }
        let n = I32F32::checked_from_num(num).ok_or(FixedQ32Error::Overflow)?;
        let d = I32F32::checked_from_num(den).ok_or(FixedQ32Error::Overflow)?;
        n.checked_div(d).map(Self).ok_or(FixedQ32Error::Overflow)
    }

    /// Construct a probability-like value from parts-per-million.
    ///
    /// `0` maps to `0.0`, `1_000_000` maps to `1.0`.
    pub fn from_ppm(ppm: u32) -> Result<Self, FixedQ32Error> {
        let n = I32F32::checked_from_num(ppm).ok_or(FixedQ32Error::Overflow)?;
        let d = I32F32::checked_from_num(PPM_SCALE).ok_or(FixedQ32Error::Overflow)?;
        n.checked_div(d).map(Self).ok_or(FixedQ32Error::Overflow)
    }

    /// Checked addition.
    #[must_use]
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        self.0.checked_add(rhs.0).map(Self)
    }

    /// Checked subtraction.
    #[must_use]
    pub fn checked_sub(self, rhs: Self) -> Option<Self> {
        self.0.checked_sub(rhs.0).map(Self)
    }

    /// Checked multiplication.
    #[must_use]
    pub fn checked_mul(self, rhs: Self) -> Option<Self> {
        self.0.checked_mul(rhs.0).map(Self)
    }

    /// Checked division.
    #[must_use]
    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        self.0.checked_div(rhs.0).map(Self)
    }

    /// Floor rounding.
    #[must_use]
    pub fn floor(self) -> Self {
        Self(self.0.floor())
    }

    /// Ceiling rounding.
    #[must_use]
    pub fn ceil(self) -> Self {
        Self(self.0.ceil())
    }

    /// Round to nearest with ties away from zero.
    #[must_use]
    pub fn round(self) -> Self {
        Self(self.0.round())
    }

    /// Convert to i64 after floor rounding.
    pub fn to_i64_floor(self) -> Result<i64, FixedQ32Error> {
        self.floor()
            .0
            .checked_to_num()
            .ok_or(FixedQ32Error::Overflow)
    }

    /// Convert to i64 after ceiling rounding.
    pub fn to_i64_ceil(self) -> Result<i64, FixedQ32Error> {
        self.ceil()
            .0
            .checked_to_num()
            .ok_or(FixedQ32Error::Overflow)
    }

    /// Convert to i64 after nearest rounding.
    pub fn to_i64_round(self) -> Result<i64, FixedQ32Error> {
        self.round()
            .0
            .checked_to_num()
            .ok_or(FixedQ32Error::Overflow)
    }
}

impl fmt::Display for FixedQ32 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Serialize for FixedQ32 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_i64(self.to_bits())
    }
}

impl<'de> Deserialize<'de> for FixedQ32 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let bits = i64::deserialize(deserializer)?;
        Ok(Self::from_bits(bits))
    }
}

impl TryFrom<i64> for FixedQ32 {
    type Error = FixedQ32Error;

    fn try_from(value: i64) -> Result<Self, Self::Error> {
        Self::try_from_i64(value)
    }
}

impl TryFrom<u64> for FixedQ32 {
    type Error = FixedQ32Error;

    fn try_from(value: u64) -> Result<Self, Self::Error> {
        Self::try_from_u64(value)
    }
}

impl TryFrom<FixedQ32> for i64 {
    type Error = FixedQ32Error;

    fn try_from(value: FixedQ32) -> Result<Self, Self::Error> {
        value.to_i64_round()
    }
}

impl TryFrom<FixedQ32> for u64 {
    type Error = FixedQ32Error;

    fn try_from(value: FixedQ32) -> Result<Self, Self::Error> {
        let i = value.to_i64_round()?;
        if i < 0 {
            return Err(FixedQ32Error::Overflow);
        }
        u64::try_from(i).map_err(|_| FixedQ32Error::Overflow)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn one_has_expected_scale_bits() {
        assert_eq!(FixedQ32::one().to_bits(), FixedQ32::SCALE);
    }

    #[test]
    fn ratio_roundtrip() {
        let x = FixedQ32::from_ratio(3, 2).expect("ratio should fit");
        assert_eq!(x.to_i64_floor().expect("floor"), 1);
        assert_eq!(x.to_i64_ceil().expect("ceil"), 2);
    }

    #[test]
    fn checked_overflow_returns_none() {
        let max = FixedQ32::from_bits(i64::MAX);
        assert!(max.checked_add(FixedQ32::one()).is_none());
    }

    #[test]
    fn serde_uses_raw_bits() {
        let x = FixedQ32::from_ratio(7, 3).expect("ratio should fit");
        let encoded = serde_json::to_string(&x).expect("serialize");
        let decoded: FixedQ32 = serde_json::from_str(&encoded).expect("deserialize");
        assert_eq!(x, decoded);
    }

    #[test]
    fn ppm_endpoints() {
        let zero = FixedQ32::from_ppm(0).expect("zero ppm");
        let one = FixedQ32::from_ppm(PPM_SCALE).expect("one ppm");
        assert_eq!(zero, FixedQ32::zero());
        assert_eq!(one, FixedQ32::one());
    }
}
