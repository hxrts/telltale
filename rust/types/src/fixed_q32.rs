//! Safe fixed-point wrapper for deterministic fractional arithmetic.

use fixed::types::I32F32;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;
use std::iter::Sum;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::str::FromStr;

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

    /// -1.
    #[must_use]
    pub const fn neg_one() -> Self {
        Self::from_bits(-Self::SCALE)
    }

    /// 1/2.
    #[must_use]
    pub fn half() -> Self {
        Self::from_bits(Self::SCALE / 2)
    }

    /// Construct from an integer, returning an error on overflow.
    ///
    /// # Errors
    ///
    /// Returns [`FixedQ32Error::Overflow`] if the value is out of range.
    pub fn try_from_i64(value: i64) -> Result<Self, FixedQ32Error> {
        I32F32::checked_from_num(value)
            .map(Self)
            .ok_or(FixedQ32Error::Overflow)
    }

    /// Construct from an unsigned integer, returning an error on overflow.
    ///
    /// # Errors
    ///
    /// Returns [`FixedQ32Error::Overflow`] if the value is out of range.
    pub fn try_from_u64(value: u64) -> Result<Self, FixedQ32Error> {
        I32F32::checked_from_num(value)
            .map(Self)
            .ok_or(FixedQ32Error::Overflow)
    }

    /// Construct from usize, returning an error on overflow.
    ///
    /// # Errors
    ///
    /// Returns [`FixedQ32Error::Overflow`] if the value is out of range.
    pub fn try_from_usize(value: usize) -> Result<Self, FixedQ32Error> {
        I32F32::checked_from_num(value)
            .map(Self)
            .ok_or(FixedQ32Error::Overflow)
    }

    /// Construct an exact fixed-point ratio `num / den`.
    ///
    /// # Errors
    ///
    /// Returns [`FixedQ32Error::DivisionByZero`] if `den` is zero, or
    /// [`FixedQ32Error::Overflow`] if the result is out of range.
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
    ///
    /// # Errors
    ///
    /// Returns [`FixedQ32Error::Overflow`] if the result is out of range.
    pub fn from_ppm(ppm: u32) -> Result<Self, FixedQ32Error> {
        let n = I32F32::checked_from_num(ppm).ok_or(FixedQ32Error::Overflow)?;
        let d = I32F32::checked_from_num(PPM_SCALE).ok_or(FixedQ32Error::Overflow)?;
        n.checked_div(d).map(Self).ok_or(FixedQ32Error::Overflow)
    }

    /// Parse from a decimal string.
    ///
    /// # Errors
    ///
    /// Returns [`FixedQ32Error::Overflow`] if parsing fails or the result is out of range.
    pub fn from_decimal_str(s: &str) -> Result<Self, FixedQ32Error> {
        s.parse::<I32F32>()
            .map(Self)
            .map_err(|_| FixedQ32Error::Overflow)
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

    /// Saturating addition.
    #[must_use]
    pub fn saturating_add(self, rhs: Self) -> Self {
        Self(self.0.saturating_add(rhs.0))
    }

    /// Saturating subtraction.
    #[must_use]
    pub fn saturating_sub(self, rhs: Self) -> Self {
        Self(self.0.saturating_sub(rhs.0))
    }

    /// Saturating multiplication.
    #[must_use]
    pub fn saturating_mul(self, rhs: Self) -> Self {
        Self(self.0.saturating_mul(rhs.0))
    }

    /// Saturating division.
    #[must_use]
    pub fn saturating_div(self, rhs: Self) -> Self {
        Self(self.0.saturating_div(rhs.0))
    }

    /// Saturating multiplication by an integer.
    #[must_use]
    pub fn saturating_mul_int(self, rhs: i64) -> Self {
        Self(self.0.saturating_mul_int(rhs))
    }

    /// Saturating division by an integer.
    #[must_use]
    pub fn saturating_div_int(self, rhs: i64) -> Self {
        Self(self.0.saturating_div_int(rhs))
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

    /// Absolute value.
    #[must_use]
    pub fn abs(self) -> Self {
        Self(self.0.abs())
    }

    /// Clamp to bounds.
    #[must_use]
    pub fn clamp(self, lo: Self, hi: Self) -> Self {
        if self < lo {
            lo
        } else if self > hi {
            hi
        } else {
            self
        }
    }

    /// Minimum.
    #[must_use]
    pub fn min(self, rhs: Self) -> Self {
        if self <= rhs {
            self
        } else {
            rhs
        }
    }

    /// Maximum.
    #[must_use]
    pub fn max(self, rhs: Self) -> Self {
        if self >= rhs {
            self
        } else {
            rhs
        }
    }

    /// Whether the value is strictly positive.
    #[must_use]
    pub fn is_positive(self) -> bool {
        self > Self::zero()
    }

    /// Whether the value is strictly negative.
    #[must_use]
    pub fn is_negative(self) -> bool {
        self < Self::zero()
    }

    /// Square the value (saturating).
    #[must_use]
    pub fn square(self) -> Self {
        self.saturating_mul(self)
    }

    /// Integer power using repeated multiplication.
    #[must_use]
    pub fn powi(self, exp: u32) -> Self {
        let mut out = Self::one();
        for _ in 0..exp {
            out = out.saturating_mul(self);
        }
        out
    }

    /// Saturating square root for non-negative values; returns zero for negatives.
    #[must_use]
    pub fn sqrt(self) -> Self {
        if self <= Self::zero() {
            return Self::zero();
        }
        // Newton iteration over fixed point.
        let two = Self::from_bits(2 * Self::SCALE);
        let mut x = self.max(Self::one());
        for _ in 0..16 {
            let q = self.saturating_div(x);
            x = x.saturating_add(q).saturating_div(two);
        }
        x
    }

    /// Approximate tanh using a rational approximation.
    ///
    /// tanh(x) ~= x * (27 + x^2) / (27 + 9x^2), clipped to [-1, 1].
    #[must_use]
    pub fn tanh_approx(self) -> Self {
        let one = Self::one();
        let three = Self::from_bits(3 * Self::SCALE);
        if self >= three {
            return one;
        }
        if self <= -three {
            return -one;
        }
        let nine = Self::from_bits(9 * Self::SCALE);
        let twenty_seven = Self::from_bits(27 * Self::SCALE);
        let x2 = self.square();
        let num = self.saturating_mul(twenty_seven.saturating_add(x2));
        let den = twenty_seven.saturating_add(nine.saturating_mul(x2));
        num.saturating_div(den).clamp(-one, one)
    }

    /// Approximate hyperbolic tangent.
    #[must_use]
    pub fn tanh(self) -> Self {
        self.tanh_approx()
    }

    /// Fixed-point values are always finite.
    #[must_use]
    pub const fn is_finite(self) -> bool {
        // Self is unused: fixed-point values are always finite by construction
        let _ = self;
        true
    }

    /// Convert to i64 after floor rounding.
    ///
    /// # Errors
    ///
    /// Returns [`FixedQ32Error::Overflow`] if the result is out of range.
    pub fn to_i64_floor(self) -> Result<i64, FixedQ32Error> {
        self.floor()
            .0
            .checked_to_num()
            .ok_or(FixedQ32Error::Overflow)
    }

    /// Convert to i64 after ceiling rounding.
    ///
    /// # Errors
    ///
    /// Returns [`FixedQ32Error::Overflow`] if the result is out of range.
    pub fn to_i64_ceil(self) -> Result<i64, FixedQ32Error> {
        self.ceil()
            .0
            .checked_to_num()
            .ok_or(FixedQ32Error::Overflow)
    }

    /// Convert to i64 after nearest rounding.
    ///
    /// # Errors
    ///
    /// Returns [`FixedQ32Error::Overflow`] if the result is out of range.
    pub fn to_i64_round(self) -> Result<i64, FixedQ32Error> {
        self.round()
            .0
            .checked_to_num()
            .ok_or(FixedQ32Error::Overflow)
    }

    /// Convert to usize after nearest rounding.
    ///
    /// # Errors
    ///
    /// Returns [`FixedQ32Error::Overflow`] if the result is out of range or negative.
    pub fn to_usize_round(self) -> Result<usize, FixedQ32Error> {
        let i = self.to_i64_round()?;
        if i < 0 {
            return Err(FixedQ32Error::Overflow);
        }
        usize::try_from(i).map_err(|_| FixedQ32Error::Overflow)
    }

    /// Convert to u64 after nearest rounding.
    ///
    /// # Errors
    ///
    /// Returns [`FixedQ32Error::Overflow`] if the result is out of range or negative.
    pub fn to_u64_round(self) -> Result<u64, FixedQ32Error> {
        let i = self.to_i64_round()?;
        if i < 0 {
            return Err(FixedQ32Error::Overflow);
        }
        u64::try_from(i).map_err(|_| FixedQ32Error::Overflow)
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
        struct FixedQ32Visitor;

        impl<'de> serde::de::Visitor<'de> for FixedQ32Visitor {
            type Value = FixedQ32;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str(
                    "a fixed-point number encoded as raw bits (i64/u64) or decimal string",
                )
            }

            fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(FixedQ32::from_bits(v))
            }

            fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                let bits = i64::try_from(v).map_err(|_| E::custom(FixedQ32Error::Overflow))?;
                Ok(FixedQ32::from_bits(bits))
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                FixedQ32::from_decimal_str(v).map_err(E::custom)
            }

            fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                self.visit_str(&v)
            }
        }

        deserializer.deserialize_any(FixedQ32Visitor)
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

impl From<f64> for FixedQ32 {
    fn from(value: f64) -> Self {
        I32F32::checked_from_num(value)
            .map(Self)
            .unwrap_or_else(|| {
                if value.is_sign_negative() {
                    Self(I32F32::MIN)
                } else {
                    Self(I32F32::MAX)
                }
            })
    }
}

impl TryFrom<usize> for FixedQ32 {
    type Error = FixedQ32Error;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        Self::try_from_usize(value)
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

impl Add for FixedQ32 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.saturating_add(rhs)
    }
}

impl AddAssign for FixedQ32 {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.saturating_add(rhs);
    }
}

impl Sub for FixedQ32 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.saturating_sub(rhs)
    }
}

impl SubAssign for FixedQ32 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.saturating_sub(rhs);
    }
}

impl Mul for FixedQ32 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.saturating_mul(rhs)
    }
}

impl MulAssign for FixedQ32 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.saturating_mul(rhs);
    }
}

impl Div for FixedQ32 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self.saturating_div(rhs)
    }
}

impl DivAssign for FixedQ32 {
    fn div_assign(&mut self, rhs: Self) {
        *self = self.saturating_div(rhs);
    }
}

impl Neg for FixedQ32 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::zero().saturating_sub(self)
    }
}

include!("fixed_q32/iter_and_parse_impls.rs");

#[cfg(test)]
mod tests {
    include!("fixed_q32/tests.rs");
}
