use super::*;
use proptest::prelude::*;

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
    assert_eq!(x.to_bits(), decoded.to_bits());
}

#[test]
fn serde_rejects_float_tokens() {
    let decoded = serde_json::from_str::<FixedQ32>("1.5");
    assert!(decoded.is_err());
}

#[test]
fn ppm_endpoints() {
    let zero = FixedQ32::from_ppm(0).expect("zero ppm");
    let one = FixedQ32::from_ppm(PPM_SCALE).expect("one ppm");
    assert_eq!(zero, FixedQ32::zero());
    assert_eq!(one, FixedQ32::one());
}

#[test]
fn tanh_approx_bounds() {
    let low = FixedQ32::from_ratio(-10, 1).expect("fit").tanh_approx();
    let high = FixedQ32::from_ratio(10, 1).expect("fit").tanh_approx();
    assert_eq!(low, FixedQ32::neg_one());
    assert_eq!(high, FixedQ32::one());
}

proptest! {
    #[test]
    fn from_ppm_stays_in_unit_interval(ppm in 0u32..=PPM_SCALE) {
        let value = FixedQ32::from_ppm(ppm).expect("ppm in range is representable");
        prop_assert!(value >= FixedQ32::zero());
        prop_assert!(value <= FixedQ32::one());
    }

    #[test]
    fn tanh_approx_is_clamped(raw in any::<i32>()) {
        let x = FixedQ32::from_bits(i64::from(raw) << FixedQ32::FRACTIONAL_BITS);
        let y = x.tanh_approx();
        prop_assert!(y >= FixedQ32::neg_one());
        prop_assert!(y <= FixedQ32::one());
    }
}
