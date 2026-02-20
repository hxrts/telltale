#![cfg(not(target_arch = "wasm32"))]
//! Contract test for threaded conformance lane execution.

#[test]
#[allow(clippy::assertions_on_constants)]
fn strict_conformance_env_requires_multi_thread_feature() {
    if std::env::var_os("TT_EXPECT_MULTI_THREAD").is_none() {
        return;
    }
    assert!(
        cfg!(feature = "multi-thread"),
        "TT_EXPECT_MULTI_THREAD=1 requires `--features multi-thread` so threaded conformance lanes cannot be skipped"
    );
}

#[cfg(feature = "multi-thread")]
#[test]
#[allow(clippy::assertions_on_constants)]
fn threaded_feature_lane_is_active() {
    assert!(cfg!(feature = "multi-thread"));
}
