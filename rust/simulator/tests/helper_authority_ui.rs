//! Compile-fail tests for non-authoritative generated helper surfaces.

#[test]
fn generated_helper_reports_do_not_expose_authoritative_fields() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/ui/generated_helper_theorem_profile.rs");
    t.compile_fail("tests/ui/generated_helper_checkpoints.rs");
    t.compile_fail("tests/ui/generated_helper_normalized_observability.rs");
    t.compile_fail("tests/ui/generated_helper_replay_contract.rs");
}
