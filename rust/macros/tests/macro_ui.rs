//! UI test harness for procedural macro compile-time diagnostics.
#[test]
fn choreography_macro_ui() {
    let t = trybuild::TestCases::new();
    t.pass("tests/ui/pass/multiparty_protocol.rs");
    t.pass("tests/ui/pass/choice_protocol.rs");
    t.pass("tests/ui/pass/broadcast_protocol.rs");
    t.pass("tests/ui/pass/authority_surface.rs");
    t.pass("tests/ui/pass/authority_control_flow.rs");
    t.pass("tests/ui/pass/commitment_surface.rs");
    t.pass("tests/ui/pass/namespaced_protocol.rs");
    t.pass("tests/ui/pass/profiled_protocol.rs");
    t.pass("tests/ui/pass/role_derive.rs");
    t.pass("tests/ui/pass/viewer_ownership_markers.rs");
    t.compile_fail("tests/ui/fail/string_literal_protocol.rs");
    t.compile_fail("tests/ui/fail/legacy_brace_protocol.rs");
    t.compile_fail("tests/ui/fail/duplicate_roles.rs");
    t.compile_fail("tests/ui/fail/undefined_role.rs");
    t.compile_fail("tests/ui/fail/conflicting_msg_payload.rs");
    t.compile_fail("tests/ui/fail/ambiguous_message_derive.rs");
    t.compile_fail("tests/ui/fail/authority_linear_choice_divergence.rs");
    t.compile_fail("tests/ui/fail/authority_observational_choice_with_check.rs");
    t.compile_fail("tests/ui/fail/missing_message_attr.rs");
    t.compile_fail("tests/ui/fail/missing_route_attr.rs");
    t.compile_fail("tests/ui/fail/actor_owned_missing_label.rs");
    t.compile_fail("tests/ui/fail/observed_only_rejects_args.rs");
    t.compile_fail("tests/ui/fail/weak_identifier_rejects_const.rs");
}
