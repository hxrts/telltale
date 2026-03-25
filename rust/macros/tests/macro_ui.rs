#[test]
fn choreography_macro_ui() {
    let t = trybuild::TestCases::new();
    t.pass("tests/ui/pass/multiparty_protocol.rs");
    t.pass("tests/ui/pass/choice_protocol.rs");
    t.pass("tests/ui/pass/broadcast_protocol.rs");
    t.pass("tests/ui/pass/namespaced_protocol.rs");
    t.pass("tests/ui/pass/profiled_protocol.rs");
    t.pass("tests/ui/pass/role_derive.rs");
    t.compile_fail("tests/ui/fail/string_literal_protocol.rs");
    t.compile_fail("tests/ui/fail/legacy_brace_protocol.rs");
    t.compile_fail("tests/ui/fail/duplicate_roles.rs");
    t.compile_fail("tests/ui/fail/undefined_role.rs");
    t.compile_fail("tests/ui/fail/conflicting_msg_payload.rs");
    t.compile_fail("tests/ui/fail/ambiguous_message_derive.rs");
    t.compile_fail("tests/ui/fail/missing_message_attr.rs");
    t.compile_fail("tests/ui/fail/missing_route_attr.rs");
}
