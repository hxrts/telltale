#[test]
fn choreography_macro_ui() {
    let t = trybuild::TestCases::new();
    t.pass("tests/ui/pass/multiparty_protocol.rs");
    t.compile_fail("tests/ui/fail/duplicate_roles.rs");
    t.compile_fail("tests/ui/fail/undefined_role.rs");
    t.compile_fail("tests/ui/fail/conflicting_msg_payload.rs");
    t.compile_fail("tests/ui/fail/ambiguous_message_derive.rs");
}
