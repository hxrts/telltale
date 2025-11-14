#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

// Basic test to verify effect system compiles

#[test]
fn test_effect_traits_compile() {
    // Just verify the module structure compiles
    // The crate name in tests is the library name with underscores
    use rumpsteak_aura_choreography::effects::RoleId;

    // Basic role enum
    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
    #[allow(dead_code)]
    enum TestRole {
        A,
        B,
    }

    // Verify it implements RoleId
    fn assert_role_id<T: RoleId>() {}
    assert_role_id::<TestRole>();
}
