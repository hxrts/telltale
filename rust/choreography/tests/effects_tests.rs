#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

// Basic test to verify effect system compiles

#[test]
fn test_effect_traits_compile() {
    // Just verify the module structure compiles
    // The crate name in tests is the library name with underscores
    use telltale_choreography::effects::{LabelId, RoleId};
    use telltale_choreography::RoleName;

    // Basic role enum
    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
    #[allow(dead_code)]
    enum TestRole {
        A,
        B,
    }

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
    enum TestLabel {
        Default,
    }

    impl LabelId for TestLabel {
        fn as_str(&self) -> &'static str {
            "default"
        }

        fn from_str(label: &str) -> Option<Self> {
            match label {
                "default" => Some(TestLabel::Default),
                _ => None,
            }
        }
    }

    impl RoleId for TestRole {
        type Label = TestLabel;

        fn role_name(&self) -> RoleName {
            match self {
                TestRole::A => RoleName::from_static("A"),
                TestRole::B => RoleName::from_static("B"),
            }
        }
    }

    // Verify it implements RoleId
    fn assert_role_id<T: RoleId>() {}
    assert_role_id::<TestRole>();
}
