use super::{parse_choreography_str, parse_declared_operation};
use crate::ast::{Protocol, ValidationError};

const SOURCE: &str = r#"
agreement_profile Selected
  visibility immediate
  rule no_agreement
  usable_at none
  finalized_at none
  evidence witness
operation Flow at A progress Progress within bounded agreement Selected =
  begin Flow
  await Flow
  resolve Flow as Success
protocol Parent =
  roles A, B
  A -> B : Start
"#;

#[test]
fn selected_empty_operation_retains_original_owner_and_full_parent_role_scope() {
    let parent = parse_choreography_str(SOURCE).expect("valid original parent");
    let (operation, selected) = parse_declared_operation(&parent, "Flow")
        .expect("operation-local boundaries need no fabricated communication");
    assert_eq!(operation.owner_role, "A");
    assert_eq!(selected.roles, parent.roles);
    assert_eq!(selected.attrs, parent.attrs);
    assert!(matches!(&selected.protocol, Protocol::Begin { .. }));
    assert!(selected
        .roles
        .iter()
        .all(|role| !selected.protocol.mentions_role(role)));
    assert!(matches!(
        selected.validate(),
        Err(ValidationError::UnusedRole(_))
    ));
    assert!(selected.validate_selected_operation(&operation).is_ok());
}

#[test]
fn ordinary_parent_unused_role_is_still_rejected_before_operation_selection() {
    let mut unused_parent = parse_choreography_str(SOURCE).expect("valid parent");
    unused_parent.protocol = Protocol::End;
    let error = parse_declared_operation(&unused_parent, "Flow").unwrap_err();
    assert!(error.to_string().contains("Role A is not used in protocol"));
}

#[test]
fn selected_operation_still_rejects_undeclared_body_role() {
    let source = SOURCE.replace("  await Flow", "  A -> Foreign : Invalid\n  await Flow");
    let parent = parse_choreography_str(&source).expect("parent role scope is unchanged");
    let error = parse_declared_operation(&parent, "Flow").unwrap_err();
    assert!(error.to_string().contains("Foreign"));
}

#[test]
fn selected_operation_requires_original_declaration_and_declared_owner() {
    let parent = parse_choreography_str(SOURCE).expect("parent");
    let (mut operation, selected) = parse_declared_operation(&parent, "Flow").expect("selected");
    operation.name = "Foreign".into();
    assert!(matches!(
        selected.validate_selected_operation(&operation),
        Err(ValidationError::ExtensionError(_))
    ));
    let source = SOURCE.replace("Flow at A", "Flow at Foreign");
    let parent =
        parse_choreography_str(&source).expect("ordinary parent communication remains valid");
    let error = parse_declared_operation(&parent, "Flow").unwrap_err();
    assert!(error
        .to_string()
        .contains("Role Foreign not declared in choreography"));
}
