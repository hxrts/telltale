// Unit tests for effects code generation.
use super::*;
use crate::ast::{Annotations, MessageType, Protocol, Role};

#[test]
fn test_generate_simple_protocol() {
    let choreography = Choreography {
        name: format_ident!("SimpleProtocol"),
        namespace: None,
        roles: vec![
            Role::new(format_ident!("Client")).expect("valid role"),
            Role::new(format_ident!("Server")).expect("valid role"),
        ],
        protocol: Protocol::End,
        attrs: std::collections::HashMap::new(),
    };

    let code = generate_effects_protocol(&choreography);
    let code_str = code.to_string();

    assert!(code_str.contains("enum Role"));
    assert!(code_str.contains("Client"));
    assert!(code_str.contains("Server"));
    assert!(code_str.contains("run_client"));
    assert!(code_str.contains("run_server"));
}

#[test]
fn test_message_codegen_is_deterministic_and_sorted() {
    let alice = Role::new(format_ident!("Alice")).expect("valid role");
    let bob = Role::new(format_ident!("Bob")).expect("valid role");

    let protocol = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: MessageType {
            name: format_ident!("Zeta"),
            type_annotation: None,
            payload: None,
        },
        continuation: Box::new(Protocol::Send {
            from: alice,
            to: bob,
            message: MessageType {
                name: format_ident!("Alpha"),
                type_annotation: None,
                payload: None,
            },
            continuation: Box::new(Protocol::End),
            annotations: Annotations::new(),
            from_annotations: Annotations::new(),
            to_annotations: Annotations::new(),
        }),
        annotations: Annotations::new(),
        from_annotations: Annotations::new(),
        to_annotations: Annotations::new(),
    };

    let code = protocol_types::generate_message_types(&protocol).to_string();
    let alpha_idx = code.find("struct Alpha").expect("find Alpha type");
    let zeta_idx = code.find("struct Zeta").expect("find Zeta type");
    assert!(alpha_idx < zeta_idx);
}

#[test]
fn effect_generator_refuses_nested_authority_binding_instead_of_erasing_it() {
    use crate::ast::{AuthorityBindingMode, AuthorityExpr};
    let protocol = Protocol::Let {
        execution_role: None,
        name: "observed".into(),
        mode: AuthorityBindingMode::Observe,
        expr: AuthorityExpr::Observe {
            effect: "Runtime".into(),
            operation: "watch".into(),
            args: vec![],
        },
        linear: false,
        continuation: Box::new(Protocol::End),
    };
    let choreography = Choreography {
        name: format_ident!("AuthorityGuard"),
        namespace: None,
        roles: vec![
            Role::new(format_ident!("A")).unwrap(),
            Role::new(format_ident!("B")).unwrap(),
        ],
        protocol: Protocol::Rec {
            label: format_ident!("Round"),
            body: Box::new(protocol),
        },
        attrs: std::collections::HashMap::new(),
    };
    let tokens = generate_effects_protocol(&choreography).to_string();
    assert!(tokens.contains("compile_error"));
    assert!(!tokens.contains("run_a"));
}

#[test]
fn explicit_placement_is_not_erased_by_direct_effect_generation() {
    let choreography = crate::compiler::parser::parse_choreography_str(
        "protocol Placed =\n  roles A, B\n  let value at B = Nothing\n  A -> B : Commit\n",
    )
    .unwrap();
    let generated =
        crate::compiler::effects_codegen::generate_effects_protocol(&choreography).to_string();
    assert!(generated.contains("compile_error"));
    assert!(!generated.contains("pub fn b_program"));
}
