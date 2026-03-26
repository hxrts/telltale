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
