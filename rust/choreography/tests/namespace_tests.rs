#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

/// Tests for namespace support in choreographic protocols
///
/// This module tests the namespace functionality added to support multiple
/// choreographies in the same crate without type conflicts.
use telltale_choreography::compiler::{
    generate_choreography_code_with_namespacing, parse_choreography_str, project,
};

#[test]
fn test_parse_simple_namespaced_choreography() {
    let input = r#"
module protocol_a exposing (SimpleProtocol)
protocol SimpleProtocol = {
    roles Alice, Bob
    Alice -> Bob: Message
}
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Failed to parse namespaced choreography: {:?}",
        result.err()
    );

    let choreo = result.unwrap();
    assert_eq!(choreo.name.to_string(), "SimpleProtocol");
    assert_eq!(choreo.namespace, Some("protocol_a".to_string()));
    assert_eq!(choreo.roles.len(), 2);
}

#[test]
fn test_parse_choreography_without_namespace() {
    let input = r#"
protocol SimpleProtocol = {
    roles Alice, Bob
    Alice -> Bob: Message
}
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Failed to parse non-namespaced choreography: {:?}",
        result.err()
    );

    let choreo = result.unwrap();
    assert_eq!(choreo.name.to_string(), "SimpleProtocol");
    assert_eq!(choreo.namespace, None);
    assert_eq!(choreo.roles.len(), 2);
}

#[test]
fn test_qualified_name_with_namespace() {
    let input = r#"
module threshold_ceremony exposing (ThresholdProtocol)
protocol ThresholdProtocol = {
    roles Coordinator, Signer1, Signer2
    Coordinator -> Signer1: Request
    Signer1 -> Coordinator: Response
}
"#;

    let choreo = parse_choreography_str(input).unwrap();
    assert_eq!(
        choreo.qualified_name(),
        "threshold_ceremony::ThresholdProtocol"
    );
}

#[test]
fn test_qualified_name_without_namespace() {
    let input = r#"
protocol SimpleProtocol = {
    roles Alice, Bob
    Alice -> Bob: Message
}
"#;

    let choreo = parse_choreography_str(input).unwrap();
    assert_eq!(choreo.qualified_name(), "SimpleProtocol");
}

#[test]
fn test_invalid_namespace_names() {
    // Test namespace with invalid characters
    let input = r#"
module invalid-name-with-dashes exposing (TestProtocol)
protocol TestProtocol = {
    roles A, B
    A -> B: Msg
}
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_err(), "Should reject namespace with dashes");

    // Test empty namespace
    let input = r#"
module  exposing (TestProtocol)
protocol TestProtocol = {
    roles A, B
    A -> B: Msg
}
"#;

    let result = parse_choreography_str(input);
    assert!(result.is_err(), "Should reject empty namespace");
}

#[test]
fn test_valid_namespace_names() {
    // Test namespace with underscores
    let input = r#"
module valid_namespace_name exposing (TestProtocol)
protocol TestProtocol = {
    roles A, B
    A -> B: Msg
}
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Should accept namespace with underscores: {:?}",
        result.err()
    );

    // Test namespace with numbers
    let input = r#"
module namespace123 exposing (TestProtocol)
protocol TestProtocol = {
    roles A, B
    A -> B: Msg
}
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Should accept namespace with numbers: {:?}",
        result.err()
    );
}

#[test]
fn test_namespace_code_generation() {
    let input = r#"
module test_namespace exposing (TestProtocol)
protocol TestProtocol = {
    roles Alice, Bob
    Alice -> Bob: Message
}
"#;

    let choreo = parse_choreography_str(input).unwrap();

    // Project to local types
    let mut local_types = Vec::new();
    for role in &choreo.roles {
        let local_type = project(&choreo, role).expect("Projection should succeed");
        local_types.push((role.clone(), local_type));
    }

    // Generate code with namespace
    let generated_code = generate_choreography_code_with_namespacing(&choreo, &local_types);
    let code_string = generated_code.to_string();

    // Check that the code is wrapped in a module
    assert!(
        code_string.contains("pub mod test_namespace"),
        "Generated code should contain namespace module: {}",
        code_string
    );
    assert!(
        code_string.contains("use super :: *"),
        "Generated code should contain super import: {}",
        code_string
    );
}

#[test]
fn test_non_namespace_code_generation() {
    let input = r#"
protocol TestProtocol = {
    roles Alice, Bob
    Alice -> Bob: Message
}
"#;

    let choreo = parse_choreography_str(input).unwrap();

    // Project to local types
    let mut local_types = Vec::new();
    for role in &choreo.roles {
        let local_type = project(&choreo, role).expect("Projection should succeed");
        local_types.push((role.clone(), local_type));
    }

    // Generate code without namespace
    let generated_code = generate_choreography_code_with_namespacing(&choreo, &local_types);
    let code_string = generated_code.to_string();

    // Check that the code does not contain a namespace module (only annotations module is allowed)
    assert!(
        !code_string.contains("pub mod test") && !code_string.contains("pub mod Test"),
        "Non-namespaced code should not contain namespace module wrapper"
    );
    // Annotations module is expected for enhanced annotation support
    assert!(
        code_string.contains("pub mod annotations"),
        "Generated code should contain annotations module for enhanced annotation support"
    );
}

#[test]
fn test_multiple_namespaced_protocols_compilation() {
    // This test verifies that multiple protocols with different namespaces
    // can be defined without conflicts (compilation test)

    let protocol_a = r#"
module protocol_a exposing (ProtocolA)
protocol ProtocolA = {
    roles Alice, Bob
    Alice -> Bob: Message
}
"#;

    let protocol_b = r#"
module protocol_b exposing (ProtocolB)
protocol ProtocolB = {
    roles Alice, Bob
    Alice -> Bob: Message
}
"#;

    let choreo_a = parse_choreography_str(protocol_a).unwrap();
    let choreo_b = parse_choreography_str(protocol_b).unwrap();

    // Both should parse successfully
    assert_eq!(choreo_a.namespace, Some("protocol_a".to_string()));
    assert_eq!(choreo_b.namespace, Some("protocol_b".to_string()));

    // Both should have the same role names but different namespaces
    assert_eq!(choreo_a.roles.len(), 2);
    assert_eq!(choreo_b.roles.len(), 2);
    assert_ne!(choreo_a.qualified_name(), choreo_b.qualified_name());
}

#[test]
fn test_namespace_with_complex_protocol() {
    let input = r#"
module complex_protocol exposing (ComplexProtocol)
protocol ComplexProtocol = {
    roles Coordinator, Worker1, Worker2, Observer
    
    Coordinator -> Worker1: Task
    Coordinator -> Worker2: Task
    
    choice at Worker1 {
        success -> {
            Worker1 -> Coordinator: Success
        }
        failure -> {
            Worker1 -> Coordinator: Failure
        }
    }
    
    choice at Worker2 {
        success -> {
            Worker2 -> Coordinator: Success
        }
        failure -> {
            Worker2 -> Coordinator: Failure
        }
    }
    
    Coordinator -> Observer: Report
}
"#;

    let result = parse_choreography_str(input);
    assert!(
        result.is_ok(),
        "Complex namespaced protocol should parse: {:?}",
        result.err()
    );

    let choreo = result.unwrap();
    assert_eq!(choreo.namespace, Some("complex_protocol".to_string()));
    assert_eq!(choreo.qualified_name(), "complex_protocol::ComplexProtocol");
}

#[test]
fn test_namespace_validation() {
    let choreo = parse_choreography_str(
        r#"
module test_validation exposing (TestProtocol)
protocol TestProtocol = {
    roles A, B, C
    A -> B: Message1
    B -> C: Message2
    C -> A: Message3
}
"#,
    )
    .unwrap();

    // Choreography validation should work normally with namespaces
    let validation_result = choreo.validate();
    assert!(
        validation_result.is_ok(),
        "Namespaced choreography should validate: {:?}",
        validation_result.err()
    );
}
