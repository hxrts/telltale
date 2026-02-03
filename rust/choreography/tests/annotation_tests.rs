#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

// Tests for the enhanced annotation framework
//
// This test suite verifies that annotations work correctly throughout
// the choreography compilation pipeline.

use proc_macro2::{Ident, Span};
use std::collections::HashMap;
use telltale_choreography::ast::{
    Annotations, Branch, Choreography, MessageType, NonEmptyVec, Protocol, ProtocolAnnotation, Role,
};
use telltale_choreography::compiler::{
    generate_choreography_code_with_namespacing, parse_choreography_str,
};

// Helper to create identifiers
fn ident(s: &str) -> Ident {
    Ident::new(s, Span::call_site())
}

// Helper to create roles
fn role(name: &str) -> Role {
    Role::new(ident(name)).unwrap()
}

// Helper to create a message type
fn msg(name: &str) -> MessageType {
    MessageType {
        name: ident(name),
        type_annotation: None,
        payload: None,
    }
}

fn annotations(pairs: &[(&str, &str)]) -> Annotations {
    let items = pairs
        .iter()
        .map(|(key, value)| ProtocolAnnotation::custom(*key, *value))
        .collect();
    Annotations::from_vec(items)
}

#[test]
fn test_protocol_annotation_storage() {
    let alice = role("Alice");
    let bob = role("Bob");

    let mut protocol = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg("Ping"),
        continuation: Box::new(Protocol::End),
        annotations: Annotations::new(),
        from_annotations: Annotations::new(),
        to_annotations: Annotations::new(),
    };

    // Test setting annotations
    assert!(protocol.add_annotation(ProtocolAnnotation::custom("priority", "high")));
    protocol
        .get_from_annotations_mut()
        .unwrap()
        .push(ProtocolAnnotation::custom("timeout", "30s"));
    protocol
        .get_to_annotations_mut()
        .unwrap()
        .push(ProtocolAnnotation::custom("retry", "3"));

    // Test getting annotations
    assert_eq!(
        protocol.get_annotation("priority"),
        Some("high".to_string())
    );
    assert_eq!(
        protocol.get_from_annotations().unwrap().get("timeout"),
        Some("30s".to_string())
    );
    assert_eq!(
        protocol.get_to_annotations().unwrap().get("retry"),
        Some("3".to_string())
    );

    // Test boolean annotations
    protocol.add_annotation(ProtocolAnnotation::custom("async", "true"));
    assert_eq!(protocol.get_annotation_as_bool("async"), Some(true));

    // Test typed annotations
    protocol.add_annotation(ProtocolAnnotation::custom("count", "42"));
    assert_eq!(protocol.get_annotation_as::<i32>("count"), Some(42));
}

#[test]
fn test_protocol_annotation_api() {
    let alice = role("Alice");
    let bob = role("Bob");

    let mut protocol = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg("Test"),
        continuation: Box::new(Protocol::End),
        annotations: Annotations::new(),
        from_annotations: Annotations::new(),
        to_annotations: Annotations::new(),
    };

    // Test has_annotation
    assert!(!protocol.has_annotation("priority"));
    protocol.add_annotation(ProtocolAnnotation::custom("priority", "high"));
    assert!(protocol.has_annotation("priority"));

    // Test annotation_matches
    assert!(protocol.annotation_matches("priority", "high"));
    assert!(protocol.annotation_matches("priority", "HIGH")); // case-insensitive
    assert!(!protocol.annotation_matches("priority", "low"));

    // Test annotation_keys
    protocol.add_annotation(ProtocolAnnotation::custom("timeout", "30s"));
    let keys: Vec<String> = protocol
        .get_annotations()
        .iter()
        .map(|annotation| annotation.key().to_string())
        .collect();
    assert!(keys.contains(&"priority".to_string()));
    assert!(keys.contains(&"timeout".to_string()));

    // Test annotation_count
    assert_eq!(protocol.annotation_count(), 2);

    // Test has_any_annotations
    assert!(protocol.has_any_annotations());

    // Test clear_annotations
    protocol.clear_annotations();
    assert!(!protocol.has_any_annotations());
    assert_eq!(protocol.annotation_count(), 0);
}

#[test]
fn test_protocol_annotation_validation() {
    let alice = role("Alice");
    let bob = role("Bob");

    let mut protocol = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg("Test"),
        continuation: Box::new(Protocol::End),
        annotations: Annotations::new(),
        from_annotations: Annotations::new(),
        to_annotations: Annotations::new(),
    };

    protocol.add_annotation(ProtocolAnnotation::custom("priority", "high"));
    protocol.add_annotation(ProtocolAnnotation::custom("timeout", "30s"));

    // Test successful validation
    let required = vec!["priority", "timeout"];
    assert!(protocol.validate_required_annotations(&required).is_ok());

    // Test failed validation
    let required = vec!["priority", "timeout", "missing"];
    let result = protocol.validate_required_annotations(&required);
    assert!(result.is_err());
    let missing = result.unwrap_err();
    assert_eq!(missing, vec!["missing".to_string()]);
}

#[test]
fn test_protocol_annotation_merging() {
    let alice = role("Alice");
    let bob = role("Bob");

    let mut protocol1 = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg("Test1"),
        continuation: Box::new(Protocol::End),
        annotations: annotations(&[("priority", "high")]),
        from_annotations: annotations(&[("timeout", "30s")]),
        to_annotations: annotations(&[("retry", "3")]),
    };

    let protocol2 = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg("Test2"),
        continuation: Box::new(Protocol::End),
        annotations: annotations(&[("priority", "low"), ("async", "true")]),
        from_annotations: annotations(&[("timeout", "60s"), ("buffer", "1024")]),
        to_annotations: annotations(&[("retry", "5"), ("backoff", "exponential")]),
    };

    protocol1.merge_annotations_from(&protocol2);

    // Verify merged annotations (merge is additive; first entry wins on lookup)
    assert_eq!(
        protocol1.get_annotation("priority"),
        Some("high".to_string())
    );
    assert_eq!(protocol1.get_annotation("async"), Some("true".to_string()));
    assert_eq!(
        protocol1.get_from_annotations().unwrap().get("timeout"),
        Some("30s".to_string())
    );
    assert_eq!(
        protocol1.get_from_annotations().unwrap().get("buffer"),
        Some("1024".to_string())
    );
    assert_eq!(
        protocol1.get_to_annotations().unwrap().get("retry"),
        Some("3".to_string())
    );
    assert_eq!(
        protocol1.get_to_annotations().unwrap().get("backoff"),
        Some("exponential".to_string())
    );
}

#[test]
fn test_protocol_annotation_filtering() {
    let alice = role("Alice");
    let bob = role("Bob");

    let mut protocol = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg("Test"),
        continuation: Box::new(Protocol::End),
        annotations: Annotations::new(),
        from_annotations: Annotations::new(),
        to_annotations: Annotations::new(),
    };

    protocol.add_annotation(ProtocolAnnotation::custom("timeout_seconds", "30"));
    protocol.add_annotation(ProtocolAnnotation::custom("timeout_retries", "3"));
    protocol.add_annotation(ProtocolAnnotation::custom("priority", "high"));

    let timeout_annotations: HashMap<String, String> = protocol
        .get_annotations()
        .iter()
        .filter_map(|annotation| {
            let key = annotation.key();
            if key.starts_with("timeout_") {
                annotation
                    .custom_value(key)
                    .map(|value| (key.to_string(), value.to_string()))
            } else {
                None
            }
        })
        .collect();
    assert_eq!(timeout_annotations.len(), 2);
    assert!(timeout_annotations.contains_key("timeout_seconds"));
    assert!(timeout_annotations.contains_key("timeout_retries"));
    assert!(!timeout_annotations.contains_key("priority"));
}

#[test]
fn test_choreography_annotation_api() {
    let mut choreo = Choreography {
        name: ident("TestChoreography"),
        namespace: None,
        roles: vec![role("Alice"), role("Bob")],
        protocol: Protocol::End,
        attrs: HashMap::new(),
    };

    // Test setting and getting choreography attributes
    choreo.set_attribute("version".to_string(), "1.0.0".to_string());
    choreo.set_attribute("author".to_string(), "test".to_string());

    assert_eq!(choreo.get_attribute("version"), Some(&"1.0.0".to_string()));
    assert_eq!(choreo.get_attribute("author"), Some(&"test".to_string()));
    assert!(choreo.has_attribute("version"));
    assert!(!choreo.has_attribute("missing"));

    // Test typed attributes
    choreo.set_attribute("debug".to_string(), "true".to_string());
    assert_eq!(choreo.get_attribute_as_bool("debug"), Some(true));

    // Test attribute validation
    let required = vec!["version", "author"];
    assert!(choreo.validate_required_attributes(&required).is_ok());

    let required = vec!["version", "author", "missing"];
    let result = choreo.validate_required_attributes(&required);
    assert!(result.is_err());
}

#[test]
fn test_protocol_traversal_with_annotations() {
    let alice = role("Alice");
    let bob = role("Bob");

    let _inner_protocol = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg("InnerMsg"),
        continuation: Box::new(Protocol::End),
        annotations: annotations(&[("inner", "true")]),
        from_annotations: Annotations::new(),
        to_annotations: Annotations::new(),
    };

    let outer_protocol = Protocol::Send {
        from: bob.clone(),
        to: alice.clone(),
        message: msg("OuterMsg"),
        continuation: Box::new(Protocol::Send {
            from: alice.clone(),
            to: bob.clone(),
            message: msg("InnerMsg"),
            continuation: Box::new(Protocol::End),
            annotations: annotations(&[("inner", "true")]),
            from_annotations: Annotations::new(),
            to_annotations: Annotations::new(),
        }),
        annotations: annotations(&[("outer", "true")]),
        from_annotations: Annotations::new(),
        to_annotations: Annotations::new(),
    };

    // Test deep annotation count
    assert_eq!(outer_protocol.deep_annotation_count(), 2);

    // Test collecting nodes with specific annotations
    let mut nodes = Vec::new();
    outer_protocol.collect_nodes_with_annotation("inner", &mut nodes);
    assert_eq!(nodes.len(), 1);

    nodes.clear();
    outer_protocol.collect_nodes_with_annotation("outer", &mut nodes);
    assert_eq!(nodes.len(), 1);

    // Test collecting nodes with specific annotation values
    nodes.clear();
    outer_protocol.collect_nodes_with_annotation_value("inner", "true", &mut nodes);
    assert_eq!(nodes.len(), 1);

    // Test visitor pattern
    let mut visited_count = 0;
    outer_protocol.visit_annotated_nodes(&mut |_| {
        visited_count += 1;
    });
    assert_eq!(visited_count, 2);
}

#[test]
fn test_choice_annotation_support() {
    let alice = role("Alice");
    let bob = role("Bob");

    let branch1 = Branch {
        label: ident("accept"),
        guard: None,
        protocol: Protocol::Send {
            from: alice.clone(),
            to: bob.clone(),
            message: msg("Accept"),
            continuation: Box::new(Protocol::End),
            annotations: Annotations::new(),
            from_annotations: Annotations::new(),
            to_annotations: Annotations::new(),
        },
    };

    let branch2 = Branch {
        label: ident("reject"),
        guard: None,
        protocol: Protocol::Send {
            from: alice.clone(),
            to: bob.clone(),
            message: msg("Reject"),
            continuation: Box::new(Protocol::End),
            annotations: Annotations::new(),
            from_annotations: Annotations::new(),
            to_annotations: Annotations::new(),
        },
    };

    let mut choice = Protocol::Choice {
        role: alice.clone(),
        branches: NonEmptyVec::from_head_tail(branch1, vec![branch2]),
        annotations: Annotations::new(),
    };

    // Test Choice annotation support
    assert!(choice.add_annotation(ProtocolAnnotation::custom("decision_timeout", "10s")));
    assert_eq!(
        choice.get_annotation("decision_timeout"),
        Some("10s".to_string())
    );
    assert!(choice.has_any_annotations());
}

#[test]
fn test_broadcast_annotation_support() {
    let alice = role("Alice");
    let bob = role("Bob");
    let carol = role("Carol");

    let mut broadcast = Protocol::Broadcast {
        from: alice.clone(),
        to_all: NonEmptyVec::from_head_tail(bob.clone(), vec![carol.clone()]),
        message: msg("Announcement"),
        continuation: Box::new(Protocol::End),
        annotations: Annotations::new(),
        from_annotations: Annotations::new(),
    };

    // Test Broadcast annotation support
    assert!(broadcast.add_annotation(ProtocolAnnotation::custom("reliability", "at_least_once")));
    broadcast
        .get_from_annotations_mut()
        .unwrap()
        .push(ProtocolAnnotation::custom("batch_size", "100"));

    assert_eq!(
        broadcast.get_annotation("reliability"),
        Some("at_least_once".to_string())
    );
    assert_eq!(
        broadcast.get_from_annotations().unwrap().get("batch_size"),
        Some("100".to_string())
    );

    // Broadcast doesn't have to_annotations
    assert!(broadcast.get_to_annotations().is_none());
}

#[test]
fn test_annotation_syntax_is_rejected() {
    let choreography_dsl = r#"
        #[version="1.0"]
        protocol TestChoreography =
          roles Alice, Bob
          Alice -> Bob : Message
    "#;

    let result = parse_choreography_str(choreography_dsl);
    assert!(result.is_err(), "Annotation syntax should be rejected");
}

#[test]
fn test_code_generation_with_annotations() {
    let alice = role("Alice");
    let bob = role("Bob");

    let choreo = Choreography {
        name: ident("AnnotatedChoreography"),
        namespace: Some("test".to_string()),
        roles: vec![alice.clone(), bob.clone()],
        protocol: Protocol::Send {
            from: alice.clone(),
            to: bob.clone(),
            message: msg("TestMessage"),
            continuation: Box::new(Protocol::End),
            annotations: annotations(&[("priority", "high")]),
            from_annotations: Annotations::new(),
            to_annotations: Annotations::new(),
        },
        attrs: HashMap::from([("version".to_string(), "1.0".to_string())]),
    };

    // Test that code generation includes annotation metadata
    let generated_code = generate_choreography_code_with_namespacing(&choreo, &[]);
    let code_string = generated_code.to_string();

    // Verify that annotation metadata is included in generated code
    assert!(code_string.contains("annotations"));
    println!(
        "Generated code includes annotation support: {}",
        code_string.contains("annotations")
    );
}

#[test]
fn test_annotation_different_types() {
    let alice = role("Alice");
    let bob = role("Bob");

    let mut protocol = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg("Test"),
        continuation: Box::new(Protocol::End),
        annotations: Annotations::new(),
        from_annotations: Annotations::new(),
        to_annotations: Annotations::new(),
    };

    // Test different annotation value types
    protocol.add_annotation(ProtocolAnnotation::custom("string_value", "hello"));
    protocol.add_annotation(ProtocolAnnotation::custom("number_value", "42"));
    protocol.add_annotation(ProtocolAnnotation::custom("boolean_true", "true"));
    protocol.add_annotation(ProtocolAnnotation::custom("boolean_false", "false"));
    protocol.add_annotation(ProtocolAnnotation::custom("boolean_yes", "yes"));
    protocol.add_annotation(ProtocolAnnotation::custom("boolean_no", "no"));

    // Test string values
    assert_eq!(
        protocol.get_annotation("string_value"),
        Some("hello".to_string())
    );

    // Test numeric parsing
    assert_eq!(protocol.get_annotation_as::<i32>("number_value"), Some(42));
    assert_eq!(protocol.get_annotation_as::<u32>("number_value"), Some(42));
    assert_eq!(
        protocol.get_annotation_as::<f64>("number_value"),
        Some(42.0)
    );

    // Test boolean parsing
    assert_eq!(protocol.get_annotation_as_bool("boolean_true"), Some(true));
    assert_eq!(
        protocol.get_annotation_as_bool("boolean_false"),
        Some(false)
    );
    assert_eq!(protocol.get_annotation_as_bool("boolean_yes"), Some(true));
    assert_eq!(protocol.get_annotation_as_bool("boolean_no"), Some(false));

    // Test invalid conversions
    assert_eq!(protocol.get_annotation_as::<i32>("string_value"), None);
    assert_eq!(protocol.get_annotation_as_bool("string_value"), None);
}
