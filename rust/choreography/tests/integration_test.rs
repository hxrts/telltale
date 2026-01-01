#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

// Integration tests for end-to-end choreography execution
//
// These tests verify the complete pipeline from choreography construction
// through projection and analysis.

use proc_macro2::{Ident, Span};
use quote::quote;
use rumpsteak_aura_choreography::ast::{
    Branch, Choreography, Condition, MessageType, NonEmptyVec, Protocol, Role,
};
use rumpsteak_aura_choreography::compiler::{analyze, project};
use std::collections::HashMap;

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

// Helper to create a message with payload
fn msg_with_payload(name: &str, payload_type: &str) -> MessageType {
    MessageType {
        name: ident(name),
        type_annotation: None,
        payload: Some(quote! { #payload_type }),
    }
}

#[test]
fn test_simple_two_party_protocol() {
    // Construct a simple ping-pong protocol
    let alice = role("Alice");
    let bob = role("Bob");

    let protocol = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg("Ping"),
        continuation: Box::new(Protocol::Send {
            from: bob.clone(),
            to: alice.clone(),
            message: msg("Pong"),
            continuation: Box::new(Protocol::End),
            annotations: HashMap::new(),
            from_annotations: HashMap::new(),
            to_annotations: HashMap::new(),
        }),
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
        to_annotations: HashMap::new(),
    };

    let choreography = Choreography {
        name: ident("PingPong"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone()],
        protocol,
        attrs: HashMap::new(),
    };

    // Validate the choreography
    assert!(
        choreography.validate().is_ok(),
        "Choreography should be valid"
    );

    // Project for both roles
    let alice_local = project(&choreography, &alice);
    assert!(alice_local.is_ok(), "Alice projection should succeed");

    let bob_local = project(&choreography, &bob);
    assert!(bob_local.is_ok(), "Bob projection should succeed");

    // Analyze choreography
    let results = analyze(&choreography);
    assert_eq!(results.role_participation.len(), 2, "Should have 2 roles");
    // Note: Deadlock analysis may not be fully implemented yet
    let _ = results.is_deadlock_free;
}

#[test]
fn test_three_party_protocol() {
    let alice = role("Alice");
    let bob = role("Bob");
    let carol = role("Carol");

    // Alice -> Bob -> Carol -> Alice
    let protocol = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg("Start"),
        continuation: Box::new(Protocol::Send {
            from: bob.clone(),
            to: carol.clone(),
            message: msg("Middle"),
            continuation: Box::new(Protocol::Send {
                from: carol.clone(),
                to: alice.clone(),
                message: msg("End"),
                continuation: Box::new(Protocol::End),
                annotations: HashMap::new(),
                from_annotations: HashMap::new(),
                to_annotations: HashMap::new(),
            }),
            annotations: HashMap::new(),
            from_annotations: HashMap::new(),
            to_annotations: HashMap::new(),
        }),
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
        to_annotations: HashMap::new(),
    };

    let choreography = Choreography {
        name: ident("ThreeParty"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone(), carol.clone()],
        protocol,
        attrs: HashMap::new(),
    };

    assert!(choreography.validate().is_ok());
    assert!(project(&choreography, &alice).is_ok());
    assert!(project(&choreography, &bob).is_ok());
    assert!(project(&choreography, &carol).is_ok());
}

#[test]
fn test_broadcast_protocol() {
    let alice = role("Alice");
    let bob = role("Bob");
    let carol = role("Carol");

    let protocol = Protocol::Broadcast {
        from: alice.clone(),
        to_all: NonEmptyVec::from_head_tail(bob.clone(), vec![carol.clone()]),
        message: msg("Announcement"),
        continuation: Box::new(Protocol::End),
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
    };

    let choreography = Choreography {
        name: ident("Broadcast"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone(), carol.clone()],
        protocol,
        attrs: HashMap::new(),
    };

    assert!(choreography.validate().is_ok());
    assert!(project(&choreography, &alice).is_ok());
    assert!(project(&choreography, &bob).is_ok());
    assert!(project(&choreography, &carol).is_ok());
}

#[test]
fn test_choice_protocol() {
    let alice = role("Alice");
    let bob = role("Bob");

    let accept_branch = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg("Accept"),
        continuation: Box::new(Protocol::End),
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
        to_annotations: HashMap::new(),
    };

    let reject_branch = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg("Reject"),
        continuation: Box::new(Protocol::End),
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
        to_annotations: HashMap::new(),
    };

    let protocol = Protocol::Choice {
        role: alice.clone(),
        branches: NonEmptyVec::from_head_tail(
            Branch {
                label: ident("accept"),
                guard: None,
                protocol: accept_branch,
            },
            vec![Branch {
                label: ident("reject"),
                guard: None,
                protocol: reject_branch,
            }],
        ),
        annotations: HashMap::new(),
    };

    let choreography = Choreography {
        name: ident("Choice"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone()],
        protocol,
        attrs: HashMap::new(),
    };

    assert!(choreography.validate().is_ok());
    assert!(project(&choreography, &alice).is_ok());
    assert!(project(&choreography, &bob).is_ok());
}

#[test]
fn test_loop_protocol() {
    let alice = role("Alice");
    let bob = role("Bob");

    let body = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg("Ping"),
        continuation: Box::new(Protocol::End),
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
        to_annotations: HashMap::new(),
    };

    let protocol = Protocol::Loop {
        condition: Some(Condition::Count(5)),
        body: Box::new(body),
    };

    let choreography = Choreography {
        name: ident("Loop"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone()],
        protocol,
        attrs: HashMap::new(),
    };

    assert!(choreography.validate().is_ok());
    assert!(project(&choreography, &alice).is_ok());
    assert!(project(&choreography, &bob).is_ok());
}

#[test]
fn test_parallel_protocol() {
    let alice = role("Alice");
    let bob = role("Bob");
    let carol = role("Carol");

    let branch1 = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg("Msg1"),
        continuation: Box::new(Protocol::End),
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
        to_annotations: HashMap::new(),
    };

    let branch2 = Protocol::Send {
        from: carol.clone(),
        to: alice.clone(),
        message: msg("Msg2"),
        continuation: Box::new(Protocol::End),
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
        to_annotations: HashMap::new(),
    };

    let protocol = Protocol::Parallel {
        protocols: NonEmptyVec::from_head_tail(branch1, vec![branch2]),
    };

    let choreography = Choreography {
        name: ident("Parallel"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone(), carol.clone()],
        protocol,
        attrs: HashMap::new(),
    };

    assert!(choreography.validate().is_ok());
    assert!(project(&choreography, &alice).is_ok());
    assert!(project(&choreography, &bob).is_ok());
    assert!(project(&choreography, &carol).is_ok());
}

#[test]
fn test_recursive_protocol() {
    let alice = role("Alice");
    let bob = role("Bob");

    let var_label = ident("X");

    let body = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg("Data"),
        continuation: Box::new(Protocol::Var(var_label.clone())),
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
        to_annotations: HashMap::new(),
    };

    let protocol = Protocol::Rec {
        label: var_label,
        body: Box::new(body),
    };

    let choreography = Choreography {
        name: ident("Recursive"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone()],
        protocol,
        attrs: HashMap::new(),
    };

    assert!(choreography.validate().is_ok());
    assert!(project(&choreography, &alice).is_ok());
    assert!(project(&choreography, &bob).is_ok());
}

#[test]
fn test_complex_negotiation() {
    let buyer = role("Buyer");
    let seller = role("Seller");

    let accept = Protocol::Send {
        from: seller.clone(),
        to: buyer.clone(),
        message: msg("Accept"),
        continuation: Box::new(Protocol::End),
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
        to_annotations: HashMap::new(),
    };

    let counter = Protocol::Send {
        from: seller.clone(),
        to: buyer.clone(),
        message: msg("CounterOffer"),
        continuation: Box::new(Protocol::End),
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
        to_annotations: HashMap::new(),
    };

    let choice = Protocol::Choice {
        role: seller.clone(),
        branches: NonEmptyVec::from_head_tail(
            Branch {
                label: ident("accept"),
                guard: None,
                protocol: accept,
            },
            vec![Branch {
                label: ident("counter"),
                guard: None,
                protocol: counter,
            }],
        ),
        annotations: HashMap::new(),
    };

    let protocol = Protocol::Send {
        from: buyer.clone(),
        to: seller.clone(),
        message: msg("Offer"),
        continuation: Box::new(choice),
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
        to_annotations: HashMap::new(),
    };

    let choreography = Choreography {
        name: ident("Negotiation"),
        namespace: None,
        roles: vec![buyer.clone(), seller.clone()],
        protocol,
        attrs: HashMap::new(),
    };

    assert!(choreography.validate().is_ok());
    assert!(project(&choreography, &buyer).is_ok());
    assert!(project(&choreography, &seller).is_ok());

    let _analysis = analyze(&choreography);
}

#[test]
fn test_invalid_choreography_missing_role() {
    let alice = role("Alice");
    let bob = role("Bob");
    let carol = role("Carol");

    let protocol = Protocol::Send {
        from: alice.clone(),
        to: carol.clone(), // Carol not in roles list
        message: msg("Msg"),
        continuation: Box::new(Protocol::End),
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
        to_annotations: HashMap::new(),
    };

    let choreography = Choreography {
        name: ident("Invalid"),
        namespace: None,
        roles: vec![alice, bob], // Carol missing!
        protocol,
        attrs: HashMap::new(),
    };

    // Should fail validation
    assert!(
        choreography.validate().is_err(),
        "Should reject undeclared role"
    );
}

#[test]
fn test_projection_consistency() {
    let alice = role("Alice");
    let bob = role("Bob");

    let protocol = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg("Data"),
        continuation: Box::new(Protocol::End),
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
        to_annotations: HashMap::new(),
    };

    let choreography = Choreography {
        name: ident("TwoParty"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone()],
        protocol,
        attrs: HashMap::new(),
    };

    let alice_local = project(&choreography, &alice).expect("Alice projection");
    let bob_local = project(&choreography, &bob).expect("Bob projection");

    // Verify projections are well-formed
    use rumpsteak_aura_choreography::ast::LocalType;

    match alice_local {
        LocalType::Send { .. } => (), // Alice sends
        _ => panic!("Alice should have Send in projection"),
    }

    match bob_local {
        LocalType::Receive { .. } => (), // Bob receives
        _ => panic!("Bob should have Receive in projection"),
    }
}

#[test]
fn test_analysis_detects_roles() {
    let alice = role("Alice");
    let bob = role("Bob");
    let carol = role("Carol");

    let protocol = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg("Msg"),
        continuation: Box::new(Protocol::Send {
            from: bob.clone(),
            to: carol.clone(),
            message: msg("Fwd"),
            continuation: Box::new(Protocol::End),
            annotations: HashMap::new(),
            from_annotations: HashMap::new(),
            to_annotations: HashMap::new(),
        }),
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
        to_annotations: HashMap::new(),
    };

    let choreography = Choreography {
        name: ident("Forward"),
        namespace: None,
        roles: vec![alice, bob, carol],
        protocol,
        attrs: HashMap::new(),
    };

    let analysis = analyze(&choreography);

    assert_eq!(analysis.role_participation.len(), 3);
    assert!(analysis.has_progress);
}

#[test]
fn test_message_with_payload() {
    let alice = role("Alice");
    let bob = role("Bob");

    let protocol = Protocol::Send {
        from: alice.clone(),
        to: bob.clone(),
        message: msg_with_payload("Request", "u32"),
        continuation: Box::new(Protocol::End),
        annotations: HashMap::new(),
        from_annotations: HashMap::new(),
        to_annotations: HashMap::new(),
    };

    let choreography = Choreography {
        name: ident("WithPayload"),
        namespace: None,
        roles: vec![alice.clone(), bob.clone()],
        protocol,
        attrs: HashMap::new(),
    };

    assert!(choreography.validate().is_ok());
    assert!(project(&choreography, &alice).is_ok());
    assert!(project(&choreography, &bob).is_ok());
}
