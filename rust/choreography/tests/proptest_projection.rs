#![cfg(not(target_arch = "wasm32"))]
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use proptest::prelude::*;
use quote::format_ident;
use std::collections::HashMap;
use telltale_choreography::ast::{
    Annotations, Choreography, LocalType, MessageType, Protocol, Role,
};
use telltale_choreography::compiler::projection::project;

fn role(name: &str) -> Role {
    Role::new(format_ident!("{}", name)).unwrap()
}

fn message(idx: usize) -> MessageType {
    MessageType {
        name: format_ident!("M{}", idx),
        type_annotation: None,
        payload: None,
    }
}

fn linear_protocol(bits: &[bool], a: &Role, b: &Role) -> Protocol {
    bits.iter()
        .enumerate()
        .rev()
        .fold(Protocol::End, |continuation, (idx, send_from_a)| {
            let (from, to) = if *send_from_a {
                (a.clone(), b.clone())
            } else {
                (b.clone(), a.clone())
            };
            Protocol::Send {
                from,
                to,
                message: message(idx),
                continuation: Box::new(continuation),
                annotations: Annotations::new(),
                from_annotations: Annotations::new(),
                to_annotations: Annotations::new(),
            }
        })
}

proptest! {
    #[test]
    fn projection_is_deterministic_for_linear_protocols(bits in prop::collection::vec(any::<bool>(), 0..8)) {
        let a = role("Alice");
        let b = role("Bob");
        let protocol = linear_protocol(&bits, &a, &b);
        let choreo = Choreography {
            name: format_ident!("Determinism"),
            namespace: None,
            roles: vec![a.clone(), b.clone()],
            protocol,
            attrs: HashMap::new(),
        };

        let first = project(&choreo, &a).expect("projection should succeed");
        let second = project(&choreo, &a).expect("projection should succeed");
        prop_assert_eq!(first, second);
    }

    #[test]
    fn nonparticipant_projects_to_end_for_linear_two_party_protocols(bits in prop::collection::vec(any::<bool>(), 1..8)) {
        let a = role("Alice");
        let b = role("Bob");
        let c = role("Charlie");
        let protocol = linear_protocol(&bits, &a, &b);
        let choreo = Choreography {
            name: format_ident!("NonParticipant"),
            namespace: None,
            roles: vec![a, b, c.clone()],
            protocol,
            attrs: HashMap::new(),
        };

        let projection = project(&choreo, &c).expect("projection should succeed");
        prop_assert_eq!(projection, LocalType::End);
    }
}

#[test]
fn end_projection_is_end() {
    let alice = role("Alice");
    let choreo = Choreography {
        name: format_ident!("EndOnly"),
        namespace: None,
        roles: vec![alice.clone()],
        protocol: Protocol::End,
        attrs: HashMap::new(),
    };

    let projected = project(&choreo, &alice).unwrap();
    assert_eq!(projected, LocalType::End);
}
