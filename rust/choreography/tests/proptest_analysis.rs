#![cfg(not(target_arch = "wasm32"))]
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

use proptest::prelude::*;
use quote::format_ident;
use std::collections::HashMap;
use telltale_choreography::ast::{Annotations, Branch, Choreography, MessageType, NonEmptyVec, Protocol, Role};
use telltale_choreography::compiler::analysis::analyze;

fn role(name: &str) -> Role {
    Role::new(format_ident!("{}", name)).unwrap()
}

fn msg(name: &str) -> MessageType {
    MessageType {
        name: format_ident!("{}", name),
        type_annotation: None,
        payload: None,
    }
}

fn linear_protocol(bits: &[bool], a: &Role, b: &Role) -> Protocol {
    bits.iter()
        .enumerate()
        .rev()
        .fold(Protocol::End, |continuation, (idx, send_from_a)| {
            let (from, to) = if *send_from_a { (a.clone(), b.clone()) } else { (b.clone(), a.clone()) };
            Protocol::Send {
                from,
                to,
                message: msg(&format!("M{idx}")),
                continuation: Box::new(continuation),
                annotations: Annotations::new(),
                from_annotations: Annotations::new(),
                to_annotations: Annotations::new(),
            }
        })
}

fn choice_protocol(chooser: &Role, peer: &Role) -> Protocol {
    Protocol::Choice {
        role: chooser.clone(),
        branches: NonEmptyVec::from_head_tail(
            Branch {
                label: format_ident!("Left"),
                guard: None,
                protocol: Protocol::Send {
                    from: chooser.clone(),
                    to: peer.clone(),
                    message: msg("LeftMsg"),
                    continuation: Box::new(Protocol::End),
                    annotations: Annotations::new(),
                    from_annotations: Annotations::new(),
                    to_annotations: Annotations::new(),
                },
            },
            vec![Branch {
                label: format_ident!("Right"),
                guard: None,
                protocol: Protocol::Send {
                    from: chooser.clone(),
                    to: peer.clone(),
                    message: msg("RightMsg"),
                    continuation: Box::new(Protocol::End),
                    annotations: Annotations::new(),
                    from_annotations: Annotations::new(),
                    to_annotations: Annotations::new(),
                },
            }],
        ),
        annotations: Annotations::new(),
    }
}

fn protocol_strategy() -> impl Strategy<Value = Protocol> {
    prop_oneof![
        any::<u8>().prop_map(|_| Protocol::End),
        prop::collection::vec(any::<bool>(), 1..6).prop_map(|bits| {
            let a = role("Alice");
            let b = role("Bob");
            linear_protocol(&bits, &a, &b)
        }),
        any::<u8>().prop_map(|_| {
            let a = role("Alice");
            let b = role("Bob");
            choice_protocol(&a, &b)
        }),
    ]
}

fn choreography_strategy() -> impl Strategy<Value = Choreography> {
    protocol_strategy().prop_map(|protocol| Choreography {
        name: format_ident!("AnalysisProp"),
        namespace: None,
        roles: vec![role("Alice"), role("Bob"), role("Charlie")],
        protocol,
        attrs: HashMap::new(),
    })
}

proptest! {
    #[test]
    fn analysis_completes_without_panicking(choreo in choreography_strategy()) {
        let _ = analyze(&choreo);
    }

    #[test]
    fn analysis_tracks_all_declared_roles(choreo in choreography_strategy()) {
        let result = analyze(&choreo);
        for role in &choreo.roles {
            prop_assert!(result.role_participation.contains_key(role));
        }
    }

    #[test]
    fn total_sends_equal_total_receives(choreo in choreography_strategy()) {
        let result = analyze(&choreo);
        let total_sends: usize = result.role_participation.values().map(|p| p.sends).sum();
        let total_receives: usize = result.role_participation.values().map(|p| p.receives).sum();
        prop_assert_eq!(total_sends, total_receives);
    }

    #[test]
    fn communication_graph_edges_match_send_count(choreo in choreography_strategy()) {
        let result = analyze(&choreo);
        let total_sends: usize = result.role_participation.values().map(|p| p.sends).sum();
        prop_assert_eq!(total_sends, result.communication_graph.edges.len());
    }
}

#[test]
fn end_only_protocol_has_no_activity() {
    let choreo = Choreography {
        name: format_ident!("EndOnly"),
        namespace: None,
        roles: vec![role("Alice"), role("Bob")],
        protocol: Protocol::End,
        attrs: HashMap::new(),
    };
    let result = analyze(&choreo);
    assert!(result.is_deadlock_free);
    assert!(result.has_progress);
    assert!(result.communication_graph.edges.is_empty());
}
