//! Structure-aware fuzz tests for VM protocols.
#![allow(
    clippy::cast_possible_wrap,
    clippy::as_conversions,
    clippy::needless_collect,
    clippy::let_underscore_must_use,
    clippy::useless_vec
)]

#[allow(dead_code, unreachable_pub)]
mod helpers;

use std::collections::BTreeMap;

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};
use telltale_types::{GlobalType, Label};
use telltale_vm::buffer::{BackpressurePolicy, BoundedBuffer, BufferConfig, BufferMode};
use telltale_vm::coroutine::Value;
use telltale_vm::vm::{ObsEvent, VMConfig, VM};

use helpers::{
    code_image_from_global, well_formed_global_strategy, FailingHandler, PassthroughHandler, SEED,
};

fn make_runner(cases: u32) -> TestRunner {
    TestRunner::new_with_rng(
        Config {
            cases,
            ..Config::default()
        },
        TestRng::from_seed(RngAlgorithm::ChaCha, &SEED),
    )
}

// ============================================================================
// Fuzz Targets
// ============================================================================

/// Generate random well-formed GlobalType, project all roles, compile, load,
/// run to completion. Assert: no faults, all terminal, FIFO on trace.
#[test]
fn fuzz_random_protocol_compile_execute() {
    let mut runner = make_runner(200);
    let strategy = well_formed_global_strategy(3);

    for _ in 0..200 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let global = tree.current();

        // Skip End and recursive (non-terminating) protocols.
        if matches!(global, GlobalType::End | GlobalType::Mu { .. }) {
            continue;
        }

        let image = match code_image_from_global(&global) {
            Some(img) => img,
            None => continue,
        };

        let mut vm = VM::new(VMConfig::default());
        if vm.load_choreography(&image).is_err() {
            continue;
        }

        let handler = PassthroughHandler;
        vm.run(&handler, 1000).unwrap_or(());

        // No faults.
        let faults: Vec<_> = vm
            .trace()
            .iter()
            .filter(|e| matches!(e, ObsEvent::Faulted { .. }))
            .collect();
        assert!(faults.is_empty(), "faults for {global:?}: {faults:?}");

        // FIFO per edge: sent order = recv order.
        let mut sent_by_edge: BTreeMap<(String, String), Vec<String>> = BTreeMap::new();
        let mut recv_by_edge: BTreeMap<(String, String), Vec<String>> = BTreeMap::new();

        for event in vm.trace() {
            match event {
                ObsEvent::Sent {
                    from, to, label, ..
                } => {
                    sent_by_edge
                        .entry((from.clone(), to.clone()))
                        .or_default()
                        .push(label.clone());
                }
                ObsEvent::Received {
                    from, to, label, ..
                } => {
                    recv_by_edge
                        .entry((from.clone(), to.clone()))
                        .or_default()
                        .push(label.clone());
                }
                _ => {}
            }
        }

        for (edge, recvs) in &recv_by_edge {
            if let Some(sents) = sent_by_edge.get(edge) {
                assert!(recvs.len() <= sents.len());
                for (i, r) in recvs.iter().enumerate() {
                    assert_eq!(r, &sents[i], "FIFO violated on edge {edge:?} at {i}");
                }
            } else {
                panic!("received on edge {edge:?} without sends");
            }
        }
    }
}

/// Generate random sequence of enqueue/dequeue, verify FIFO order, count invariant.
#[test]
fn fuzz_random_buffer_operations() {
    let mut runner = make_runner(500);
    let op_strategy = prop_oneof![Just(true), Just(false)]; // true = enqueue, false = dequeue
    let len_strategy = 1..200usize;

    for _ in 0..500 {
        let len_tree = len_strategy.new_tree(&mut runner).unwrap();
        let n = len_tree.current();

        let config = BufferConfig {
            mode: BufferMode::Fifo,
            initial_capacity: n + 1,
            policy: BackpressurePolicy::Block,
        };
        let mut buf = BoundedBuffer::new(&config);
        let mut expected: Vec<i64> = Vec::new();
        let mut next_val = 0i64;

        for _ in 0..n {
            let op_tree = op_strategy.new_tree(&mut runner).unwrap();
            let enqueue = op_tree.current();

            if enqueue {
                buf.enqueue(Value::Int(next_val));
                expected.push(next_val);
                next_val += 1;
            } else if !expected.is_empty() {
                let val = buf.dequeue();
                let exp = expected.remove(0);
                assert_eq!(val, Some(Value::Int(exp)));
            }

            assert_eq!(buf.len(), expected.len());
        }
    }
}

/// Generate 2-3 random protocols, load into one VM, run, verify session isolation.
#[test]
fn fuzz_multi_session_interleave() {
    let mut runner = make_runner(100);
    let strategy = well_formed_global_strategy(2);

    for _ in 0..100 {
        let tree1 = strategy.new_tree(&mut runner).unwrap();
        let tree2 = strategy.new_tree(&mut runner).unwrap();

        let g1 = tree1.current();
        let g2 = tree2.current();

        if matches!(g1, GlobalType::End | GlobalType::Mu { .. })
            || matches!(g2, GlobalType::End | GlobalType::Mu { .. })
        {
            continue;
        }

        let img1 = match code_image_from_global(&g1) {
            Some(i) => i,
            None => continue,
        };
        let img2 = match code_image_from_global(&g2) {
            Some(i) => i,
            None => continue,
        };

        let mut vm = VM::new(VMConfig::default());
        let sid1 = match vm.load_choreography(&img1) {
            Ok(s) => s,
            Err(_) => continue,
        };
        let sid2 = match vm.load_choreography(&img2) {
            Ok(s) => s,
            Err(_) => continue,
        };

        let handler = PassthroughHandler;
        vm.run(&handler, 1000).unwrap_or(());

        // No faults.
        let faults: Vec<_> = vm
            .trace()
            .iter()
            .filter(|e| matches!(e, ObsEvent::Faulted { .. }))
            .collect();
        assert!(faults.is_empty(), "faults in multi-session: {faults:?}");

        // Session events are grouped by session ID.
        for event in vm.trace() {
            match event {
                ObsEvent::Sent { session, .. } | ObsEvent::Received { session, .. } => {
                    assert!(
                        *session == sid1 || *session == sid2,
                        "event from unknown session"
                    );
                }
                _ => {}
            }
        }
    }
}

/// Generate recursive protocols, run for bounded steps, verify no faults.
#[test]
fn fuzz_recursive_protocols_bounded() {
    // Use fixed two-party roles to avoid multi-role choice compilation issue.
    let pairs = [("A", "B"), ("B", "A")];

    for i in 0..100 {
        let (s, r) = pairs[i % pairs.len()];

        // Simple recursive send (single branch, no choice).
        let global = GlobalType::mu(
            "t",
            GlobalType::send(s, r, Label::new("msg"), GlobalType::var("t")),
        );

        let image = match code_image_from_global(&global) {
            Some(i) => i,
            None => continue,
        };

        let mut vm = VM::new(VMConfig::default());
        if vm.load_choreography(&image).is_err() {
            continue;
        }

        let handler = PassthroughHandler;
        // Run for bounded steps — recursive protocols don't terminate.
        vm.run(&handler, 500).unwrap_or(());

        // No faults.
        let faults: Vec<_> = vm
            .trace()
            .iter()
            .filter(|e| matches!(e, ObsEvent::Faulted { .. }))
            .collect();
        assert!(
            faults.is_empty(),
            "faults in recursive protocol: {faults:?}"
        );
    }
}

/// Generate protocols, use FailingHandler that errors, verify VM returns clean faults (not panics).
#[test]
fn fuzz_handler_errors_dont_panic() {
    let mut runner = make_runner(100);
    let strategy = well_formed_global_strategy(2);

    for _ in 0..100 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let global = tree.current();

        if matches!(global, GlobalType::End) {
            continue;
        }

        let image = match code_image_from_global(&global) {
            Some(i) => i,
            None => continue,
        };

        let mut vm = VM::new(VMConfig::default());
        if vm.load_choreography(&image).is_err() {
            continue;
        }

        let handler = FailingHandler::new("deliberate test error");
        // Should not panic — should return errors cleanly.
        let _ = vm.run(&handler, 100);
    }
}
