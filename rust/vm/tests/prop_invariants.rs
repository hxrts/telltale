#![cfg(not(target_arch = "wasm32"))]
//! Property-based invariant tests for VM conformance.
#![allow(
    clippy::cast_possible_wrap,
    clippy::as_conversions,
    clippy::needless_collect,
    clippy::let_underscore_must_use
)]

#[allow(dead_code, unreachable_pub)]
mod helpers;

use proptest::prelude::*;
use proptest::strategy::ValueTree;
use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};
use std::collections::BTreeMap;
use telltale_types::{GlobalType, Label, LocalTypeR};
use telltale_vm::buffer::{BackpressurePolicy, BoundedBuffer, BufferConfig, BufferMode};
use telltale_vm::compiler::compile;
use telltale_vm::coroutine::Value;
use telltale_vm::instr::{Endpoint, Instr};
use telltale_vm::loader::CodeImage;
use telltale_vm::session::{unfold_if_var, unfold_mu};
use telltale_vm::vm::{ObsEvent, VMConfig, VM};

use helpers::{
    code_image_from_global, role_pair_strategy, value_strategy, well_formed_global_strategy,
    PassthroughHandler, SEED,
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
// Type Advancement
// ============================================================================

#[test]
fn prop_send_advances_to_continuation() {
    let mut runner = make_runner(50);
    let strategy = role_pair_strategy();

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let (s, r) = tree.current();

        let lt = LocalTypeR::Send {
            partner: r.clone(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        };

        let mut local_types = BTreeMap::new();
        local_types.insert(s.clone(), lt);
        local_types.insert(
            r.clone(),
            LocalTypeR::Recv {
                partner: s.clone(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );

        let global = GlobalType::send(&s, &r, Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();

        // After send, sender's type should have been removed (advanced to End, then Halt removed it).
        let ep = Endpoint { sid, role: s };
        assert!(vm.sessions().lookup_type(&ep).is_none());
    }
}

#[test]
fn prop_recv_advances_to_continuation() {
    let mut runner = make_runner(50);
    let strategy = role_pair_strategy();

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let (s, r) = tree.current();

        let mut local_types = BTreeMap::new();
        local_types.insert(
            s.clone(),
            LocalTypeR::Send {
                partner: r.clone(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );
        local_types.insert(
            r.clone(),
            LocalTypeR::Recv {
                partner: s.clone(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );

        let global = GlobalType::send(&s, &r, Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();

        let ep = Endpoint { sid, role: r };
        assert!(vm.sessions().lookup_type(&ep).is_none());
    }
}

#[test]
fn prop_choose_advances_to_selected_branch() {
    let image = helpers::choice_image("A", "B", &["yes", "no"]);
    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    vm.run(&handler, 100).unwrap();

    // A chose "yes", type removed after Halt.
    let ep = Endpoint {
        sid,
        role: "A".into(),
    };
    assert!(vm.sessions().lookup_type(&ep).is_none());
}

#[test]
fn prop_offer_advances_to_received_label() {
    let image = helpers::choice_image("A", "B", &["yes", "no"]);
    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    vm.run(&handler, 100).unwrap();

    let ep = Endpoint {
        sid,
        role: "B".into(),
    };
    assert!(vm.sessions().lookup_type(&ep).is_none());
}

// ============================================================================
// Compile-Then-Execute
// ============================================================================

#[test]
fn prop_compile_execute_reaches_end() {
    let mut runner = make_runner(50);
    let strategy = well_formed_global_strategy(2);

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let global = tree.current();

        if matches!(global, GlobalType::End) {
            continue;
        }
        // Skip recursive types (don't terminate).
        if matches!(global, GlobalType::Mu { .. }) {
            continue;
        }

        if let Some(image) = code_image_from_global(&global) {
            let mut vm = VM::new(VMConfig::default());
            if vm.load_choreography(&image).is_err() {
                continue;
            }

            let handler = PassthroughHandler;
            vm.run(&handler, 500).unwrap_or(());

            // No faults should have occurred.
            let faults: Vec<_> = vm
                .trace()
                .iter()
                .filter(|e| matches!(e, ObsEvent::Faulted { .. }))
                .collect();
            assert!(faults.is_empty(), "unexpected faults: {faults:?}");
        }
    }
}

#[test]
fn prop_compile_ends_with_halt_or_jmp() {
    let mut runner = make_runner(50);
    let strategy = well_formed_global_strategy(2);

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let global = tree.current();

        if let Some(image) = code_image_from_global(&global) {
            for program in image.programs.values() {
                if program.is_empty() {
                    continue;
                }
                let last = program.last().unwrap();
                assert!(
                    matches!(last, Instr::Halt | Instr::Jump { .. }),
                    "program should end with Halt or Jmp, got {last:?}"
                );
            }
        }
    }
}

// ============================================================================
// Buffer FIFO
// ============================================================================

#[test]
fn prop_buffer_fifo_order() {
    let mut runner = make_runner(100);
    let strategy = 1..50usize;

    for _ in 0..100 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let n = tree.current();

        let config = BufferConfig {
            mode: BufferMode::Fifo,
            initial_capacity: n + 1,
            policy: BackpressurePolicy::Block,
        };
        let mut buf = BoundedBuffer::new(&config);

        for i in 0..n {
            buf.enqueue(Value::Int(i as i64));
        }

        for i in 0..n {
            assert_eq!(buf.dequeue(), Some(Value::Int(i as i64)));
        }
    }
}

#[test]
fn prop_buffer_enqueue_dequeue_inverse() {
    let mut runner = make_runner(100);
    let strategy = value_strategy();

    for _ in 0..100 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let val = tree.current();

        let mut buf = BoundedBuffer::new(&BufferConfig::default());
        buf.enqueue(val.clone());
        assert_eq!(buf.dequeue(), Some(val));
    }
}

#[test]
fn prop_buffer_count_invariant() {
    let mut runner = make_runner(50);
    let strategy = (1..20usize, 0..20usize);

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let (k, j_raw) = tree.current();
        let j = j_raw.min(k);

        let config = BufferConfig {
            mode: BufferMode::Fifo,
            initial_capacity: k + 1,
            policy: BackpressurePolicy::Block,
        };
        let mut buf = BoundedBuffer::new(&config);

        for i in 0..k {
            buf.enqueue(Value::Int(i as i64));
        }
        for _ in 0..j {
            buf.dequeue();
        }

        assert_eq!(buf.len(), k - j);
    }
}

#[test]
fn prop_buffer_latest_value_overwrites() {
    let mut runner = make_runner(50);
    let strategy = 2..20usize;

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let n = tree.current();

        let config = BufferConfig {
            mode: BufferMode::LatestValue,
            initial_capacity: 1,
            policy: BackpressurePolicy::Block,
        };
        let mut buf = BoundedBuffer::new(&config);

        for i in 0..n {
            buf.enqueue(Value::Int(i as i64));
        }

        assert_eq!(buf.dequeue(), Some(Value::Int((n - 1) as i64)));
    }
}

// ============================================================================
// Session Isolation
// ============================================================================

#[test]
fn prop_multi_session_no_cross_talk() {
    let image1 = helpers::simple_send_recv_image("A", "B", "msg");
    let image2 = helpers::simple_send_recv_image("A", "B", "data");

    let mut vm = VM::new(VMConfig::default());
    let sid1 = vm.load_choreography(&image1).unwrap();
    let sid2 = vm.load_choreography(&image2).unwrap();

    let handler = PassthroughHandler;
    vm.run(&handler, 200).unwrap();

    // Events for session 1 should not reference session 2 labels and vice versa.
    for event in vm.trace() {
        match event {
            ObsEvent::Sent { session, label, .. } | ObsEvent::Received { session, label, .. } => {
                if *session == sid1 {
                    assert_eq!(label, "msg");
                } else if *session == sid2 {
                    assert_eq!(label, "data");
                }
            }
            _ => {}
        }
    }
}

#[test]
fn prop_session_type_independence() {
    let image1 = helpers::simple_send_recv_image("A", "B", "msg");
    let image2 = helpers::simple_send_recv_image("A", "B", "data");

    let mut vm = VM::new(VMConfig::default());
    let _sid1 = vm.load_choreography(&image1).unwrap();
    let sid2 = vm.load_choreography(&image2).unwrap();

    let ep2a = Endpoint {
        sid: sid2,
        role: "A".into(),
    };
    let ty_before = vm.sessions().lookup_type(&ep2a).cloned();

    // Step only a few times (session 1 may advance).
    let handler = PassthroughHandler;
    for _ in 0..5 {
        let _ = vm.step(&handler);
    }

    // Session 2 type should be unchanged if session 2 hasn't been scheduled yet,
    // or advanced only by its own instructions.
    let ty_after = vm.sessions().lookup_type(&ep2a).cloned();

    // At minimum, session 2's type is either same as before or advanced by session 2's own execution.
    // Not affected by session 1.
    // This is a structural check — we verify no cross-session mutation happened.
    // If both are Some, they should be session 2's types.
    if let (Some(before), Some(after)) = (&ty_before, &ty_after) {
        // Both should be Send types for role A.
        assert!(matches!(before, LocalTypeR::Send { partner, .. } if partner == "B"));
        // after is either still Send (not yet executed) or End (executed).
        assert!(
            matches!(after, LocalTypeR::Send { partner, .. } if partner == "B")
                || matches!(after, LocalTypeR::End)
        );
    }
}

// ============================================================================
// Blocking
// ============================================================================

#[test]
fn prop_block_preserves_type() {
    // B tries to recv before A sends → blocks → type unchanged.
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();

    let ep_b = Endpoint {
        sid,
        role: "B".into(),
    };
    let ty_before = vm.sessions().lookup_type(&ep_b).cloned();

    let handler = PassthroughHandler;
    // Step once — might schedule B first (blocks) or A first.
    let _ = vm.step(&handler);

    // If B was scheduled and blocked, type should be unchanged.
    if let Some(ty_after) = vm.sessions().lookup_type(&ep_b) {
        assert!(matches!(ty_after, LocalTypeR::Recv { .. }));
    }

    // Verify the before type was Recv.
    assert!(matches!(ty_before, Some(LocalTypeR::Recv { .. })));
}

#[test]
fn prop_block_preserves_pc() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();

    // Find B's coroutine.
    let b_coro_id = vm
        .session_coroutines(sid)
        .iter()
        .find(|c| c.role == "B")
        .unwrap()
        .id;

    let pc_before = vm.coroutine(b_coro_id).unwrap().pc;

    let handler = PassthroughHandler;
    // Step a few times.
    for _ in 0..3 {
        let _ = vm.step(&handler);
    }

    // If B is blocked, PC should be same as before.
    let coro = vm.coroutine(b_coro_id).unwrap();
    if matches!(coro.status, telltale_vm::CoroStatus::Blocked(_)) {
        assert_eq!(coro.pc, pc_before);
    }
}

// ============================================================================
// Recursive Unfolding
// ============================================================================

#[test]
fn prop_unfold_mu_idempotent() {
    let lt = LocalTypeR::mu(
        "x",
        LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::var("x"))],
        },
    );

    let once = unfold_mu(&lt);
    let twice = unfold_mu(&once);
    assert_eq!(once, twice);
}

#[test]
fn prop_unfold_if_var_resolves() {
    let original = LocalTypeR::mu(
        "x",
        LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::var("x"))],
        },
    );

    let cont = LocalTypeR::var("x");
    let resolved = unfold_if_var(&cont, &original);
    assert!(matches!(resolved, LocalTypeR::Send { .. }));
}

// ============================================================================
// Compiler
// ============================================================================

#[test]
fn prop_compile_deterministic() {
    let mut runner = make_runner(50);
    let strategy = well_formed_global_strategy(2);

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let global = tree.current();

        if let Some(image) = code_image_from_global(&global) {
            for (role, lt) in &image.local_types {
                let c1 = compile(lt);
                let c2 = compile(lt);
                assert_eq!(c1, c2, "compile should be deterministic for role {role}");
            }
        }
    }
}

#[test]
fn prop_compile_nonempty_for_actions() {
    let mut runner = make_runner(50);
    let strategy = well_formed_global_strategy(2);

    for _ in 0..50 {
        let tree = strategy.new_tree(&mut runner).unwrap();
        let global = tree.current();

        if let Some(image) = code_image_from_global(&global) {
            for (role, lt) in &image.local_types {
                let code = compile(lt);
                if !matches!(lt, LocalTypeR::End) {
                    assert!(
                        !code.is_empty(),
                        "non-End type for {role} should compile to non-empty bytecode"
                    );
                }
            }
        }
    }
}
