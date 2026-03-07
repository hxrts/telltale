#![cfg(not(target_arch = "wasm32"))]
//! Session lifecycle and buffer functional tests.
#![allow(clippy::needless_collect, clippy::let_underscore_must_use)]

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use std::collections::BTreeMap;

use assert_matches::assert_matches;
use telltale_types::{Label, LocalTypeR};
use telltale_vm::buffer::{
    BackpressurePolicy, BoundedBuffer, BufferConfig, BufferMode, EnqueueResult,
};
use telltale_vm::coroutine::{CoroStatus, Value};
use telltale_vm::instr::Endpoint;
use telltale_vm::session::{SessionStatus, SessionStore};
use telltale_vm::vm::{ObservabilityRetentionConfig, ObservabilityRetentionMode, VMConfig, VM};

use test_support::PassthroughHandler;

fn simple_send_recv_types() -> BTreeMap<String, LocalTypeR> {
    let mut types = BTreeMap::new();
    types.insert(
        "A".to_string(),
        LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End),
    );
    types.insert(
        "B".to_string(),
        LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End),
    );
    types
}

// ============================================================================
// Session Lifecycle
// ============================================================================

#[test]
fn test_session_active_to_closed() {
    let image = test_support::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    vm.run(&handler, 100).unwrap();

    // After completion, session should still be accessible.
    let session = vm.sessions().get(sid).unwrap();
    // Status is Active since we didn't explicitly close.
    assert_matches!(session.status, SessionStatus::Active);
}

#[test]
fn test_session_active_to_closed_clears_pending_buffers() {
    let mut store = SessionStore::new();
    let sid = store.open(
        vec!["A".into(), "B".into()],
        &BufferConfig::default(),
        &simple_send_recv_types(),
    );

    // Put a message in the buffer.
    let session = store.get_mut(sid).unwrap();
    let _ = session.send("A", "B", Value::Nat(1)).unwrap();

    // Lean-aligned close: closes immediately and clears pending buffers.
    store.close(sid).unwrap();
    let session = store.get(sid).unwrap();
    assert_matches!(session.status, SessionStatus::Closed);
    assert!(session.buffers.is_empty());
}

#[test]
fn test_session_ids_monotonic() {
    let mut store = SessionStore::new();
    let sid1 = store.open(
        vec!["A".into(), "B".into()],
        &BufferConfig::default(),
        &simple_send_recv_types(),
    );
    let sid2 = store.open(
        vec!["A".into(), "B".into()],
        &BufferConfig::default(),
        &simple_send_recv_types(),
    );
    let sid3 = store.open(
        vec!["A".into(), "B".into()],
        &BufferConfig::default(),
        &BTreeMap::new(),
    );

    assert!(sid1 < sid2);
    assert!(sid2 < sid3);
}

#[test]
fn test_active_count_tracks_sessions() {
    let mut store = SessionStore::new();
    assert_eq!(store.active_count(), 0);

    let sid1 = store.open(
        vec!["A".into(), "B".into()],
        &BufferConfig::default(),
        &BTreeMap::new(),
    );
    assert_eq!(store.active_count(), 1);

    let _sid2 = store.open(
        vec!["A".into(), "B".into()],
        &BufferConfig::default(),
        &BTreeMap::new(),
    );
    assert_eq!(store.active_count(), 2);

    store.close(sid1).unwrap();
    // Closed sessions are not active.
    assert_eq!(store.active_count(), 1);
}

#[test]
fn test_vm_reap_closed_sessions_removes_terminal_coroutines_and_live_session_state() {
    let mut vm = VM::new(VMConfig::default());
    let sid = vm
        .load_choreography(&test_support::simple_send_recv_image("A", "B", "msg"))
        .expect("load choreography");

    vm.sessions_mut().close(sid).expect("close session");
    let coro_ids: Vec<usize> = vm
        .session_coroutines(sid)
        .iter()
        .map(|coro| coro.id)
        .collect();
    for coro_id in &coro_ids {
        vm.coroutine_mut(*coro_id).expect("coroutine exists").status = CoroStatus::Done;
    }

    let before = vm.memory_usage();
    assert_eq!(before.session_store.live_sessions, 1);
    assert_eq!(before.session_store.live_closed_sessions, 1);
    assert_eq!(before.coroutine_records, coro_ids.len());
    assert!(before.retained_bytes.total > 0);
    assert!(before.retained_bytes.session_store > 0);
    assert!(before.retained_bytes.coroutines > 0);

    let reaped = vm.reap_closed_sessions();
    assert_eq!(reaped.len(), 1);
    assert_eq!(reaped[0].sid, sid);
    assert_eq!(vm.live_session_count(), 0);
    assert_eq!(vm.coroutine_count(), 0);
    assert!(vm.wf_vm_state().is_ok());

    let after = vm.memory_usage();
    assert_eq!(after.session_store.live_sessions, 0);
    assert_eq!(after.session_store.live_closed_sessions, 0);
    assert_eq!(after.session_store.archived_closed_sessions, 1);
    assert_eq!(after.coroutine_records, 0);
    assert_eq!(after.retained_bytes.coroutines, 0);
    assert!(after.retained_bytes.session_store > 0);
    assert!(after.retained_bytes.total < before.retained_bytes.total);
}

#[test]
fn test_vm_reap_closed_sessions_skips_nonterminal_coroutines() {
    let mut vm = VM::new(VMConfig::default());
    let sid = vm
        .load_choreography(&test_support::simple_send_recv_image("A", "B", "msg"))
        .expect("load choreography");

    vm.sessions_mut().close(sid).expect("close session");
    let reaped = vm.reap_closed_sessions();
    assert!(reaped.is_empty());
    assert_eq!(vm.live_session_count(), 1);
}

#[test]
fn test_vm_observability_retention_capped_keeps_latest_suffix_in_order() {
    let image = test_support::simple_send_recv_image("A", "B", "msg");
    let handler = PassthroughHandler;

    let mut full = VM::new(VMConfig::default());
    full.load_choreography(&image).expect("load choreography");
    full.run(&handler, 100).expect("run choreography");
    let full_trace = full.trace().to_vec();
    let full_effect_trace = full.effect_trace().to_vec();

    let cap = 3;
    let mut capped = VM::new(VMConfig {
        observability_retention: ObservabilityRetentionConfig {
            mode: ObservabilityRetentionMode::Capped,
            capacity: cap,
        },
        ..VMConfig::default()
    });
    capped.load_choreography(&image).expect("load choreography");
    capped.run(&handler, 100).expect("run choreography");

    let expected_trace_start = full_trace.len().saturating_sub(cap);
    let expected_effect_start = full_effect_trace.len().saturating_sub(cap);
    assert_eq!(capped.trace(), &full_trace[expected_trace_start..]);
    assert_eq!(
        capped.effect_trace(),
        &full_effect_trace[expected_effect_start..]
    );

    let drained_trace = capped.drain_obs_trace();
    assert_eq!(drained_trace, full_trace[expected_trace_start..].to_vec());
    assert!(capped.trace().is_empty());

    let drained_effect_trace = capped.drain_effect_trace();
    assert_eq!(
        drained_effect_trace,
        full_effect_trace[expected_effect_start..].to_vec()
    );
    assert!(capped.effect_trace().is_empty());
}

#[test]
fn test_vm_observability_retention_disabled_drops_storage_without_changing_faults() {
    let image = test_support::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig {
        observability_retention: ObservabilityRetentionConfig {
            mode: ObservabilityRetentionMode::Disabled,
            capacity: 1,
        },
        ..VMConfig::default()
    });
    vm.load_choreography(&image).expect("load choreography");
    vm.run(&PassthroughHandler, 100).expect("run choreography");

    assert!(vm.trace().is_empty());
    assert!(vm.effect_trace().is_empty());
    assert!(vm.output_condition_checks().is_empty());
    assert!(vm.communication_consumption_artifacts().is_empty());

    let usage = vm.memory_usage();
    assert_eq!(usage.obs_events, 0);
    assert_eq!(usage.effect_trace_entries, 0);
    assert_eq!(usage.output_condition_checks, 0);
    assert_eq!(usage.communication_artifacts, 0);
    assert!(usage.retained_bytes.traces > 0);
    assert!(usage.retained_bytes.output_condition_checks > 0);
}

#[test]
fn test_vm_reuses_immutable_program_storage_across_identical_loads() {
    let image = test_support::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());

    let sid1 = vm.load_choreography(&image).expect("load choreography");
    let usage_after_first = vm.memory_usage();
    assert_eq!(vm.unique_program_count(), 2);
    let program_instruction_count = usage_after_first.program_instruction_count;
    assert!(program_instruction_count > 0);

    let sid2 = vm.load_choreography(&image).expect("load choreography");
    let usage_after_second = vm.memory_usage();

    assert_ne!(sid1, sid2);
    assert_eq!(vm.unique_program_count(), 2);
    assert_eq!(
        usage_after_second.program_instruction_count,
        program_instruction_count
    );
    assert_eq!(vm.coroutine_count(), 4);
}

#[test]
fn test_vm_session_churn_with_reaping_and_capped_retention_stays_bounded() {
    let image = test_support::simple_send_recv_image("A", "B", "msg");
    let cap = 8;
    let mut vm = VM::new(VMConfig {
        observability_retention: ObservabilityRetentionConfig {
            mode: ObservabilityRetentionMode::Capped,
            capacity: cap,
        },
        ..VMConfig::default()
    });
    let handler = PassthroughHandler;

    for _ in 0..32 {
        let sid = vm.load_choreography(&image).expect("load choreography");
        vm.run(&handler, 100).expect("run choreography");
        vm.sessions_mut().close(sid).expect("close session");
        let coro_ids: Vec<usize> = vm
            .session_coroutines(sid)
            .iter()
            .map(|coro| coro.id)
            .collect();
        for coro_id in coro_ids {
            vm.coroutine_mut(coro_id).expect("coroutine exists").status = CoroStatus::Done;
        }

        let reaped = vm.reap_closed_sessions();
        assert_eq!(reaped.len(), 1);

        let usage = vm.memory_usage();
        assert_eq!(usage.session_store.live_sessions, 0);
        assert_eq!(usage.session_store.live_closed_sessions, 0);
        assert_eq!(usage.coroutine_records, 0);
        assert!(usage.obs_events <= cap);
        assert!(usage.effect_trace_entries <= cap);
    }
}

// ============================================================================
// Buffer Mode × Policy Matrix
// ============================================================================

#[test]
fn test_fifo_block() {
    let config = BufferConfig {
        mode: BufferMode::Fifo,
        initial_capacity: 2,
        policy: BackpressurePolicy::Block,
    };
    let mut buf = BoundedBuffer::new(&config);
    buf.enqueue(Value::Nat(1));
    buf.enqueue(Value::Nat(2));
    assert_matches!(buf.enqueue(Value::Nat(3)), EnqueueResult::WouldBlock);
}

#[test]
fn test_fifo_drop() {
    let config = BufferConfig {
        mode: BufferMode::Fifo,
        initial_capacity: 2,
        policy: BackpressurePolicy::Drop,
    };
    let mut buf = BoundedBuffer::new(&config);
    buf.enqueue(Value::Nat(1));
    buf.enqueue(Value::Nat(2));
    assert_matches!(buf.enqueue(Value::Nat(3)), EnqueueResult::Dropped);
    // First two values still intact.
    assert_eq!(buf.dequeue(), Some(Value::Nat(1)));
    assert_eq!(buf.dequeue(), Some(Value::Nat(2)));
}

#[test]
fn test_fifo_error() {
    let config = BufferConfig {
        mode: BufferMode::Fifo,
        initial_capacity: 2,
        policy: BackpressurePolicy::Error,
    };
    let mut buf = BoundedBuffer::new(&config);
    buf.enqueue(Value::Nat(1));
    buf.enqueue(Value::Nat(2));
    assert_matches!(buf.enqueue(Value::Nat(3)), EnqueueResult::Full);
}

#[test]
fn test_fifo_resize() {
    let config = BufferConfig {
        mode: BufferMode::Fifo,
        initial_capacity: 2,
        policy: BackpressurePolicy::Resize { max_capacity: 8 },
    };
    let mut buf = BoundedBuffer::new(&config);
    buf.enqueue(Value::Nat(1));
    buf.enqueue(Value::Nat(2));
    assert_matches!(buf.enqueue(Value::Nat(3)), EnqueueResult::Ok);
    assert_eq!(buf.len(), 3);
    // FIFO order preserved.
    assert_eq!(buf.dequeue(), Some(Value::Nat(1)));
    assert_eq!(buf.dequeue(), Some(Value::Nat(2)));
    assert_eq!(buf.dequeue(), Some(Value::Nat(3)));
}

#[test]
fn test_latest_value_overwrites() {
    let config = BufferConfig {
        mode: BufferMode::LatestValue,
        initial_capacity: 1,
        policy: BackpressurePolicy::Block,
    };
    let mut buf = BoundedBuffer::new(&config);
    buf.enqueue(Value::Nat(1));
    buf.enqueue(Value::Nat(2));
    buf.enqueue(Value::Nat(3));
    assert_eq!(buf.dequeue(), Some(Value::Nat(3)));
}

#[test]
fn test_latest_value_dequeue_clears() {
    let config = BufferConfig {
        mode: BufferMode::LatestValue,
        initial_capacity: 1,
        policy: BackpressurePolicy::Block,
    };
    let mut buf = BoundedBuffer::new(&config);
    buf.enqueue(Value::Nat(1));
    assert_eq!(buf.len(), 1);
    buf.dequeue();
    assert_eq!(buf.len(), 0);
    assert!(buf.is_empty());
}

#[test]
fn test_buffer_empty_dequeue_none() {
    let mut buf: BoundedBuffer<Value> = BoundedBuffer::new(&BufferConfig::default());
    assert_eq!(buf.dequeue(), None);
}

#[test]
fn test_buffer_resize_preserves_order() {
    let config = BufferConfig {
        mode: BufferMode::Fifo,
        initial_capacity: 2,
        policy: BackpressurePolicy::Resize { max_capacity: 16 },
    };
    let mut buf = BoundedBuffer::new(&config);

    // Partially fill and dequeue to offset head.
    buf.enqueue(Value::Nat(0));
    buf.dequeue();

    // Fill beyond initial capacity.
    for i in 1..=5 {
        buf.enqueue(Value::Nat(i));
    }

    // Verify FIFO.
    for i in 1..=5 {
        assert_eq!(buf.dequeue(), Some(Value::Nat(i)));
    }
}

// ============================================================================
// Multi-Session Isolation
// ============================================================================

#[test]
fn test_two_sessions_independent_types() {
    let image1 = test_support::simple_send_recv_image("A", "B", "msg");
    let image2 = test_support::simple_send_recv_image("A", "B", "data");

    let mut vm = VM::new(VMConfig::default());
    let sid1 = vm.load_choreography(&image1).unwrap();
    let sid2 = vm.load_choreography(&image2).unwrap();

    let ep1a = Endpoint {
        sid: sid1,
        role: "A".into(),
    };
    let ep2a = Endpoint {
        sid: sid2,
        role: "A".into(),
    };

    // Types should be independent.
    let t1 = vm.sessions().lookup_type(&ep1a).cloned();
    let t2 = vm.sessions().lookup_type(&ep2a).cloned();

    assert_matches!(t1, Some(LocalTypeR::Send { .. }));
    assert_matches!(t2, Some(LocalTypeR::Send { .. }));

    let handler = PassthroughHandler;
    vm.run(&handler, 200).unwrap();

    // Both completed independently.
    assert!(vm.sessions().lookup_type(&ep1a).is_none());
    assert!(vm.sessions().lookup_type(&ep2a).is_none());
}

#[test]
fn test_two_sessions_independent_buffers() {
    let mut store = SessionStore::new();
    let sid1 = store.open(
        vec!["A".into(), "B".into()],
        &BufferConfig::default(),
        &simple_send_recv_types(),
    );
    let sid2 = store.open(
        vec!["A".into(), "B".into()],
        &BufferConfig::default(),
        &simple_send_recv_types(),
    );

    // Send in session 1.
    store
        .get_mut(sid1)
        .unwrap()
        .send("A", "B", Value::Nat(1))
        .unwrap();

    // Session 2 should not see the message.
    assert!(!store.get(sid2).unwrap().has_message("A", "B"));
}

#[test]
fn test_three_sessions_complete_independently() {
    let image = test_support::simple_send_recv_image("A", "B", "msg");

    let mut vm = VM::new(VMConfig::default());
    let sid1 = vm.load_choreography(&image).unwrap();
    let sid2 = vm.load_choreography(&image).unwrap();
    let sid3 = vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    vm.run(&handler, 500).unwrap();

    for sid in [sid1, sid2, sid3] {
        assert!(
            vm.session_coroutines(sid).iter().all(|c| c.is_terminal()),
            "session {sid} should have all terminal coroutines"
        );
    }
}
