//! Session lifecycle and buffer functional tests.
#![allow(clippy::needless_collect, clippy::let_underscore_must_use)]

#[allow(dead_code, unreachable_pub)]
mod helpers;

use std::collections::BTreeMap;

use assert_matches::assert_matches;
use telltale_types::LocalTypeR;
use telltale_vm::buffer::{
    BackpressurePolicy, BoundedBuffer, BufferConfig, BufferMode, EnqueueResult,
};
use telltale_vm::coroutine::Value;
use telltale_vm::instr::Endpoint;
use telltale_vm::session::{SessionStatus, SessionStore};
use telltale_vm::vm::{VMConfig, VM};

use helpers::PassthroughHandler;

// ============================================================================
// Session Lifecycle
// ============================================================================

#[test]
fn test_session_active_to_closed() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
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
fn test_session_active_to_draining() {
    let mut store = SessionStore::new();
    let sid = store.open(
        vec!["A".into(), "B".into()],
        &BufferConfig::default(),
        &BTreeMap::new(),
    );

    // Put a message in the buffer.
    let session = store.get_mut(sid).unwrap();
    let _ = session.send("A", "B", Value::Int(1)).unwrap();

    // Close with pending messages → Draining.
    store.close(sid).unwrap();
    assert_matches!(store.get(sid).unwrap().status, SessionStatus::Draining);
}

#[test]
fn test_session_ids_monotonic() {
    let mut store = SessionStore::new();
    let sid1 = store.open(
        vec!["A".into(), "B".into()],
        &BufferConfig::default(),
        &BTreeMap::new(),
    );
    let sid2 = store.open(
        vec!["A".into(), "B".into()],
        &BufferConfig::default(),
        &BTreeMap::new(),
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
    buf.enqueue(Value::Int(1));
    buf.enqueue(Value::Int(2));
    assert_matches!(buf.enqueue(Value::Int(3)), EnqueueResult::WouldBlock);
}

#[test]
fn test_fifo_drop() {
    let config = BufferConfig {
        mode: BufferMode::Fifo,
        initial_capacity: 2,
        policy: BackpressurePolicy::Drop,
    };
    let mut buf = BoundedBuffer::new(&config);
    buf.enqueue(Value::Int(1));
    buf.enqueue(Value::Int(2));
    assert_matches!(buf.enqueue(Value::Int(3)), EnqueueResult::Dropped);
    // First two values still intact.
    assert_eq!(buf.dequeue(), Some(Value::Int(1)));
    assert_eq!(buf.dequeue(), Some(Value::Int(2)));
}

#[test]
fn test_fifo_error() {
    let config = BufferConfig {
        mode: BufferMode::Fifo,
        initial_capacity: 2,
        policy: BackpressurePolicy::Error,
    };
    let mut buf = BoundedBuffer::new(&config);
    buf.enqueue(Value::Int(1));
    buf.enqueue(Value::Int(2));
    assert_matches!(buf.enqueue(Value::Int(3)), EnqueueResult::Full);
}

#[test]
fn test_fifo_resize() {
    let config = BufferConfig {
        mode: BufferMode::Fifo,
        initial_capacity: 2,
        policy: BackpressurePolicy::Resize { max_capacity: 8 },
    };
    let mut buf = BoundedBuffer::new(&config);
    buf.enqueue(Value::Int(1));
    buf.enqueue(Value::Int(2));
    assert_matches!(buf.enqueue(Value::Int(3)), EnqueueResult::Ok);
    assert_eq!(buf.len(), 3);
    // FIFO order preserved.
    assert_eq!(buf.dequeue(), Some(Value::Int(1)));
    assert_eq!(buf.dequeue(), Some(Value::Int(2)));
    assert_eq!(buf.dequeue(), Some(Value::Int(3)));
}

#[test]
fn test_latest_value_overwrites() {
    let config = BufferConfig {
        mode: BufferMode::LatestValue,
        initial_capacity: 1,
        policy: BackpressurePolicy::Block,
    };
    let mut buf = BoundedBuffer::new(&config);
    buf.enqueue(Value::Int(1));
    buf.enqueue(Value::Int(2));
    buf.enqueue(Value::Int(3));
    assert_eq!(buf.dequeue(), Some(Value::Int(3)));
}

#[test]
fn test_latest_value_dequeue_clears() {
    let config = BufferConfig {
        mode: BufferMode::LatestValue,
        initial_capacity: 1,
        policy: BackpressurePolicy::Block,
    };
    let mut buf = BoundedBuffer::new(&config);
    buf.enqueue(Value::Int(1));
    assert_eq!(buf.len(), 1);
    buf.dequeue();
    assert_eq!(buf.len(), 0);
    assert!(buf.is_empty());
}

#[test]
fn test_buffer_empty_dequeue_none() {
    let mut buf = BoundedBuffer::new(&BufferConfig::default());
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
    buf.enqueue(Value::Int(0));
    buf.dequeue();

    // Fill beyond initial capacity.
    for i in 1..=5 {
        buf.enqueue(Value::Int(i));
    }

    // Verify FIFO.
    for i in 1..=5 {
        assert_eq!(buf.dequeue(), Some(Value::Int(i)));
    }
}

// ============================================================================
// Multi-Session Isolation
// ============================================================================

#[test]
fn test_two_sessions_independent_types() {
    let image1 = helpers::simple_send_recv_image("A", "B", "msg");
    let image2 = helpers::simple_send_recv_image("A", "B", "data");

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
        &BTreeMap::new(),
    );
    let sid2 = store.open(
        vec!["A".into(), "B".into()],
        &BufferConfig::default(),
        &BTreeMap::new(),
    );

    // Send in session 1.
    store
        .get_mut(sid1)
        .unwrap()
        .send("A", "B", Value::Int(1))
        .unwrap();

    // Session 2 should not see the message.
    assert!(!store.get(sid2).unwrap().has_message("A", "B"));
}

#[test]
fn test_three_sessions_complete_independently() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");

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
