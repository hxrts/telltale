//! Property and scenario tests for channel abstractions.
//!
//! Verifies correctness of core channel invariants:
//! - FIFO message ordering
//! - Seal behavior (terminates stream, idempotent)
//! - Bidirectional Sink/Stream delegation
//! - Channel pair isolation
//! - Nil channel behavior

#![allow(clippy::unwrap_used)]

use crate::channel::{Bidirectional, Nil, Pair};
use crate::Sealable;
use futures::channel::mpsc::{self, UnboundedReceiver, UnboundedSender};
use futures::{SinkExt, StreamExt};
use proptest::prelude::*;

type TestChannel = Bidirectional<UnboundedSender<i32>, UnboundedReceiver<i32>>;

// ============================================================================
// Nil Channel Tests
// ============================================================================

#[test]
fn test_nil_pair_returns_nil_nil() {
    let (a, b) = Nil::pair();
    assert_eq!(a, Nil);
    assert_eq!(b, Nil);
}

#[test]
fn test_nil_seal_is_noop() {
    let mut nil = Nil;
    nil.seal();
    // Should not panic, and state doesn't change
    assert!(!nil.is_sealed());
}

#[test]
fn test_nil_is_sealed_always_false() {
    let nil = Nil;
    assert!(!nil.is_sealed());
}

#[test]
fn test_nil_default_and_clone() {
    let nil1 = Nil;
    let nil2 = nil1;
    assert_eq!(nil1, nil2);
}

// ============================================================================
// UnboundedSender/Receiver Pair Tests
// ============================================================================

#[test]
fn test_unbounded_pair_creates_connected_channels() {
    let (tx, mut rx): (UnboundedSender<i32>, UnboundedReceiver<i32>) = Pair::pair();

    // Should be able to send and receive
    tx.unbounded_send(42).unwrap();
    let received = rx.try_next().unwrap();
    assert_eq!(received, Some(42));
}

#[test]
fn test_unbounded_pair_reverse_order() {
    // Test the reverse pair implementation
    let (rx, tx): (UnboundedReceiver<i32>, UnboundedSender<i32>) = Pair::pair();

    tx.unbounded_send(123).unwrap();
    let mut rx = rx;
    let received = rx.try_next().unwrap();
    assert_eq!(received, Some(123));
}

#[test]
fn test_unbounded_sender_seal() {
    let (mut tx, _rx): (UnboundedSender<i32>, UnboundedReceiver<i32>) = Pair::pair();

    assert!(!tx.is_sealed());
    tx.seal();
    assert!(tx.is_sealed());

    // Sending should fail after seal
    assert!(tx.unbounded_send(42).is_err());
}

#[test]
fn test_unbounded_receiver_seal() {
    let (tx, mut rx): (UnboundedSender<i32>, UnboundedReceiver<i32>) = Pair::pair();

    // Receiver seal closes it
    rx.seal();

    // Sender should now fail (receiver closed)
    assert!(tx.unbounded_send(42).is_err());
}

// ============================================================================
// Bidirectional Channel Tests
// ============================================================================

#[test]
fn test_bidirectional_pair_creates_connected_channels() {
    let (mut a, mut b): (TestChannel, TestChannel) = Pair::pair();

    // A sends to B
    futures::executor::block_on(async {
        a.send(1).await.unwrap();
        let received = b.next().await;
        assert_eq!(received, Some(1));
    });
}

#[test]
fn test_bidirectional_pair_both_directions() {
    let (mut a, mut b): (TestChannel, TestChannel) = Pair::pair();

    futures::executor::block_on(async {
        // A -> B
        a.send(10).await.unwrap();
        assert_eq!(b.next().await, Some(10));

        // B -> A
        b.send(20).await.unwrap();
        assert_eq!(a.next().await, Some(20));
    });
}

#[test]
fn test_channel_pair_isolation() {
    // Messages sent A→B should not appear on B→A channel
    let (mut a, mut b): (TestChannel, TestChannel) = Pair::pair();

    futures::executor::block_on(async {
        // Send from A to B
        a.send(100).await.unwrap();
        a.send(200).await.unwrap();

        // B should receive both
        assert_eq!(b.next().await, Some(100));
        assert_eq!(b.next().await, Some(200));

        // A should NOT receive these (they went to B)
        // Send from B to A to verify A's receive channel is separate
        b.send(999).await.unwrap();
        assert_eq!(a.next().await, Some(999));
    });
}

#[test]
fn test_bidirectional_new_constructor() {
    let (tx, rx) = mpsc::unbounded::<i32>();
    let channel = Bidirectional::new(tx, rx);

    assert!(!channel.is_sealed());
}

// ============================================================================
// Seal Behavior Tests
// ============================================================================

#[test]
fn test_bidirectional_seal_terminates_stream() {
    let (mut a, _b): (TestChannel, TestChannel) = Pair::pair();

    futures::executor::block_on(async {
        // Seal the channel
        a.seal();
        assert!(a.is_sealed());

        // Stream should return None immediately
        let result = a.next().await;
        assert_eq!(result, None);
    });
}

#[test]
fn test_seal_idempotent() {
    let (mut a, _b): (TestChannel, TestChannel) = Pair::pair();

    // Multiple seals should not panic
    a.seal();
    a.seal();
    a.seal();

    assert!(a.is_sealed());
}

#[test]
fn test_seal_preserves_pending_messages() {
    let (mut a, mut b): (TestChannel, TestChannel) = Pair::pair();

    futures::executor::block_on(async {
        // Send messages before sealing
        a.send(1).await.unwrap();
        a.send(2).await.unwrap();
        a.send(3).await.unwrap();

        // Seal A (this seals A's receive side, not B's)
        a.seal();

        // B should still receive all messages that were sent
        assert_eq!(b.next().await, Some(1));
        assert_eq!(b.next().await, Some(2));
        assert_eq!(b.next().await, Some(3));
    });
}

#[test]
fn test_is_sealed_before_seal() {
    let (a, _b): (TestChannel, TestChannel) = Pair::pair();
    assert!(!a.is_sealed());
}

#[test]
fn test_sealed_channel_returns_none_repeatedly() {
    let (mut a, _b): (TestChannel, TestChannel) = Pair::pair();

    futures::executor::block_on(async {
        a.seal();

        // Multiple calls should all return None
        assert_eq!(a.next().await, None);
        assert_eq!(a.next().await, None);
        assert_eq!(a.next().await, None);
    });
}

// ============================================================================
// FIFO Ordering Property Tests
// ============================================================================

proptest! {
    #[test]
    fn prop_fifo_ordering(messages in prop::collection::vec(any::<i32>(), 0..100)) {
        let (mut a, mut b): (TestChannel, TestChannel) = Pair::pair();

        futures::executor::block_on(async {
            // Send all messages
            for &msg in &messages {
                a.send(msg).await.unwrap();
            }

            // Receive all messages and verify order
            for &expected in &messages {
                let received = b.next().await;
                prop_assert_eq!(received, Some(expected));
            }

            Ok(())
        })?;
    }

    #[test]
    fn prop_bidirectional_fifo_both_directions(
        a_to_b in prop::collection::vec(any::<i32>(), 0..50),
        b_to_a in prop::collection::vec(any::<i32>(), 0..50)
    ) {
        let (mut a, mut b): (TestChannel, TestChannel) = Pair::pair();

        futures::executor::block_on(async {
            // Send all A→B messages
            for &msg in &a_to_b {
                a.send(msg).await.unwrap();
            }

            // Send all B→A messages
            for &msg in &b_to_a {
                b.send(msg).await.unwrap();
            }

            // Verify A→B ordering
            for &expected in &a_to_b {
                let received = b.next().await;
                prop_assert_eq!(received, Some(expected));
            }

            // Verify B→A ordering
            for &expected in &b_to_a {
                let received = a.next().await;
                prop_assert_eq!(received, Some(expected));
            }

            Ok(())
        })?;
    }

    #[test]
    fn prop_seal_terminates_stream_with_pending(
        messages in prop::collection::vec(any::<i32>(), 0..20)
    ) {
        let (mut a, mut b): (TestChannel, TestChannel) = Pair::pair();

        futures::executor::block_on(async {
            // Send messages
            for &msg in &messages {
                a.send(msg).await.unwrap();
            }

            // Seal the receiver side
            b.seal();

            // B's stream should return None (sealed)
            let result = b.next().await;
            prop_assert_eq!(result, None);

            Ok(())
        })?;
    }

    #[test]
    fn prop_seal_idempotent_property(seal_count in 1usize..10) {
        let (mut a, _b): (TestChannel, TestChannel) = Pair::pair();

        // Multiple seals should all succeed without panic
        for _ in 0..seal_count {
            a.seal();
        }

        prop_assert!(a.is_sealed());
    }
}

// ============================================================================
// Sink/Stream Trait Delegation Tests
// ============================================================================

#[test]
fn test_sink_poll_ready() {
    let (mut a, _b): (TestChannel, TestChannel) = Pair::pair();

    futures::executor::block_on(async {
        // poll_ready should succeed for unbounded channel
        futures::future::poll_fn(|cx| {
            use std::pin::Pin;
            let pinned = Pin::new(&mut a);
            let result = futures::Sink::poll_ready(pinned, cx);
            assert!(result.is_ready());
            std::task::Poll::Ready(())
        })
        .await;
    });
}

#[test]
fn test_sink_start_send_and_flush() {
    let (mut a, mut b): (TestChannel, TestChannel) = Pair::pair();

    futures::executor::block_on(async {
        // Use SinkExt methods which wrap the raw Sink trait
        a.send(42).await.unwrap();
        a.flush().await.unwrap();

        let received = b.next().await;
        assert_eq!(received, Some(42));
    });
}

#[test]
fn test_sink_close() {
    let (mut a, mut b): (TestChannel, TestChannel) = Pair::pair();

    futures::executor::block_on(async {
        // Send a message first
        a.send(123).await.unwrap();

        // Close the sink (this closes the sender side)
        a.close().await.unwrap();

        // B should receive the message
        assert_eq!(b.next().await, Some(123));

        // B's stream should eventually end (sender closed)
        assert_eq!(b.next().await, None);
    });
}

// ============================================================================
// Edge Cases
// ============================================================================

#[test]
fn test_empty_channel_receive() {
    let (mut _a, mut b): (TestChannel, TestChannel) = Pair::pair();

    // Drop sender
    drop(_a);

    futures::executor::block_on(async {
        // Receiver should get None when sender is dropped
        let result = b.next().await;
        assert_eq!(result, None);
    });
}

#[test]
fn test_multiple_channel_pairs_independent() {
    let (mut a1, mut b1): (TestChannel, TestChannel) = Pair::pair();
    let (mut a2, mut b2): (TestChannel, TestChannel) = Pair::pair();

    futures::executor::block_on(async {
        // Send on pair 1
        a1.send(111).await.unwrap();

        // Send on pair 2
        a2.send(222).await.unwrap();

        // Each pair should receive its own messages
        assert_eq!(b1.next().await, Some(111));
        assert_eq!(b2.next().await, Some(222));
    });
}

#[test]
fn test_channel_with_string_type() {
    type StringChannel = Bidirectional<UnboundedSender<String>, UnboundedReceiver<String>>;
    let (mut a, mut b): (StringChannel, StringChannel) = Pair::pair();

    futures::executor::block_on(async {
        a.send("hello".to_string()).await.unwrap();
        a.send("world".to_string()).await.unwrap();

        assert_eq!(b.next().await, Some("hello".to_string()));
        assert_eq!(b.next().await, Some("world".to_string()));
    });
}
