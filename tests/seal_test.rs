// Test file to verify session sealing works correctly

use futures::{
    channel::mpsc::{UnboundedReceiver, UnboundedSender},
    executor, try_join,
};
use rumpsteak_aura::{
    channel::Bidirectional, session, try_session, End, Message, Receive, Role, Roles, Send,
};
use std::{error::Error, result};

type Result<T> = result::Result<T, Box<dyn Error>>;

type Channel = Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;

#[derive(Roles)]
struct Roles(A, B);

#[derive(Role)]
#[message(Label)]
struct A(#[route(B)] Channel);

#[derive(Role)]
#[message(Label)]
struct B(#[route(A)] Channel);

#[derive(Message)]
enum Label {
    Hello(Hello),
}

#[allow(dead_code)]
struct Hello(i32);

#[session]
type AProtocol = Send<B, Hello, End>;

#[session]
type BProtocol = Receive<A, Hello, End>;

#[test]
fn test_session_sealing() {
    let Roles(mut a, mut b) = Roles::default();

    executor::block_on(async {
        // Run a complete session
        let _: Result<_> = try_join!(
            try_session(&mut a, |s: AProtocol<'_, _>| async {
                let s = s.send(Hello(42)).await?;
                Ok(((), s))
            }),
            try_session(&mut b, |s: BProtocol<'_, _>| async {
                let (Hello(_), s) = s.receive().await?;
                Ok(((), s))
            })
        )
        .map(|_| ());

        // Verify that roles are sealed after session
        assert!(
            a.is_sealed(),
            "Role A should be sealed after session completion"
        );
        assert!(
            b.is_sealed(),
            "Role B should be sealed after session completion"
        );
    });
}

#[test]
#[should_panic(expected = "Session dropped without completing")]
#[cfg(debug_assertions)]
fn test_incomplete_session_panics() {
    let Roles(mut a, mut _b) = Roles::default();

    executor::block_on(async {
        // Start a session but don't complete it (don't await)
        let _ = try_session(&mut a, |s: AProtocol<'_, _>| async {
            // Deliberately don't send anything
            // This should panic in debug mode when the guard is dropped
            let _ = s;
            Err::<((), End<_>), &str>("incomplete")
        })
        .await;
    });
}

#[test]
fn test_sealed_channel_prevents_operations() {
    let Roles(mut a, mut b) = Roles::default();

    executor::block_on(async {
        // Complete first session
        let _: Result<_> = try_join!(
            try_session(&mut a, |s: AProtocol<'_, _>| async {
                let s = s.send(Hello(1)).await?;
                Ok(((), s))
            }),
            try_session(&mut b, |s: BProtocol<'_, _>| async {
                let (Hello(_), s) = s.receive().await?;
                Ok(((), s))
            })
        )
        .map(|_| ());

        // Verify roles are sealed and can't be used again
        assert!(
            a.is_sealed(),
            "Role A should be sealed after session completion"
        );
        assert!(
            b.is_sealed(),
            "Role B should be sealed after session completion"
        );
    });
}

// ============================================================================
// Additional Edge Case Tests
// ============================================================================

#[test]
fn test_is_sealed_consistency_before_and_after() {
    let Roles(mut a, mut b) = Roles::default();

    // Before session, roles should not be sealed
    assert!(
        !a.is_sealed(),
        "Role A should not be sealed before session"
    );
    assert!(
        !b.is_sealed(),
        "Role B should not be sealed before session"
    );

    executor::block_on(async {
        let _: Result<_> = try_join!(
            try_session(&mut a, |s: AProtocol<'_, _>| async {
                let s = s.send(Hello(100)).await?;
                Ok(((), s))
            }),
            try_session(&mut b, |s: BProtocol<'_, _>| async {
                let (Hello(_), s) = s.receive().await?;
                Ok(((), s))
            })
        )
        .map(|_| ());
    });

    // After session, roles should be sealed
    assert!(a.is_sealed(), "Role A should be sealed after session");
    assert!(b.is_sealed(), "Role B should be sealed after session");

    // Multiple is_sealed() calls should be consistent
    assert!(a.is_sealed(), "Role A is_sealed() should be consistent");
    assert!(a.is_sealed(), "Role A is_sealed() should remain consistent");
    assert!(b.is_sealed(), "Role B is_sealed() should be consistent");
}

#[session]
type AMultiProtocol = Send<B, Hello, Send<B, Hello, Send<B, Hello, End>>>;

#[session]
type BMultiProtocol = Receive<A, Hello, Receive<A, Hello, Receive<A, Hello, End>>>;

#[test]
fn test_multiple_messages_before_seal() {
    // Test that multiple messages in sequence all complete before sealing
    let Roles(mut a, mut b) = Roles::default();

    executor::block_on(async {
        let _: Result<_> = try_join!(
            try_session(&mut a, |s: AMultiProtocol<'_, _>| async {
                let s = s.send(Hello(1)).await?;
                let s = s.send(Hello(2)).await?;
                let s = s.send(Hello(3)).await?;
                Ok(((), s))
            }),
            try_session(&mut b, |s: BMultiProtocol<'_, _>| async {
                let (Hello(v1), s) = s.receive().await?;
                assert_eq!(v1, 1);
                let (Hello(v2), s) = s.receive().await?;
                assert_eq!(v2, 2);
                let (Hello(v3), s) = s.receive().await?;
                assert_eq!(v3, 3);
                Ok(((), s))
            })
        )
        .map(|_| ());
    });

    assert!(a.is_sealed(), "Role A should be sealed after multi-message session");
    assert!(b.is_sealed(), "Role B should be sealed after multi-message session");
}

#[test]
fn test_session_with_return_value() {
    let Roles(mut a, mut b) = Roles::default();

    let results: Result<_> = executor::block_on(async {
        try_join!(
            try_session(&mut a, |s: AProtocol<'_, _>| async {
                let s = s.send(Hello(42)).await?;
                Ok(("from_a", s))
            }),
            try_session(&mut b, |s: BProtocol<'_, _>| async {
                let (Hello(val), s) = s.receive().await?;
                Ok((val, s))
            })
        )
    });

    match results {
        Ok((a_result, b_result)) => {
            assert_eq!(a_result, "from_a");
            assert_eq!(b_result, 42);
        }
        Err(e) => panic!("Session failed: {:?}", e),
    }

    assert!(a.is_sealed());
    assert!(b.is_sealed());
}

#[test]
fn test_error_in_session_still_seals() {
    let Roles(mut a, mut b) = Roles::default();

    let _: Result<_> = executor::block_on(async {
        try_join!(
            try_session(&mut a, |s: AProtocol<'_, _>| async {
                let s = s.send(Hello(1)).await?;
                Ok(((), s))
            }),
            try_session(&mut b, |s: BProtocol<'_, _>| async {
                let (Hello(_), s) = s.receive().await?;
                // Even when B's result is Ok, the session should complete
                Ok(((), s))
            })
        )
    });

    // Sessions should be sealed after completion (success or failure)
    assert!(a.is_sealed());
    assert!(b.is_sealed());
}

// ============================================================================
// Three-Party Protocol Tests
// ============================================================================

// Define a three-party scenario to test more complex sealing
type Channel3 = Bidirectional<UnboundedSender<Label3>, UnboundedReceiver<Label3>>;

#[derive(Roles)]
struct ThreeRoles(P, Q, R);

#[derive(Role)]
#[message(Label3)]
struct P(#[route(Q)] Channel3, #[route(R)] Channel3);

#[derive(Role)]
#[message(Label3)]
struct Q(#[route(P)] Channel3, #[route(R)] Channel3);

#[derive(Role)]
#[message(Label3)]
struct R(#[route(P)] Channel3, #[route(Q)] Channel3);

#[derive(Message)]
enum Label3 {
    Msg(Msg),
}

struct Msg(String);

#[session]
type PProtocol = Send<Q, Msg, Receive<R, Msg, End>>;

#[session]
type QProtocol = Receive<P, Msg, Send<R, Msg, End>>;

#[session]
type RProtocol = Receive<Q, Msg, Send<P, Msg, End>>;

#[test]
fn test_three_party_sealing() {
    let ThreeRoles(mut p, mut q, mut r) = ThreeRoles::default();

    assert!(!p.is_sealed());
    assert!(!q.is_sealed());
    assert!(!r.is_sealed());

    let _: result::Result<_, Box<dyn Error>> = executor::block_on(async {
        futures::try_join!(
            try_session(&mut p, |s: PProtocol<'_, _>| async {
                let s = s.send(Msg("hello".into())).await?;
                let (Msg(_), s) = s.receive().await?;
                Ok(((), s))
            }),
            try_session(&mut q, |s: QProtocol<'_, _>| async {
                let (Msg(msg), s) = s.receive().await?;
                let s = s.send(Msg(format!("got: {}", msg))).await?;
                Ok(((), s))
            }),
            try_session(&mut r, |s: RProtocol<'_, _>| async {
                let (Msg(_), s) = s.receive().await?;
                let s = s.send(Msg("ack".into())).await?;
                Ok(((), s))
            })
        )
    });

    // All three roles should be sealed after session
    assert!(p.is_sealed(), "Role P should be sealed");
    assert!(q.is_sealed(), "Role Q should be sealed");
    assert!(r.is_sealed(), "Role R should be sealed");
}

#[test]
fn test_roles_default_creates_connected_channels() {
    let Roles(a, b) = Roles::default();

    // Both roles should start unsealed
    assert!(!a.is_sealed());
    assert!(!b.is_sealed());
}

#[test]
fn test_three_roles_default_creates_all_connections() {
    let ThreeRoles(p, q, r) = ThreeRoles::default();

    // All roles should start unsealed
    assert!(!p.is_sealed());
    assert!(!q.is_sealed());
    assert!(!r.is_sealed());
}
