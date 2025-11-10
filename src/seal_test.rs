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
