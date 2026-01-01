//! Behavioral tests for the Session macro.
//!
//! Verifies that generated session type wrappers work correctly:
//! - Lifetime parameter added correctly
//! - FromState/IntoSession implemented
//! - Generic parameters preserved
//! - Choice branching correct

#![allow(clippy::unwrap_used)]

use futures::{
    channel::mpsc::{UnboundedReceiver, UnboundedSender},
    executor, try_join,
};
use rumpsteak_aura::{
    channel::Bidirectional, session, try_session, Branch, End, Message, Receive, Role, Roles,
    Select, Send,
};
use std::{error::Error, result};

type Result<T> = result::Result<T, Box<dyn Error>>;

type Channel = Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;

#[derive(Roles)]
struct TestRoles(Client, Server);

#[derive(Role)]
#[message(Label)]
struct Client(#[route(Server)] Channel);

#[derive(Role)]
#[message(Label)]
struct Server(#[route(Client)] Channel);

#[derive(Message)]
enum Label {
    Request(Request),
    Response(Response),
    Accept(Accept),
    Reject(Reject),
}

#[derive(Debug)]
struct Request(String);

#[derive(Debug)]
struct Response(i32);

struct Accept;
struct Reject;

// ============================================================================
// Basic Session Type Tests
// ============================================================================

#[session]
type SimpleClientSession = Send<Server, Request, Receive<Server, Response, End>>;

#[session]
type SimpleServerSession = Receive<Client, Request, Send<Client, Response, End>>;

#[test]
fn test_session_struct_from_state() {
    let TestRoles(mut client, mut server) = TestRoles::default();

    let result: Result<_> = executor::block_on(async {
        try_join!(
            try_session(&mut client, |s: SimpleClientSession<'_, _>| async {
                let s = s.send(Request("hello".to_string())).await?;
                let (Response(val), s) = s.receive().await?;
                assert_eq!(val, 42);
                Ok(((), s))
            }),
            try_session(&mut server, |s: SimpleServerSession<'_, _>| async {
                let (Request(msg), s) = s.receive().await?;
                assert_eq!(msg, "hello");
                let s = s.send(Response(42)).await?;
                Ok(((), s))
            })
        )
    });

    assert!(result.is_ok());
}

#[test]
fn test_session_into_session() {
    // The session macro adds FromState which enables try_session to work
    // This test verifies the generated code compiles and runs correctly
    let TestRoles(mut client, mut server) = TestRoles::default();

    let result: Result<_> = executor::block_on(async {
        try_join!(
            try_session(&mut client, |s: SimpleClientSession<'_, _>| async {
                let s = s.send(Request("test".to_string())).await?;
                let (_, s) = s.receive().await?;
                Ok(((), s))
            }),
            try_session(&mut server, |s: SimpleServerSession<'_, _>| async {
                let (_, s) = s.receive().await?;
                let s = s.send(Response(0)).await?;
                Ok(((), s))
            })
        )
    });

    assert!(result.is_ok());
}

// ============================================================================
// Choice Session Tests
// ============================================================================

#[session]
type ClientWithChoice = Select<Server, AcceptChoice, RejectChoice>;

#[session]
type AcceptChoice = Send<Server, Accept, End>;

#[session]
type RejectChoice = Send<Server, Reject, End>;

#[session]
type ServerWithChoice = Branch<Client, AcceptHandler, RejectHandler>;

#[session]
type AcceptHandler = Receive<Client, Accept, End>;

#[session]
type RejectHandler = Receive<Client, Reject, End>;

#[test]
fn test_session_choice_select_first() {
    let TestRoles(mut client, mut server) = TestRoles::default();

    let result: Result<_> = executor::block_on(async {
        try_join!(
            try_session(&mut client, |s: ClientWithChoice<'_, _>| async {
                // Select first branch (Accept)
                let s = s.select_left().await?;
                let s = s.send(Accept).await?;
                Ok(((), s))
            }),
            try_session(&mut server, |s: ServerWithChoice<'_, _>| async {
                // Branch and handle whatever the client chose
                match s.branch().await? {
                    rumpsteak_aura::Choices::Left(s) => {
                        let (_, s) = s.receive().await?;
                        Ok(((), s))
                    }
                    rumpsteak_aura::Choices::Right(s) => {
                        let (_, s) = s.receive().await?;
                        Ok(((), s))
                    }
                }
            })
        )
    });

    assert!(result.is_ok());
}

#[test]
fn test_session_choice_select_second() {
    let TestRoles(mut client, mut server) = TestRoles::default();

    let result: Result<_> = executor::block_on(async {
        try_join!(
            try_session(&mut client, |s: ClientWithChoice<'_, _>| async {
                // Select second branch (Reject)
                let s = s.select_right().await?;
                let s = s.send(Reject).await?;
                Ok(((), s))
            }),
            try_session(&mut server, |s: ServerWithChoice<'_, _>| async {
                match s.branch().await? {
                    rumpsteak_aura::Choices::Left(s) => {
                        let (_, s) = s.receive().await?;
                        Ok(((), s))
                    }
                    rumpsteak_aura::Choices::Right(s) => {
                        let (_, s) = s.receive().await?;
                        Ok(((), s))
                    }
                }
            })
        )
    });

    assert!(result.is_ok());
}

// ============================================================================
// Multi-Message Session Tests
// ============================================================================

#[session]
type ThreeMessageClient = Send<Server, Request, Send<Server, Request, Send<Server, Request, End>>>;

#[session]
type ThreeMessageServer =
    Receive<Client, Request, Receive<Client, Request, Receive<Client, Request, End>>>;

#[test]
fn test_session_multi_message() {
    let TestRoles(mut client, mut server) = TestRoles::default();

    let result: Result<_> = executor::block_on(async {
        try_join!(
            try_session(&mut client, |s: ThreeMessageClient<'_, _>| async {
                let s = s.send(Request("1".to_string())).await?;
                let s = s.send(Request("2".to_string())).await?;
                let s = s.send(Request("3".to_string())).await?;
                Ok(((), s))
            }),
            try_session(&mut server, |s: ThreeMessageServer<'_, _>| async {
                let (Request(m1), s) = s.receive().await?;
                assert_eq!(m1, "1");
                let (Request(m2), s) = s.receive().await?;
                assert_eq!(m2, "2");
                let (Request(m3), s) = s.receive().await?;
                assert_eq!(m3, "3");
                Ok(((), s))
            })
        )
    });

    assert!(result.is_ok());
}

// ============================================================================
// Ping-Pong Session Tests
// ============================================================================

#[session]
type PingSession = Send<Server, Request, Receive<Server, Response, End>>;

#[session]
type PongSession = Receive<Client, Request, Send<Client, Response, End>>;

#[test]
fn test_session_ping_pong() {
    let TestRoles(mut client, mut server) = TestRoles::default();

    let (client_result, server_result): (i32, String) = executor::block_on(async {
        try_join!(
            try_session(&mut client, |s: PingSession<'_, _>| async {
                let s = s.send(Request("ping".to_string())).await?;
                let (Response(val), s) = s.receive().await?;
                Ok((val, s))
            }),
            try_session(&mut server, |s: PongSession<'_, _>| async {
                let (Request(msg), s) = s.receive().await?;
                let s = s.send(Response(42)).await?;
                Ok((msg, s))
            })
        )
    })
    .unwrap();

    assert_eq!(client_result, 42);
    assert_eq!(server_result, "ping");
}

// ============================================================================
// Session Return Value Tests
// ============================================================================

#[test]
fn test_session_returns_value() {
    let TestRoles(mut client, mut server) = TestRoles::default();

    let results: Result<_> = executor::block_on(async {
        try_join!(
            try_session(&mut client, |s: SimpleClientSession<'_, _>| async {
                let s = s.send(Request("query".to_string())).await?;
                let (Response(result), s) = s.receive().await?;
                Ok((result * 2, s)) // Return computed value
            }),
            try_session(&mut server, |s: SimpleServerSession<'_, _>| async {
                let (Request(_), s) = s.receive().await?;
                let s = s.send(Response(21)).await?;
                Ok(("handled", s)) // Return status
            })
        )
    });

    match results {
        Ok((client_val, server_val)) => {
            assert_eq!(client_val, 42);
            assert_eq!(server_val, "handled");
        }
        Err(e) => panic!("Session failed: {:?}", e),
    }
}

// ============================================================================
// Nested Session Type Tests
// ============================================================================

#[session]
type DeepClientSession = Send<
    Server,
    Request,
    Receive<Server, Response, Send<Server, Request, Receive<Server, Response, End>>>,
>;

#[session]
type DeepServerSession = Receive<
    Client,
    Request,
    Send<Client, Response, Receive<Client, Request, Send<Client, Response, End>>>,
>;

#[test]
fn test_session_deeply_nested() {
    let TestRoles(mut client, mut server) = TestRoles::default();

    let result: Result<_> = executor::block_on(async {
        try_join!(
            try_session(&mut client, |s: DeepClientSession<'_, _>| async {
                let s = s.send(Request("req1".to_string())).await?;
                let (Response(r1), s) = s.receive().await?;
                assert_eq!(r1, 1);
                let s = s.send(Request("req2".to_string())).await?;
                let (Response(r2), s) = s.receive().await?;
                assert_eq!(r2, 2);
                Ok(((), s))
            }),
            try_session(&mut server, |s: DeepServerSession<'_, _>| async {
                let (Request(m1), s) = s.receive().await?;
                assert_eq!(m1, "req1");
                let s = s.send(Response(1)).await?;
                let (Request(m2), s) = s.receive().await?;
                assert_eq!(m2, "req2");
                let s = s.send(Response(2)).await?;
                Ok(((), s))
            })
        )
    });

    assert!(result.is_ok());
}
