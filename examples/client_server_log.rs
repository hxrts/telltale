//! Client-server protocol with a logging side-channel.
//!
//! A client sends a request to a server, which processes it and replies with
//! one of three outcomes:
//!
//! - **Fault** -- the server encountered a fatal error and the protocol ends.
//! - **Success** -- the request succeeded. The server sends data back to the
//!   client and forwards a log entry to a dedicated logger role.
//! - **Retry** -- the server asks the client to resend, then succeeds on the
//!   second attempt.
//!
//! The original implementation used infinite recursive session types (the
//! logging loop `S -> L : Log` cycled forever with no `End` state). This
//! version models a single request-response cycle with all three outcomes,
//! demonstrating the same three-role topology and choice-based branching
//! in a form the `tell!` macro can project.
//!
//! The server notifies both the client and the logger in every branch so that
//! each role's projected session type is compatible across all choice arms
//! (a requirement for well-formed multiparty projection).
//! Uses the `tell!` macro to derive session types, roles, messages,
//! and channel wiring from the global protocol specification.

use futures::{executor, try_join};
use std::error::Error;
use telltale::{tell, try_session};

#[derive(Clone, Copy, Debug)]
enum ServerOutcome {
    Fault,
    Success(i32),
    RetryThenSuccess(i32),
}

fn server_outcome() -> ServerOutcome {
    match std::env::var("CLIENT_SERVER_LOG_OUTCOME").ok().as_deref() {
        Some("fault") => ServerOutcome::Fault,
        Some("retry") => ServerOutcome::RetryThenSuccess(420),
        _ => ServerOutcome::Success(420),
    }
}

tell! {
    -- // Client submits one request and the server decides the outcome.
    protocol ClientServerLog =
      roles C, S, L
      C -> S : Request(i32)
      choice S at
        -- // Fatal failure is broadcast to both client and logger.
        | Fault =>
          S -> C : Fault
          S -> L : Fault
        -- // Successful completion returns data and emits the log entry.
        | Success =>
          S -> C : Success(i32)
          S -> L : Success(i32)
        -- // Retry asks for one more request before completing successfully.
        | Retry =>
          S -> C : Retry
          S -> L : Retry
          C -> S : Request(i32)
          S -> C : Success(i32)
          S -> L : Success(i32)
}

use ClientServerLog::sessions::*;

// ---------------------------------------------------------------------------
// Client
// ---------------------------------------------------------------------------

async fn client(role: &mut C) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: CSession<'_, _>| async {
        let s = s.send(Request(42)).await?;
        println!("C: sent Request(42)");

        match s.branch().await? {
            CChoice1::Fault(Fault, end) => {
                println!("C: server faulted");
                Ok(((), end))
            }
            CChoice1::Success(Success(d), end) => {
                println!("C: received Success({d})");
                Ok(((), end))
            }
            CChoice1::Retry(Retry, s) => {
                println!("C: server asked to retry");

                let s = s.send(Request(42)).await?;
                println!("C: resent Request(42)");

                let (Success(d), end) = s.receive().await?;
                println!("C: received Success({d}) after retry");
                Ok(((), end))
            }
        }
    })
    .await
}

// ---------------------------------------------------------------------------
// Server
// ---------------------------------------------------------------------------

async fn server(role: &mut S) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: SSession<'_, _>| async {
        let (Request(i), s) = s.receive().await?;
        println!("S: received Request({i})");

        match server_outcome() {
            ServerOutcome::Fault => {
                let s = s.select(Fault).await?;
                let end = s.send(Fault).await?;
                println!("S: sent Fault to C and L");
                Ok(((), end))
            }
            ServerOutcome::Success(result) => {
                let s = s.select(Success(result)).await?;
                let end = s.send(Success(result)).await?;
                println!("S: sent Success({result}) to C and L");
                Ok(((), end))
            }
            ServerOutcome::RetryThenSuccess(result) => {
                let s = s.select(Retry).await?;
                let (Request(retried), s) = s.send(Retry).await?.receive().await?;
                println!("S: received retry Request({retried})");
                let end = s.send(Success(result)).await?.send(Success(result)).await?;
                println!("S: sent Success({result}) after retry");
                Ok(((), end))
            }
        }
    })
    .await
}

// ---------------------------------------------------------------------------
// Logger
// ---------------------------------------------------------------------------

async fn logger(role: &mut L) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: LSession<'_, _>| async {
        match s.branch().await? {
            LChoice1::Fault(Fault, end) => {
                println!("L: server faulted, no log entry");
                Ok(((), end))
            }
            LChoice1::Success(Success(entry), end) => {
                println!("L: logged entry {entry}");
                Ok(((), end))
            }
            LChoice1::Retry(Retry, s) => {
                println!("L: retry in progress, waiting for result");
                let (Success(entry), end) = s.receive().await?;
                println!("L: logged entry {entry} (after retry)");
                Ok(((), end))
            }
        }
    })
    .await
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() -> Result<(), Box<dyn Error>> {
    let Roles(mut c, mut s, mut l) = Roles::default();
    executor::block_on(async { try_join!(client(&mut c), server(&mut s), logger(&mut l)) })?;
    println!("\nClient-server-log protocol completed successfully");
    Ok(())
}
