//! OAuth example demonstrating authentication session types.
//!
//! This is a projection-surface example: `tell!` owns the protocol-visible
//! cancel/login/auth-result branches, while Rust supplies the server's local
//! intent and the authenticator's local approval policy.
//!
//! Adapted from: Stay safe under panic: Rust programming with affine MPST
use futures::{executor, try_join};
use std::error::Error;
use telltale::{tell, try_session};

#[derive(Clone, Copy, Debug)]
enum ServerIntent {
    Cancel(i32),
    Login(i32),
}

#[derive(Clone, Copy, Debug)]
enum AuthDecision {
    Grant,
    Deny,
}

fn login_configuration() -> (ServerIntent, AuthDecision) {
    match std::env::var("OAUTH_SCENARIO").ok().as_deref() {
        Some("cancel") => (ServerIntent::Cancel(10), AuthDecision::Grant),
        Some("deny") => (ServerIntent::Login(10), AuthDecision::Deny),
        _ => (ServerIntent::Login(10), AuthDecision::Grant),
    }
}

tell! {
    -- // Server first decides whether authentication proceeds or is cancelled.
    protocol OAuth =
      roles S, C, A
      choice S at
        -- // Login asks the client for credentials, then relays the auth result.
        | Login =>
          S -> C : LoginReq(i32)
          choice C at
            -- // Client submits credentials and waits for the server's final relay.
            | Proceed =>
              C -> A : Password(i32)
              choice A at
                -- // Authenticator grants access and the server notifies the client.
                | Granted =>
                  A -> S : Approved(i32)
                  choice S at
                    | AuthOk =>
                      S -> C : AuthNotice(i32)
                -- // Authenticator denies access and the server forwards the failure.
                | Denied =>
                  A -> S : Rejected(i32)
                  choice S at
                    | AuthFail =>
                      S -> C : FailNotice(i32)
        -- // Cancel aborts before credentials are checked.
        | Cancel =>
          S -> C : CancelReq(i32)
          choice C at
            | Abort =>
              C -> A : Quit(i32)
}

use OAuth::sessions::*;

// ---------------------------------------------------------------------------
// Endpoint implementations
// ---------------------------------------------------------------------------

async fn client(role: &mut C) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: CSession<'_, _>| async {
        match s.branch().await? {
            CChoice1::Login(Login, cont) => {
                let (LoginReq(i), s) = cont.receive().await?;
                let s = s.select(Proceed).await?;
                let s = s.send(Password(i)).await?;
                match s.branch().await? {
                    CChoice3::AuthOk(AuthOk, cont) => {
                        let (AuthNotice(_i), end) = cont.receive().await?;
                        println!("Authenticated");
                        Ok(((), end))
                    }
                    CChoice3::AuthFail(AuthFail, cont) => {
                        let (FailNotice(_i), end) = cont.receive().await?;
                        println!("Authentication failed");
                        Ok(((), end))
                    }
                }
            }
            CChoice1::Cancel(Cancel, cont) => {
                let (CancelReq(i), s) = cont.receive().await?;
                let s = s.select(Abort).await?;
                let s = s.send(Quit(i)).await?;
                println!("Authentication cancelled");
                Ok(((), s))
            }
        }
    })
    .await
}

async fn auth(role: &mut A, decision: AuthDecision) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: ASession<'_, _>| async {
        match s.branch().await? {
            AChoice1::Proceed(Proceed, cont) => {
                let (Password(i), s) = cont.receive().await?;
                match decision {
                    AuthDecision::Grant => {
                        let s = s.select(Granted).await?;
                        let end = s.send(Approved(i)).await?;
                        Ok(((), end))
                    }
                    AuthDecision::Deny => {
                        let s = s.select(Denied).await?;
                        let end = s.send(Rejected(i)).await?;
                        Ok(((), end))
                    }
                }
            }
            AChoice1::Abort(Abort, cont) => {
                let (Quit(_i), end) = cont.receive().await?;
                Ok(((), end))
            }
        }
    })
    .await
}

async fn server(role: &mut S, intent: ServerIntent) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: SSession<'_, _>| async {
        match intent {
            ServerIntent::Cancel(i) => {
                let s = s.select(Cancel).await?;
                let end = s.send(CancelReq(i)).await?;
                Ok(((), end))
            }
            ServerIntent::Login(i) => {
                let s = s.select(Login).await?;
                let s = s.send(LoginReq(i)).await?;
                match s.branch().await? {
                    SChoice2::Granted(Granted, cont) => {
                        let (Approved(i), s) = cont.receive().await?;
                        let s = s.select(AuthOk).await?;
                        let end = s.send(AuthNotice(i)).await?;
                        Ok(((), end))
                    }
                    SChoice2::Denied(Denied, cont) => {
                        let (Rejected(i), s) = cont.receive().await?;
                        let s = s.select(AuthFail).await?;
                        let end = s.send(FailNotice(i)).await?;
                        Ok(((), end))
                    }
                }
            }
        }
    })
    .await
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() -> Result<(), Box<dyn Error>> {
    let Roles(mut s, mut c, mut a) = Roles::default();
    let (intent, decision) = login_configuration();
    executor::block_on(async { try_join!(client(&mut c), server(&mut s, intent), auth(&mut a, decision)) })?;
    Ok(())
}
