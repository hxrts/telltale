//! OAuth example demonstrating authentication session types.
//!
//! This example uses the `tell!` macro to define the protocol with nested
//! choice/branching. The outer choice is made by S (server) selecting Login or
//! Cancel. In the Login path, A (authenticator) decides Granted or Denied, and S
//! forwards the result to C (client) via explicit relay choices.
//!
//! Adapted from: Stay safe under panic: Rust programming with affine MPST
use futures::{executor, try_join};
use std::error::Error;
use telltale::{tell, try_session};

#[derive(Clone, Copy, Debug)]
enum LoginScenario {
    Cancel(i32),
    Grant(i32),
    Deny(i32),
}

fn login_scenario() -> LoginScenario {
    match std::env::var("OAUTH_SCENARIO").ok().as_deref() {
        Some("cancel") => LoginScenario::Cancel(10),
        Some("deny") => LoginScenario::Deny(10),
        _ => LoginScenario::Grant(10),
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

async fn auth(role: &mut A) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: ASession<'_, _>| async {
        match s.branch().await? {
            AChoice1::Proceed(Proceed, cont) => {
                let (Password(i), s) = cont.receive().await?;
                match login_scenario() {
                    LoginScenario::Grant(_) => {
                        let s = s.select(Granted).await?;
                        let end = s.send(Approved(i)).await?;
                        Ok(((), end))
                    }
                    LoginScenario::Deny(_) => {
                        let s = s.select(Denied).await?;
                        let end = s.send(Rejected(i)).await?;
                        Ok(((), end))
                    }
                    LoginScenario::Cancel(_) => {
                        unreachable!("cancel never reaches the authenticator")
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

async fn server(role: &mut S) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: SSession<'_, _>| async {
        match login_scenario() {
            LoginScenario::Cancel(i) => {
                let s = s.select(Cancel).await?;
                let end = s.send(CancelReq(i)).await?;
                Ok(((), end))
            }
            LoginScenario::Grant(i) | LoginScenario::Deny(i) => {
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
    executor::block_on(async { try_join!(client(&mut c), server(&mut s), auth(&mut a)) })?;
    Ok(())
}
