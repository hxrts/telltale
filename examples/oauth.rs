//! OAuth example demonstrating authentication session types.
//!
//! This example uses the `choreography!` macro to define the protocol with nested
//! choice/branching. The outer choice is made by S (server) selecting Login or
//! Cancel. In the Login path, A (authenticator) decides Granted or Denied, and S
//! forwards the result to C (client) via explicit relay choices.
//!
//! Adapted from: Stay safe under panic: Rust programming with affine MPST
//!
//! ```tell
//! protocol OAuth =
//!   roles S, C, A
//!   choice S at
//!     | Login =>
//!       S -> C : LoginReq of i32
//!       choice C at
//!         | Proceed =>
//!           C -> A : Password of i32
//!           choice A at
//!             | Granted =>
//!               A -> S : Approved of i32
//!               choice S at
//!                 | AuthOk =>
//!                   S -> C : AuthNotice of i32
//!             | Denied =>
//!               A -> S : Rejected of i32
//!               choice S at
//!                 | AuthFail =>
//!                   S -> C : FailNotice of i32
//!     | Cancel =>
//!       S -> C : CancelReq of i32
//!       choice C at
//!         | Abort =>
//!           C -> A : Quit of i32
//! ```
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]
#![allow(missing_docs)]

use futures::{executor, try_join};
use std::error::Error;
use telltale::try_session;
use telltale_macros::choreography;

choreography! {
    protocol OAuth =
      roles S, C, A
      choice S at
        | Login =>
          S -> C : LoginReq(i32)
          choice C at
            | Proceed =>
              C -> A : Password(i32)
              choice A at
                | Granted =>
                  A -> S : Approved(i32)
                  choice S at
                    | AuthOk =>
                      S -> C : AuthNotice(i32)
                | Denied =>
                  A -> S : Rejected(i32)
                  choice S at
                    | AuthFail =>
                      S -> C : FailNotice(i32)
        | Cancel =>
          S -> C : CancelReq(i32)
          choice C at
            | Abort =>
              C -> A : Quit(i32)
}

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
                if i == 10 {
                    // Password is 10
                    let s = s.select(Granted).await?;
                    let end = s.send(Approved(i)).await?;
                    Ok(((), end))
                } else {
                    let s = s.select(Denied).await?;
                    let end = s.send(Rejected(i)).await?;
                    Ok(((), end))
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
        // Change here for something != 10, so that authentication fails.
        let i: i32 = 10;

        // For the sake of the example, assume that we never Cancel.
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
    })
    .await
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    let Roles(mut s, mut c, mut a) = Roles::default();
    executor::block_on(async {
        try_join!(client(&mut c), server(&mut s), auth(&mut a)).unwrap();
    });
}
