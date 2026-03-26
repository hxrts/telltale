//! OAuth example demonstrating authentication session types.
//!
//! This is an effect-boundary example: `tell!` owns the protocol-visible
//! cancel/login/auth-result branches, while generated effect traits model the
//! server's session plan and the authenticator's verification decision.

use futures::{executor, try_join};
use std::error::Error;
use telltale::{tell, try_session};

tell! {
    -- // Execution profile keeps the example on the proof-backed effect boundary.
    profile Replay fairness eventual admissibility replay escalation_window bounded

    -- // Server-side intent for one authentication session.
    type LoginPlan =
      | Cancel(Int)
      | Login(Int)

    -- // Authenticator-side decision over submitted credentials.
    type AuthDecision =
      | Grant
      | Deny

    -- // Server host decides whether this session should log in or cancel.
    effect ServerControl
      command plan : Session -> LoginPlan
      {
        class : best_effort
        progress : immediate
        region : session
        agreement_use : none
        reentrancy : allow
      }

    -- // Authenticator host decides whether the provided password is accepted.
    effect AuthService
      command verify : Int -> AuthDecision
      {
        class : best_effort
        progress : immediate
        region : session
        agreement_use : none
        reentrancy : allow
      }

    -- // Server first decides whether authentication proceeds or is cancelled.
    protocol OAuth uses ServerControl, AuthService under Replay =
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

use OAuth::effects;
use OAuth::sessions::*;

struct ServerHost {
    plan: effects::LoginPlan,
}

struct AuthHost {
    decision: effects::AuthDecision,
}

impl effects::ServerControl for ServerHost {
    fn plan(&mut self, _input: effects::Session) -> effects::LoginPlan {
        self.plan.clone()
    }
}

impl effects::AuthService for AuthHost {
    fn verify(&mut self, _input: i64) -> effects::AuthDecision {
        self.decision.clone()
    }
}

fn login_configuration() -> (effects::LoginPlan, effects::AuthDecision) {
    match std::env::var("OAUTH_SCENARIO").ok().as_deref() {
        Some("cancel") => (effects::LoginPlan::Cancel(10), effects::AuthDecision::Grant),
        Some("deny") => (effects::LoginPlan::Login(10), effects::AuthDecision::Deny),
        _ => (effects::LoginPlan::Login(10), effects::AuthDecision::Grant),
    }
}

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

async fn auth(role: &mut A, host: &mut AuthHost) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: ASession<'_, _>| async {
        match s.branch().await? {
            AChoice1::Proceed(Proceed, cont) => {
                let (Password(i), s) = cont.receive().await?;
                match effects::AuthService::verify(host, i.into()) {
                    effects::AuthDecision::Grant => {
                        let s = s.select(Granted).await?;
                        let end = s.send(Approved(i)).await?;
                        Ok(((), end))
                    }
                    effects::AuthDecision::Deny => {
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

async fn server(role: &mut S, host: &mut ServerHost) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: SSession<'_, _>| async {
        match effects::ServerControl::plan(host, effects::Session::new("oauth")) {
            effects::LoginPlan::Cancel(i) => {
                let i = i32::try_from(i)?;
                let s = s.select(Cancel).await?;
                let end = s.send(CancelReq(i)).await?;
                Ok(((), end))
            }
            effects::LoginPlan::Login(i) => {
                let i = i32::try_from(i)?;
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

fn main() -> Result<(), Box<dyn Error>> {
    let Roles(mut s, mut c, mut a) = Roles::default();
    let (plan, decision) = login_configuration();
    let mut server_host = ServerHost { plan };
    let mut auth_host = AuthHost { decision };
    println!(
        "execution profiles = {:?}",
        OAuth::proof_status::EXECUTION_PROFILES
    );
    println!(
        "session projectable = {}",
        OAuth::proof_status::SESSION_PROJECTABLE
    );
    executor::block_on(async {
        try_join!(
            client(&mut c),
            server(&mut s, &mut server_host),
            auth(&mut a, &mut auth_host)
        )
    })?;
    Ok(())
}
