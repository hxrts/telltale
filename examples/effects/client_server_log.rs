//! Client-server protocol with a logging side-channel.
//!
//! This is an effect-boundary example: `tell!` owns the outcome branches, and
//! the generated effect interfaces describe the server decision capability and
//! the external audit sink.

use futures::{executor, try_join};
use serde_json::json;
use std::error::Error;
use telltale::{tell, try_session};

tell! {
    -- // Execution profile keeps the example on the proof-backed effect boundary.
    profile Replay fairness eventual admissibility replay escalation_window bounded

    -- // Host-side server execution policy.
    type ServerDecision =
      | Fault
      | Success(Int)
      | RetryThenSuccess(Int)

    -- // Runtime decides how one request attempt resolves.
    effect ServerRuntime
      command decide : Int -> ServerDecision
      {
        class : best_effort
        progress : immediate
        region : session
        agreement_use : none
        reentrancy : allow
      }

    -- // Logger sink records externally visible audit events.
    effect Audit
      observe record : AuditEvent -> Unit
      {
        class : observational
        progress : immediate
        region : global
        agreement_use : forbidden
        reentrancy : allow
      }

    -- // Client submits one request and the server decides the outcome.
    protocol ClientServerLog uses ServerRuntime, Audit under Replay =
      roles C, S, L
      C -> S : Request of i32
      choice S at
        -- // Fatal failure is broadcast to both client and logger.
        | Fault =>
          S -> C : Fault
          S -> L : Fault
        -- // Successful completion returns data and emits the log entry.
        | Success =>
          S -> C : Success of i32
          S -> L : Success of i32
        -- // Retry asks for one more request before completing successfully.
        | Retry =>
          S -> C : Retry
          S -> L : Retry
          C -> S : Request of i32
          S -> C : Success of i32
          S -> L : Success of i32
}

use ClientServerLog::effects;
use ClientServerLog::sessions::*;

struct ServerHost {
    decision: effects::ServerDecision,
}

#[derive(Default)]
struct LoggerHost {
    audit_log: Vec<String>,
}

impl effects::ServerRuntime for ServerHost {
    fn decide(&mut self, _input: i64) -> effects::ServerDecision {
        self.decision.clone()
    }
}

impl effects::Audit for LoggerHost {
    fn record(&mut self, input: effects::AuditEvent) {
        self.audit_log.push(input.to_string());
    }
}

fn server_outcome() -> effects::ServerDecision {
    match std::env::var("CLIENT_SERVER_LOG_OUTCOME").ok().as_deref() {
        Some("fault") => effects::ServerDecision::Fault,
        Some("retry") => effects::ServerDecision::RetryThenSuccess(420),
        _ => effects::ServerDecision::Success(420),
    }
}

async fn client(role: &mut C) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: CSession<'_, _>| async {
        let s = s.send(Request(42)).await?;
        println!("C: sent Request(42)");

        match s.branch().await? {
            CChoice1::Fault(Fault, end) => {
                println!("C: server faulted");
                Ok(((), end))
            }
            CChoice1::Success(Success(data), end) => {
                println!("C: received Success({data})");
                Ok(((), end))
            }
            CChoice1::Retry(Retry, s) => {
                println!("C: server asked to retry");

                let s = s.send(Request(42)).await?;
                println!("C: resent Request(42)");

                let (Success(data), end) = s.receive().await?;
                println!("C: received Success({data}) after retry");
                Ok(((), end))
            }
        }
    })
    .await
}

async fn server(role: &mut S, host: &mut ServerHost) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: SSession<'_, _>| async {
        let (Request(request), s) = s.receive().await?;
        println!("S: received Request({request})");

        match effects::ServerRuntime::decide(host, request.into()) {
            effects::ServerDecision::Fault => {
                let s = s.select(Fault).await?;
                let end = s.send(Fault).await?;
                println!("S: sent Fault to C and L");
                Ok(((), end))
            }
            effects::ServerDecision::Success(result) => {
                let result = i32::try_from(result)?;
                let s = s.select(Success(result)).await?;
                let end = s.send(Success(result)).await?;
                println!("S: sent Success({result}) to C and L");
                Ok(((), end))
            }
            effects::ServerDecision::RetryThenSuccess(result) => {
                let result = i32::try_from(result)?;
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

async fn logger(role: &mut L, host: &mut LoggerHost) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: LSession<'_, _>| async {
        match s.branch().await? {
            LChoice1::Fault(Fault, end) => {
                effects::Audit::record(host, json!({ "event": "server_fault" }));
                println!("L: server faulted, no log entry");
                Ok(((), end))
            }
            LChoice1::Success(Success(entry), end) => {
                effects::Audit::record(host, json!({ "event": "logged", "entry": entry }));
                println!("L: logged entry {entry}");
                Ok(((), end))
            }
            LChoice1::Retry(Retry, s) => {
                println!("L: retry in progress, waiting for result");
                let (Success(entry), end) = s.receive().await?;
                effects::Audit::record(
                    host,
                    json!({ "event": "logged_after_retry", "entry": entry }),
                );
                println!("L: logged entry {entry} (after retry)");
                Ok(((), end))
            }
        }
    })
    .await
}

fn main() -> Result<(), Box<dyn Error>> {
    let Roles(mut c, mut s, mut l) = Roles::default();
    let mut server_host = ServerHost {
        decision: server_outcome(),
    };
    let mut logger_host = LoggerHost::default();
    println!(
        "execution profiles = {:?}",
        ClientServerLog::proof_status::EXECUTION_PROFILES
    );
    println!(
        "session projectable = {}",
        ClientServerLog::proof_status::SESSION_PROJECTABLE
    );
    executor::block_on(async {
        try_join!(
            client(&mut c),
            server(&mut s, &mut server_host),
            logger(&mut l, &mut logger_host)
        )
    })?;
    println!("\nClient-server-log protocol completed successfully");
    Ok(())
}
