//! Generated effect-interface example.
//!
//! This shows the primary developer path: `tell!` emits typed algebraic
//! effect traits and request/outcome enums directly, and host code implements
//! those traits without any intermediate file export step.

use serde_json::json;
use telltale::tell;

tell! {
    -- // Effect-domain data: failure variants returned by Runtime operations.
    type CommitError =
      | NotReady
      | TimedOut

    -- // Effect-domain data: evidence and receipts moved between Runtime operations.
    type alias ReadyWitness = { epoch : Int, issuedBy : Role }
    type alias CommitReceipt = { commitId : String, publishedBy : Role }

    -- // Effects declare capabilities; the surrounding types are the data those capabilities use.
    effect Runtime
      authoritative ready : Session -> Result CommitError ReadyWitness
      command publish : ReadyWitness -> Result CommitError CommitReceipt
      observe watchPresence : Session -> PresenceView

    -- // Audit capability used to record externally visible milestones.
    effect Audit
      observe record : AuditEvent -> Unit

    -- // Minimal commit flow used to generate effect-facing Rust interfaces.
    protocol CommitFlow uses Runtime, Audit =
      roles Coordinator, Worker, Client
      Coordinator -> Worker : Commit
      Worker -> Client : Published
}

// Import the generated effect surface as one module: traits, requests, outcomes, and
// effect-domain data all live together here because they describe one boundary.
use CommitFlow::effects;

#[derive(Default)]
struct HostRuntime {
    audit_log: Vec<String>,
}

// Host code implements the generated effect traits directly.
impl effects::Runtime for HostRuntime {
    fn ready(
        &mut self,
        _input: effects::Session,
    ) -> Result<effects::ReadyWitness, effects::CommitError> {
        Ok(effects::ReadyWitness {
            epoch: 7,
            issued_by: effects::Role::new("Coordinator"),
        })
    }

    fn publish(
        &mut self,
        input: effects::ReadyWitness,
    ) -> Result<effects::CommitReceipt, effects::CommitError> {
        Ok(effects::CommitReceipt {
            commit_id: format!("commit-{}", input.epoch),
            published_by: input.issued_by,
        })
    }

    fn watch_presence(&mut self, _input: effects::Session) -> effects::PresenceView {
        json!({
            "visible": true,
            "pending_review": false
        })
    }
}

// Audit is a second generated capability on the same effect boundary.
impl effects::Audit for HostRuntime {
    fn record(&mut self, input: effects::AuditEvent) {
        self.audit_log.push(input.to_string());
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut host = HostRuntime::default();
    let session = effects::Session::new("commit-flow-7");

    // Direct trait calls are the primary developer path for effectful work.
    let witness = effects::Runtime::ready(&mut host, session.clone())?;
    let receipt = effects::Runtime::publish(&mut host, witness.clone())?;

    // The generated request/outcome enums are the typed dispatch form of the same effect surface.
    match effects::Runtime::handle(&mut host, effects::RuntimeRequest::WatchPresence(session)) {
        effects::RuntimeOutcome::WatchPresence(view) => {
            println!("presence visible: {}", view["visible"]);
        }
        _ => unreachable!("watch_presence must produce the matching outcome variant"),
    }

    match effects::Audit::handle(
        &mut host,
        effects::AuditRequest::Record(json!({
            "event": "commit_published",
            "commitId": receipt.commit_id,
        })),
    ) {
        effects::AuditOutcome::Record(()) => {}
    }

    println!("issued_by = {}", witness.issued_by.0);
    println!("audit entries = {}", host.audit_log.len());
    Ok(())
}
