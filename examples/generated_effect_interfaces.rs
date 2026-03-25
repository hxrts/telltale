//! Generated effect-interface example.
//!
//! This shows the primary developer path: `tell!` emits typed algebraic
//! effect traits and request/outcome enums directly, and host code implements
//! those traits without any intermediate file export step.

use serde_json::json;
use telltale::tell;

tell! {
    -- // Execution profile metadata is part of the generated proof status surface.
    profile Replay fairness eventual admissibility replay escalation_window bounded

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
    protocol CommitFlow uses Runtime, Audit under Replay =
      roles Coordinator, Worker, Client
      observe let presence = observe Runtime.watchPresence(commitSession)
      authoritative let witness = check Runtime.ready(commitSession)
      publish witness as CommitPublication
      materialize commitProof from CommitPublication
      Coordinator -> Worker : Commit
      Worker -> Client : Published
}

// Import the generated effect surface as one module: traits, requests, outcomes, and
// effect-domain data all live together here because they describe one boundary.
use CommitFlow::authority;
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

    println!(
        "strongest tier = {}",
        CommitFlow::proof_status::STRONGEST_TIER
    );
    println!(
        "session projectable = {}",
        CommitFlow::proof_status::SESSION_PROJECTABLE
    );
    println!(
        "execution profiles = {:?}",
        CommitFlow::proof_status::EXECUTION_PROFILES
    );

    // Direct trait calls are the primary developer path for effectful work.
    let witness = effects::Runtime::ready(&mut host, session.clone())?;
    let receipt = effects::Runtime::publish(&mut host, witness.clone())?;

    let observed = authority::observed_binding("presence")
        .ok_or("missing generated observe binding metadata")?
        .observed_read("presence-read#1", 7, "host-runtime");
    let authoritative = authority::authoritative_binding("witness")
        .ok_or("missing generated authoritative binding metadata")?
        .authoritative_read("ready-read#1");
    let publication = authority::publication("CommitPublication")
        .ok_or("missing generated publication metadata")?
        .publication_event("publication#1", "commit-flow#1");
    let materialization = authority::materialization("commitProof")
        .ok_or("missing generated materialization metadata")?;
    let proof = materialization.materialization_proof(
        "proof#1",
        "Runtime.ready",
        format!("digest:{}", receipt.commit_id),
    );
    let handle = materialization.canonical_handle("handle#1", &proof);

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
    println!("observed binding = {}", observed.read_id);
    println!("authoritative binding = {}", authoritative.read_id);
    println!("publication = {}", publication.publication);
    println!("canonical handle = {}", handle.handle_id);
    println!("audit entries = {}", host.audit_log.len());
    Ok(())
}
