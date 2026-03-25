//! This is an effect-boundary example for domain agreement profiles: `tell!`
//! owns the commitment, progress, and agreement/finality semantics, while Rust
//! only reads the generated proof-backed metadata.
//!
//! The example deliberately uses an Aura-shaped soft-safe/finalized agreement
//! profile without baking Aura policy into Telltale core semantics.

use telltale::tell;

tell! {
    -- // Execution profile used by the explicit progress contract.
    profile Replay fairness eventual admissibility replay escalation_window bounded

    -- // Named agreement profile keeps visibility, evidence, and finalization semantics reusable.
    agreement_profile SoftSafe
      visibility pending
      rule aura_soft_safe
      usable_at soft_safe
      finalized_at finalized
      evidence commit_fact

    -- // Operation metadata defines the parity-critical commitment boundary.
    operation syncLedger(entryId : Int) at Coordinator progress LedgerProgress requires Replay within bounded on timeout => escalate on stall => diagnose agreement SoftSafe prestate LedgerState compose first_success =
      publish SyncQueued(entryId)

    -- // Protocol-visible commitment lifecycle is expressed directly in the guest language.
    protocol CommitLifecycle under Replay =
      roles Coordinator, Worker
      begin syncLedger(42) progress LedgerProgress requires Replay within bounded on timeout => escalate on stall => diagnose
      Coordinator -> Worker : Prepare
      await syncLedger
      resolve syncLedger as Success
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let sync = CommitLifecycle::commitments::operation("syncLedger")
        .ok_or("generated commitment metadata must expose syncLedger")?;
    let agreement = CommitLifecycle::agreements::operation("syncLedger")
        .ok_or("generated agreement metadata must expose syncLedger")?;
    let agreement_profile = CommitLifecycle::proof_status::agreement_profile("SoftSafe")
        .ok_or("generated proof-status metadata must expose SoftSafe")?;
    let operation = sync.operation_instance("sync-ledger#1");
    let progress = sync.progress_contract(operation.operation_id.clone());
    let contract = agreement.agreement_contract(operation.operation_id.clone());

    println!(
        "strongest tier = {}",
        CommitLifecycle::proof_status::STRONGEST_TIER
    );
    println!(
        "session projectable = {}",
        CommitLifecycle::proof_status::SESSION_PROJECTABLE
    );
    println!(
        "parity-critical operations = {:?}",
        CommitLifecycle::proof_status::PARITY_CRITICAL_OPERATIONS
    );
    println!("operation = {}", sync.operation_name);
    println!("owner = {}", sync.owner_role);
    println!("progress contract = {}", sync.progress.contract_name);
    println!("agreement profile = {}", agreement.profile_name);
    println!("agreement visibility = {:?}", agreement.visibility);
    println!("agreement finalized at = {:?}", agreement_profile.finalized_at);
    println!(
        "child effect aggregation = {:?}",
        agreement.child_effect_aggregation
    );
    println!("requires profile = {:?}", sync.progress.requires_profile);
    println!("within window = {:?}", sync.progress.within_window);
    println!("operation phase = {:?}", operation.phase);
    println!("progress state = {:?}", progress.state);
    println!("agreement contract = {}", contract.contract_name);
    Ok(())
}
