//! Commitment lifecycle example.
//!
//! This shows the D2 guest-language surface for explicit commitment lifecycle
//! and progress escalation. The protocol is intentionally not session
//! projectable; the point is the semantic commitment/progress surface generated
//! by `tell!`.

use telltale::tell;

tell! {
    -- // Execution profile used by the explicit progress contract.
    profile Replay fairness eventual admissibility replay escalation_window bounded

    -- // Operation metadata defines the parity-critical commitment boundary.
    operation syncLedger(entryId : Int) at Coordinator progress LedgerProgress requires Replay within bounded on timeout => escalate on stall => diagnose compose fallback =
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
    let operation = sync.operation_instance("sync-ledger#1");
    let progress = sync.progress_contract(operation.operation_id.clone());

    println!(
        "strongest tier = {}",
        CommitLifecycle::proof_status::STRONGEST_TIER
    );
    println!(
        "session projectable = {}",
        CommitLifecycle::proof_status::SESSION_PROJECTABLE
    );
    println!("operation = {}", sync.operation_name);
    println!("owner = {}", sync.owner_role);
    println!("progress contract = {}", sync.progress.contract_name);
    println!("requires profile = {:?}", sync.progress.requires_profile);
    println!("within window = {:?}", sync.progress.within_window);
    println!("operation phase = {:?}", operation.phase);
    println!("progress state = {:?}", progress.state);
    Ok(())
}
