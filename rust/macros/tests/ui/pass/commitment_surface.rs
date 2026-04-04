//! Pass: commitment surface with profiles and operations.
use telltale::tell;

tell! {
    profile Replay fairness eventual admissibility replay escalation_window bounded
    agreement_profile SoftSafe
      visibility pending
      rule aura_soft_safe
      usable_at soft_safe
      finalized_at finalized
      evidence commit_fact

    operation syncLedger(entryId : Int) at Coordinator progress LedgerProgress requires Replay within bounded on timeout => escalate on stall => diagnose agreement SoftSafe prestate LedgerState compose first_success =
      publish SyncQueued(entryId)

    protocol CommitLifecycle under Replay =
      roles Coordinator, Worker
      begin syncLedger(42) progress LedgerProgress requires Replay within bounded on timeout => escalate on stall => diagnose
      Coordinator -> Worker : Prepare
      await syncLedger
      resolve syncLedger as Success
}

fn main() {
    let metadata = CommitLifecycle::commitments::operation("syncLedger").unwrap();
    let agreement = CommitLifecycle::agreements::operation("syncLedger").unwrap();
    let profile = CommitLifecycle::proof_status::agreement_profile("SoftSafe").unwrap();
    let agreement_from_status = CommitLifecycle::proof_status::agreement_operation("syncLedger").unwrap();
    let operation = metadata.operation_instance("sync-ledger#1");
    let progress = metadata.progress_contract("sync-ledger#1");
    let contract = agreement.agreement_contract("sync-ledger#1");
    assert_eq!(metadata.progress.contract_name, "LedgerProgress");
    assert_eq!(operation.kind, "syncLedger");
    assert!(progress.bounded);
    assert_eq!(agreement.profile_name, "SoftSafe");
    assert_eq!(profile.finalized_at, telltale::dsl::semantic::AgreementLevel::Finalized);
    assert_eq!(agreement_from_status.profile_name, "SoftSafe");
    assert_eq!(contract.profile_name.as_deref(), Some("SoftSafe"));
    assert_eq!(
        agreement.child_effect_aggregation,
        Some(telltale::dsl::semantic::EffectCompositionPolicy::First)
    );
    assert_eq!(CommitLifecycle::proof_status::PARITY_CRITICAL_OPERATIONS, ["syncLedger"]);
    assert!(!CommitLifecycle::proof_status::SESSION_PROJECTABLE);
    assert!(CommitLifecycle::proof_status::PROTOCOL_MACHINE_EXECUTABLE);
}
