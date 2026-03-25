use telltale::tell;

tell! {
    profile Replay fairness eventual admissibility replay escalation_window bounded

    operation syncLedger(entryId : Int) at Coordinator progress LedgerProgress requires Replay within bounded on timeout => escalate on stall => diagnose compose fallback =
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
    let operation = metadata.operation_instance("sync-ledger#1");
    let progress = metadata.progress_contract("sync-ledger#1");
    assert_eq!(metadata.progress.contract_name, "LedgerProgress");
    assert_eq!(operation.kind, "syncLedger");
    assert!(progress.bounded);
    assert!(!CommitLifecycle::proof_status::SESSION_PROJECTABLE);
    assert!(CommitLifecycle::proof_status::PROTOCOL_MACHINE_EXECUTABLE);
}
