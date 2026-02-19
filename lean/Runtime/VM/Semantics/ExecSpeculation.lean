import Runtime.VM.Semantics.ExecHelpers


/-! # Speculation Instruction Semantics

Step functions for `fork`, `join`, and `abort`, the speculation lifecycle
described in `runtime.md` §17.

`stepFork` enters speculative mode by reading a ghost session id from a register
and setting `specState` on the coroutine, with configuration-gated depth checks.
`stepJoin` and `stepAbort` require active speculation and clear the speculation
state. Checkpoint/restore and reconciliation semantics remain deferred to later
V2 phases.
-/

set_option autoImplicit false

universe u

/-! ## Speculation semantics -/

mutual

private def localTypeMatches : LocalType → LocalType → Bool
  | .send r1 t1 l1, .send r2 t2 l2 =>
      decide (r1 = r2) && decide (t1 = t2) && localTypeMatches l1 l2
  | .recv r1 t1 l1, .recv r2 t2 l2 =>
      decide (r1 = r2) && decide (t1 = t2) && localTypeMatches l1 l2
  | .select r1 bs1, .select r2 bs2 =>
      decide (r1 = r2) && branchListMatches bs1 bs2
  | .branch r1 bs1, .branch r2 bs2 =>
      decide (r1 = r2) && branchListMatches bs1 bs2
  | .end_, .end_ => true
  | .var n1, .var n2 => decide (n1 = n2)
  | .mu l1, .mu l2 => localTypeMatches l1 l2
  | _, _ => false

private def branchListMatches : List (Label × LocalType) → List (Label × LocalType) → Bool
  | [], [] => true
  | (lbl1, l1) :: rest1, (lbl2, l2) :: rest2 =>
      decide (lbl1 = lbl2) && localTypeMatches l1 l2 && branchListMatches rest1 rest2
  | _, _ => false

end

private def localTypeSnapshotMatches :
    List (Endpoint × LocalType) → List (Endpoint × LocalType) → Bool
  | [], [] => true
  | (ep1, l1) :: rest1, (ep2, l2) :: rest2 =>
      decide (ep1 = ep2) && localTypeMatches l1 l2 && localTypeSnapshotMatches rest1 rest2
  | _, _ => false

private def localTypesForSid {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (sid : SessionId) : List (Endpoint × LocalType) :=
  match st.sessions.find? (fun p => decide (p.1 = sid)) with
  | some (_, sess) => sess.localTypes
  | none => []

/-- Operational reconciliation predicate: ghost snapshot and live local types
must align by constructor and recursive structure. -/
def matchesRealState {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (ghostSid : GhostSessionId) : Bool :=
  match st.ghostSessions.sessions.get? ghostSid with
  | none => false
  | some ghost =>
      localTypeSnapshotMatches ghost.projectedLocalTypes (localTypesForSid st ghost.realSid)

def stepFork {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (sidReg : Reg) : StepPack ι γ π ε ν :=
  -- Enter speculation mode for a ghost session id, respecting configured limits.
  if !st.config.speculationEnabled then
    faultPack st coro (.specFault "speculation is disabled") "fork while speculation disabled"
  else
    let nextDepth? :=
      match coro.specState with
      | none =>
          if st.config.maxSpeculationDepth = 0 then none else some (st.config.maxSpeculationDepth - 1)
      | some spec =>
          if spec.depth = 0 then none else some (spec.depth - 1)
    match nextDepth? with
    | none =>
        faultPack st coro (.specFault "speculation depth exhausted") "fork depth exhausted"
    | some depth =>
      match readReg coro.regs sidReg with
      | some (.nat gsid) =>
          let snapshot := localTypesForSid st gsid
          let ghost : VMGhostSession :=
            { ghostSid := gsid
            , realSid := gsid
            , owner := coro.id
            , projectedLocalTypes := snapshot
            , createdTick := st.clock }
          let checkpoint : VMSpeculationCheckpoint :=
            { ghostSid := gsid
            , tick := st.clock
            , coroId := coro.id
            , traceLen := st.obsTrace.length
            , nextEffectNonce := st.nextEffectNonce
            , needsReconciliation := st.needsReconciliation }
          let ghostState' : GhostRuntimeState :=
            { st.ghostSessions with
                sessions := st.ghostSessions.sessions.insert gsid ghost
                checkpoints := st.ghostSessions.checkpoints.insert gsid checkpoint }
          let st' := { st with ghostSessions := ghostState', needsReconciliation := true }
          let coro' := advancePc { coro with specState := some { ghostSid := gsid, depth := depth } }
          pack coro' st' (mkRes (.forked gsid) (some (.obs (.forked gsid gsid))))
      | some v =>
          faultPack st coro (.typeViolation .nat (valTypeOf v)) "bad fork operand"
      | none =>
          faultPack st coro .outOfRegisters "missing fork operand"
def stepJoin {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) : StepPack ι γ π ε ν :=
  -- Join speculation: requires active speculation state.
  match coro.specState with
  | none =>
      faultPack st coro (.specFault "join requires active speculation") "join without speculation"
  | some spec =>
      if matchesRealState st spec.ghostSid then
        let checkpoints' := st.ghostSessions.checkpoints.erase spec.ghostSid
        let ghostState' : GhostRuntimeState :=
          { st.ghostSessions with
              sessions := st.ghostSessions.sessions.erase spec.ghostSid
              checkpoints := checkpoints' }
        let st' := { st with ghostSessions := ghostState', needsReconciliation := !checkpoints'.isEmpty }
        let coro' := advancePc { coro with specState := none }
        pack coro' st' (mkRes .joined (some (.obs (.joined spec.ghostSid))))
      else
        faultPack st coro (.specFault "join reconciliation predicate failed") "join reconciliation mismatch"


def stepAbort {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) : StepPack ι γ π ε ν :=
  -- Abort speculation: requires active speculation state.
  match coro.specState with
  | none =>
      faultPack st coro (.specFault "abort requires active speculation") "abort without speculation"
  | some spec =>
      let checkpoint? := st.ghostSessions.checkpoints.get? spec.ghostSid
      let checkpoints' := st.ghostSessions.checkpoints.erase spec.ghostSid
      let ghostState' : GhostRuntimeState :=
        { st.ghostSessions with
            sessions := st.ghostSessions.sessions.erase spec.ghostSid
            checkpoints := checkpoints' }
      -- Restore deterministic checkpointed fields when a checkpoint exists.
      let restoredTrace :=
        match checkpoint? with
        | some checkpoint => st.obsTrace.take checkpoint.traceLen
        | none => st.obsTrace
      let restoredNonce :=
        match checkpoint? with
        | some checkpoint => checkpoint.nextEffectNonce
        | none => st.nextEffectNonce
      let restoredNeedsRecon :=
        match checkpoint? with
        | some checkpoint => checkpoint.needsReconciliation
        | none => st.needsReconciliation
      let st' :=
        { st with
            ghostSessions := ghostState'
            obsTrace := restoredTrace
            nextEffectNonce := restoredNonce
            needsReconciliation := restoredNeedsRecon || !checkpoints'.isEmpty }
      let coro' := advancePc { coro with specState := none }
      pack coro' st' (mkRes .aborted (some (.obs (.aborted spec.ghostSid))))
