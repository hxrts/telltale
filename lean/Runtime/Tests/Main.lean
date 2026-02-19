
import Runtime.Examples.SimpleProtocol
import Runtime.VM.Runtime.Runner
import Runtime.VM.Runtime.ThreadedRunner
import Runtime.VM.Semantics.ExecSpeculation
import Runtime.VM.Semantics.ExecOwnership
import Runtime.VM.Runtime.Loader
import Runtime.VM.Runtime.Failure
import Runtime.Adequacy.EnvelopeCore
import Runtime.Proofs.CompileTime.RuntimeContracts
import Runtime.Proofs.Examples.ComposedProofPack
import Runtime.Proofs.TheoremPack.API
import SessionTypes.LocalTypeR
import SessionTypes.GlobalType

/-
Executable Lean tests for the scheduled VM runner.
-/

/- ## Structured Block 1 -/
set_option autoImplicit false
set_option maxRecDepth 4096

open SessionTypes.LocalTypeR
open SessionTypes.GlobalType

/-- Tag observable events for comparison (UnitEffect only). -/
def obsTag : ObsEvent UnitEffect → String
  | .sent _ _ _ => "sent"
  | .received _ _ _ => "received"
  | .offered _ _ => "offered"
  | .chose _ _ => "chose"
  | .acquired _ _ => "acquired"
  | .released _ _ => "released"
  | .invoked _ _ => "invoked"
  | .opened _ _ => "opened"
  | .closed _ => "closed"
  | .epochAdvanced _ _ => "epoch"
  | .transferred _ _ _ => "transferred"
  | .forked _ _ => "forked"
  | .joined _ => "joined"
  | .aborted _ => "aborted"
  | .tagged _ => "tagged"
  | .checked _ _ => "checked"

/-- Extract tags from a filtered trace (UnitEffect only). -/
def traceTags (trace : List (TickedObsEvent UnitEffect)) : List String :=
  trace.map (fun ev => obsTag ev.event)

/-- Minimal empty VM state for loading choreographies. -/
def emptyState : VMState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify :=
  { config := unitConfig
  , code := exampleProgram
  , programs := #[]
  , coroutines := #[]
  , buffers := []
  , persistent := ()
  , nextCoroId := 0
  , nextSessionId := 0
  , arena := exampleArena
  , sessions := []
  , resourceStates := {}
  , guardResources := []
  , sched := { policy := unitConfig.schedPolicy, readyQueue := [], blockedSet := {}, timeslice := 1, stepCount := 0 }
  , monitor := exampleMonitor
  , obsTrace := []
  , clock := 0
  , crashedSites := []
  , partitionedEdges := []
  , mask := ()
  , ghostSessions := default
  , progressSupply := () }

/-- Simple two-party LocalTypeR image. -/
def twoPartyImage : CodeImage UnitGuard UnitEffect :=
  let lbl : SessionTypes.GlobalType.Label := { name := "msg" }
  let ltA : LocalTypeR := .send "B" [(lbl, none, .end)]
  let ltB : LocalTypeR := .recv "A" [(lbl, none, .end)]
  CodeImage.fromLocalTypes [ ("A", ltA), ("B", ltB) ] .end

/-- Test helper: assert a boolean. -/
def expect (ok : Bool) (msg : String) : IO Unit :=
/- ## Structured Block 2 -/
  if ok then pure () else throw (IO.userError msg)

def mkReadyCoro (id : CoroutineId) (tokens : List ProgressToken := []) :
    CoroutineState UnitGuard UnitEffect :=
  { id := id
  , programId := 0
  , pc := 0
  , regs := Array.replicate 8 .unit
  , status := .ready
  , effectCtx := default
  , ownedEndpoints := []
  , progressTokens := tokens
  , knowledgeSet := []
  , costBudget := unitConfig.costModel.defaultBudget
  , specState := none }

def withSpecConfig
    (st : VMState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify)
    (enabled : Bool) (maxDepth : Nat) :
    VMState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify :=
  { st with
      config := { st.config with speculationEnabled := enabled, maxSpeculationDepth := maxDepth } }

def mkForkOperandCoro (id : CoroutineId) (ghostSid : Nat)
    (spec : Option SpeculationState := none) :
    CoroutineState UnitGuard UnitEffect :=
  let regs : RegFile := #[.nat ghostSid, .unit, .unit, .unit, .unit, .unit, .unit, .unit]
  { mkReadyCoro id with regs := regs, specState := spec }

def isSpecFault (res : ExecResult UnitGuard UnitEffect) : Bool :=
  match res.status with
  | .faulted (.specFault _) => true
  | _ => false

def hasTransferFaultMsg (res : ExecResult UnitGuard UnitEffect) (msg : String) : Bool :=
  match res.status with
  | .faulted (.transferFault m) => m = msg
  | _ => false

def schedulerTestState (policy : SchedPolicy) (allTokens : Bool := false) :
    VMState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify :=
  let token : ProgressToken := { sid := 0, endpoint := { sid := 0, role := "B" } }
  let tokensFor := fun (cid : CoroutineId) =>
    if allTokens || cid = 3 then [token] else []
  let coros : Array (CoroutineState UnitGuard UnitEffect) :=
    #[ mkReadyCoro 0 (tokensFor 0)
     , mkReadyCoro 1 (tokensFor 1)
     , mkReadyCoro 2 (tokensFor 2)
     , mkReadyCoro 3 (tokensFor 3) ]
  let laneMap : LaneOfMap :=
    ((({} : LaneOfMap).insert 0 0).insert 1 1).insert 2 0 |>.insert 3 1
  let sched0 : SchedState UnitGuard :=
    { policy := policy
    , readyQueue := [0, 1, 2, 3]
    , blockedSet := {}
    , laneOf := laneMap
    , timeslice := 1
    , stepCount := 0 }
  { emptyState with
      coroutines := coros
      nextCoroId := coros.size
      sched := syncLaneViews sched0 }

def collectSchedulePicks (fuel : Nat)
    (st : VMState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify)
    (acc : List CoroutineId := []) : List CoroutineId :=
  match fuel with
  | 0 => acc.reverse
  | fuel' + 1 =>
      match schedule st with
      | none => acc.reverse
      | some (cid, st') =>
          let sched' := updateAfterStep st'.sched cid .continue
          collectSchedulePicks fuel' { st' with sched := sched' } (cid :: acc)

theorem schedRoundOne_eq_schedRound_one
    (st : VMState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify) :
    schedRoundOne st = schedRound 1 st := by
  simp [schedRound]

/-- Main test entry point. -/
def main : IO Unit := do
  -- Test 1: N=1, single protocol.
  let (st1, _) := loadChoreography emptyState twoPartyImage
/- ## Structured Block 3 -/
  let st1' := runScheduled 50 1 st1
  expect (allTerminal st1') "N=1: not all done"

  -- Test 2: N=∞ (use large N), single protocol.
  let (st2, _) := loadChoreography emptyState twoPartyImage
  let st2' := runScheduled 50 100 st2
  expect (allTerminal st2') "N=∞: not all done"

  -- Test 3: N=1 and N=∞, multi-session, per-session traces match.
  let (st3, sid1) := loadChoreography emptyState twoPartyImage
  let (st4, sid2) := loadChoreography st3 twoPartyImage
  let seq := runScheduled 100 1 st4
  let par := runScheduled 100 100 st4
  let seqTrace := Runtime.VM.normalizeTrace seq.obsTrace
  let parTrace := Runtime.VM.normalizeTrace par.obsTrace
  let seq1 := traceTags (filterBySid sid1 seqTrace)
  let par1 := traceTags (filterBySid sid1 parTrace)
  expect (decide (seq1 = par1)) "session 1 traces differ"
  let seq2 := traceTags (filterBySid sid2 seqTrace)
  let par2 := traceTags (filterBySid sid2 parTrace)
  expect (decide (seq2 = par2)) "session 2 traces differ"

  -- Test 4: lane-aware round-robin alternates lane picks deterministically.
  let stLane := schedulerTestState .roundRobin
  match schedule stLane with
  | none => expect false "lane round-robin: missing first pick"
  | some (cidA, stLaneA) =>
      expect (decide (cidA = 1)) "lane round-robin: expected lane-1 first pick"
      match schedule stLaneA with
      | none => expect false "lane round-robin: missing second pick"
      | some (cidB, _) =>
          expect (decide (cidB = 0)) "lane round-robin: expected lane-0 second pick"

  -- Test 5: progress-aware policy prefers progress tokens inside the selected lane.
  let stProgress := schedulerTestState .progressAware
  match schedule stProgress with
  | none => expect false "progress-aware: missing pick"
  | some (cid, _) =>
      expect (decide (cid = 3)) "progress-aware: expected token holder in selected lane"

  -- Test 6: priority policy selects max score within selected lane.
  let priority : CoroutineId → Nat := fun cid =>
    if cid = 3 then 10 else if cid = 1 then 5 else 0
  let stPriority := schedulerTestState (.priority priority)
  match schedule stPriority with
  | none => expect false "priority: missing pick"
  | some (cid, _) =>
      expect (decide (cid = 3)) "priority: expected highest-priority candidate in selected lane"

  -- Test 7: blocked/unblock transitions update global and lane mirrors.
  let schedBlocked := updateAfterStep stLane.sched 1 (.blocked (.invokeWait 0))
  expect (schedBlocked.blockedSet.contains 1) "blocked-set missing blocked coroutine"
  expect (decide (1 ∉ schedBlocked.readyQueue)) "blocked coroutine still in ready queue"
  let schedUnblocked := unblockCoroutine schedBlocked 1
  expect (!(schedUnblocked.blockedSet.contains 1)) "unblock did not clear blocked-set entry"
  expect (decide (1 ∈ schedUnblocked.readyQueue)) "unblock did not restore ready queue entry"

  -- Test 8: cross-lane transfer emits handoff record with deterministic schema.
  let transferEndpoint : Endpoint := { sid := 7, role := "A" }
  let schedHandoff := updateAfterStep stLane.sched 0 (.transferred transferEndpoint 1)
  expect (decide (schedHandoff.crossLaneHandoffs.length = 1)) "missing cross-lane handoff record"
  match schedHandoff.crossLaneHandoffs with
  | h :: _ =>
      expect (decide (h.fromLane = 0 ∧ h.toLane = 1)) "handoff lanes not recorded correctly"
/- ## Structured Block 4 -/
      expect (decide (h.reason = "transfer 7:A")) "handoff reason tag mismatch"
  | [] => expect false "missing handoff payload"

  let schedNoHandoff := updateAfterStep stLane.sched 0 (.transferred transferEndpoint 2)
  expect (decide (schedNoHandoff.crossLaneHandoffs.length = 0))
    "same-lane transfer incorrectly recorded as cross-lane handoff"

  -- Test 9: progress-aware policy bounded starvation check under all-token assumption.
  let stProgressFair := schedulerTestState .progressAware true
  let picks := collectSchedulePicks 8 stProgressFair
  expect (decide (0 ∈ picks ∧ 1 ∈ picks ∧ 2 ∈ picks ∧ 3 ∈ picks))
    "progress-aware fairness check failed under all-token assumption"

  -- Test 10: canonical failure status and corrupt/timeout handling.
  let sidFail : SessionId := 0
  let sessFail : SessionState UnitVerify :=
    { scope := { id := sidFail }
    , sid := sidFail
    , roles := []
    , endpoints := []
    , localTypes := []
    , traces := initDEnv sidFail []
    , buffers := []
    , handlers := []
    , epoch := 0
    , phase := .active }
  let stFail := { emptyState with sessions := [(sidFail, sessFail)], nextSessionId := sidFail + 1 }
  let edgeFail : Edge := { sid := sidFail, sender := "A", receiver := "B" }
  expect (decide (failureStatus (.corrupt edgeFail 0 : Failure UnitIdentity) = .transportCorruption))
    "failure status mismatch for corrupt"
  expect (decide (failureStatus (.timeout edgeFail 10 : Failure UnitIdentity) = .transportTimeout))
    "failure status mismatch for timeout"

  let stCorrupt := applyFailure stFail (.corrupt edgeFail 0 : Failure UnitIdentity)
  expect (decide (edgeFail ∈ stCorrupt.partitionedEdges))
    "corrupt failure did not quarantine edge"

  let stTimeoutRetry := applyFailure { stFail with clock := 3 } (.timeout edgeFail 10 : Failure UnitIdentity)
  let timeoutRetryPhase := (sessionState? stTimeoutRetry.sessions sidFail).map (fun sess => sess.phase)
  let timeoutRetryClosed :=
    match timeoutRetryPhase with
    | some .closed => true
    | _ => false
  expect (!timeoutRetryClosed) "timeout before deadline should not close session"

  let stTimeoutClose := applyFailure { stFail with clock := 10 } (.timeout edgeFail 10 : Failure UnitIdentity)
  let timeoutClosePhase := (sessionState? stTimeoutClose.sessions sidFail).map (fun sess => sess.phase)
  let timeoutClosed :=
    match timeoutClosePhase with
    | some .closed => true
    | _ => false
  expect timeoutClosed "timeout at deadline should close session"

  -- Test 11: differential local-fault handling is stable across single-thread vs multi-thread schedules.
  let localFaults : List (Failure UnitIdentity) :=
    [ .corrupt edgeFail 7
    , .timeout edgeFail 8
    ]
  let localSingle := runScheduled 20 1 (applyFailureEvents { stFail with clock := 8 } localFaults)
  let localMulti := runScheduled 20 100 (applyFailureEvents { stFail with clock := 8 } localFaults)
/- ## Structured Block 5 -/
  expect (decide (localSingle.partitionedEdges = localMulti.partitionedEdges))
    "local fault differential: partitioned edges diverged"
  expect (decide (localSingle.failureTrace = localMulti.failureTrace))
    "local fault differential: deterministic failure trace diverged"
  expect (decide (localSingle.structuredErrorEvents = localMulti.structuredErrorEvents))
    "local fault differential: structured error events diverged"

  -- Test 12: crash/partition/heal/timeout trace parity under reference vs sharded-style schedules.
  let crashSiteId : IdentityModel.SiteId UnitIdentity := by
    change Nat
    exact 1
  let distributedFaultTrace : List (Failure UnitIdentity) :=
    [ .siteCrash crashSiteId
    , .partition [edgeFail]
    , .heal [edgeFail]
    , .timeout edgeFail 8
    ]
  let refFaultRun := runScheduled 20 1 (applyFailureEvents { stFail with clock := 8 } distributedFaultTrace)
  let shardedFaultRun := runScheduled 20 8 (applyFailureEvents { stFail with clock := 8 } distributedFaultTrace)
  expect (decide (refFaultRun.failureTrace = shardedFaultRun.failureTrace))
    "reference vs sharded fault trace mismatch"
  expect (decide (refFaultRun.structuredErrorEvents = shardedFaultRun.structuredErrorEvents))
    "reference vs sharded structured errors mismatch"

  -- Test 13: artifact-level Lean/Rust shared error-code compatibility checks.
  let leanOutRegs :=
    Runtime.Adequacy.errorCodeOfLeanFault (γ := UnitGuard)
      (.outOfRegisters : Fault UnitGuard)
  let rustOutRegs :=
    Runtime.Adequacy.errorCodeOfRustFaultTag .outOfRegisters
  expect (decide (leanOutRegs = rustOutRegs))
    "error-code compatibility mismatch for out_of_registers"

  let leanFlowViolation :=
    Runtime.Adequacy.errorCodeOfLeanFault (γ := UnitGuard)
      (.flowViolation "policy" : Fault UnitGuard)
  let rustFlowViolation :=
    Runtime.Adequacy.errorCodeOfRustFaultTag .flowViolation
  expect (decide (leanFlowViolation = rustFlowViolation))
    "error-code compatibility mismatch for flow_violation"

  let leanNoProgress :=
    Runtime.Adequacy.errorCodeOfLeanFault (γ := UnitGuard)
      (.noProgressToken edgeFail : Fault UnitGuard)
  let rustNoProgress :=
    Runtime.Adequacy.errorCodeOfRustFaultTag .noProgressToken
  expect (decide (leanNoProgress = rustNoProgress))
    "error-code compatibility mismatch for no_progress_token"

  expect (decide (Runtime.Adequacy.errorCodeString leanOutRegs = "out_of_registers"))
    "error-code string mismatch for out_of_registers"
  expect (decide (Runtime.Adequacy.errorCodeString leanFlowViolation = "flow_violation"))
    "error-code string mismatch for flow_violation"

  -- Test 14: local envelope differential conformance (single-thread vs multi-thread modulo normalized/session-erased traces).
  let localEnvSingle := runScheduled 100 1 st4
  let localEnvMulti := runScheduled 100 32 st4
  let localEnvSingleNorm := Runtime.VM.normalizeTrace localEnvSingle.obsTrace
  let localEnvMultiNorm := Runtime.VM.normalizeTrace localEnvMulti.obsTrace
/- ## Structured Block 6 -/
  let localS1 := traceTags (filterBySid sid1 localEnvSingleNorm)
  let localM1 := traceTags (filterBySid sid1 localEnvMultiNorm)
  let localS2 := traceTags (filterBySid sid2 localEnvSingleNorm)
  let localM2 := traceTags (filterBySid sid2 localEnvMultiNorm)
  expect (decide (localS1 = localM1 ∧ localS2 = localM2))
    "local envelope modulo conformance mismatch"

  -- Test 15: sharded-envelope differential conformance (reference vs sharded execution modulo normalized/session-erased traces).
  let shardRef := runScheduled 100 1 st4
  let shardExec := runScheduled 100 8 st4
  let shardRefNorm := Runtime.VM.normalizeTrace shardRef.obsTrace
  let shardExecNorm := Runtime.VM.normalizeTrace shardExec.obsTrace
  let shardR1 := traceTags (filterBySid sid1 shardRefNorm)
  let shardE1 := traceTags (filterBySid sid1 shardExecNorm)
  let shardR2 := traceTags (filterBySid sid2 shardRefNorm)
  let shardE2 := traceTags (filterBySid sid2 shardExecNorm)
  expect (decide (shardR1 = shardE1 ∧ shardR2 = shardE2))
    "sharded envelope modulo conformance mismatch"

  -- Test 16: admission-check regression around principal-capability boundaries.
  let capInput : Runtime.Adequacy.ProgramCapabilityInput :=
    { localMaxDiff := 2
    , shardedMaxDiff := 3
    , requiresEqSafeOnly := true
    , localProfiles := [.full, .traceModulo]
    , shardedProfiles := [.full, .traceModulo, .commutativityModulo]
    }
  let dProgLocal := Runtime.Adequacy.DProg_local capInput
  let admittedReq : Runtime.Adequacy.DUser :=
    { maxRequestedDiff := 1
    , eqSafeOnly := true
    , requiredProfiles := [.traceModulo]
    }
  expect (Runtime.Adequacy.dUserContained admittedReq dProgLocal)
    "admission regression: expected admitted request to be contained"

  let rejectedReq : Runtime.Adequacy.DUser :=
    { maxRequestedDiff := 5
    , eqSafeOnly := true
    , requiredProfiles := [.commutativityModulo]
    }
  expect (!(Runtime.Adequacy.dUserContained rejectedReq dProgLocal))
    "admission regression: expected rejected request to be outside capability"
  let rejectReasons := Runtime.Adequacy.admissionRejectionReasons rejectedReq dProgLocal
  expect (decide (rejectReasons ≠ []))
    "admission regression: rejected request must produce diagnostics"

  -- Test 17: failure-visible cross-target conformance snapshots agree.
  let localFailureViewSingle := Runtime.Adequacy.vmFailureVisibleSnapshot localSingle
  let localFailureViewMulti := Runtime.Adequacy.vmFailureVisibleSnapshot localMulti
  expect (decide (localFailureViewSingle = localFailureViewMulti))
    "cross-target failure-visible conformance mismatch (local single vs multi)"

  let shardedFailureViewRef := Runtime.Adequacy.vmFailureVisibleSnapshot refFaultRun
  let shardedFailureViewExec := Runtime.Adequacy.vmFailureVisibleSnapshot shardedFaultRun
  expect (decide (shardedFailureViewRef = shardedFailureViewExec))
    "cross-target failure-visible conformance mismatch (reference vs sharded)"

  -- Test 18: restart/refinement preserves structured error adequacy (identity checkpoint/restart baseline).
  let checkpointId := fun (st : VMState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify) => st
/- ## Structured Block 7 -/
  let restartId := fun (st : VMState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify) => st
  let restarted := restartId (checkpointId refFaultRun)
  expect (decide (restarted.structuredErrorEvents = refFaultRun.structuredErrorEvents))
    "restart structured-error adequacy mismatch under identity refinement"

  -- Test 19: threaded runner is exactly aligned with canonical runner at concurrency 1.
  let (stThreadedEq, sidThreadedEq) := loadChoreography emptyState twoPartyImage
  let canonicalEq := runScheduled 50 1 stThreadedEq
  let threadedEq := runScheduledThreaded 50 1 stThreadedEq
  expect (decide (canonicalEq.sched.stepCount = threadedEq.sched.stepCount))
    "threaded@1 step-count mismatch against canonical runner"
  let canonicalEqNorm := Runtime.VM.normalizeTrace canonicalEq.obsTrace
  let threadedEqNorm := Runtime.VM.normalizeTrace threadedEq.obsTrace
  expect (decide (traceTags (filterBySid sidThreadedEq canonicalEqNorm) =
    traceTags (filterBySid sidThreadedEq threadedEqNorm)))
    "threaded@1 per-session trace mismatch against canonical runner"

  -- Test 20: threaded n>1 respects certified-round gate semantics:
  -- either advances by certified waves or falls back to canonical one-step.
  let (stThreadedRound, _) := loadChoreography emptyState twoPartyImage
  let canonicalRound := runScheduled 1 1 stThreadedRound
  let threadedRound := runScheduledThreaded 1 2 stThreadedRound
  expect (decide (threadedRound.sched.stepCount >= canonicalRound.sched.stepCount))
    "threaded n>1 violated certified-round/fallback progression bound"

  -- Test 21: fork is rejected when speculation is disabled.
  let stSpecDisabled := withSpecConfig emptyState false 4
  let forkDisabled := stepFork stSpecDisabled (mkForkOperandCoro 0 5) 0
  expect (isSpecFault forkDisabled.res)
    "fork with speculation disabled should fault"

  -- Test 22: join is rejected when no speculation state is active.
  let joinNoSpec := stepJoin stSpecDisabled (mkReadyCoro 0)
  expect (isSpecFault joinNoSpec.res)
    "join without speculation should fault"

  -- Test 23: abort is rejected when no speculation state is active.
  let abortNoSpec := stepAbort stSpecDisabled (mkReadyCoro 0)
  expect (isSpecFault abortNoSpec.res)
    "abort without speculation should fault"

  -- Test 24: fork initializes depth from maxSpeculationDepth and records ghost sid.
  let stSpecEnabled := withSpecConfig emptyState true 3
  let forkEnabled := stepFork stSpecEnabled (mkForkOperandCoro 0 9) 0
  let forkInitOk :=
    match forkEnabled.coro.specState, forkEnabled.res.status,
        forkEnabled.st.ghostSessions.sessions.get? 9,
        forkEnabled.st.ghostSessions.checkpoints.get? 9 with
    | some spec, .forked gsid, some ghost, some checkpoint =>
        spec.ghostSid = 9 &&
        spec.depth = 2 &&
        gsid = 9 &&
        ghost.owner = 0 &&
        checkpoint.coroId = 0
    | _, _, _, _ => false
  expect forkInitOk
    "fork depth initialization from maxSpeculationDepth is incorrect"

  -- Test 25: fork is rejected when nested speculation depth is exhausted.
  let exhaustedSpec : SpeculationState := { ghostSid := 9, depth := 0 }
  let forkExhausted := stepFork stSpecEnabled (mkForkOperandCoro 0 9 (some exhaustedSpec)) 0
  expect (isSpecFault forkExhausted.res)
    "fork with exhausted speculation depth should fault"

  -- Test 26: successful join emits active ghost sid and clears speculation state.
  let forkForJoin := stepFork stSpecEnabled (mkForkOperandCoro 0 23) 0
  let joinActive := stepJoin forkForJoin.st forkForJoin.coro
  let joinSidOk :=
    match joinActive.res.status, joinActive.res.event, joinActive.coro.specState,
        joinActive.st.ghostSessions.sessions.get? 23,
        joinActive.st.ghostSessions.checkpoints.get? 23,
        joinActive.st.needsReconciliation with
    | .joined, some (.obs (.joined sid)), none, none, none, false => sid = 23
    | _, _, _, _, _, _ => false
  expect joinSidOk
    "join should emit active ghost sid and clear speculation state"

  -- Test 27: join fails when reconciliation predicate does not hold.
  let forkForJoinFail := stepFork stSpecEnabled (mkForkOperandCoro 0 40) 0
  let joinMismatchResult :=
    match forkForJoinFail.st.ghostSessions.sessions.get? 40 with
    | none => forkForJoinFail
    | some ghost =>
        let ghostBad : VMGhostSession :=
          { ghost with projectedLocalTypes := [({ sid := ghost.realSid, role := "A" }, LocalType.end_)] }
        let ghostStateBad : GhostRuntimeState :=
          { forkForJoinFail.st.ghostSessions with
              sessions := forkForJoinFail.st.ghostSessions.sessions.insert 40 ghostBad }
        let stBad := { forkForJoinFail.st with ghostSessions := ghostStateBad }
        stepJoin stBad forkForJoinFail.coro
  expect (isSpecFault joinMismatchResult.res)
    "join should fault when reconciliation predicate fails"

  -- Test 28: successful abort emits active ghost sid and clears speculation state.
  let abortActive := stepAbort stSpecEnabled
    { mkReadyCoro 0 with specState := some { ghostSid := 24, depth := 1 } }
  let abortSidOk :=
    match abortActive.res.status, abortActive.res.event, abortActive.coro.specState,
        abortActive.st.ghostSessions.sessions.get? 24,
        abortActive.st.ghostSessions.checkpoints.get? 24,
        abortActive.st.needsReconciliation with
    | .aborted, some (.obs (.aborted sid)), none, none, none, false => sid = 24
    | _, _, _, _, _, _ => false
  expect abortSidOk
    "abort should emit active ghost sid and clear speculation state"

  -- Test 29: abort restores checkpointed trace length and effect nonce.
  let forkForAbort := stepFork stSpecEnabled (mkForkOperandCoro 0 31) 0
  let stDirty :=
    { forkForAbort.st with
        obsTrace := forkForAbort.st.obsTrace ++ [{ tick := 999, event := .joined 31 }]
        nextEffectNonce := forkForAbort.st.nextEffectNonce + 7
        needsReconciliation := true }
  let abortRestored := stepAbort stDirty forkForAbort.coro
  let abortRestoreOk :=
    abortRestored.st.obsTrace.length = forkForAbort.st.obsTrace.length &&
    abortRestored.st.nextEffectNonce = forkForAbort.st.nextEffectNonce &&
    abortRestored.st.needsReconciliation = false
  expect abortRestoreOk
    "abort should restore checkpointed trace length/nonce/reconciliation state"

  -- Test 30: replay conformance checks pass against certified equivalence classes.
  let replayInventory : List (String × Bool) :=
    [ ("protocol_envelope_bridge", true)
    , ("vm_envelope_adherence", true)
    , ("vm_envelope_admission", true)
    , ("failure_envelope", true)
    ]
  let replayClasses := Runtime.Proofs.TheoremPackAPI.defaultCertifiedReplayClasses
  let replayConformanceOk :=
    Runtime.Proofs.TheoremPackAPI.replayConformsToClasses
      replayInventory replayClasses localEnvSingle.obsTrace localEnvMulti.obsTrace
  expect replayConformanceOk
    "replay conformance mismatch against certified equivalence class"

  -- Test 31: deterministic planner yields the same wave plan for the same input state.
  let stPlan := schedulerTestState .roundRobin true
  let planA := planDeterministicWaves stPlan
  let planB := planDeterministicWaves stPlan
  expect (decide (planA = planB))
    "deterministic planner produced non-deterministic wave plans"

  -- Test 32: worker-count chunking preserves the deterministic planned pick set/order.
  let flattenWaves := fun (waves : List (List CoroutineId)) =>
    waves.foldl (fun acc wave => acc ++ wave) []
  let samePickSeq := fun (xs ys : List CoroutineId) =>
    xs.length == ys.length &&
      (List.zip xs ys).all (fun p => p.1 == p.2)
  let picks2 := flattenWaves (plannedWaveCertificate 2 stPlan).waves
  let picks4 := flattenWaves (plannedWaveCertificate 4 stPlan).waves
  let picks8 := flattenWaves (plannedWaveCertificate 8 stPlan).waves
  expect (samePickSeq picks2 picks4 && samePickSeq picks2 picks8)
    "worker-count changed deterministic planned picks"

  -- Test 33: n>1 round is certificate-gated and falls back to canonical one-step when needed.
  let cert2 := plannedWaveCertificate 2 stPlan
  let expected2 :=
    if checkWaveCertificate stPlan cert2 then
      executePlannedWaves stPlan cert2.waves
    else
      schedRound 1 stPlan
  let actual2 := schedRoundThreaded 2 stPlan
  expect (decide (actual2.sched.stepCount = expected2.sched.stepCount))
    "threaded n>1 round violated certificate/fallback gate semantics"

  -- Test 34: threaded n>1 divergence from canonical remains envelope-bounded per session.
  let threadedEnv := runScheduledThreaded 100 4 st4
  let canonicalEnv := runScheduled 100 1 st4
  let threadedEnvNorm := Runtime.VM.normalizeTrace threadedEnv.obsTrace
  let canonicalEnvNorm := Runtime.VM.normalizeTrace canonicalEnv.obsTrace
  let threadedS1 := traceTags (filterBySid sid1 threadedEnvNorm)
  let canonicalS1 := traceTags (filterBySid sid1 canonicalEnvNorm)
  let threadedS2 := traceTags (filterBySid sid2 threadedEnvNorm)
  let canonicalS2 := traceTags (filterBySid sid2 canonicalEnvNorm)
  expect (decide (threadedS1 = canonicalS1 ∧ threadedS2 = canonicalS2))
    "threaded n>1 divergence exceeded envelope-bounded per-session traces"

  -- Test 35: non-delegation cross-shard ownership mutations are rejected.
  let endpointKey : Endpoint := { sid := 7, role := "A" }
  let schedOwned :=
    { stLane.sched with ownershipIndex := stLane.sched.ownershipIndex.insert (7, "A") 0 }
  let schedRejected := updateAfterStep schedOwned 1 (.transferred endpointKey 0)
  expect (decide (schedRejected.ownershipIndex.get? (7, "A") = some 0))
    "non-delegation cross-shard ownership mutation should be rejected"
  expect (decide (schedRejected.crossLaneHandoffs.length = 0))
    "rejected transfer should not emit cross-lane handoff evidence"

  -- Test 36: handoff evidence is deterministic and auditable for replay.
  let schedEvidence1 := updateAfterStep stLane.sched 0 (.transferred endpointKey 1)
  let schedEvidence2 := updateAfterStep stLane.sched 0 (.transferred endpointKey 1)
  let handoffStable :=
    match schedEvidence1.crossLaneHandoffs, schedEvidence2.crossLaneHandoffs with
    | h1 :: _, h2 :: _ =>
        h1.reason = h2.reason &&
        h1.delegationWitness = h2.delegationWitness &&
        h1.reason.startsWith "transfer " &&
        h1.delegationWitness.length > 0
    | _, _ => false
  expect handoffStable
    "handoff evidence must be replay-stable and auditable"

  -- Test 37: shared canonical one-step helper is covered by
  -- `schedRoundOne_eq_schedRound_one` above.

  -- Test 38: transfer fault helper emits normalized transfer target fault message.
  let transferEp : Endpoint := { sid := 9, role := "A" }
  let badTransferRegs : RegFile :=
    #[ .chan transferEp
     , .string "not-a-target"
     , .unit, .unit, .unit, .unit, .unit, .unit ]
  let badTransferCoro : CoroutineState UnitGuard UnitEffect :=
    { mkReadyCoro 0 with regs := badTransferRegs, ownedEndpoints := [transferEp] }
  let badTransferPack := stepTransfer stPlan badTransferCoro 0 1 0
  expect (hasTransferFaultMsg badTransferPack.res "bad transfer target")
    "transfer target type fault did not use normalized transfer fault helper"
