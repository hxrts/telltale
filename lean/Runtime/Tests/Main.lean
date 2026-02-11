import Runtime.Examples.SimpleProtocol
import Runtime.VM.Runtime.Runner
import Runtime.VM.Runtime.Loader
import Runtime.VM.Runtime.Failure
import Runtime.Adequacy.EnvelopeCore
import SessionTypes.LocalTypeR
import SessionTypes.GlobalType

/-
Executable Lean tests for the scheduled VM runner.
-/

set_option autoImplicit false

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
  , ghostSessions := ()
  , progressSupply := () }

/-- Simple two-party LocalTypeR image. -/
def twoPartyImage : CodeImage UnitGuard UnitEffect :=
  let lbl : SessionTypes.GlobalType.Label := { name := "msg" }
  let ltA : LocalTypeR := .send "B" [(lbl, none, .end)]
  let ltB : LocalTypeR := .recv "A" [(lbl, none, .end)]
  CodeImage.fromLocalTypes [ ("A", ltA), ("B", ltB) ] .end

/-- Test helper: assert a boolean. -/
def expect (ok : Bool) (msg : String) : IO Unit :=
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

/-- Main test entry point. -/
def main : IO Unit := do
  -- Test 1: N=1, single protocol.
  let (st1, _) := loadChoreography emptyState twoPartyImage
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
