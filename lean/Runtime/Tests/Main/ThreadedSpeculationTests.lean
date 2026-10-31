import Runtime.Tests.Main.Helpers

/-! # Runtime tests: threaded runner and speculation

Tests 19-29 of the `runtime_tests` executable: threaded-runner alignment with the
canonical runner and fork/join/abort speculation semantics.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

open SessionTypes.LocalTypeR
open SessionTypes.GlobalType

/-- Tests 19-29: threaded runner alignment and speculation fork/join/abort. -/
def runThreadedSpeculationTests : IO Unit := do
  -- Test 19: threaded runner is exactly aligned with canonical runner at concurrency 1.
  let (stThreadedEq, sidThreadedEq) := loadChoreography emptyState twoPartyImage
  let canonicalEq := runScheduled 50 1 stThreadedEq
  let threadedEq := runScheduledThreaded 50 1 stThreadedEq
  expect (decide (canonicalEq.sched.stepCount = threadedEq.sched.stepCount))
    "threaded@1 step-count mismatch against canonical runner"
  let canonicalEqNorm := Runtime.ProtocolMachine.normalizeTrace canonicalEq.obsTrace
  let threadedEqNorm := Runtime.ProtocolMachine.normalizeTrace threadedEq.obsTrace
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
        let ghostBad : ProtocolMachineGhostSession :=
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
