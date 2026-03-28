
import Runtime.ProtocolMachine.Model.State
import Runtime.ProtocolMachine.Semantics.ExecHelpers
import Runtime.ProtocolMachine.Model.Program
import Runtime.Resources.Arena
import Protocol.Environments.Core
import Choreography.Projection.Project.Core

/-! # Runtime.ProtocolMachine.Runtime.Loader

Pure state transformer that adds a session and its coroutines to a running protocol machine.
-/

/-
The Problem. Runtime choreography loading must validate images, allocate fresh
session identifiers, and install new coroutines/session state without violating
existing protocol machine capacity and structural invariants.

Solution Structure. This module builds executable checks and loader primitives,
then packages result-typed and compatibility APIs plus monotonicity lemmas for
the allocated session identifier.
-/

/- ## Structured Block 1 -/
set_option autoImplicit false

universe u

private def allEdges (sid : SessionId) (roles : List Role) : List Edge :=
  roles.foldl
    (fun acc r1 => acc ++ roles.map (fun r2 => { sid := sid, sender := r1, receiver := r2 }))
    []

-- Session disjointness (executable checks)

-- # Existing id inspection and fresh-id selection

/-- Existing session ids in a protocol machine state. -/
def existingSessionIds {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν] :
    ProtocolMachineState ι γ π ε ν → List SessionId :=
  fun st => st.sessions.map (fun p => p.fst)

/-- Two sessions have disjoint resources when they have distinct identifiers. -/
def SessionDisjoint {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : ProtocolMachineState ι γ π ε ν) (sid1 sid2 : SessionId) : Prop :=
  sid1 ≠ sid2

/-- Executable session-id availability check for loader admission. -/
def sessionIdAvailable {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (sid : SessionId) : Bool :=
  !(existingSessionIds st).contains sid

-- ## Fresh-id synthesis and lower bound

/-- Deterministically choose a fresh session id even if state ids are non-canonical. -/
def nextFreshSessionId {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) : SessionId :=
  let sid := st.nextSessionId
  if sessionIdAvailable st sid then
    sid
  else
    let maxSeen := (existingSessionIds st).foldl Nat.max sid
/- ## Structured Block 2 -/
    maxSeen + 1

-- # Loader result type and image validation

/-- Outcome of choreography loading with explicit error categories. -/
inductive ChoreographyLoadResult (ι γ π ε ν : Type u) [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν] where
  | ok (state : ProtocolMachineState ι γ π ε ν) (sid : SessionId)
  | validationFailed (reason : String)
  | tooManySessions (max : Nat)
  | tooManyCoroutines (max : Nat)

mutual
  private def localTypeREq : SessionTypes.LocalTypeR.LocalTypeR → SessionTypes.LocalTypeR.LocalTypeR → Bool
    | .end, .end => true
    | .var v1, .var v2 => v1 == v2
    | .mu v1 b1, .mu v2 b2 => (v1 == v2) && localTypeREq b1 b2
    | .send p1 bs1, .send p2 bs2 => (p1 == p2) && branchesEq bs1 bs2
    | .recv p1 bs1, .recv p2 bs2 => (p1 == p2) && branchesEq bs1 bs2
    | _, _ => false

  private def branchesEq : List SessionTypes.LocalTypeR.BranchR → List SessionTypes.LocalTypeR.BranchR → Bool
    | [], [] => true
    | b1 :: bs1, b2 :: bs2 => branchEq b1 b2 && branchesEq bs1 bs2
    | _, _ => false

  private def branchEq : SessionTypes.LocalTypeR.BranchR → SessionTypes.LocalTypeR.BranchR → Bool
    | (l1, v1, t1), (l2, v2, t2) =>
        decide (l1 = l2) && decide (v1 = v2) && localTypeREq t1 t2
end

private def validateImage? {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (image : CodeImage γ ε) : Option String :=
  let lookupLocalType :=
    fun (roles : List (Role × SessionTypes.LocalTypeR.LocalTypeR)) (role : Role) =>
      (roles.find? (fun p => p.1 = role)).map Prod.snd
  let entryRoles := image.program.entryPoints.map Prod.fst
  let localRoles := image.program.localTypesR.map Prod.fst
  if entryRoles.length ≠ localRoles.length then
    some "entry/local role arity mismatch"
  else if entryRoles.eraseDups.length ≠ entryRoles.length then
    some "duplicate entry-point role"
  else if localRoles.eraseDups.length ≠ localRoles.length then
    some "duplicate local-type role"
  else if !entryRoles.all (fun r => localRoles.contains r) then
    some "entry/local role mismatch"
  else
    match entryRoles.find? (fun role =>
      match lookupLocalType image.program.localTypesR role with
      | none => true
      | some claimed =>
          let projected? := Choreography.Projection.Project.projectR? image.globalType role
          match projected? with
          | none => true
          | some projected =>
/- ## Structured Block 3 -/
              !localTypeREq projected.1 claimed) with
    | some role => some s!"projection mismatch for role {role}"
    | none => none

-- # Core trusted loader path

/-- Core trusted loader path used by checked and compatibility APIs. -/
private def loadChoreographyCore {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    [Inhabited (EffectRuntime.EffectCtx ε)]
    (st : ProtocolMachineState ι γ π ε ν) (image : CodeImage γ ε) (sid : SessionId) :
    ProtocolMachineState ι γ π ε ν :=
  let programId := st.programs.size
  let programs' := st.programs.push image.program
  let roles := image.program.entryPoints.map (fun p => p.fst)
  let endpoints := roles.map (fun r => { sid := sid, role := r })
  let edges := allEdges sid roles
  let buffers := signedBuffersEnsure st.buffers edges
  let localTypes := image.program.localTypes.map (fun p => ({ sid := sid, role := p.1 }, p.2))
  let handlers := edges.map (fun e => (e, 0))
  let session : SessionState ν :=
    { scope := { id := sid }
    , sid := sid
    , roles := roles
    , endpoints := endpoints
    , localTypes := localTypes
    , traces := initDEnv sid roles
    , buffers := buffersFor buffers sid
    , handlers := handlers
    , epoch := 0
    , phase := .active }
  let sessions' := (sid, session) :: st.sessions

  -- ## Coroutine installation for each entry role

  let mkCoro := fun (acc : Array (CoroutineState γ ε) × List CoroutineId × CoroutineId)
      (entry : Role × PC) =>
    let (coros, ready, nextId) := acc
    let coro : CoroutineState γ ε :=
      let endpoint : Endpoint := { sid := sid, role := entry.1 }
      { id := nextId
      , programId := programId
      , pc := entry.2
      , regs := (Array.replicate 8 .unit).set! 0 (.chan endpoint)
      , status := .ready
      , effectCtx := default
      , ownedEndpoints := [endpoint]
      , progressTokens := []
      , knowledgeSet := []
      , costBudget := st.config.costModel.defaultBudget
      , specState := none }
    (coros.push coro, ready ++ [nextId], nextId + 1)
  let (coroutines', readyQueue', nextCoroId') :=
/- ## Structured Block 4 -/
    image.program.entryPoints.foldl mkCoro (st.coroutines, st.sched.readyQueue, st.nextCoroId)
  let sched' := { st.sched with readyQueue := readyQueue' }
  let trace' := st.obsTrace ++ [{ tick := st.clock, event := .opened sid roles }]
  let st' := { st with
    programs := programs'
    coroutines := coroutines'
    buffers := buffers
    sessions := sessions'
    sched := sched'
    obsTrace := trace'
    nextCoroId := nextCoroId'
    nextSessionId := sid + 1 }
  st'

-- # Public loader APIs

/-- Load a choreography with explicit validation and capacity error results. -/
def loadChoreographyResult {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    [Inhabited (EffectRuntime.EffectCtx ε)]
    (st : ProtocolMachineState ι γ π ε ν) (image : CodeImage γ ε) :
    ChoreographyLoadResult ι γ π ε ν :=
  match validateImage? image with
  | some reason => .validationFailed reason
  | none =>
      if st.sessions.length >= st.config.maxSessions then
        .tooManySessions st.config.maxSessions
      else if st.coroutines.size + image.program.entryPoints.length > st.config.maxCoroutines then
        .tooManyCoroutines st.config.maxCoroutines
      else
        let sid := nextFreshSessionId st
        let st' := loadChoreographyCore st image sid
        .ok st' sid

/-- Load a choreography into a running protocol machine, returning the updated state and session id. -/
def loadChoreography {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    [Inhabited (EffectRuntime.EffectCtx ε)]
    (st : ProtocolMachineState ι γ π ε ν) (image : CodeImage γ ε) :
    ProtocolMachineState ι γ π ε ν × SessionId :=
  match loadChoreographyResult st image with
  | .ok st' sid => (st', sid)
  | _ => (st, st.nextSessionId)

/-! Proof-only loader lemmas are in `Runtime.Proofs.ProtocolMachine.LoadChoreography`. -/
