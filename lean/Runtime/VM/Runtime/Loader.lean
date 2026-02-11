import Runtime.VM.Model.State
import Runtime.VM.Semantics.ExecHelpers
import Runtime.VM.Model.Program
import Runtime.Resources.Arena
import Protocol.Environments.Core
import Choreography.Projection.Project.Core

/-! # Runtime.VM.Runtime.Loader

Pure state transformer that adds a session and its coroutines to a running VM.
-/

/-
The Problem. Runtime choreography loading must validate images, allocate fresh
session identifiers, and install new coroutines/session state without violating
existing VM capacity and structural invariants.

Solution Structure. This module builds executable checks and loader primitives,
then packages result-typed and compatibility APIs plus monotonicity lemmas for
the allocated session identifier.
-/

set_option autoImplicit false

universe u

private def allEdges (sid : SessionId) (roles : List Role) : List Edge :=
  roles.foldl
    (fun acc r1 => acc ++ roles.map (fun r2 => { sid := sid, sender := r1, receiver := r2 }))
    []

private lemma foldl_max_ge_start (xs : List Nat) (start : Nat) :
    start ≤ xs.foldl Nat.max start := by
  induction xs generalizing start with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.foldl]
      exact Nat.le_trans (Nat.le_max_left start x) (ih (Nat.max start x))

/-! ## Session disjointness (executable checks) -/

/-- Existing session ids in a VM state. -/
def existingSessionIds {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν] :
    VMState ι γ π ε ν → List SessionId :=
  fun st => st.sessions.map (fun p => p.fst)

/-- Two sessions have disjoint resources when they have distinct identifiers. -/
def SessionDisjoint {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (sid1 sid2 : SessionId) : Prop :=
  sid1 ≠ sid2

/-- Executable session-id availability check for loader admission. -/
def sessionIdAvailable {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (sid : SessionId) : Bool :=
  !(existingSessionIds st).contains sid

/-- Deterministically choose a fresh session id even if state ids are non-canonical. -/
def nextFreshSessionId {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : SessionId :=
  let sid := st.nextSessionId
  if sessionIdAvailable st sid then
    sid
  else
    let maxSeen := (existingSessionIds st).foldl Nat.max sid
    maxSeen + 1

private lemma nextFreshSessionId_ge {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) :
    st.nextSessionId ≤ nextFreshSessionId st := by
  unfold nextFreshSessionId
  by_cases hAvail : sessionIdAvailable st st.nextSessionId
  · simp [hAvail]
  · simp [hAvail]
    exact Nat.le_trans
      (foldl_max_ge_start (existingSessionIds st) st.nextSessionId)
      (Nat.le_succ _)

/-- Outcome of choreography loading with explicit error categories. -/
inductive ChoreographyLoadResult (ι γ π ε ν : Type u) [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν] where
  | ok (state : VMState ι γ π ε ν) (sid : SessionId)
  | validationFailed (reason : String)
  | tooManySessions (max : Nat)
  | tooManyCoroutines (max : Nat)

private def validateImage? {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (image : CodeImage γ ε) : Option String :=
  let lookupLocalType :=
    fun (roles : List (Role × LocalType)) (role : Role) =>
      (roles.find? (fun p => p.1 = role)).map Prod.snd
  let entryRoles := image.program.entryPoints.map Prod.fst
  let localRoles := image.program.localTypes.map Prod.fst
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
      match lookupLocalType image.program.localTypes role with
      | none => true
      | some claimed =>
          let projected? := Choreography.Projection.Project.projectR? image.globalType role
          match projected? with
          | none => true
          | some projected =>
              reprStr (localTypeRToLocalType projected.1) != reprStr claimed) with
    | some role => some s!"projection mismatch for role {role}"
    | none => none

/-- Core trusted loader path used by checked and compatibility APIs. -/
private def loadChoreographyCore {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    [Inhabited (EffectRuntime.EffectCtx ε)]
    (st : VMState ι γ π ε ν) (image : CodeImage γ ε) :
    VMState ι γ π ε ν × SessionId :=
  let sid := nextFreshSessionId st
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
  let mkCoro := fun (acc : Array (CoroutineState γ ε) × List CoroutineId × CoroutineId)
      (entry : Role × PC) =>
    let (coros, ready, nextId) := acc
    let coro : CoroutineState γ ε :=
      { id := nextId
      , programId := programId
      , pc := entry.2
      , regs := Array.replicate 8 .unit
      , status := .ready
      , effectCtx := default
      , ownedEndpoints := [{ sid := sid, role := entry.1 }]
      , progressTokens := []
      , knowledgeSet := []
      , costBudget := st.config.costModel.defaultBudget
      , specState := none }
    (coros.push coro, ready ++ [nextId], nextId + 1)
  let (coroutines', readyQueue', nextCoroId') :=
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
  (st', sid)

/-- Load a choreography with explicit validation and capacity error results. -/
def loadChoreographyResult {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    [Inhabited (EffectRuntime.EffectCtx ε)]
    (st : VMState ι γ π ε ν) (image : CodeImage γ ε) :
    ChoreographyLoadResult ι γ π ε ν :=
  match validateImage? image with
  | some reason => .validationFailed reason
  | none =>
      if st.sessions.length >= st.config.maxSessions then
        .tooManySessions st.config.maxSessions
      else if st.coroutines.size + image.program.entryPoints.length > st.config.maxCoroutines then
        .tooManyCoroutines st.config.maxCoroutines
      else
        let (st', sid) := loadChoreographyCore st image
        .ok st' sid

/-- Load a choreography into a running VM, returning the updated state and session id. -/
def loadChoreography {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    [Inhabited (EffectRuntime.EffectCtx ε)]
    (st : VMState ι γ π ε ν) (image : CodeImage γ ε) :
    VMState ι γ π ε ν × SessionId :=
  match loadChoreographyResult st image with
  | .ok st' sid => (st', sid)
  | _ => (st, st.nextSessionId)

theorem loadChoreography_snd_ge_nextSessionId
    {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    [Inhabited (EffectRuntime.EffectCtx ε)]
    (st : VMState ι γ π ε ν) (image : CodeImage γ ε) :
    st.nextSessionId ≤ (loadChoreography st image).2 := by
  unfold loadChoreography loadChoreographyResult
  cases hVal : validateImage? image with
  | some reason =>
      simp
  | none =>
      by_cases hSess : st.sessions.length >= st.config.maxSessions
      · simp [hSess]
      · by_cases hCoros :
            st.coroutines.size + image.program.entryPoints.length > st.config.maxCoroutines
        · simp [hSess, hCoros]
        · simp [hSess, hCoros, loadChoreographyCore, nextFreshSessionId_ge]

/-!
Proof-only disjointness lemmas for `loadChoreography` live in:
`Runtime.Proofs.VM.LoadChoreography`.
-/
