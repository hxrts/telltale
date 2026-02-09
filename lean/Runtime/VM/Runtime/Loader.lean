import Runtime.VM.Model.State
import Runtime.VM.Semantics.ExecHelpers
import Runtime.VM.Model.Program
import Runtime.Resources.Arena
import Protocol.Environments.Core

/-!
# Dynamic Choreography Loading

Pure state transformer that adds a session and its coroutines to a running VM.
-/

set_option autoImplicit false

universe u

private def allEdges (sid : SessionId) (roles : List Role) : List Edge :=
  roles.foldl
    (fun acc r1 => acc ++ roles.map (fun r2 => { sid := sid, sender := r1, receiver := r2 }))
    []

/-! ## Session disjointness (stubs) -/

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
  let sid := st.nextSessionId
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

/-!
Proof-only disjointness lemmas for `loadChoreography` live in:
`Runtime.Proofs.VM.LoadChoreography`.
-/
