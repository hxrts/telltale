import Runtime.Resources.ResourceModel
import Runtime.VM.ExecHelpers

/-!
# Ownership and Knowledge Instruction Semantics

Step functions for `transfer`, `tag`, and `check`.

`stepTransfer` moves an owned endpoint from one coroutine to another. It applies a
(currently empty) resource transaction at the endpoint's session scope, migrates
progress tokens and knowledge facts that are bound to the transferred endpoint,
and emits a `transferred` event. This is the operational counterpart of the owned
protocol continuation transfer described in `runtime.md` §19.

`stepTag` records a knowledge fact (endpoint + string) in the coroutine's knowledge
set and emits a `tagged` event. `stepCheck` queries whether a fact exists in the
knowledge set and whether the flow policy permits it to reach a target role, writing
a boolean result to a destination register. Together these implement the epistemic
separation logic instructions from `runtime.md` §16.
-/

set_option autoImplicit false

universe u

/-! ## Ownership and knowledge semantics -/

private def splitTokens {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (coro : CoroutineState γ ε) (ep : Endpoint) : List ProgressToken × List ProgressToken :=
  -- Partition progress tokens by endpoint.
  let moved := coro.progressTokens.filter (fun t => decide (t.endpoint = ep))
  let kept := coro.progressTokens.filter (fun t => decide (t.endpoint ≠ ep))
  (moved, kept)

private def splitKnowledge {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (coro : CoroutineState γ ε) (ep : Endpoint) : KnowledgeSet × KnowledgeSet :=
  -- Partition knowledge facts by endpoint.
  let moved := coro.knowledgeSet.filter (fun k => decide (k.endpoint = ep))
  let kept := coro.knowledgeSet.filter (fun k => decide (k.endpoint ≠ ep))
  (moved, kept)

private def updateTargetCoro {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (coros : Array (CoroutineState γ ε)) (tid : Nat) (ep : Endpoint)
    (movedTokens : List ProgressToken) (movedFacts : KnowledgeSet) : Array (CoroutineState γ ε) :=
  -- Update the target coroutine when the index is in range.
  if h : tid < coros.size then
    let cT := coros[tid]'h
    let cT' :=
      { cT with ownedEndpoints := ep :: cT.ownedEndpoints
               , progressTokens := movedTokens ++ cT.progressTokens
               , knowledgeSet := movedFacts ++ cT.knowledgeSet }
    coros.set (i := tid) (v := cT') (h := h)
  else
    coros

private def transferCommit {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint)
    (tid : Nat) (resources' : List (ScopeId × ResourceState ν)) : StepPack ι γ π ε ν :=
  -- Move ownership, tokens, and facts between coroutines.
  let (movedTokens, keptTokens) := splitTokens coro ep
  let (movedFacts, keptFacts) := splitKnowledge coro ep
  let coros' := updateTargetCoro st.coroutines tid ep movedTokens movedFacts
  let st' := { st with coroutines := coros', resourceStates := resources' }
  let coro' := advancePc { coro with ownedEndpoints := coro.ownedEndpoints.filter (fun e => decide (e ≠ ep))
                                    , progressTokens := keptTokens
                                    , knowledgeSet := keptFacts }
  pack coro' st' (mkRes (.transferred ep tid) (some (.obs (.transferred ep coro.id tid))))

/-! ## Transfer conservation lemmas -/

/-- Transfer preserves session-level state: the session store and signed buffer
    store are unchanged by `transferCommit`. This mirrors the conservation
    pattern from Gibbs's `drift_conserves` — transfer rearranges coroutine
    ownership (a zero-sum operation) without modifying session-level typing
    state. Since session coherence (`EdgeCoherent`) depends on `GEnv` and `DEnv`
    (ghost state in the Iris sense), not on which coroutine owns which endpoint,
    coherence is automatically preserved by any operation that leaves the
    session store and buffers untouched. -/
def transfer_preserves_coherent_prop : Prop :=
  ∀ {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (ep : Endpoint) (tid : Nat) (resources' : List (ScopeId × ResourceState ν)),
    (transferCommit st coro ep tid resources').st.sessions = st.sessions ∧
    (transferCommit st coro ep tid resources').st.buffers = st.buffers

theorem transfer_preserves_coherent_proof : transfer_preserves_coherent_prop :=
  fun _st _coro _ep _tid _resources' => ⟨rfl, rfl⟩

private def transferWithEndpoint {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) (ep : Endpoint) (tid : Nat) :
    StepPack ι γ π ε ν :=
  -- Validate ownership and apply the transfer transaction.
  if owns coro ep then
    let tx : Transaction ν :=
      { created := []
      , consumed := []
      , deltaProof := ()
      , logicProofs := []
      , complianceProofs := []
      , authorizedImbalance := true }
    match applyTransactionAtScope st.resourceStates { id := ep.sid } tx with
    | none =>
        faultPack st coro (.transferFault "resource transaction failed") "resource transaction failed"
    | some resources' => transferCommit st coro ep tid resources'
  else
    faultPack st coro (.transferFault "endpoint not owned") "endpoint not owned"


def stepTransfer {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (endpoint targetCoro _bundle : Reg) : StepPack ι γ π ε ν :=
  -- Transfer an owned endpoint to another coroutine.
  match readReg coro.regs endpoint, readReg coro.regs targetCoro with
  | some (.chan ep), some (.nat tid) => transferWithEndpoint st coro ep tid
  | some (.chan _), none => faultPack st coro .outOfRegisters "missing transfer target"
  | some (.chan _), some v =>
      faultPack st coro (.typeViolation .nat (valTypeOf v)) "bad transfer target"
  | some v, _ => faultPack st coro (.typeViolation (.chan 0 "") (valTypeOf v)) "bad transfer endpoint"
  | none, _ => faultPack st coro .outOfRegisters "missing transfer endpoint"


def stepTag {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (fact dst : Reg) : StepPack ι γ π ε ν :=
  -- Record a knowledge fact and return success.
  match readReg coro.regs fact with
  | some (.prod (.chan ep) (.string s)) =>
      match setReg coro.regs dst (.bool true) with
      | none => faultPack st coro .outOfRegisters "bad dst reg"
      | some regs' =>
          let fact' := { endpoint := ep, fact := s }
          let know' := fact' :: coro.knowledgeSet
          let ev := StepEvent.obs (.tagged fact')
          continuePack st { coro with regs := regs', knowledgeSet := know' } (some ev)
  | some v =>
      faultPack st coro (.typeViolation (.prod (.chan 0 "") .string) (valTypeOf v)) "bad fact"
  | none =>
      faultPack st coro .outOfRegisters "missing fact"


def stepCheck {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (knowledge target dst : Reg) : StepPack ι γ π ε ν :=
  -- Check whether a fact is in the knowledge set.
  match readReg coro.regs knowledge with
  | some (.prod (.chan ep) (.string s)) =>
      let fact := { endpoint := ep, fact := s }
      let permitted := st.config.flowPolicy.allowed fact
      let tgtRole : Role :=
        match readReg coro.regs target with
        | some (.string r) => r
        | _ => ""
      let ok := permitted tgtRole && coro.knowledgeSet.any (fun k => k == fact)
      match setReg coro.regs dst (.bool ok) with
      | none => faultPack st coro .outOfRegisters "bad dst reg"
      | some regs' =>
          let ev := StepEvent.obs (.checked tgtRole ok)
          continuePack st { coro with regs := regs' } (some ev)
  | some v =>
      faultPack st coro (.typeViolation (.prod (.chan 0 "") .string) (valTypeOf v)) "bad knowledge"
  | none =>
      faultPack st coro .outOfRegisters "missing knowledge"
