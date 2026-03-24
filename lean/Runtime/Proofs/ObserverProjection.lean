import Runtime.Proofs.ProtocolMachinePotential
import Runtime.Resources.Arena
import ClassicalAnalysisAPI

/-! # Protocol-Machine Observer/Projection Bridge

Protocol-machine observer projection plus noninterference and information-theoretic
bridge lemmas for coroutine-local views. -/

/-
The Problem. Individual coroutines should only observe session state relevant to
their owned endpoints, enabling noninterference arguments and information-theoretic
bounds on what each participant can learn.

Solution Structure. Defines `CoroutineView` as the projection of protocol-machine state visible
to a single coroutine: local types, incoming traces, incoming buffers, progress
tokens, and knowledge set. Provides `coroutineProjection` and `coroutineView`
functions with noninterference lemmas showing unrelated operations don't affect
views.
-/

set_option autoImplicit false

section

universe u

/-- Coroutine-local observable projection from protocol-machine state. -/
structure CoroutineView where
  localTypes : List (Endpoint × Option LocalType)
  incomingTraces : List (Edge × List ValType)
  incomingBuffers : List (Edge × Buffer)
  progressTokens : List ProgressToken
  knowledgeSet : KnowledgeSet

private def tracesForEndpoint (D : DEnv) (ep : Endpoint) : List (Edge × List ValType) :=
  D.list.filter (fun p => p.1.sid = ep.sid ∧ p.1.receiver = ep.role)

private def buffersForEndpoint (bufs : Buffers) (ep : Endpoint) : List (Edge × Buffer) :=
  bufs.filter (fun p => p.1.sid = ep.sid ∧ p.1.receiver = ep.role)

/-! ## Coroutine Projection Operators -/

/-- Projection of one coroutine against the current session store. -/
def coroutineProjection {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) : CoroutineView :=
  let D := SessionStore.toDEnv st.sessions
  let bufs := SessionStore.toBuffers st.sessions
  { localTypes := coro.ownedEndpoints.map (fun ep => (ep, SessionStore.lookupType st.sessions ep))
    incomingTraces := coro.ownedEndpoints.foldr (fun ep acc => tracesForEndpoint D ep ++ acc) []
    incomingBuffers := coro.ownedEndpoints.foldr (fun ep acc => buffersForEndpoint bufs ep ++ acc) []
    progressTokens := coro.progressTokens
    knowledgeSet := coro.knowledgeSet }

/-- Public observer view of a coroutine id in protocol-machine state. -/
def coroutineView {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (cid : CoroutineId) : Option CoroutineView :=
  (st.coroutines[cid]?).map (coroutineProjection st)

/-- Explicit projection function (name used in Paper 3 task list). -/
def coroutineProjectionAt {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (cid : CoroutineId) : Option CoroutineView :=
  match st.coroutines[cid]? with
  | none => none
  | some coro => some (coroutineProjection st coro)

theorem coroutine_view_eq_projection {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (cid : CoroutineId) :
    coroutineView st cid = coroutineProjectionAt st cid := by
  cases hco : st.coroutines[cid]? <;> simp [coroutineView, coroutineProjectionAt, hco]

/-! ## Observer Equivalence -/

/-- Protocol-machine observational equivalence for one coroutine id. -/
def CoroutineViewEquiv {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st₁ st₂ : VMState ι γ π ε ν) (cid : CoroutineId) : Prop :=
  coroutineView st₁ cid = coroutineView st₂ cid

theorem coroutine_view_equiv_refl {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (cid : CoroutineId) :
    CoroutineViewEquiv st st cid := rfl

theorem coroutine_view_equiv_symm {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    {st₁ st₂ : VMState ι γ π ε ν} {cid : CoroutineId}
    (h : CoroutineViewEquiv st₁ st₂ cid) :
    CoroutineViewEquiv st₂ st₁ cid := Eq.symm h

theorem coroutine_view_equiv_trans {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    {st₁ st₂ st₃ : VMState ι γ π ε ν} {cid : CoroutineId}
    (h₁₂ : CoroutineViewEquiv st₁ st₂ cid) (h₂₃ : CoroutineViewEquiv st₂ st₃ cid) :
    CoroutineViewEquiv st₁ st₃ cid := Eq.trans h₁₂ h₂₃

/-! ## Topology-Change Noninterference -/

/-- Topology-only failure events are blind to coroutine-local projections. -/
theorem topology_change_preserves_coroutine_view {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (tc : TopologyChange (ι := ι)) (cid : CoroutineId) :
    coroutineView (applyTopologyChange st tc) cid = coroutineView st cid := by
  unfold coroutineView
  cases hco : st.coroutines[cid]? with
  | none =>
      cases tc with
      | crash site =>
          by_cases hmem : site ∈ st.crashedSites <;>
            simp [applyTopologyChange, crashSite, hmem, hco]
      | partition edges =>
          simp [applyTopologyChange, disconnectEdges, hco]
      | heal edges =>
          simp [applyTopologyChange, reconnectEdges, hco]
  | some coro =>
      cases tc with
      | crash site =>
          by_cases hmem : site ∈ st.crashedSites <;>
            simp [applyTopologyChange, crashSite, hmem, hco, coroutineProjection]
      | partition edges =>
          simp [applyTopologyChange, disconnectEdges, hco, coroutineProjection]
      | heal edges =>
          simp [applyTopologyChange, reconnectEdges, hco, coroutineProjection]

/-- Protocol-machine noninterference: topology changes preserve observer equivalence. -/
theorem topology_change_preserves_coroutine_view_equiv {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (tc : TopologyChange (ι := ι)) (cid : CoroutineId) :
    CoroutineViewEquiv (applyTopologyChange st tc) st cid := by
  exact topology_change_preserves_coroutine_view st tc cid

/-! ## Information-Theoretic Protocol-Machine Bridge -/

/-- Joint label/observation distribution induced by protocol-machine observer projection. -/
def coroutineViewJoint (L : Type*) {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    [DecidableEq (Option CoroutineView)]
    (states : L → VMState ι γ π ε ν) (cid : CoroutineId)
    (labelDist : L → ℝ) : L × Option CoroutineView → ℝ :=
  fun lo => if coroutineView (states lo.1) cid = lo.2 then labelDist lo.1 else 0

theorem coroutine_view_mutual_info_zero_of_erasure
    {L : Type} [Fintype L] [Fintype (Option CoroutineView)] [DecidableEq (Option CoroutineView)]
    [EntropyAPI.Laws]
    {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (states : L → VMState ι γ π ε ν) (cid : CoroutineId)
    (labelDist : L → ℝ) (h_nn : ∀ l, 0 ≤ labelDist l) (h_sum : ∑ l, labelDist l = 1) :
    EntropyAPI.IsErasureKernel labelDist (coroutineViewJoint L states cid labelDist) →
    EntropyAPI.mutualInfo (coroutineViewJoint L states cid labelDist) = 0 := by
  intro hErase
  exact EntropyAPI.Laws.mutual_info_zero_of_erasure
    (self := inferInstance) (L := L) (O := Option CoroutineView)
    labelDist h_nn h_sum (coroutineViewJoint L states cid labelDist) hErase
