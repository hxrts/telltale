import Runtime.Proofs.VMPotential
import Runtime.Resources.Arena
import ClassicalAnalysisAPI

/-! # VM Observer/Projection Bridge

VM-level observer projection plus noninterference and information-theoretic
bridge lemmas for coroutine-local views. -/

/-
The Problem. Individual coroutines should only observe session state relevant to
their owned endpoints, enabling noninterference arguments and information-theoretic
bounds on what each participant can learn.

Solution Structure. Defines `CoroutineView` as the projection of VM state visible
to a single coroutine: local types, incoming traces, incoming buffers, progress
tokens, and knowledge set. Provides `coroutineProjection` and `coroutineView`
functions with noninterference lemmas showing unrelated operations don't affect
views.
-/

set_option autoImplicit false

section

universe u

/-- Coroutine-local observable projection from VM state. -/
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

/-- Public observer view of a coroutine id in VM state. -/
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

theorem coroutineView_eq_projection {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (cid : CoroutineId) :
    coroutineView st cid = coroutineProjectionAt st cid := by
  cases hco : st.coroutines[cid]? <;> simp [coroutineView, coroutineProjectionAt, hco]

/-- VM observational equivalence for one coroutine id. -/
def VMCEquiv {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st₁ st₂ : VMState ι γ π ε ν) (cid : CoroutineId) : Prop :=
  coroutineView st₁ cid = coroutineView st₂ cid

theorem vmCEquiv_refl {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (cid : CoroutineId) :
    VMCEquiv st st cid := rfl

theorem vmCEquiv_symm {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    {st₁ st₂ : VMState ι γ π ε ν} {cid : CoroutineId}
    (h : VMCEquiv st₁ st₂ cid) :
    VMCEquiv st₂ st₁ cid := Eq.symm h

theorem vmCEquiv_trans {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    {st₁ st₂ st₃ : VMState ι γ π ε ν} {cid : CoroutineId}
    (h₁₂ : VMCEquiv st₁ st₂ cid) (h₂₃ : VMCEquiv st₂ st₃ cid) :
    VMCEquiv st₁ st₃ cid := Eq.trans h₁₂ h₂₃

/-- Topology-only failure events are blind to coroutine-local projections. -/
theorem topology_change_preserves_coroutineView {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
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

/-- VM-level noninterference: topology changes preserve observer equivalence. -/
theorem topology_change_preserves_VMCEquiv {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (tc : TopologyChange (ι := ι)) (cid : CoroutineId) :
    VMCEquiv (applyTopologyChange st tc) st cid := by
  exact topology_change_preserves_coroutineView st tc cid

/-! ## Information-Theoretic VM Bridge -/

/-- Joint label/observation distribution induced by VM observer projection. -/
def vmViewJoint (L : Type*) {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    [DecidableEq (Option CoroutineView)]
    (states : L → VMState ι γ π ε ν) (cid : CoroutineId)
    (labelDist : L → ℝ) : L × Option CoroutineView → ℝ :=
  fun lo => if coroutineView (states lo.1) cid = lo.2 then labelDist lo.1 else 0

theorem vm_mutualInfo_zero_of_erasure
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
    EntropyAPI.IsErasureKernel labelDist (vmViewJoint L states cid labelDist) →
    EntropyAPI.mutualInfo (vmViewJoint L states cid labelDist) = 0 := by
  intro hErase
  exact EntropyAPI.Laws.mutualInfo_zero_of_erasure
    (self := inferInstance) (L := L) (O := Option CoroutineView)
    labelDist h_nn h_sum (vmViewJoint L states cid labelDist) hErase
