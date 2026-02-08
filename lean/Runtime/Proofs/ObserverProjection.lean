import Runtime.Proofs.VMPotential
import Runtime.Resources.Arena
import Protocol.InformationCost

/-!
# VM Observer/Projection Bridge

VM-level observer projection plus noninterference and information-theoretic
bridge lemmas for coroutine-local views.
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

def vmViewProjectionMap (L : Type*) {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (states : L → VMState ι γ π ε ν) (cid : CoroutineId) :
    InformationCost.ProjectionMap L (Option CoroutineView) :=
  { proj := fun l => coroutineView (states l) cid }

theorem vm_mutualInfo_zero_of_constant_projection
    {L : Type*} [Fintype L] [Fintype (Option CoroutineView)] [DecidableEq (Option CoroutineView)]
    (p : InformationCost.ProjectionMap L (Option CoroutineView))
    (hConst : p.isConstant)
    (labelDist : L → ℝ) (h_nn : ∀ l, 0 ≤ labelDist l) (h_sum : ∑ l, labelDist l = 1) :
    InformationCost.mutualInfo
      (fun lt : L × Option CoroutineView => if p.proj lt.1 = lt.2 then labelDist lt.1 else 0) = 0 := by
  exact InformationCost.mutualInfo_zero_of_constant_projection p hConst labelDist h_nn h_sum

theorem vm_projection_preserves_local_information
    {L : Type*} [Fintype L]
    (p : InformationCost.ProjectionMap L (Option CoroutineView))
    (hConst : p.isConstant)
    (labelDist : L → ℝ) (h_nn : ∀ l, 0 ≤ labelDist l) (h_sum : ∑ l, labelDist l = 1)
    (localInfo : Option CoroutineView → ℝ) :
    ∑ l, labelDist l * localInfo (p.proj l) = localInfo (Classical.choose hConst) := by
  exact InformationCost.projection_preserves_local_information
    p hConst labelDist h_nn h_sum localInfo

def vmBlindObservationCost : ℝ := InformationCost.blindObservationCost

theorem vmBlindObservationCost_eq_zero : vmBlindObservationCost = 0 := by
  simp [vmBlindObservationCost, InformationCost.blindObservationCost_eq_zero]
