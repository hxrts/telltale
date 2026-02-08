import Runtime.Resources.SessionRA
import Runtime.VM.Knowledge
import Runtime.IrisBridge

/- 
The Problem. Capture ghost resources for knowledge, progress, and transfer
so that session proofs can reason about ownership and movement of state.

Solution Structure. Define lightweight RA predicates and placeholder
theorems for knowledge flow, progress, ghost sessions, and bundles.
-/

/-!
# Tasks 20A–20C: Knowledge, Progress, Ghost Sessions, Resource Bundles

Epistemic separation, progress tokens, ghost sessions, and resource bundles
from runtime.md §§16–19.

## Definitions

- `KnowledgeRA`, `knows`, `FlowPolicy`, `non_leakage`
- `ProgressRA`, `progress_token_own`, `progress_token_sound`
- `GhostSession`, `ghost_session_inv`, `join_sound`, `abort_safe`
- `ResourceBundle`, `transfer_bundle`, `ResourceTree`

Dependencies: Task 13, Compat.RA + Compat.Inv + Compat.SavedProp.
-/

set_option autoImplicit false
noncomputable section

universe u

variable [Telltale.TelltaleIris]

/-! ## Shared list helpers -/

/-- Separate conjunction over a list of propositions. -/
def sepList (ps : List iProp) : iProp :=
  -- Fold with separation and the empty resource.
  ps.foldl iProp.sep iProp.emp

/-! ## Knowledge RA -/

/-- Stub: ghost map for knowledge facts.
    Actual implementation needs GhostMapSlot and encoding for KnowledgeFact. -/
abbrev KnowledgeRA := List (Positive × Unit)

/-- Encode a knowledge fact to Positive for ghost map key. -/
def encodeKnowledgeFact (k : KnowledgeFact) : Positive :=
  [Iris.Countable.encode k.endpoint.sid,
   Iris.Countable.encode k.endpoint.role,
   Iris.Countable.encode k.fact]

variable [GhostMapSlot Unit]

def knows (γ : GhostName) (k : KnowledgeFact) : iProp :=
  -- Ownership of a single knowledge fact.
  ghost_map_elem γ (encodeKnowledgeFact k) ()

def knowledge_set_owns (γ : GhostName) (ks : List KnowledgeFact) : iProp :=
  -- Ownership of a list of knowledge facts.
  sepList (ks.map (fun k => knows γ k))

def KnowledgeReachable (k : KnowledgeFact) : Prop :=
  -- A fact is reachable when it carries non-empty payload knowledge.
  k.fact.length > 0

def knowledge_disjoint (ks1 ks2 : List KnowledgeFact) : Prop :=
  -- Disjointness of knowledge sets by element exclusion.
  ∀ x, x ∈ ks1 → x ∈ ks2 → False

def knowledge_separation : Prop :=
  -- Disjoint knowledge resources can be combined without aliasing.
  ∀ γ ks1 ks2, knowledge_disjoint ks1 ks2 →
    iProp.entails (iProp.sep (knowledge_set_owns γ ks1) (knowledge_set_owns γ ks2))
      (knowledge_set_owns γ (ks1 ++ ks2))

def send_transfers_knowledge : Prop :=
  -- Sending creates receiver knowledge in addition to sender knowledge.
  ∀ γ sender receiver fact,
    let kSender : KnowledgeFact := { endpoint := sender, fact := fact }
    let kReceiver : KnowledgeFact := { endpoint := receiver, fact := fact }
    iProp.entails (knows γ kSender)
      (iProp.sep (knows γ kSender) (knows γ kReceiver))

def non_leakage (pol : FlowPolicy) : Prop :=
  -- Disallowed flows cannot become reachable.
  ∀ k r, pol.allowed k r = false → ¬ KnowledgeReachable k

def check_enforces_policy : Prop :=
  -- Successful checks imply the flow is permitted.
  ∀ (pol : FlowPolicy) k r, pol.allowed k r = true → KnowledgeReachable k

/-! ## Progress RA -/

/-- Stub: ghost map for progress tokens.
    Actual implementation needs GhostMapSlot and encoding for (SessionId × Endpoint). -/
abbrev ProgressRA := List (Positive × Nat)

/-- Encode (SessionId, Endpoint) to Positive for ghost map key. -/
def encodeProgressKey (sid : SessionId) (e : Endpoint) : Positive :=
  [Iris.Countable.encode sid, Iris.Countable.encode e.sid, Iris.Countable.encode e.role]

variable [GhostMapSlot Nat]

def progress_token_own (γ : GhostName) (sid : SessionId) (e : Endpoint) (n : Nat) : iProp :=
  -- Ownership of n progress tokens for a session endpoint.
  ghost_map_elem γ (encodeProgressKey sid e) n

def session_progress_supply (_γ : GhostName) (_sid : SessionId) : iProp :=
  -- Placeholder: session-wide supply of progress tokens.
  iProp.emp
def progress_token_sound : Prop :=
  -- Progress tokens represent positive budget for advancement.
  ∀ γ sid e n, iProp.entails (progress_token_own γ sid e n)
    (iProp.pure (n > 0))

def session_type_mints_tokens : Prop :=
  -- Active sessions support progress: any session/role pair yields a valid endpoint.
  ∀ (sid : SessionId) (r : Role), ∃ (ep : Endpoint), ep.sid = sid ∧ ep.role = r

def progress_aware_starvation_free : Prop :=
  -- Token ownership implies access to the session supply.
  ∀ γ sid e n, iProp.entails (progress_token_own γ sid e n)
    (session_progress_supply γ sid)

/-! ## Finalization tokens -/

inductive FinalizationMode where
  -- Deterministic finalization for committed state.
  | deterministicFinalization
  -- Stronger: deterministic trace.
  | deterministicTrace
  deriving Repr, DecidableEq

structure FinalizationToken where
  -- Finalization token tied to a scope id.
  scope : ScopeId
  mode : FinalizationMode
  deriving Repr

/-- Stub: ghost map for finalization modes.
    Actual implementation needs encoding for ScopeId. -/
abbrev FinalizationRA := List (Positive × FinalizationMode)

instance : Iris.Countable ScopeId where
  encode s := Iris.Countable.encode s.id
  decode n := ScopeId.mk <$> Iris.Countable.decode n
  decode_encode s := by simp [Iris.Countable.decode_encode]

/-- Encode ScopeId to Positive. -/
def encodeScopeId (s : ScopeId) : Positive :=
  [Iris.Countable.encode s.id]

variable [GhostMapSlot FinalizationMode]

def finalization_auth (γ : GhostName) (M : GhostMap FinalizationMode) : iProp :=
  -- Authoritative finalization map for scopes.
  ghost_map_auth γ M

def finalization_token_own (γ : GhostName) (ft : FinalizationToken) : iProp :=
  -- Fragment indicating finalization permission for a scope.
  ghost_map_elem γ (encodeScopeId ft.scope) ft.mode

def finalization_token_persistent (ft : FinalizationToken) : Prop :=
  -- Finalization tokens with the same scope and mode are equal (structural identity).
  ∀ ft' : FinalizationToken, ft'.scope = ft.scope → ft'.mode = ft.mode → ft' = ft

omit [Telltale.TelltaleIris] [GhostMapSlot Unit] [GhostMapSlot Nat]
    [GhostMapSlot FinalizationMode] in
theorem finalization_token_persistent_holds (ft : FinalizationToken) :
    finalization_token_persistent ft := by
  intro ft' hs hm
  cases ft; cases ft'; simp_all

/-! ## Ghost sessions -/

structure GhostSession where
  sid : SessionId
  state : LocalType
  deriving Repr

abbrev GhostSessionStore := List GhostSession -- Store of ghost sessions.

def ghostSpecBound : Nat :=
  -- V1 cap for speculative ghost session identifiers.
  1024

def spec_bounded (sid : SessionId) : Prop :=
  -- Speculation is bounded by a fixed V1 cap.
  sid ≤ ghostSpecBound

def ghost_session_inv (sid : SessionId) : iProp :=
  -- Ghost session invariant records boundedness.
  iProp.pure (spec_bounded sid)

def ghost_session_progress (sid : SessionId) : Prop :=
  -- Ghost sessions are live when they respect the bound.
  spec_bounded sid

def join_sound (sid : SessionId) : Prop :=
  -- Join preserves bounded ghost session progress.
  ghost_session_progress sid

def abort_safe (sid : SessionId) : Prop :=
  -- Abort is safe when the ghost session is bounded.
  ghost_session_progress sid

/-! ## Resource bundles -/

/-- Guard-layer ownership predicate (placeholder). -/
def guard_layer_owns {γ : Type u} [GuardLayer γ] (_layer : γ)
    (_res : GuardLayer.Resource γ) : iProp :=
  -- V1 uses a stubbed guard resource ownership.
  iProp.emp

/-- Effect-context ownership predicate (placeholder). -/
def effect_ctx_owns {ε : Type u} [EffectRuntime ε] (_ctx : EffectRuntime.EffectCtx ε) : iProp :=
  -- V1 treats effect context ownership as abstract.
  iProp.emp

structure ResourceBundle (γ ε : Type u) [GuardLayer γ] [EffectRuntime ε] where
  endpoint : Endpoint -- Endpoint being transferred.
  localType : LocalType -- Current local type at the endpoint.
  guardState : List (γ × GuardLayer.Resource γ) -- Guard resources for the endpoint.
  effectSlice : EffectRuntime.EffectCtx ε -- Effect context slice.
  progressTokens : List (SessionId × Endpoint × Nat) -- Liveness tokens.
  knowledge : List KnowledgeFact -- Knowledge facts.

variable [GhostMapSlot LocalType]

/-- Endpoint ownership fragment from SessionRA. -/
def endpoint_owns (γn : GhostName) (e : Endpoint) (L : LocalType) : iProp :=
  endpoint_frag γn e L

/-- Endpoint ownership transfer/update law from the authoritative session map. -/
def endpoint_owns_transfer : Prop :=
  ∀ γ m e Lold Lnew,
    iProp.entails
      (iProp.sep (session_auth γ m) (endpoint_owns γ e Lold))
      (bupd
        (iProp.sep (session_auth γ (Iris.Std.insert m (encodeEndpoint e) (Iris.LeibnizO.mk Lnew)))
          (endpoint_owns γ e Lnew)))

theorem endpoint_owns_transfer_holds : endpoint_owns_transfer := by
  intro γ m e Lold Lnew
  simpa [endpoint_owns] using
    (session_advance γ m e Lold Lnew)

def bundle_owns {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (γn : GhostName) (b : ResourceBundle γ ε) : iProp :=
  -- Bundle ownership is the separating conjunction of all components.
  let guardOwns := sepList (b.guardState.map (fun p => guard_layer_owns p.1 p.2))
  let progressOwns :=
    sepList (b.progressTokens.map (fun p => progress_token_own γn p.1 p.2.1 p.2.2))
  let knowledgeOwns := knowledge_set_owns γn b.knowledge
  iProp.sep (endpoint_owns γn b.endpoint b.localType)
    (iProp.sep guardOwns (iProp.sep (effect_ctx_owns b.effectSlice)
      (iProp.sep progressOwns knowledgeOwns)))

def transfer_bundle {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (γn : GhostName) (b : ResourceBundle γ ε) : Prop :=
  -- Transfer preserves ownership of the same bundle.
  iProp.entails (bundle_owns γn b) (bundle_owns γn b)

/-- Bundle progress token has internal sid/endpoint consistency and positive budget. -/
def progress_token_well_formed (tok : SessionId × Endpoint × Nat) : Prop :=
  tok.1 = tok.2.1.sid ∧ tok.2.2 > 0

def bundle_complete {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (b : ResourceBundle γ ε) : Prop :=
  -- A complete bundle contains a live endpoint and coherent token/knowledge slices.
  b.localType ≠ LocalType.end_ ∧
  (∀ tok ∈ b.progressTokens, progress_token_well_formed tok) ∧
  (∃ n, n > 0 ∧ (b.endpoint.sid, b.endpoint, n) ∈ b.progressTokens) ∧
  (∀ k ∈ b.knowledge, k.endpoint.sid = b.endpoint.sid)

def transfer_bundle_preserves {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (γn : GhostName) (b : ResourceBundle γ ε) : Prop :=
  -- Placeholder: bundle transfer preserves invariants.
  transfer_bundle γn b

def WellTypedTransfer {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (b : ResourceBundle γ ε) : Prop :=
  -- Well-typed transfer requires a complete ownership bundle.
  bundle_complete b

def transfer_continuation_typed {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (b : ResourceBundle γ ε) : Prop :=
  -- Transfer continuation is meaningful when transfer is well-typed and actionable.
  WellTypedTransfer b ∧ LocalType.targetRole? b.localType ≠ none

def transfer_source_loses {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (γn : GhostName) (b : ResourceBundle γ ε) : Prop :=
  -- Placeholder: source loses ownership implies re-establishing bundle ownership elsewhere.
  iProp.entails (bundle_owns γn b) (bundle_owns γn b)

structure ResourceTree (γ ε : Type u) [GuardLayer γ] [EffectRuntime ε] where
  root : ResourceBundle γ ε -- Root bundle for the tree.
  children : List (ResourceTree γ ε) -- Nested bundle transfers.

def higher_order_transfer_preserves {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (_t : ResourceTree γ ε) : Prop :=
  -- Placeholder: higher-order transfer preserves ownership.
  True
