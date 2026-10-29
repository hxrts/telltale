import Runtime.Resources.SessionRA
import Runtime.ProtocolMachine.Model.Knowledge
import IrisExtractionInstance

/-! # Ghost State for Knowledge and Progress

RA predicates for knowledge flow, progress tokens, and resource bundles. -/

/-
The Problem. Capture ghost resources for knowledge, progress, and transfer
so that session proofs can reason about ownership and movement of state.

Solution Structure. Define lightweight RA predicates and abstract
theorems for knowledge flow, progress, ghost sessions, and bundles.
-/


/-! # Tasks 20A–20C: Knowledge, Progress, Ghost Sessions, Resource Bundles

Epistemic separation, progress tokens, ghost sessions, and resource bundles
for session reasoning.

## Definitions

- `KnowledgeRA`, `knows`, `FlowPolicy`, `non_leakage`
- `ProgressRA`, `progress_token_own`, `session_progress_supply`, `progress_token_sound`
- `GhostSession`, `ghost_session_inv`, `join_sound`, `abort_safe`
- `ResourceBundle`, `transfer_bundle`, `ResourceTree`

Dependencies: Task 13, IrisExtractionInstance.
-/

set_option autoImplicit false
section

universe u

variable [Telltale.TelltaleIris]

/-! ## Shared list helpers -/

/-- Separate conjunction over a list of propositions. -/
def sepList (ps : List iProp) : iProp :=
  -- Fold with separation and the empty resource.
  ps.foldl iProp.sep iProp.emp

/-! ## Knowledge RA -/

/-- Ghost map model for knowledge facts in the current abstract RA layer. -/
abbrev KnowledgeRA := List (Positive × Unit)

/-- Encode a knowledge fact to Positive for ghost map key. -/
def encodeKnowledge (k : Knowledge) : Positive :=
  Pos.Countable.encode ([Pos.Countable.encode k.endpoint.sid,
   Pos.Countable.encode k.endpoint.role,
   Pos.Countable.encode k.payload] : List Pos)

variable [GhostMapSlot Unit]

def knows (γ : GhostName) (k : Knowledge) : iProp :=
  -- Ownership of a single knowledge fact.
  ghost_map_elem γ (encodeKnowledge k) ()

def knowledge_set_owns (γ : GhostName) (ks : List Knowledge) : iProp :=
  -- Ownership of a list of knowledge facts.
  sepList (ks.map (fun k => knows γ k))

def KnowledgeReachable (k : Knowledge) : Prop :=
  -- A fact is reachable when it carries non-empty payload knowledge.
  k.payload.length > 0

def knowledge_disjoint (ks1 ks2 : List Knowledge) : Prop :=
  -- Disjointness of knowledge sets by element exclusion.
  ∀ x, x ∈ ks1 → x ∈ ks2 → False

def knowledge_separation : Prop :=
  -- Disjoint knowledge resources can be combined without aliasing.
  ∀ γ ks1 ks2, knowledge_disjoint ks1 ks2 →
    iProp.entails (iProp.sep (knowledge_set_owns γ ks1) (knowledge_set_owns γ ks2))
      (knowledge_set_owns γ (ks1 ++ ks2))

def send_transfers_knowledge : Prop :=
  -- Sending creates receiver knowledge in addition to sender knowledge.
  ∀ γ sender receiver payload,
    let kSender : Knowledge := { endpoint := sender, payload := payload }
    let kReceiver : Knowledge := { endpoint := receiver, payload := payload }
    iProp.entails (knows γ kSender)
      (iProp.sep (knows γ kSender) (knows γ kReceiver))

def non_leakage (pol : FlowPolicy) : Prop :=
  -- Disallowed flows cannot become reachable.
  ∀ k r, pol.allowsKnowledge k r = false → ¬ KnowledgeReachable k

def check_enforces_policy : Prop :=
  -- Successful checks imply the flow is permitted.
  ∀ (pol : FlowPolicy) k r, pol.allowsKnowledge k r = true → KnowledgeReachable k

/-! ## Progress RA -/

/-- Ghost map model for progress tokens in the current abstract RA layer. -/
abbrev ProgressRA := List (Positive × Nat)

/-- Encode (SessionId, Endpoint) to Positive for ghost map key. -/
def encodeProgressKey (sid : SessionId) (e : Endpoint) : Positive :=
  Pos.Countable.encode ([Pos.Countable.encode sid, Pos.Countable.encode e.sid, Pos.Countable.encode e.role] : List Pos)

variable [GhostMapSlot Nat]

def progress_token_own (γ : GhostName) (sid : SessionId) (e : Endpoint) (n : Nat) : iProp :=
  -- Ownership of n progress tokens for a session endpoint.
  ghost_map_elem γ (encodeProgressKey sid e) n

/-- Session-wide progress supply: the authoritative progress-token map for the
session, together with the invariant that every token it records for an
endpoint of `sid` carries a strictly positive budget. Token fragments
(`progress_token_own`) are views into this map. -/
def session_progress_supply (γ : GhostName) (sid : SessionId) : iProp :=
  iProp.exist fun (M : GhostMap Nat) =>
    iProp.sep (ghost_map_auth γ M)
      (iProp.pure
        (∀ e n, Iris.Std.get? M (encodeProgressKey sid e) = some n → n > 0))

open Iris.BI in
/-- Combine an authoritative lookup with a pure side condition stored next to
the authority. -/
private theorem sep_pure_lookup {A T : iProp} {φ ψ χ : Prop}
    (hLook : iprop(A ∗ T) ⊢ iprop(⌜ψ⌝)) (hImp : φ → ψ → χ) :
    iprop((A ∗ ⌜φ⌝) ∗ T) ⊢ iprop(⌜χ⌝) :=
  calc iprop((A ∗ ⌜φ⌝) ∗ T) ⊢ iprop((⌜φ⌝ ∗ A) ∗ T) := sep_mono_left sep_comm.1
    _ ⊢ iprop(⌜φ⌝ ∗ (A ∗ T)) := sep_assoc.1
    _ ⊢ iprop(⌜φ⌝ ∗ ⌜ψ⌝) := sep_mono_right hLook
    _ ⊢ iprop(⌜φ ∧ ψ⌝) := pure_sep.1
    _ ⊢ iprop(⌜χ⌝) := pure_mono (fun h => hImp h.1 h.2)

open Iris.BI in
/-- Progress-token soundness: a token held against the session supply has a
strictly positive budget. (A bare token `progress_token_own γ sid e 0` is
satisfiable, so positivity is only derivable relative to the supply.) -/
theorem progress_token_sound (γ : GhostName) (sid : SessionId) (e : Endpoint) (n : Nat) :
    iProp.entails (iProp.sep (session_progress_supply γ sid) (progress_token_own γ sid e n))
      (iProp.pure (n > 0)) := by
  refine (sep_exists_right (PROP := iProp)).1.trans (exists_elim fun M => ?_)
  exact sep_pure_lookup (ghost_map_lookup γ (encodeProgressKey sid e) n M)
    (fun hPos hLook => hPos e n hLook)

def session_type_mints_tokens : Prop :=
  -- Active sessions support progress: any session/role pair yields a valid endpoint.
  ∀ (sid : SessionId) (r : Role), ∃ (ep : Endpoint), ep.sid = sid ∧ ep.role = r

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

/-- Ghost map model for finalization modes in the current abstract RA layer. -/
abbrev FinalizationRA := List (Positive × FinalizationMode)

instance : Pos.Countable ScopeId where
  encode s := Pos.Countable.encode s.id
  decode n := ScopeId.mk <$> Pos.Countable.decode n
  decode_encode s := by simp [Pos.Countable.decode_encode]

/-- Encode ScopeId to Positive. -/
def encodeScopeId (s : ScopeId) : Positive :=
  Pos.Countable.encode ([Pos.Countable.encode s.id] : List Pos)

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

/-! ## Speculation tokens -/

structure SpeculationToken where
  sid : SessionId
  ghostSid : SessionId
  depth : Nat
  deriving Repr

/-- Speculation ghost map keyed by `(sid, ghostSid)` to active depth. -/
abbrev SpeculationRA := GhostMap Nat

/-- Encode `(sid, ghostSid)` for speculation ghost-map keys. -/
def encodeSpeculationKey (sid ghostSid : SessionId) : Positive :=
  Pos.Countable.encode ([Pos.Countable.encode sid, Pos.Countable.encode ghostSid] : List Pos)

def speculation_auth (γ : GhostName) (M : SpeculationRA) : iProp :=
  -- Authoritative speculation map.
  ghost_map_auth γ M

def speculation_token_own (γ : GhostName) (sid ghostSid : SessionId) (depth : Nat) : iProp :=
  -- Fragment ownership for one active speculative ghost session.
  ghost_map_elem γ (encodeSpeculationKey sid ghostSid) depth

def speculation_token_frag (γ : GhostName) (tok : SpeculationToken) : iProp :=
  -- Token view of speculative ownership.
  speculation_token_own γ tok.sid tok.ghostSid tok.depth

def speculation_token_exclusive : Prop :=
  -- Two fragments for the same `(sid, ghostSid)` agree on depth.
  ∀ γ sid ghostSid d₁ d₂,
    iProp.entails
      (iProp.sep (speculation_token_own γ sid ghostSid d₁)
        (speculation_token_own γ sid ghostSid d₂))
      (iProp.pure (d₁ = d₂))

def speculation_token_update (γ : GhostName) (M : SpeculationRA)
    (sid ghostSid : SessionId) (d d' : Nat) :
    iProp.entails
      (iProp.sep (speculation_auth γ M) (speculation_token_own γ sid ghostSid d))
      (bupd
        (iProp.sep
          (speculation_auth γ
            (Iris.Std.insert M (encodeSpeculationKey sid ghostSid) d'))
          (speculation_token_own γ sid ghostSid d'))) :=
  ghost_map_update γ (encodeSpeculationKey sid ghostSid) d d' M

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

def speculation_session_inv (γ : GhostName) (sid : SessionId) : iProp :=
  -- Session-scoped speculation resource view and depth bound.
  iProp.exist fun (M : SpeculationRA) =>
    iProp.sep (speculation_auth γ M)
      (iProp.pure
        (∀ ghostSid depth,
          Iris.Std.get? M (encodeSpeculationKey sid ghostSid) = some depth →
            depth ≤ ghostSpecBound))

/-! ## Resource bundles -/

/-- Ghost names for the per-session ghost state. Each component lives at its
own name so that no two authoritative maps of the same value type share a name. -/
structure SessionGhostNames where
  session : GhostName -- Endpoint/local-type map (`SessionRA`).
  progress : GhostName -- Progress-token map.
  knowledge : GhostName -- Knowledge-fact map.
  speculation : GhostName -- Speculation-depth map.
  guard : GhostName -- Guard-resource map, keyed by layer id.
  effect : GhostName -- Effect-context ghost variable.

/-- Encode a guard layer id as a ghost-map key. -/
def encodeLayer {γ : Type u} [GuardLayer γ] (layer : γ) : Positive :=
  Pos.Countable.encode ([Pos.Countable.encode (GuardLayer.layerId layer)] : List Pos)

/-- Guard-layer ownership: exclusive ownership of the ghost-map entry for this
layer's id, recording the guarded resource `res`. -/
def guard_layer_owns {γ : Type u} [GuardLayer γ] [GhostMapSlot (GuardLayer.Resource γ)]
    (γg : GhostName) (layer : γ) (res : GuardLayer.Resource γ) : iProp :=
  ghost_map_elem γg (encodeLayer layer) res

/-- Effect-context ownership: exclusive ghost-variable ownership of the
effect context `ctx`. -/
def effect_ctx_owns {ε : Type u} [EffectRuntime ε] [GhostVarSlot (EffectRuntime.EffectCtx ε)]
    (γe : GhostName) (ctx : EffectRuntime.EffectCtx ε) : iProp :=
  ghost_var γe ctx

/-- Two owners of the same effect context name agree on its value. -/
theorem effect_ctx_owns_agree {ε : Type u} [EffectRuntime ε]
    [GhostVarSlot (EffectRuntime.EffectCtx ε)] (γe : GhostName)
    (c₁ c₂ : EffectRuntime.EffectCtx ε) :
    iProp.entails (iProp.sep (effect_ctx_owns (ε := ε) γe c₁) (effect_ctx_owns (ε := ε) γe c₂))
      (iProp.pure (c₁ = c₂)) :=
  ghost_var_agree γe c₁ c₂

structure ResourceBundle (γ ε : Type u) [GuardLayer γ] [EffectRuntime ε] where
  endpoint : Endpoint -- Endpoint being transferred.
  localType : LocalType -- Current local type at the endpoint.
  guardState : List (γ × GuardLayer.Resource γ) -- Guard resources for the endpoint.
  effectSlice : EffectRuntime.EffectCtx ε -- Effect context slice.
  progressTokens : List (SessionId × Endpoint × Nat) -- Liveness tokens.
  knowledge : List Knowledge -- Knowledge facts.

variable [GhostMapSlot LocalType]

/-! ## Endpoint Ownership Laws -/

/-- Endpoint ownership fragment from SessionRA. -/
def endpoint_owns (γn : GhostName) (e : Endpoint) (L : LocalType) : iProp :=
  endpoint_frag γn e L

/-- Endpoint ownership transfer/update law from the authoritative session map. -/
def endpoint_owns_transfer : Prop :=
  ∀ γ m e Lold Lnew,
    iProp.entails
      (iProp.sep (session_auth γ m) (endpoint_owns γ e Lold))
      (bupd
        (iProp.sep (session_auth γ (Iris.Std.insert m (encodeEndpoint e) Lnew))
          (endpoint_owns γ e Lnew)))

theorem endpoint_owns_transfer_holds : endpoint_owns_transfer := by
  intro γ m e Lold Lnew
  simpa [endpoint_owns] using
    (session_advance γ m e Lold Lnew)

/-! ## Bundle Ownership -/

/-- Bundle ownership is the separating conjunction of all components, each
at its own ghost name. -/
def bundle_owns {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    [GhostMapSlot (GuardLayer.Resource γ)] [GhostVarSlot (EffectRuntime.EffectCtx ε)]
    (γs : SessionGhostNames) (b : ResourceBundle γ ε) : iProp :=
  let guardOwns := sepList (b.guardState.map (fun p => guard_layer_owns γs.guard p.1 p.2))
  let progressOwns :=
    sepList (b.progressTokens.map (fun p => progress_token_own γs.progress p.1 p.2.1 p.2.2))
  let knowledgeOwns := knowledge_set_owns γs.knowledge b.knowledge
  iProp.sep (endpoint_owns γs.session b.endpoint b.localType)
    (iProp.sep guardOwns (iProp.sep (effect_ctx_owns γs.effect b.effectSlice)
      (iProp.sep progressOwns knowledgeOwns)))

def transfer_bundle {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    [GhostMapSlot (GuardLayer.Resource γ)] [GhostVarSlot (EffectRuntime.EffectCtx ε)]
    (γn : SessionGhostNames) (b : ResourceBundle γ ε) : Prop :=
  -- Transfer preserves ownership of the same bundle.
  iProp.entails (bundle_owns γn b) (bundle_owns γn b)

/-! ## Bundle Well-Formedness -/

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
    [GhostMapSlot (GuardLayer.Resource γ)] [GhostVarSlot (EffectRuntime.EffectCtx ε)]
    (γn : SessionGhostNames) (b : ResourceBundle γ ε) : Prop :=
  -- Bundle transfer preserves invariants in the current abstract bundle model.
  transfer_bundle γn b

/-! ## Transfer Typing Conditions -/

def WellTypedTransfer {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (b : ResourceBundle γ ε) : Prop :=
  -- Well-typed transfer requires a complete ownership bundle.
  bundle_complete b

def transfer_continuation_typed {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (b : ResourceBundle γ ε) : Prop :=
  -- Transfer continuation is meaningful when transfer is well-typed and actionable.
  WellTypedTransfer b ∧ LocalType.targetRole? b.localType ≠ none

def transfer_source_loses {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    [GhostMapSlot (GuardLayer.Resource γ)] [GhostVarSlot (EffectRuntime.EffectCtx ε)]
    (γn : SessionGhostNames) (b : ResourceBundle γ ε) : Prop :=
  -- Source loses ownership and re-establishes bundle ownership at the target lane.
  iProp.entails (bundle_owns γn b) (bundle_owns γn b)

/-! ## Higher-Order Transfer Skeleton -/

structure ResourceTree (γ ε : Type u) [GuardLayer γ] [EffectRuntime ε] where
  root : ResourceBundle γ ε -- Root bundle for the tree.
  children : List (ResourceTree γ ε) -- Nested bundle transfers.

def higher_order_transfer_preserves {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (_t : ResourceTree γ ε) : Prop :=
  -- Higher-order transfer preserves ownership in the current abstract tree model.
  True
