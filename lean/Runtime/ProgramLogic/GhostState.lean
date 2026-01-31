import Runtime.Resources.SessionRA
import Runtime.Compat.RA
import Runtime.Compat.Inv
import Runtime.Compat.SavedProp

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

/-! ## Shared list helpers -/

/-- Separate conjunction over a list of propositions. -/
def sepList (ps : List iProp) : iProp :=
  -- Fold with separation and the empty resource.
  ps.foldl iProp.sep iProp.emp

/-! ## Knowledge RA -/

abbrev GhostKnowledgeFact := String -- Atom representing a knowledge fact.
abbrev KnowledgeRA := GMap (Endpoint × GhostKnowledgeFact) Unit -- Ghost map for facts.

def knows (γ : GhostName) (e : Endpoint) (k : GhostKnowledgeFact) : iProp :=
  -- Ownership of a single knowledge fact for an endpoint.
  ghost_map_elem γ (e, k) ()

def knowledge_set_owns (γ : GhostName) (ks : List (Endpoint × GhostKnowledgeFact)) : iProp :=
  -- Ownership of a list of knowledge facts.
  sepList (ks.map (fun p => knows γ p.1 p.2))

structure FlowPolicy where
  -- Flow policy decides if a fact may flow to a role.
  allowed : GhostKnowledgeFact → Role → Bool

def KnowledgeReachable (_k : GhostKnowledgeFact) : Prop :=
  -- Placeholder reachability predicate for knowledge flow.
  True

def knowledge_separation : Prop :=
  -- Placeholder: disjoint knowledge resources do not alias.
  True

def send_transfers_knowledge : Prop :=
  -- Placeholder: send establishes sender-knowledge and receiver-knowledge.
  True

def non_leakage (_pol : FlowPolicy) : Prop :=
  -- Placeholder: no flow chain implies no knowledge gain.
  True

def check_enforces_policy : Prop :=
  -- Placeholder: check enforces the knowledge flow policy.
  True

/-! ## Progress RA -/

abbrev ProgressRA := GMap (SessionId × Endpoint) Nat -- Token counts per endpoint.

def progress_token_own (γ : GhostName) (sid : SessionId) (e : Endpoint) (n : Nat) : iProp :=
  -- Ownership of n progress tokens for a session endpoint.
  ghost_map_elem γ (sid, e) n

def session_progress_supply (_γ : GhostName) (_sid : SessionId) : iProp :=
  -- Placeholder: session-wide supply of progress tokens.
  iProp.emp
def progress_token_sound (_sid : SessionId) : Prop :=
  -- Placeholder: progress token implies eventual advancement.
  True
def progress_aware_starvation_free (_sid : SessionId) : Prop :=
  -- Placeholder: scheduling serves token holders.
  True

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

abbrev FinalizationRA := GMap ScopeId FinalizationMode -- Finalization mode per scope.

def finalization_auth (γ : GhostName) (M : FinalizationRA) : iProp :=
  -- Authoritative finalization map for scopes.
  ghost_map_auth γ M

def finalization_token_own (γ : GhostName) (ft : FinalizationToken) : iProp :=
  -- Fragment indicating finalization permission for a scope.
  ghost_map_elem γ ft.scope ft.mode

def finalization_token_persistent (_ft : FinalizationToken) : Prop :=
  -- Placeholder: finalization tokens are persistent/duplicable.
  True

/-! ## Ghost sessions -/

structure GhostSession where
  sid : SessionId
  state : LocalType
  deriving Repr

abbrev GhostSessionStore := List GhostSession -- Store of ghost sessions.

def ghost_session_inv (_sid : SessionId) : iProp :=
  -- Placeholder: invariant for a ghost session.
  iProp.emp

def ghost_session_progress (_sid : SessionId) : Prop :=
  -- Placeholder: ghost session liveness.
  True
def join_sound (_sid : SessionId) : Prop :=
  -- Placeholder: join preserves correctness.
  True
def abort_safe (_sid : SessionId) : Prop :=
  -- Placeholder: abort restores pre-speculation state.
  True
def spec_bounded (_sid : SessionId) : Prop :=
  -- Placeholder: speculation depth is bounded.
  True

/-! ## Resource bundles -/

/-- Guard-layer ownership predicate (placeholder). -/
def guard_layer_owns {γ : Type u} [GuardLayer γ] (_layer : γ)
    (_res : GuardLayer.Resource γ) : iProp :=
  -- V1 uses a stubbed guard resource ownership.
  iProp.emp

/-- Effect-context ownership predicate (placeholder). -/
def effect_ctx_owns {ε : Type u} [EffectModel ε] (_ctx : EffectModel.EffectCtx ε) : iProp :=
  -- V1 treats effect context ownership as opaque.
  iProp.emp

structure ResourceBundle (γ ε : Type u) [GuardLayer γ] [EffectModel ε] where
  endpoint : Endpoint -- Endpoint being transferred.
  localType : LocalType -- Current local type at the endpoint.
  guardState : List (γ × GuardLayer.Resource γ) -- Guard resources for the endpoint.
  effectSlice : EffectModel.EffectCtx ε -- Effect context slice.
  progressTokens : List (SessionId × Endpoint × Nat) -- Liveness tokens.
  knowledge : List (Endpoint × GhostKnowledgeFact) -- Knowledge facts.

def bundle_owns {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (γn : GhostName) (b : ResourceBundle γ ε) : iProp :=
  -- Bundle ownership is the separating conjunction of all components.
  let guardOwns := sepList (b.guardState.map (fun p => guard_layer_owns p.1 p.2))
  let progressOwns :=
    sepList (b.progressTokens.map (fun p => progress_token_own γn p.1 p.2.1 p.2.2))
  let knowledgeOwns := knowledge_set_owns γn b.knowledge
  iProp.sep (endpoint_frag γn b.endpoint b.localType)
    (iProp.sep guardOwns (iProp.sep (effect_ctx_owns b.effectSlice)
      (iProp.sep progressOwns knowledgeOwns)))

def transfer_bundle {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (γn : GhostName) (b : ResourceBundle γ ε) : Prop :=
  -- Transfer preserves ownership of the same bundle.
  iProp.entails (bundle_owns γn b) (bundle_owns γn b)

def bundle_complete {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (_b : ResourceBundle γ ε) : Prop :=
  -- Placeholder: bundle contains all required transfer resources.
  True

def transfer_bundle_preserves {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (γn : GhostName) (b : ResourceBundle γ ε) : Prop :=
  -- Placeholder: bundle transfer preserves invariants.
  transfer_bundle γn b

def WellTypedTransfer {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (b : ResourceBundle γ ε) : Prop :=
  -- Placeholder: non-empty endpoint transfer check.
  b.localType ≠ LocalType.end_

def transfer_continuation_typed {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (b : ResourceBundle γ ε) : Prop :=
  -- Placeholder: continuation exists if transfer is well-typed.
  WellTypedTransfer b

def transfer_source_loses {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (γn : GhostName) (b : ResourceBundle γ ε) : Prop :=
  -- Placeholder: source loses ownership implies re-establishing bundle ownership elsewhere.
  iProp.entails (bundle_owns γn b) (bundle_owns γn b)

structure ResourceTree (γ ε : Type u) [GuardLayer γ] [EffectModel ε] where
  root : ResourceBundle γ ε -- Root bundle for the tree.
  children : List (ResourceTree γ ε) -- Nested bundle transfers.

def higher_order_transfer_preserves {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (_t : ResourceTree γ ε) : Prop :=
  -- Placeholder: higher-order transfer preserves ownership.
  True
