import Runtime.Resources.SessionRA
import Runtime.Compat.RA
import Runtime.Compat.Inv
import Runtime.Compat.SavedProp

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

/-! ## Knowledge RA -/

abbrev GhostKnowledgeFact := String
abbrev KnowledgeRA := GMap (Endpoint × GhostKnowledgeFact) Unit

def knows (γ : GhostName) (e : Endpoint) (k : GhostKnowledgeFact) : iProp :=
  ghost_map_elem γ (e, k) ()

structure FlowPolicy where
  allowed : GhostKnowledgeFact → Role → Bool

def KnowledgeReachable (_k : GhostKnowledgeFact) : Prop :=
  True

def non_leakage (_pol : FlowPolicy) : Prop := True

/-! ## Progress RA -/

abbrev ProgressRA := GMap (SessionId × Endpoint) Nat

def progress_token_own (γ : GhostName) (sid : SessionId) (e : Endpoint) (n : Nat) : iProp :=
  ghost_map_elem γ (sid, e) n

def session_progress_supply (_γ : GhostName) (_sid : SessionId) : iProp :=
  iProp.emp
def progress_token_sound (_sid : SessionId) : Prop := True
def progress_aware_starvation_free (_sid : SessionId) : Prop := True

/-! ## Ghost sessions -/

structure GhostSession where
  sid : SessionId
  state : LocalType
  deriving Repr

abbrev GhostSessionStore := List GhostSession

def ghost_session_inv (_sid : SessionId) : iProp :=
  iProp.emp

def ghost_session_progress (_sid : SessionId) : Prop := True
def join_sound (_sid : SessionId) : Prop := True
def abort_safe (_sid : SessionId) : Prop := True
def spec_bounded (_sid : SessionId) : Prop := True

/-! ## Resource bundles -/

/-- Separate conjunction over a list of propositions. -/
def sepList (ps : List iProp) : iProp :=
  -- Fold with separation and the empty resource.
  ps.foldl iProp.sep iProp.emp

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
  let knowledgeOwns := sepList (b.knowledge.map (fun p => knows γn p.1 p.2))
  iProp.sep (endpoint_frag γn b.endpoint b.localType)
    (iProp.sep guardOwns (iProp.sep (effect_ctx_owns b.effectSlice)
      (iProp.sep progressOwns knowledgeOwns)))

def transfer_bundle {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (γn : GhostName) (b : ResourceBundle γ ε) : Prop :=
  -- Transfer preserves ownership of the same bundle.
  iProp.entails (bundle_owns γn b) (bundle_owns γn b)

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
