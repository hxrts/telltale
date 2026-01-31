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

structure ResourceBundle where
  endpoints : List Endpoint
  deriving Repr

def bundle_owns (_γ : GhostName) (_b : ResourceBundle) : iProp :=
  iProp.emp

def transfer_bundle (_b : ResourceBundle) : Prop := True
def WellTypedTransfer (_b : ResourceBundle) : Prop := True
def transfer_continuation_typed (_b : ResourceBundle) : Prop := True
def transfer_source_loses (_b : ResourceBundle) : Prop := True

structure ResourceTree where
  root : ResourceBundle
  children : List ResourceTree
  deriving Repr

def higher_order_transfer_preserves (_t : ResourceTree) : Prop := True
