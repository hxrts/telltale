import Protocol.Environments.Part1
import Runtime.Resources.SessionRA
import Runtime.ProgramLogic.GhostState
import Runtime.VM.State
import Runtime.Compat.Inv
import Runtime.Compat.SavedProp

/-
The Problem. The runtime needs a per-session cancelable invariant that
ties session coherence, buffer typing, progress supply, and knowledge
tracking into a single Iris resource.

Solution Structure. Define the invariant body with local stubs for
coherence/buffer typing, add lifecycle event types, and provide
placeholder correctness statements that match runtime.md §7.
-/

/-!
# Task 16: Session Cancelable Invariants

Per-session cancelable invariant from iris_runtime_2.md §7.

## Definitions

- `sessionNs sid` — namespace per session
- `session_inv γ sid ct` — cancelable invariant body
- `session_ns_disjoint`
- `session_inv_alloc` / `session_inv_open` / `session_inv_close`
- `Participation` — per-endpoint lifecycle token
- `LifecycleEvent` — open, join, leave, close
- `open_coherent`, `leave_preserves_coherent`, `close_empty`

Dependencies: Task 13, Shim.Invariants + Shim.SavedProp.
-/

set_option autoImplicit false
noncomputable section

/-! ## Session coherence stubs -/

def session_coherent (_sid : SessionId) (_G : SessionMap) (_D : DEnv) : iProp :=
  -- Placeholder coherence predicate for per-session environments.
  iProp.emp

def buffers_typed (_sid : SessionId) (_G : SessionMap) (_D : DEnv)
    (_bufs : Buffers) : iProp :=
  -- Placeholder buffer-typing predicate.
  iProp.emp

def head_coherent (_sid : SessionId) (_G : SessionMap) (_D : DEnv) : iProp :=
  -- Placeholder for trace head coherence.
  iProp.emp

def knowledge_inv (_γ : GhostName) (_sid : SessionId) (_e : Endpoint) : iProp :=
  -- Placeholder per-endpoint knowledge invariant.
  iProp.emp

def knowledge_inv_all (_γ : GhostName) (_sid : SessionId) (_G : SessionMap) : iProp :=
  -- Placeholder for a big-separation conjunction of knowledge invariants.
  iProp.emp

/-! ## Cancelable session invariant -/

def session_inv_body (γ : GhostName) (sid : SessionId) : iProp :=
  -- Session invariant body with coherence, buffers, and progress.
  iProp.exist fun G =>
    iProp.exist fun D =>
      iProp.exist fun bufs =>
        iProp.sep (session_coherent sid G D)
          (iProp.sep (buffers_typed sid G D bufs)
            (iProp.sep (session_auth γ G)
              (iProp.sep (head_coherent sid G D)
                (iProp.sep (session_progress_supply γ sid)
                  (knowledge_inv_all γ sid G)))))

def sessionNs (sid : SessionId) : Namespace :=
  -- Namespace for a session invariant.
  Namespace.append_nat Namespace.root sid

def session_inv (_γ : GhostName) (sid : SessionId) (ct : CancelToken) : iProp :=
  -- Session invariant ties coherence, buffers, progress, and knowledge.
  cinv (sessionNs sid) ct (session_inv_body _γ sid)

def session_ns_disjoint (sid₁ sid₂ : SessionId)
    (hNs : sessionNs sid₁ ≠ sessionNs sid₂) :
  Mask.disjoint (namespace_to_mask (sessionNs sid₁)) (namespace_to_mask (sessionNs sid₂)) :=
  -- Namespaces for distinct session ids are disjoint.
  namespace_disjoint (sessionNs sid₁) (sessionNs sid₂) hNs

def session_inv_alloc (γ : GhostName) (sid : SessionId) (E : Mask) :
  iProp.entails (iProp.later (session_inv_body γ sid))
    (fupd E E (iProp.exist fun ct => iProp.sep (session_inv γ sid ct) (cancel_token_own ct))) :=
  -- Allocate a fresh cancelable invariant for a session.
  cinv_alloc (sessionNs sid) E (session_inv_body γ sid)

def session_inv_open (γ : GhostName) (sid : SessionId) (ct : CancelToken) (E : Mask)
    (hSub : Mask.subseteq (namespace_to_mask (sessionNs sid)) E) :
  iProp.entails (session_inv γ sid ct)
    (fupd E (Mask.diff E (namespace_to_mask (sessionNs sid)))
      (iProp.sep (iProp.later (session_inv_body γ sid))
        (iProp.wand (iProp.later (session_inv_body γ sid))
          (fupd (Mask.diff E (namespace_to_mask (sessionNs sid))) E iProp.emp)))) :=
  -- Open the session invariant under mask difference.
  cinv_acc (sessionNs sid) E ct (session_inv_body γ sid) hSub

def session_inv_close (γ : GhostName) (sid : SessionId) (ct : CancelToken) (E : Mask)
    (hSub : Mask.subseteq (namespace_to_mask (sessionNs sid)) E) :
  iProp.entails (iProp.sep (session_inv γ sid ct) (cancel_token_own ct))
    (fupd E (Mask.diff E (namespace_to_mask (sessionNs sid)))
      (iProp.later (session_inv_body γ sid))) :=
  -- Cancel the session invariant with the cancel token.
  cinv_cancel (sessionNs sid) E ct (session_inv_body γ sid) hSub

/-! ## Conservation invariants -/

def conservation_inv (_γ : GhostName) (_sid : SessionId)
    {M : Type} [AddCommMonoid M]
    (_proj : Endpoint → M) (_total : M) : iProp :=
  -- Placeholder conservation invariant over endpoints.
  iProp.emp

def conservation_inv_preserved (_γ : GhostName) (_sid : SessionId)
    {M : Type} [AddCommMonoid M]
    (_proj : Endpoint → M) (_total : M) : Prop :=
  -- Placeholder preservation statement for conservation invariants.
  True

/-! ## Participation and lifecycle events -/

structure Participation (ι : Type) [IdentityModel ι] where
  -- Participation token for a role in a session.
  participant : IdentityModel.ParticipantId ι
  session : SessionId
  role : Role
  endpoint : Endpoint
  site : IdentityModel.SiteId ι

inductive LifecycleEvent (ι : Type) [IdentityModel ι]
    (γ ε : Type) [GuardLayer γ] [EffectModel ε] where
  -- Session creation and membership changes.
  | open (sid : SessionId) (roles : RoleSet)
      (assignment : Role → IdentityModel.ParticipantId ι)
      (siteChoice : IdentityModel.ParticipantId ι → IdentityModel.SiteId ι)
      (types : Role → LocalType)
      (spatialReq : SpatialReq)
      (handlers : List (Edge × HandlerId))
  | join (p : IdentityModel.ParticipantId ι) (sid : SessionId)
      (role : Role) (localType : LocalType)
  | leave (p : IdentityModel.ParticipantId ι) (sid : SessionId) (role : Role)
  | close (sid : SessionId)
  | migrate (sid : SessionId) (role : Role)
      (fromSite toSite : IdentityModel.SiteId ι)
  | epochAdvance (sid : SessionId) (newEpoch : Nat)
  | transfer (sid : SessionId) (endpoint : Endpoint)
      (fromCoro toCoro : Nat) (bundle : ResourceBundle γ ε)

/-! ## Lifecycle correctness stubs -/

def open_coherent {ι : Type} [IdentityModel ι]
    (_roles : RoleSet) (_types : Role → LocalType)
    (_spatialReq : SpatialReq)
    (_assignment : Role → IdentityModel.ParticipantId ι)
    (_siteChoice : IdentityModel.ParticipantId ι → IdentityModel.SiteId ι) : Prop :=
  -- Placeholder coherence statement for session open.
  True

def migrate_preserves_spatial {ι : Type} [IdentityModel ι]
    (_spatialReq : SpatialReq)
    (_assignment : Role → IdentityModel.ParticipantId ι)
    (_siteChoice _siteChoice' : IdentityModel.ParticipantId ι → IdentityModel.SiteId ι) : Prop :=
  -- Placeholder spatial preservation under migration.
  True

def leave_preserves_coherent (_sid : SessionId) (_role : Role) : Prop :=
  -- Placeholder coherence preservation for leave.
  True

def close_empty (_sid : SessionId) : Prop :=
  -- Placeholder: closing implies empty buffers/endpoints.
  True

def close_makes_inaccessible {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_st : VMState ι γ π ε ν) (_sid : SessionId) : Prop :=
  -- Placeholder: closed sessions are inaccessible to instructions.
  True
