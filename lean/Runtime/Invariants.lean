import Protocol.Environments.Core
import Protocol.Coherence.Consume
import Runtime.Resources.SessionRA
import Runtime.ProgramLogic.GhostState
import Runtime.ProtocolMachine.Model.State
import IrisExtractionInstance

/-! # Session Cancelable Invariants

Per-session cancelable invariant tying coherence, buffer typing, and progress. -/

/-
The Problem. The runtime needs a per-session cancelable invariant that
ties session coherence, buffer typing, progress supply, and knowledge
tracking into a single Iris resource.

Solution Structure. Define the invariant body with local schematic layers for
coherence/buffer typing, add lifecycle event types, and provide
scaffold statements for cancelable invariants without over-claiming completeness.
-/


/-! # Task 16: Session Cancelable Invariants

Per-session cancelable invariant for session coherence and buffer typing.

## Definitions

- `sessionNs sid` — namespace per session
- `session_inv γs sid ct` — cancelable invariant body
- `session_ns_disjoint`
- `session_inv_alloc` / `session_inv_open` / `session_inv_close`
- `Participation` — per-endpoint lifecycle token
- `LifecycleEvent` — open, join, leave, close
- `open_coherent`, `leave_preserves_coherent`, `close_empty`

Dependencies: Task 13, IrisExtractionInstance.
-/

set_option autoImplicit false
section

variable [Telltale.TelltaleIris]
variable [GhostMapSlot Unit]
variable [GhostMapSlot Nat]
variable [GhostMapSlot LocalType]

/-! ## Session coherence definitions -/

def session_coherent (sid : SessionId) (G : SessionMap) (D : DEnv) : iProp :=
  -- Coherence: every endpoint can consume its own pending trace.
  iProp.pure
    (∀ e L, GMap.lookup G e = some L →
      Consume e.role L (lookupD D { sid := sid, sender := e.role, receiver := e.role }) ≠ none)

def buffers_typed (_sid : SessionId) (G : SessionMap) (_D : DEnv)
    (bufs : Buffers) : iProp :=
  -- Buffer values correspond to known receiver endpoints.
  iProp.pure
    (∀ edge v, v ∈ lookupBuf bufs edge →
      ∃ L, GMap.lookup G { sid := edge.sid, role := edge.receiver } = some L)

def head_coherent (sid : SessionId) (G : SessionMap) (D : DEnv) : iProp :=
  -- Head coherence matches the full consume condition in V1.
  session_coherent sid G D

def knowledge_fact (sid : SessionId) (e : Endpoint) : Knowledge :=
  -- Stable per-endpoint fact tag for knowledge ownership.
  { endpoint := e, payload := toString sid ++ ":" ++ e.role }

def knowledge_inv (γ : GhostName) (sid : SessionId) (e : Endpoint) : iProp :=
  -- Endpoint-specific knowledge invariant.
  knows γ (knowledge_fact sid e)

/-- Knowledge invariant over the whole session map: the authoritative
knowledge map registers the per-endpoint fact of every endpoint in `G`, so
any `knowledge_inv` fragment is backed by a live session endpoint. -/
def knowledge_inv_all (γ : GhostName) (sid : SessionId) (G : SessionMap) : iProp :=
  iProp.exist fun (K : GhostMap Unit) =>
    iProp.sep (ghost_map_auth γ K)
      (iProp.pure
        (∀ e L, GMap.lookup G e = some L →
          Iris.Std.get? K (encodeKnowledge (knowledge_fact sid e)) = some ()))

/-! ## Cancelable session invariant -/

/-- Session invariant body: coherence, buffer typing, the authoritative session
map, the progress-token supply, speculation bounds, and knowledge registration,
each at its own ghost name. -/
def session_inv_body (γs : SessionGhostNames) (sid : SessionId) : iProp :=
  iProp.exist fun G =>
    iProp.exist fun D =>
      iProp.exist fun bufs =>
        iProp.sep (session_coherent sid G D)
          (iProp.sep (buffers_typed sid G D bufs)
            (iProp.sep (session_auth γs.session G)
              (iProp.sep (head_coherent sid G D)
                (iProp.sep (session_progress_supply γs.progress sid)
                  (iProp.sep (speculation_session_inv γs.speculation sid)
                    (knowledge_inv_all γs.knowledge sid G))))))

def sessionNs (sid : SessionId) : Namespace :=
  -- Namespace for a session invariant.
  Namespace.append_nat Namespace.root sid

def session_inv (γs : SessionGhostNames) (sid : SessionId) (ct : CancelToken) : iProp :=
  -- Session invariant ties coherence, buffers, progress, and knowledge.
  cinv (sessionNs sid) ct (session_inv_body γs sid)

theorem session_ns_disjoint (sid₁ sid₂ : SessionId)
    (hNs : sessionNs sid₁ ≠ sessionNs sid₂) :
  Mask.disjoint (namespace_to_mask (sessionNs sid₁)) (namespace_to_mask (sessionNs sid₂)) :=
  -- Namespaces for distinct session ids are disjoint.
  by
    have hSid : sid₁ ≠ sid₂ := by
      intro hEq
      apply hNs
      simp [sessionNs, hEq]
    simpa [sessionNs] using namespace_disjoint Namespace.root sid₁ sid₂ hSid

theorem session_inv_alloc (γ : SessionGhostNames) (sid : SessionId) (E : Mask) :
  iProp.entails (iProp.later (session_inv_body γ sid))
    (fupd E E (iProp.exist fun ct => iProp.sep (session_inv γ sid ct) (cancel_token_own ct))) :=
  -- Allocate a fresh cancelable invariant for a session.
  cinv_alloc (sessionNs sid) E (session_inv_body γ sid)

theorem session_inv_open (γ : SessionGhostNames) (sid : SessionId) (ct : CancelToken) (E : Mask)
    (hSub : Mask.subseteq (namespace_to_mask (sessionNs sid)) E) :
  iProp.entails (iProp.sep (session_inv γ sid ct) (cancel_token_own ct))
    (fupd E (Mask.diff E (namespace_to_mask (sessionNs sid)))
      (iProp.sep (iProp.later (session_inv_body γ sid))
        (iProp.sep (cancel_token_own ct)
          (iProp.wand (iProp.later (session_inv_body γ sid))
            (fupd (Mask.diff E (namespace_to_mask (sessionNs sid))) E (iProp.pure True)))))) :=
  -- Open the session invariant under mask difference.
  cinv_acc (sessionNs sid) E ct (session_inv_body γ sid) hSub

/-- Close (cancel) the session invariant: consuming the full cancel token
permanently gives up the invariant and returns its body `▷ session_inv_body`
to the caller. Unlike `session_inv_open`, no closing obligation remains. -/
theorem session_inv_close (γ : SessionGhostNames) (sid : SessionId) (ct : CancelToken)
    (E : Mask) (hSub : Mask.subseteq (namespace_to_mask (sessionNs sid)) E) :
    iProp.entails (iProp.sep (session_inv γ sid ct) (cancel_token_own ct))
      (fupd E E (iProp.later (session_inv_body γ sid))) :=
  cinv_cancel (sessionNs sid) E ct (session_inv_body γ sid) hSub

/-! ## Conservation invariants

A conserved quantity `proj : Endpoint → M` summed over a duplicate-free cover of
the session's endpoints. The lemmas below prove the two algebraic shapes every
session operation must take to preserve it: joining/leaving with a zero
contribution, and a transfer between two endpoints that keeps their combined
contribution. They do not yet connect to the machine's `open`/`send`/`recv`/
`close` step functions; that connection is the remaining obligation. -/

/-- Sum of the conserved quantity over an endpoint cover. -/
def coverSum {M : Type} [AddCommMonoid M] (proj : Endpoint → M) (eps : List Endpoint) : M :=
  (eps.map proj).sum

def conservation_inv (sid : SessionId)
    {M : Type} [AddCommMonoid M]
    (proj : Endpoint → M) (total : M) : iProp :=
  -- Conservation holds when a duplicate-free cover of the session sums to the total.
  iProp.exist fun (eps : List Endpoint) =>
    iProp.pure (eps.Nodup ∧ (∀ e ∈ eps, e.sid = sid) ∧ coverSum proj eps = total)

omit [Telltale.TelltaleIris] [GhostMapSlot Unit] [GhostMapSlot Nat]
    [GhostMapSlot LocalType] in
/-- Joining an endpoint whose contribution is zero preserves the sum. -/
theorem conservation_join_zero {M : Type} [AddCommMonoid M]
    (proj : Endpoint → M) (eps : List Endpoint) (e₀ : Endpoint) (h : proj e₀ = 0) :
    coverSum proj (e₀ :: eps) = coverSum proj eps := by
  simp [coverSum, h]

omit [Telltale.TelltaleIris] [GhostMapSlot Unit] [GhostMapSlot Nat]
    [GhostMapSlot LocalType] in
/-- Helper: split off two distinct members of a duplicate-free cover. -/
theorem coverSum_split2 {M : Type} [AddCommMonoid M] (proj : Endpoint → M)
    {eps : List Endpoint} {a b : Endpoint} (ha : a ∈ eps) (hb : b ∈ eps) (hab : a ≠ b) :
    coverSum proj eps = proj a + (proj b + coverSum proj ((eps.erase a).erase b)) := by
  have hb' : b ∈ eps.erase a := List.mem_erase_of_ne (Ne.symm hab) |>.2 hb
  unfold coverSum
  rw [← List.sum_map_erase _ ha, ← List.sum_map_erase _ hb']

omit [Telltale.TelltaleIris] [GhostMapSlot Unit] [GhostMapSlot Nat]
    [GhostMapSlot LocalType] in
/-- A transfer between two distinct endpoints that keeps their combined
contribution (and leaves all others unchanged) preserves the cover sum. -/
theorem conservation_transfer {M : Type} [AddCommMonoid M]
    (proj proj' : Endpoint → M) {eps : List Endpoint} {a b : Endpoint}
    (hNodup : eps.Nodup) (ha : a ∈ eps) (hb : b ∈ eps) (hab : a ≠ b)
    (hFrame : ∀ e, e ≠ a → e ≠ b → proj' e = proj e)
    (hPair : proj' a + proj' b = proj a + proj b) :
    coverSum proj' eps = coverSum proj eps := by
  rw [coverSum_split2 proj ha hb hab, coverSum_split2 proj' ha hb hab]
  have hRest : coverSum proj' ((eps.erase a).erase b) = coverSum proj ((eps.erase a).erase b) := by
    unfold coverSum
    congr 1
    refine List.map_congr_left (fun e he => hFrame e ?_ ?_)
    · exact (hNodup.mem_erase_iff.1 (List.mem_of_mem_erase he)).1
    · exact ((hNodup.erase a).mem_erase_iff.1 he).1
  rw [hRest, ← add_assoc, ← add_assoc, hPair]

/-! ## Participation and lifecycle events -/

structure Participation (ι : Type) [IdentityModel ι] where
  -- Participation token for a role in a session.
  participant : IdentityModel.ParticipantId ι
  session : SessionId
  role : Role
  endpoint : Endpoint
  site : IdentityModel.SiteId ι

inductive LifecycleEvent (ι : Type) [IdentityModel ι]
    (γ ε : Type) [GuardLayer γ] [EffectRuntime ε] where
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

/-! ## Lifecycle correctness properties -/

def open_coherent {ι : Type} [IdentityModel ι]
    (_roles : RoleSet) (_types : Role → LocalType)
    (_spatialReq : SpatialReq)
    (_assignment : Role → IdentityModel.ParticipantId ι)
    (_siteChoice : IdentityModel.ParticipantId ι → IdentityModel.SiteId ι) : Prop :=
  -- Session creation is coherent when the spatial constraint is satisfiable.
  ∃ hSiteChoice,
    canCreate _spatialReq _roles _assignment _siteChoice hSiteChoice ∧
    (∀ r, r ∈ _roles → _types r ≠ LocalType.end_)

def migrate_preserves_spatial {ι : Type} [IdentityModel ι]
    (_spatialReq : SpatialReq)
    (_assignment : Role → IdentityModel.ParticipantId ι)
    (_siteChoice _siteChoice' : IdentityModel.ParticipantId ι → IdentityModel.SiteId ι) : Prop :=
  -- Migration preserves spatial satisfiability when both site choices
  -- induce the same topology (i.e., the migrated participant's new site
  -- produces an identical deployment topology).
  ∀ roles hSiteChoice hSiteChoice',
    IdentityModel.toTopology roles _assignment _siteChoice hSiteChoice =
      IdentityModel.toTopology roles _assignment _siteChoice' hSiteChoice' →
    canCreate _spatialReq roles _assignment _siteChoice hSiteChoice →
      canCreate _spatialReq roles _assignment _siteChoice' hSiteChoice'

omit [Telltale.TelltaleIris] [GhostMapSlot Unit] [GhostMapSlot Nat]
    [GhostMapSlot LocalType] in
theorem migrate_preserves_spatial_holds {ι : Type} [IdentityModel ι]
    (spatialReq : SpatialReq)
    (assignment : Role → IdentityModel.ParticipantId ι)
    (siteChoice siteChoice' : IdentityModel.ParticipantId ι → IdentityModel.SiteId ι) :
    migrate_preserves_spatial spatialReq assignment siteChoice siteChoice' := by
  intro roles hsc hsc' hTopoEq hCreate
  unfold canCreate at *
  rw [← hTopoEq]
  exact hCreate

/-! ## Lifecycle Monotonicity Properties -/

def leave_preserves_coherent (sid : SessionId) (role : Role) : Prop :=
  -- Leaving preserves coherence: coherence over all endpoints implies
  -- coherence for every endpoint whose role differs from the leaving role.
  -- (Coherence is per-endpoint, so narrowing the set is monotone.)
  ∀ (G : SessionMap) (D : DEnv),
    (∀ (e : Endpoint) (L : LocalType), GMap.lookup G e = some L →
      Consume e.role L (lookupD D { sid := sid, sender := e.role, receiver := e.role }) ≠ none) →
    ∀ (e : Endpoint) (L : LocalType), e.role ≠ role → GMap.lookup G e = some L →
      Consume e.role L (lookupD D { sid := sid, sender := e.role, receiver := e.role }) ≠ none

omit [GhostMapSlot Unit] [GhostMapSlot Nat] [GhostMapSlot LocalType] in
theorem leave_preserves_coherent_holds (sid : SessionId) (role : Role) :
    leave_preserves_coherent sid role :=
  fun _ _ hCoh e L _ hLook => hCoh e L hLook

/-! ## Close-Phase Properties -/

def close_empty (_sid : SessionId) : Prop :=
  -- Closing implies empty buffers and traces for the session id.
  ∀ {ν : Type} [VerificationModel ν] (stSess : SessionState ν),
    stSess.sid = _sid →
      stSess.phase = .closed →
        stSess.buffers = [] ∧ stSess.traces = (∅ : DEnv)

def close_makes_inaccessible {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (sid : SessionId) : Prop :=
  -- Closed sessions expose no buffers or traces.
  ∀ stSess, (sid, stSess) ∈ st.sessions → stSess.phase = .closed →
    stSess.buffers = [] ∧ stSess.traces = (∅ : DEnv)
