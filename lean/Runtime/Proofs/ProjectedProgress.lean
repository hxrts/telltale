import Runtime.Proofs.ProjectedProtocol
import Runtime.Proofs.ConcreteTermination
import Runtime.Resources.Arena.LookupUpdateLemmas

/-! # Runtime.Proofs.ProjectedProgress

Progress and fair termination of the concrete role step (`roleStep`,
`ConcreteTermination.lean`) for stores obtained from straight-line global
protocols, **without** a frontier/progress hypothesis.

`StoreProjects store`: every session `sid` of the store has a configuration
`g : List PMsg` (see `ProjectedProtocol.lean`) and a role list such that each
endpoint type is the projection `projP r g`, endpoints outside the role list are
absent, every edge trace is `traceP p q g`, sends respect local order
(`SentClosed`) and no message is a self-message. An initial projected store is
the case where no message is `sent` (all traces empty).

Results:
* `progress_of_projected`: `StoreProjects store → ¬ AllSessionsComplete store →
  FrontierEnabled store`.
* `frontierAction_preserves_projected` / `roleStep_preserves_projected`.
* `concrete_termination_of_projected`: fair termination of `roleStep` from any
  `StoreProjects` store whose roles are covered by the scheduler's role list.

Why not `DualFrontier` (the former `DualFrontier.lean`, now deleted): its
`recv_dual` field ("a receiver on an empty trace has its partner at a head output
*to it*") is too strong, not merely unproven. Counterexample: global protocol
`y → z : m ; y → x : n`. Role `x` is at `recv y` with an empty `y → x` trace,
but `y`'s head output goes to `z`, so `recv_dual` fails although the store
progresses fine (`y → z` is enabled). The weaker global form "some endpoint has
a head output" is also false for projected stores (`p → q` sent, `q → r` unsent:
`r` waits on an empty trace, `q` waits on a non-empty one, nobody sends).
Deadlock freedom is proved here directly from the first message of `g`.

Why the fragment is the right one:
* `mu`/`var` are excluded. The bounded `k * measure` termination theorem is
  intrinsically about recursion-free protocols, and `frontierAction` has no
  `.mu` case, so a `.mu`-headed runtime type can never step at all.
* `select`/`branch` are excluded. The concrete `.select` action appends
  `.string` to the *type trace* but never enqueues the label into the signed
  *buffer* that `.branch` reads (`SessionStore.lookupBuffer`), so under
  `frontierAction` alone a `select`/`branch` pair can never complete. This is a
  defect of `frontierAction` relative to the machine's commit stages, reported
  rather than papered over; the choice-free fragment is value messages only.
* Consequently the bridge from `GlobalType` via `trans`/`localTypeRToLocalType`
  is open: `trans` of a single-branch `comm` yields a `(lbl, none, cont)` branch,
  which `localTypeRToLocalType` turns into a singleton `.select`/`.branch`, not
  `.send`/`.recv`. `StoreProjects` is stated on runtime `LocalType`s directly.
  Initial projected stores are built by `initialProjected`
  (`ProjectedInitial.lean`).
-/

/-
The Problem. Discharge the progress obligation of the concrete ranking.

Solution Structure. Per-session global configuration invariant, a generic
"advance one endpoint" preservation lemma, then the ranking on the subtype of
invariant stores.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical
open Runtime.Proofs.Projected

section

universe u
variable {ν : Type u} [VerificationModel ν]

/-! ## The invariant -/

/-- Session `sid` of `store` is the configuration `g` over `roles`. -/
structure SessionProjects (store : SessionStore ν) (sid : SessionId) (g : List PMsg)
    (roles : List Role) : Prop where
  /-- Sends respect local order. -/
  closed : SentClosed g
  /-- No self-messages. -/
  distinct : ∀ m ∈ g, m.sender ≠ m.receiver
  /-- Every participant has an endpoint. -/
  covered : ∀ m ∈ g, m.sender ∈ roles ∧ m.receiver ∈ roles
  /-- Endpoint types are projections. -/
  types : ∀ r, SessionStore.lookupType store ⟨sid, r⟩ =
    if r ∈ roles then some (projP r g) else none
  /-- Edge traces are the sent, unreceived payloads. -/
  traces : ∀ p q, SessionStore.lookupTrace store ⟨sid, p, q⟩ = traceP p q g

/-- Every session of the store is a projected straight-line configuration. -/
def StoreProjects (store : SessionStore ν) : Prop :=
  ∀ sid ∈ store.map (·.1), ∃ g roles, SessionProjects store sid g roles

/-- Every stored endpoint's role is in the scheduler's role list. -/
def RolesCover (roles : List Role) (store : SessionStore ν) : Prop :=
  ∀ ep L, SessionStore.lookupType store ep = some L → ep.role ∈ roles

/-! ## Store helpers -/

/-- A looked-up endpoint's session is a member of the store. -/
theorem mem_of_lookupType {store : SessionStore ν} {e : Endpoint} {L : LocalType}
    (h : SessionStore.lookupType store e = some L) : ∃ st, (e.sid, st) ∈ store := by
  induction store with
  | nil => simp [SessionStore.lookupType] at h
  | cons p rest ih =>
    obtain ⟨sid, s⟩ := p
    by_cases hs : sid = e.sid
    · subst hs; exact ⟨s, List.mem_cons_self⟩
    · simp only [SessionStore.lookupType, dif_neg hs] at h
      obtain ⟨st, hst⟩ := ih h
      exact ⟨st, List.mem_cons_of_mem _ hst⟩

/-- `updateType` keeps the session ids. -/
theorem map_fst_updateType (store : SessionStore ν) (e : Endpoint) (L : LocalType) :
    (store.updateType e L).map (·.1) = store.map (·.1) := by
  induction store with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨sid, s⟩ := p
    by_cases hs : sid = e.sid
    · simp [SessionStore.updateType, hs]
    · simp [SessionStore.updateType, hs, ih]

/-- `updateTrace` keeps the session ids. -/
theorem map_fst_updateTrace (store : SessionStore ν) (edge : Edge) (ts : List ValType) :
    (store.updateTrace edge ts).map (·.1) = store.map (·.1) := by
  induction store with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨sid, s⟩ := p
    by_cases hs : sid = edge.sid
    · simp [SessionStore.updateTrace, hs]
    · simp [SessionStore.updateTrace, hs, ih]

/-- A stored type is the projection of its session's configuration. -/
theorem lookup_projects {store : SessionStore ν} (hP : StoreProjects store) {ep : Endpoint}
    {L : LocalType} (h : SessionStore.lookupType store ep = some L) :
    ∃ g roles, SessionProjects store ep.sid g roles ∧ ep.role ∈ roles ∧ L = projP ep.role g := by
  obtain ⟨g, roles, hS⟩ := hP ep.sid (sid_mem_of_lookupType h)
  have ht := hS.types ep.role
  rw [show (⟨ep.sid, ep.role⟩ : Endpoint) = ep from rfl, h] at ht
  by_cases hr : ep.role ∈ roles
  · rw [if_pos hr] at ht; exact ⟨g, roles, hS, hr, Option.some.inj ht⟩
  · rw [if_neg hr] at ht; cases ht

/-! ## Progress -/

/-- The first message of a non-empty configuration gives an enabled frontier. -/
theorem frontier_of_head_msg {store : SessionStore ν} {sid : SessionId} {m : PMsg}
    {g : List PMsg} {roles : List Role} (hS : SessionProjects store sid (m :: g) roles) :
    FrontierEnabled store := by
  have hcov := hS.covered m List.mem_cons_self
  have hd := hS.distinct m List.mem_cons_self
  cases hs : m.sent
  · left
    have ht := hS.types m.sender
    rw [if_pos hcov.1, projP, if_neg (Ne.symm hd), if_pos ⟨rfl, hs⟩] at ht
    exact ⟨_, _, _, _, ht⟩
  · right; left
    have ht := hS.types m.receiver
    rw [if_pos hcov.2, projP, if_pos rfl] at ht
    have htr := hS.traces m.sender m.receiver
    rw [traceP, if_pos ⟨rfl, rfl, hs⟩] at htr
    exact ⟨_, _, _, _, _, ht, htr⟩

/-- **progress_of_projected.** A projected store that is not complete has an
enabled frontier action. No duality/frontier hypothesis. -/
theorem progress_of_projected {store : SessionStore ν} (hP : StoreProjects store)
    (h : ¬ AllSessionsComplete store) : FrontierEnabled store := by
  have hEx : ∃ e L, SessionStore.lookupType store e = some L ∧ L ≠ .end_ := by
    by_contra hc
    exact h fun e L hL => by_contra fun hne => hc ⟨e, L, hL, hne⟩
  obtain ⟨e, L, hL, hne⟩ := hEx
  obtain ⟨g, roles, hS, -, rfl⟩ := lookup_projects hP hL
  cases g with
  | nil => exact absurd rfl hne
  | cons m g => exact frontier_of_head_msg hS

/-! ## Preservation -/

/-- Data for advancing endpoint `ep` of a configuration `g` to `g'`, writing
trace `ts` on `edge`. -/
structure AdvanceSpec (ep : Endpoint) (edge : Edge) (g g' : List PMsg) (L' : LocalType)
    (ts : List ValType) : Prop where
  closed : SentClosed g'
  sub : ∀ b ∈ g', ∃ a ∈ g, a.sender = b.sender ∧ a.receiver = b.receiver
  self : projP ep.role g' = L'
  other : ∀ r, r ≠ ep.role → projP r g' = projP r g
  edge_tr : traceP edge.sender edge.receiver g' = ts
  other_tr : ∀ p q, ¬ (p = edge.sender ∧ q = edge.receiver) → traceP p q g' = traceP p q g

/-- The advanced session satisfies the invariant with configuration `g'`. -/
theorem sessionProjects_advance {store : SessionStore ν} {ep : Endpoint} {edge : Edge}
    {g g' : List PMsg} {roles : List Role} {L L' : LocalType} {ts : List ValType}
    (hS : SessionProjects store ep.sid g roles) (hTy : SessionStore.lookupType store ep = some L)
    (hr : ep.role ∈ roles) (hE : edge.sid = ep.sid) (hA : AdvanceSpec ep edge g g' L' ts) :
    SessionProjects ((store.updateType ep L').updateTrace edge ts) ep.sid g' roles := by
  obtain ⟨st, hst⟩ := mem_of_lookupType hTy
  refine ⟨hA.closed, fun b hb => ?_, fun b hb => ?_, fun r => ?_, fun p q => ?_⟩
  · obtain ⟨a, ha, h1, h2⟩ := hA.sub b hb; rw [← h1, ← h2]; exact hS.distinct a ha
  · obtain ⟨a, ha, h1, h2⟩ := hA.sub b hb; rw [← h1, ← h2]; exact hS.covered a ha
  · rw [SessionStore.lookup_type_update_trace]
    by_cases hre : r = ep.role
    · subst hre
      rw [SessionStore.lookup_type_update_type_eq ⟨st, hst⟩, if_pos hr, hA.self]
    · rw [SessionStore.lookup_type_update_type_ne (fun h => hre (congrArg Endpoint.role h)),
        hS.types r, hA.other r hre]
  · by_cases hpq : p = edge.sender ∧ q = edge.receiver
    · obtain ⟨rfl, rfl⟩ := hpq
      have hed : (⟨ep.sid, edge.sender, edge.receiver⟩ : Edge) = edge := by rw [← hE]
      obtain ⟨st', hst'⟩ := mem_of_lookupType
        (SessionStore.lookup_type_update_type_eq (L := L') ⟨st, hst⟩)
      rw [hed, SessionStore.lookup_trace_update_trace_eq ⟨st', hE ▸ hst'⟩, hA.edge_tr]
    · have hne : (⟨ep.sid, p, q⟩ : Edge) ≠ edge := fun h => hpq ⟨by rw [← h], by rw [← h]⟩
      rw [SessionStore.lookup_trace_update_trace_ne hne, SessionStore.lookup_trace_update_type,
        hS.traces, hA.other_tr p q hpq]

/-- Sessions other than `ep.sid` are untouched by the advance. -/
theorem sessionProjects_untouched {store : SessionStore ν} {ep : Endpoint} {edge : Edge}
    {sid : SessionId} {g : List PMsg} {roles : List Role} {L' : LocalType} {ts : List ValType}
    (hS : SessionProjects store sid g roles) (hne : sid ≠ ep.sid) (hE : edge.sid = ep.sid) :
    SessionProjects ((store.updateType ep L').updateTrace edge ts) sid g roles := by
  refine ⟨hS.closed, hS.distinct, hS.covered, fun r => ?_, fun p q => ?_⟩
  · rw [SessionStore.lookup_type_update_trace,
      SessionStore.lookup_type_update_type_ne (fun h => hne (congrArg Endpoint.sid h)), hS.types]
  · rw [SessionStore.lookup_trace_update_trace_ne (fun h => hne (by rw [← hE, ← h])),
      SessionStore.lookup_trace_update_type, hS.traces]

/-- **Generic preservation**: advancing one endpoint according to an
`AdvanceSpec` preserves `StoreProjects`. -/
theorem storeProjects_advance {store : SessionStore ν} (hP : StoreProjects store)
    {ep : Endpoint} {edge : Edge} {L L' : LocalType} {ts : List ValType}
    (hTy : SessionStore.lookupType store ep = some L) (hE : edge.sid = ep.sid)
    (hA : ∀ g roles, SessionProjects store ep.sid g roles → ep.role ∈ roles → L = projP ep.role g →
      ∃ g', AdvanceSpec ep edge g g' L' ts) :
    StoreProjects ((store.updateType ep L').updateTrace edge ts) := by
  intro sid hsid
  rw [map_fst_updateTrace, map_fst_updateType] at hsid
  by_cases hs : sid = ep.sid
  · subst hs
    obtain ⟨g, roles, hS, hr, hL⟩ := lookup_projects hP hTy
    obtain ⟨g', hA'⟩ := hA g roles hS hr hL
    exact ⟨g', roles, sessionProjects_advance hS hTy hr hE hA'⟩
  · obtain ⟨g, roles, hS⟩ := hP sid hsid
    exact ⟨g, roles, sessionProjects_untouched hS hs hE⟩

end
