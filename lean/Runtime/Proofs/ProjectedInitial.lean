import Runtime.Proofs.ProjectedProgress

/-! # Runtime.Proofs.ProjectedInitial

An explicit constructor for initial projected stores, so that the invariant
`StoreProjects` (and hence `concrete_termination_of_projected`) can be
instantiated from the outside.

`initialProjected scope sessions` builds one session per entry
`(sid, msgs)` where `msgs : List (Role × Role × ValType)` lists the protocol's
messages `p → q : T` in global order. Every message is unsent, all traces and
buffers are empty, and each participating role's endpoint type is the projection
`projP r` of the message list. `initialProjected_projects` proves
`StoreProjects` from distinct session ids and no self-messages;
`initialProjected_rolesCover` proves `RolesCover roles` when `roles` contains
every participant.
-/

/-
The Problem. `StoreProjects` is an invariant; without a witness store it cannot
be used.

Solution Structure. Build the store by `map`, then compute every lookup by
induction over the session list and over the role list.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Runtime.Proofs.Projected

section

universe u
variable {ν : Type u} [VerificationModel ν]

/-! ## Construction -/

/-- A straight-line protocol as a list of messages `(sender, receiver, payload)`. -/
abbrev MsgSpec := Role × Role × ValType

/-- The configuration of an unstarted protocol: every message unsent. -/
def initialMsgs (ms : List MsgSpec) : List PMsg :=
  ms.map fun m => ⟨m.1, m.2.1, m.2.2, false⟩

/-- All participants of a message list (with repetitions; harmless for lookup). -/
def initialRoles (ms : List MsgSpec) : List Role :=
  ms.map (·.1) ++ ms.map (·.2.1)

/-- The local-type environment of a session: each role projects the messages. -/
def initialTypes (sid : SessionId) (g : List PMsg) (roles : List Role) : GEnv :=
  roles.map fun r => (⟨sid, r⟩, projP r g)

/-- The initial session state for `sid` running the messages `ms`. -/
def initialSession (scope : ScopeId) (sid : SessionId) (ms : List MsgSpec) : SessionState ν :=
  { scope := scope
    sid := sid
    roles := initialRoles ms
    endpoints := (initialRoles ms).map fun r => ⟨sid, r⟩
    localTypes := initialTypes sid (initialMsgs ms) (initialRoles ms)
    traces := ∅
    buffers := []
    handlers := []
    epoch := 0
    phase := .active }

/-- **initialProjected.** The store with one initial session per `(sid, msgs)`. -/
def initialProjected (scope : ScopeId) (sessions : List (SessionId × List MsgSpec)) :
    SessionStore ν :=
  sessions.map fun s => (s.1, initialSession scope s.1 s.2)

/-! ## Configuration facts -/

/-- Unsent messages produce empty traces. -/
theorem traceP_initialMsgs (p q : Role) : ∀ ms : List MsgSpec, traceP p q (initialMsgs ms) = []
  | [] => rfl
  | m :: ms => by
    simp only [initialMsgs, List.map_cons, traceP, Bool.false_eq_true, and_false, if_false]
    exact traceP_initialMsgs p q ms

/-- Unsent messages are trivially `SentClosed`. -/
theorem sentClosed_initialMsgs : ∀ ms : List MsgSpec, SentClosed (initialMsgs ms)
  | [] => List.Pairwise.nil
  | m :: ms => by
    refine List.pairwise_cons.mpr ⟨fun b hb hs => ?_, sentClosed_initialMsgs ms⟩
    obtain ⟨b', -, rfl⟩ := List.mem_map.mp hb
    cases hs

/-- Members of `initialMsgs` come from the spec list. -/
theorem mem_initialMsgs {ms : List MsgSpec} {m : PMsg} (h : m ∈ initialMsgs ms) :
    ∃ s ∈ ms, m.sender = s.1 ∧ m.receiver = s.2.1 := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
  exact ⟨s, hs, rfl, rfl⟩

/-- Every message's participants are in `initialRoles`. -/
theorem initialRoles_covers {ms : List MsgSpec} {s : MsgSpec} (h : s ∈ ms) :
    s.1 ∈ initialRoles ms ∧ s.2.1 ∈ initialRoles ms :=
  ⟨List.mem_append_left _ (List.mem_map_of_mem h), List.mem_append_right _ (List.mem_map_of_mem h)⟩

/-! ## Lookup computations -/

/-- Lookup in `initialTypes` is the projection for listed roles. -/
theorem lookupG_initialTypes (sid : SessionId) (g : List PMsg) (r : Role) :
    ∀ roles : List Role, lookupG (initialTypes sid g roles) ⟨sid, r⟩ =
      if r ∈ roles then some (projP r g) else none
  | [] => by simp [initialTypes, lookupG]
  | r' :: roles => by
    by_cases hr : r = r'
    · subst hr; simp [initialTypes, lookupG]
    · have hne : (⟨sid, r⟩ : Endpoint) ≠ ⟨sid, r'⟩ := fun h => hr (congrArg Endpoint.role h)
      have hb : ((⟨sid, r⟩ : Endpoint) == ⟨sid, r'⟩) = false := beq_false_of_ne hne
      have ih := lookupG_initialTypes sid g r roles
      simp only [initialTypes, List.map_cons, lookupG, List.lookup_cons, hb] at ih ⊢
      rw [ih]; simp [hr]

/-- Session lookups in `initialProjected` reduce to the named session. -/
theorem initialProjected_lookups (scope : ScopeId) {sid : SessionId} {ms : List MsgSpec} :
    ∀ {sessions : List (SessionId × List MsgSpec)}, (sessions.map (·.1)).Nodup →
      (sid, ms) ∈ sessions →
      (∀ e : Endpoint, e.sid = sid → SessionStore.lookupType (initialProjected (ν := ν) scope sessions) e =
        (initialSession (ν := ν) scope sid ms).lookupType e) ∧
      (∀ edge : Edge, edge.sid = sid →
        SessionStore.lookupTrace (initialProjected (ν := ν) scope sessions) edge = [])
  | [], _, h => by simp at h
  | (sid', ms') :: rest, hN, h => by
    have hN' : sid' ∉ rest.map (·.1) ∧ (rest.map (·.1)).Nodup := by
      rw [List.map_cons] at hN; exact List.nodup_cons.mp hN
    by_cases hs : sid' = sid
    · subst hs
      have hms : ms' = ms := by
        rcases List.mem_cons.mp h with h | h
        · exact (Prod.mk.inj h).2.symm
        · exact absurd (List.mem_map_of_mem (f := (·.1)) h) hN'.1
      subst hms
      refine ⟨fun e he => ?_, fun edge he => ?_⟩
      · simp [initialProjected, SessionStore.lookupType, he]
      · simp [initialProjected, SessionStore.lookupTrace, he, initialSession,
          SessionState.lookupTrace]
    · have hmem : (sid, ms) ∈ rest := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd (Prod.mk.inj h).1.symm hs
        · exact h
      obtain ⟨ih1, ih2⟩ := initialProjected_lookups scope hN'.2 hmem
      refine ⟨fun e he => ?_, fun edge he => ?_⟩
      · have : sid' ≠ e.sid := fun h' => hs (h'.trans he)
        simpa [initialProjected, SessionStore.lookupType, this] using ih1 e he
      · have : sid' ≠ edge.sid := fun h' => hs (h'.trans he)
        simpa [initialProjected, SessionStore.lookupTrace, this] using ih2 edge he

/-! ## The invariant holds initially -/

/-- One initial session satisfies `SessionProjects`. -/
theorem initialSession_projects (scope : ScopeId) {sessions : List (SessionId × List MsgSpec)}
    (hN : (sessions.map (·.1)).Nodup) {sid : SessionId} {ms : List MsgSpec}
    (hmem : (sid, ms) ∈ sessions) (hd : ∀ s ∈ ms, s.1 ≠ s.2.1) :
    SessionProjects (initialProjected (ν := ν) scope sessions) sid (initialMsgs ms)
      (initialRoles ms) := by
  obtain ⟨h1, h2⟩ := initialProjected_lookups (ν := ν) scope hN hmem
  refine ⟨sentClosed_initialMsgs ms, fun m hm => ?_, fun m hm => ?_, fun r => ?_, fun p q => ?_⟩
  · obtain ⟨s, hs, e1, e2⟩ := mem_initialMsgs hm; rw [e1, e2]; exact hd s hs
  · obtain ⟨s, hs, e1, e2⟩ := mem_initialMsgs hm; rw [e1, e2]; exact initialRoles_covers hs
  · rw [h1 ⟨sid, r⟩ rfl]
    exact lookupG_initialTypes sid (initialMsgs ms) r (initialRoles ms)
  · rw [h2 ⟨sid, p, q⟩ rfl, traceP_initialMsgs]

/-- **initialProjected_projects.** With distinct session ids and no
self-messages, the initial store satisfies the projected invariant. -/
theorem initialProjected_projects (scope : ScopeId) {sessions : List (SessionId × List MsgSpec)}
    (hN : (sessions.map (·.1)).Nodup) (hd : ∀ s ∈ sessions, ∀ m ∈ s.2, m.1 ≠ m.2.1) :
    StoreProjects (initialProjected (ν := ν) scope sessions) := by
  intro sid hsid
  have : sid ∈ sessions.map (·.1) := by
    simpa [initialProjected, List.map_map, Function.comp] using hsid
  obtain ⟨⟨sid', ms⟩, hmem, rfl⟩ := List.mem_map.mp this
  exact ⟨_, _, initialSession_projects scope hN hmem (hd _ hmem)⟩

/-- **initialProjected_rolesCover.** The initial store's endpoints are covered
by any role list containing every participant. -/
theorem initialProjected_rolesCover (scope : ScopeId) {sessions : List (SessionId × List MsgSpec)}
    {roles : List Role} (hR : ∀ s ∈ sessions, ∀ m ∈ s.2, m.1 ∈ roles ∧ m.2.1 ∈ roles) :
    RolesCover roles (initialProjected (ν := ν) scope sessions) := by
  intro ep L h
  induction sessions with
  | nil => simp [initialProjected, SessionStore.lookupType] at h
  | cons s rest ih =>
    obtain ⟨sid, ms⟩ := s
    by_cases hs : sid = ep.sid
    · have h' : lookupG (initialTypes sid (initialMsgs ms) (initialRoles ms)) ep = some L := by
        simpa [initialProjected, SessionStore.lookupType, hs, SessionState.lookupType,
          initialSession, lookupG] using h
      have hin : ep.role ∈ initialRoles ms := by
        have := lookupG_initialTypes sid (initialMsgs ms) ep.role (initialRoles ms)
        have hep : (⟨sid, ep.role⟩ : Endpoint) = ep := by
          obtain ⟨es, er⟩ := ep; cases hs; rfl
        rw [hep, h'] at this
        by_contra hc; rw [if_neg hc] at this; cases this
      rcases List.mem_append.mp hin with hin | hin <;>
        obtain ⟨m, hm, hme⟩ := List.mem_map.mp hin
      · rw [← hme]; exact (hR _ List.mem_cons_self m hm).1
      · rw [← hme]; exact (hR _ List.mem_cons_self m hm).2
    · have h' : SessionStore.lookupType (initialProjected (ν := ν) scope rest) ep = some L := by
        simpa [initialProjected, SessionStore.lookupType, hs] using h
      exact ih (fun s hs' => hR s (List.mem_cons_of_mem _ hs')) h'

end
