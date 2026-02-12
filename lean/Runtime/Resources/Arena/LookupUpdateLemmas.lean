import Runtime.Resources.Arena.MemoryAndState

/-! # SessionStore Lookup and Update Lemmas

Core lemmas for SessionStore operations: findSession, lookupType,
updateType, with standard lookup-update laws. -/

/-
The Problem. SessionStore operations (lookup, update) must satisfy
expected algebraic laws: update-then-lookup returns the new value,
update at one endpoint doesn't affect lookup at another, etc.

Solution Structure. Define `SessionStore.findSession` for session
retrieval. Prove `lookupType_updateType_eq` for same-endpoint lookup
and `lookupType_updateType_ne` for different-endpoint lookup.
-/

set_option autoImplicit false

universe u

variable {ν : Type u} [VerificationModel ν]

/-! ## Session Lookup -/

def SessionStore.findSession (store : SessionStore ν) (sid : SessionId) : Option (SessionState ν) :=
  match store with
  | [] => none
  | (sid', st) :: rest =>
      if sid' = sid then some st
      else SessionStore.findSession rest sid

/-- Updating type at endpoint e, then looking up e, gives the new type. -/
@[simp] theorem SessionStore.lookupType_updateType_eq {store : SessionStore ν} {e : Endpoint} {L : LocalType}
    (hMem : ∃ st, (e.sid, st) ∈ store) :
    SessionStore.lookupType (store.updateType e L) e = some L := by
  induction store with
  | nil => simp at hMem
  | cons hd tl ih =>
    obtain ⟨sid, st⟩ := hd
    by_cases hsid : sid = e.sid
    · simp [SessionStore.updateType, SessionStore.lookupType, hsid,
        SessionState.lookupType_updateType_eq]
    · have hMem' : ∃ st, (e.sid, st) ∈ tl := by
        obtain ⟨st', hst'⟩ := hMem
        cases hst' with
        | head =>
            cases hsid rfl
        | tail _ htl =>
            exact ⟨st', htl⟩
      simp [SessionStore.updateType, SessionStore.lookupType, hsid]
      exact ih hMem'

/-- Updating type at endpoint e doesn't affect lookups at other endpoints. -/
theorem SessionStore.lookupType_updateType_ne {store : SessionStore ν} {e e' : Endpoint} {L : LocalType}
    (hne : e' ≠ e) :
    SessionStore.lookupType (store.updateType e L) e' = SessionStore.lookupType store e' := by
  induction store with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨sid, st⟩ := hd
    by_cases hsid : sid = e.sid
    · by_cases hsid' : sid = e'.sid
      · simp [SessionStore.updateType, SessionStore.lookupType, hsid,
          SessionState.lookupType_updateType_ne hne]
      · have hsid_ne : e.sid ≠ e'.sid := by
          simpa [hsid] using hsid'
        simp [SessionStore.updateType, SessionStore.lookupType, hsid, hsid_ne]
    · by_cases hsid' : sid = e'.sid
      · have hsid_ne : e'.sid ≠ e.sid := by
          simpa [hsid'] using hsid
        simp [SessionStore.updateType, SessionStore.lookupType, hsid', hsid_ne]
      · simp [SessionStore.updateType, SessionStore.lookupType, hsid, hsid', ih]

/-- Updating type at endpoint doesn't affect trace lookups. -/
@[simp] theorem SessionStore.lookupTrace_updateType {store : SessionStore ν} {e : Endpoint} {L : LocalType} {edge : Edge} :
    SessionStore.lookupTrace (store.updateType e L) edge = SessionStore.lookupTrace store edge := by
  induction store with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨sid, st⟩ := hd
    by_cases hsid : sid = e.sid
    · by_cases hsid_edge : sid = edge.sid
      · have heq : edge.sid = e.sid := by
          calc
            edge.sid = sid := hsid_edge.symm
            _ = e.sid := hsid
        simp [SessionStore.updateType, SessionStore.lookupTrace, hsid, heq,
          SessionState.lookupTrace_updateType]
      · have hsid_ne : edge.sid ≠ e.sid := by
          intro h
          apply hsid_edge
          calc
            sid = e.sid := hsid
            _ = edge.sid := h.symm
        simp [SessionStore.updateType, SessionStore.lookupTrace, hsid]
    · by_cases hsid_edge : sid = edge.sid
      · have hsid_ne : edge.sid ≠ e.sid := by
          intro h
          apply hsid
          calc
            sid = edge.sid := hsid_edge
            _ = e.sid := h
        simp [SessionStore.updateType, SessionStore.lookupTrace, hsid_edge, hsid_ne]
      · simp [SessionStore.updateType, SessionStore.lookupTrace, hsid, hsid_edge, ih]

/-- Updating trace at edge, then looking up that edge, gives the new trace. -/
@[simp] theorem SessionStore.lookupTrace_updateTrace_eq {store : SessionStore ν} {edge : Edge} {ts : List ValType}
    (hMem : ∃ st, (edge.sid, st) ∈ store) :
    SessionStore.lookupTrace (store.updateTrace edge ts) edge = ts := by
  induction store with
  | nil => simp at hMem
  | cons hd tl ih =>
    obtain ⟨sid, st⟩ := hd
    by_cases hsid : sid = edge.sid
    · simp [SessionStore.updateTrace, SessionStore.lookupTrace, hsid,
        SessionState.lookupTrace_updateTrace_eq]
    · have hMem' : ∃ st, (edge.sid, st) ∈ tl := by
        obtain ⟨st', hst'⟩ := hMem
        cases hst' with
        | head =>
            cases hsid rfl
        | tail _ htl =>
            exact ⟨st', htl⟩
      simp [SessionStore.updateTrace, SessionStore.lookupTrace, hsid]
      exact ih hMem'

/-- Updating trace at edge doesn't affect lookups at other edges. -/
theorem SessionStore.lookupTrace_updateTrace_ne {store : SessionStore ν} {edge edge' : Edge} {ts : List ValType}
    (hne : edge' ≠ edge) :
    SessionStore.lookupTrace (store.updateTrace edge ts) edge' = SessionStore.lookupTrace store edge' := by
  induction store with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨sid, st⟩ := hd
    by_cases hsid : sid = edge.sid
    · by_cases hsid' : sid = edge'.sid
      · simp [SessionStore.updateTrace, SessionStore.lookupTrace, hsid,
          SessionState.lookupTrace_updateTrace_ne hne]
      · have hsid_ne : edge.sid ≠ edge'.sid := by
          simpa [hsid] using hsid'
        simp [SessionStore.updateTrace, SessionStore.lookupTrace, hsid, hsid_ne]
    · by_cases hsid' : sid = edge'.sid
      · have hsid_ne : edge'.sid ≠ edge.sid := by
          simpa [hsid'] using hsid
        simp [SessionStore.updateTrace, SessionStore.lookupTrace, hsid', hsid_ne]
      · simp [SessionStore.updateTrace, SessionStore.lookupTrace, hsid, hsid', ih]

/-- Updating trace doesn't affect type lookups. -/
@[simp] theorem SessionStore.lookupType_updateTrace {store : SessionStore ν} {edge : Edge} {ts : List ValType} {e : Endpoint} :
    SessionStore.lookupType (store.updateTrace edge ts) e = SessionStore.lookupType store e := by
  induction store with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨sid, st⟩ := hd
    by_cases hsid_edge : sid = edge.sid
    · by_cases hsid_e : sid = e.sid
      · simp [SessionStore.updateTrace, SessionStore.lookupType, hsid_edge,
          SessionState.lookupType_updateTrace]
      · have hsid_ne : e.sid ≠ edge.sid := by
          intro h
          apply hsid_e
          calc
            sid = edge.sid := hsid_edge
            _ = e.sid := h.symm
        simp [SessionStore.updateTrace, SessionStore.lookupType, hsid_edge]
    · by_cases hsid_e : sid = e.sid
      · have hsid_ne : e.sid ≠ edge.sid := by
          intro h
          apply hsid_edge
          calc
            sid = e.sid := hsid_e
            _ = edge.sid := h
        simp [SessionStore.updateTrace, SessionStore.lookupType, hsid_e, hsid_ne]
      · simp [SessionStore.updateTrace, SessionStore.lookupType, hsid_edge, hsid_e, ih]

/-- Updating type doesn't affect buffer lookups. -/
@[simp] theorem SessionStore.lookupBuffer_updateType {store : SessionStore ν} {e : Endpoint} {L : LocalType} {edge : Edge} :
    SessionStore.lookupBuffer (store.updateType e L) edge = SessionStore.lookupBuffer store edge := by
  induction store with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨sid, st⟩ := hd
    by_cases hsid : sid = e.sid
    · by_cases hsid_edge : sid = edge.sid
      · have heq : e.sid = edge.sid := by
          calc
            e.sid = sid := hsid.symm
            _ = edge.sid := hsid_edge
        simp [SessionStore.updateType, SessionStore.lookupBuffer, hsid, heq,
          SessionState.updateType, SessionState.lookupBuffer]
      · have hsid_ne : e.sid ≠ edge.sid := by
          intro h
          apply hsid_edge
          calc
            sid = e.sid := hsid
            _ = edge.sid := h
        simp [SessionStore.updateType, SessionStore.lookupBuffer, hsid, hsid_ne]
    · by_cases hsid_edge : sid = edge.sid
      · have hsid_ne : edge.sid ≠ e.sid := by
          intro h
          apply hsid
          calc
            sid = edge.sid := hsid_edge
            _ = e.sid := h
        simp [SessionStore.updateType, SessionStore.lookupBuffer, hsid_edge, hsid_ne]
      · simp [SessionStore.updateType, SessionStore.lookupBuffer, hsid, hsid_edge, ih]

/-- Updating trace doesn't affect buffer lookups. -/
@[simp] theorem SessionStore.lookupBuffer_updateTrace {store : SessionStore ν} {edge : Edge} {ts : List ValType} {edge' : Edge} :
    SessionStore.lookupBuffer (store.updateTrace edge ts) edge' = SessionStore.lookupBuffer store edge' := by
  induction store with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨sid, st⟩ := hd
    by_cases hsid : sid = edge.sid
    · by_cases hsid_edge : sid = edge'.sid
      · have heq : edge.sid = edge'.sid := by
          calc
            edge.sid = sid := hsid.symm
            _ = edge'.sid := hsid_edge
        simp [SessionStore.updateTrace, SessionStore.lookupBuffer, hsid, heq,
          SessionState.updateTrace, SessionState.lookupBuffer]
      · have hsid_ne : edge.sid ≠ edge'.sid := by
          intro h
          apply hsid_edge
          calc
            sid = edge.sid := hsid
            _ = edge'.sid := h
        simp [SessionStore.updateTrace, SessionStore.lookupBuffer, hsid, hsid_ne]
    · by_cases hsid_edge : sid = edge'.sid
      · have hsid_ne : edge'.sid ≠ edge.sid := by
          intro h
          apply hsid
          calc
            sid = edge'.sid := hsid_edge
            _ = edge.sid := h
        simp [SessionStore.updateTrace, SessionStore.lookupBuffer, hsid_edge, hsid_ne]
      · simp [SessionStore.updateTrace, SessionStore.lookupBuffer, hsid, hsid_edge, ih]

/-! ## Session consistency predicates -/

/-- A session state is consistent if all endpoints in localTypes have the session's sid,
    and all edges in traces have the session's sid. -/
def SessionState.consistent {ν : Type u} [VerificationModel ν] (st : SessionState ν) : Prop :=
  (∀ e L, (e, L) ∈ st.localTypes → e.sid = st.sid) ∧
  (∀ edge, st.traces.find? edge ≠ none → edge.sid = st.sid)

/-- A session store is consistent if all sessions are consistent and keyed correctly. -/
def SessionStore.consistent {ν : Type u} [VerificationModel ν] (store : SessionStore ν) : Prop :=
  ∀ sid st, (sid, st) ∈ store → st.sid = sid ∧ st.consistent

/-- If a session state is consistent and an endpoint has different sid, it's not in localTypes. -/
theorem SessionState.lookupG_none_of_sid_ne {st : SessionState ν} {e : Endpoint}
    (hCons : st.consistent) (hne : e.sid ≠ st.sid) :
    lookupG st.localTypes e = none := by
  by_contra h
  push_neg at h
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp (Option.ne_none_iff_isSome.mp h)
  have hMem := lookupG_mem st.localTypes e L hL
  have hEq := hCons.1 e L hMem
  exact hne hEq

/-- If a session state is consistent and an edge has different sid, it's not in traces. -/
theorem SessionState.traces_find?_none_of_sid_ne {st : SessionState ν} {edge : Edge}
    (hCons : st.consistent) (hne : edge.sid ≠ st.sid) :
    st.traces.find? edge = none := by
  by_contra h
  have hEq := hCons.2 edge h
  exact hne hEq

/-! ## DEnv Update Helpers -/

theorem DEnv_find?_updateD_neq (env : DEnv) (e e' : Edge) (ts : List ValType) (hne : e ≠ e') :
    (updateD env e ts).find? e' = env.find? e' := by
  have hne' : compare e' e ≠ .eq := by
    intro hEq
    exact hne ((Edge.compare_eq_iff_eq e' e).1 hEq).symm
  have hfind :=
    Batteries.RBMap.find?_insert_of_ne (t := env.map) (k := e) (v := ts) (k' := e') hne'
  calc
    (updateD env e ts).find? e'
        = (DEnv.ofMap (env.map.insert e ts)).find? e' := by
            rfl
    _ = (env.map.insert e ts).find? e' := by
            simp
    _ = env.map.find? e' := hfind
    _ = env.find? e' := by
            rfl

/-- updateType preserves session consistency. -/
theorem SessionState.updateType_preserves_consistent {st : SessionState ν} {e : Endpoint} {L : LocalType}
    (hCons : st.consistent) (hSid : e.sid = st.sid) :
    (st.updateType e L).consistent := by
  constructor
  · intro e' L' hMem
    simp only [SessionState.updateType] at hMem
    cases updateG_mem_of st.localTypes e L e' L' hMem with
    | inl heq => exact heq.1 ▸ hSid
    | inr hmem => exact hCons.1 e' L' hmem
  · intro edge h
    simp only [SessionState.updateType] at h
    exact hCons.2 edge h

/-- updateTrace preserves session consistency. -/
theorem SessionState.updateTrace_preserves_consistent {st : SessionState ν} {edge : Edge} {ts : List ValType}
    (hCons : st.consistent) (hSid : edge.sid = st.sid) :
    (st.updateTrace edge ts).consistent := by
  constructor
  · intro e L hMem
    simp only [SessionState.updateTrace] at hMem
    exact hCons.1 e L hMem
  · intro edge' h
    simp only [SessionState.updateTrace] at h
    by_cases he : edge' = edge
    · exact he ▸ hSid
    · -- edge' ≠ edge, so find? is unchanged
      have hNe : edge ≠ edge' := Ne.symm he
      have hEq := DEnv_find?_updateD_neq (env := st.traces) (e := edge) (e' := edge') (ts := ts) hNe
      have hOrig : st.traces.find? edge' ≠ none := by
        intro hnone
        apply h
        simp [hEq, hnone]
      exact hCons.2 edge' hOrig

/-- SessionState.updateType preserves sid field. -/
@[simp] theorem SessionState.updateType_sid {st : SessionState ν} {e : Endpoint} {L : LocalType} :
    (st.updateType e L).sid = st.sid := rfl

/-- SessionState.updateTrace preserves sid field. -/
@[simp] theorem SessionState.updateTrace_sid {st : SessionState ν} {edge : Edge} {ts : List ValType} :
    (st.updateTrace edge ts).sid = st.sid := rfl

/-- SessionStore.updateType preserves store consistency. -/
theorem SessionStore.updateType_preserves_consistent {store : SessionStore ν} {e : Endpoint} {L : LocalType}
    (hCons : store.consistent)
    (hMem : ∃ st, (e.sid, st) ∈ store) :
    (store.updateType e L).consistent := by
  intro sid st hMemUpdated
  induction store with
  | nil => simp [SessionStore.updateType] at hMemUpdated
  | cons hd tl ih =>
    obtain ⟨sid', st'⟩ := hd
    simp only [SessionStore.updateType] at hMemUpdated
    by_cases hsid : sid' = e.sid
    · -- Found the session to update
      simp only [hsid, ↓reduceIte] at hMemUpdated
      -- After simp: hMemUpdated : (sid, st) ∈ (e.sid, st'.updateType e L) :: updateType tl e L
      simp only [List.mem_cons] at hMemUpdated
      cases hMemUpdated with
      | inl heq =>
        -- head case: (sid, st) = (e.sid, st'.updateType e L)
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hsid_eq, hst_eq⟩ := heq
        have hOrigCons := hCons sid' st' (List.Mem.head _)
        constructor
        · -- st.sid = sid
          rw [hst_eq, hsid_eq]
          simp [hOrigCons.1, hsid]
        · -- st.consistent
          rw [hst_eq]
          have hSidEq : e.sid = st'.sid := by
            rw [← hsid]
            exact hOrigCons.1.symm
          exact SessionState.updateType_preserves_consistent hOrigCons.2 hSidEq
      | inr hmem =>
        -- tail case: (sid, st) ∈ tl
        have hTlCons : SessionStore.consistent tl := fun sid'' st'' h =>
          hCons sid'' st'' (List.Mem.tail _ h)
        exact hTlCons sid st hmem
    · -- Not the session to update
      simp only [hsid, ↓reduceIte] at hMemUpdated
      -- After simp: hMemUpdated : (sid, st) ∈ (sid', st') :: updateType tl e L
      simp only [List.mem_cons] at hMemUpdated
      cases hMemUpdated with
      | inl heq =>
        -- head case: (sid, st) = (sid', st')
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hsid_eq, hst_eq⟩ := heq
        have hOrigCons := hCons sid' st' (List.Mem.head _)
        constructor
        · rw [hst_eq, hsid_eq]; exact hOrigCons.1
        · rw [hst_eq]; exact hOrigCons.2
      | inr hmem =>
        -- tail case: recurse
        have hTlCons : SessionStore.consistent tl := fun sid'' st'' h =>
          hCons sid'' st'' (List.Mem.tail _ h)
        have hTlMem : ∃ st, (e.sid, st) ∈ tl := by
          obtain ⟨st'', hst''⟩ := hMem
          simp only [List.mem_cons] at hst''
          cases hst'' with
          | inl heq =>
            simp only [Prod.mk.injEq] at heq
            exact absurd heq.1.symm hsid
          | inr hmem' => exact ⟨st'', hmem'⟩
        exact ih hTlCons hTlMem hmem

/-- SessionStore.updateTrace preserves store consistency. -/
theorem SessionStore.updateTrace_preserves_consistent {store : SessionStore ν} {edge : Edge} {ts : List ValType}
    (hCons : store.consistent)
    (hMem : ∃ st, (edge.sid, st) ∈ store) :
    (store.updateTrace edge ts).consistent := by
  intro sid st hMemUpdated
  induction store with
  | nil => simp [SessionStore.updateTrace] at hMemUpdated
  | cons hd tl ih =>
    obtain ⟨sid', st'⟩ := hd
    simp only [SessionStore.updateTrace] at hMemUpdated
    by_cases hsid : sid' = edge.sid
    · -- Found the session to update
      simp only [hsid, ↓reduceIte] at hMemUpdated
      simp only [List.mem_cons] at hMemUpdated
      cases hMemUpdated with
      | inl heq =>
        -- head case
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hsid_eq, hst_eq⟩ := heq
        have hOrigCons := hCons sid' st' (List.Mem.head _)
        constructor
        · rw [hst_eq, hsid_eq]
          simp [hOrigCons.1, hsid]
        · rw [hst_eq]
          have hSidEq : edge.sid = st'.sid := by
            rw [← hsid]
            exact hOrigCons.1.symm
          exact SessionState.updateTrace_preserves_consistent hOrigCons.2 hSidEq
      | inr hmem =>
        -- tail case
        have hTlCons : SessionStore.consistent tl := fun sid'' st'' h =>
          hCons sid'' st'' (List.Mem.tail _ h)
        exact hTlCons sid st hmem
    · -- Not the session to update
      simp only [hsid, ↓reduceIte] at hMemUpdated
      simp only [List.mem_cons] at hMemUpdated
      cases hMemUpdated with
      | inl heq =>
        -- head case
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hsid_eq, hst_eq⟩ := heq
        have hOrigCons := hCons sid' st' (List.Mem.head _)
        constructor
        · rw [hst_eq, hsid_eq]; exact hOrigCons.1
        · rw [hst_eq]; exact hOrigCons.2
      | inr hmem =>
        -- tail case
        have hTlCons : SessionStore.consistent tl := fun sid'' st'' h =>
          hCons sid'' st'' (List.Mem.tail _ h)
        have hTlMem : ∃ st, (edge.sid, st) ∈ tl := by
          obtain ⟨st'', hst''⟩ := hMem
          simp only [List.mem_cons] at hst''
          cases hst'' with
          | inl heq =>
            simp only [Prod.mk.injEq] at heq
            exact absurd heq.1.symm hsid
          | inr hmem' => exact ⟨st'', hmem'⟩
        exact ih hTlCons hTlMem hmem

/-! ## toGEnv/toDEnv under updates

Follow-on lemmas are in `Runtime.Resources.Arena.EnvProjectionLemmas`.
-/
