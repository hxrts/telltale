import Runtime.Resources.Arena.EnvProjectionLemmas

/-! # Well-Formed SessionStore

Well-formedness conditions for SessionStore and preservation lemmas
showing updates maintain consistency with projected environments. -/

/-
The Problem. SessionStore must maintain internal consistency: session
IDs match, endpoints belong to their session, and projections agree
with direct environment operations. We need to show updates preserve
these conditions.

Solution Structure. Prove `wf_session_store_nil` for the empty store.
Prove `update_type_preserves_session_consistency` showing type updates
don't break session ID consistency.
-/

set_option autoImplicit false

universe u

variable {ν : Type u} [VerificationModel ν]

/-! ## Empty Store Well-Formedness -/

theorem wf_session_store_nil : sessionStore_refines_envs ([] : SessionStore ν) := by
  simp only [sessionStore_refines_envs, SessionStore.toGEnv, SessionStore.toDEnv, SessionStore.toBuffers]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _ h; cases h
  · intro e; simp [lookupG, SessionStore.lookupType]
  · intro edge; simp [lookup_d_empty, SessionStore.lookupTrace]
  · intro edge; simp [lookupBuf, SessionStore.lookupBuffer]

/-! ## Session-Consistency Preservation Helpers -/

/-- Helper: session consistency is preserved by updateType. -/
theorem update_type_preserves_session_consistency {store : SessionStore ν} {e : Endpoint} {L : LocalType}
    (hSid : ∀ sid st, (sid, st) ∈ store → st.sid = sid ∧ (∀ e ∈ st.endpoints, e.sid = sid)) :
    ∀ sid st, (sid, st) ∈ store.updateType e L → st.sid = sid ∧ (∀ e ∈ st.endpoints, e.sid = sid) := by
  -- updateType only modifies localTypes, not sid or endpoints
  intro sid st hIn
  induction store with
  | nil =>
      simp [SessionStore.updateType] at hIn
  | cons hd tl ih =>
      obtain ⟨sid', st'⟩ := hd
      by_cases hsid : sid' = e.sid
      · simp only [SessionStore.updateType, hsid, ↓reduceIte, List.mem_cons] at hIn
        cases hIn with
        | inl hEq =>
            cases hEq
            have hHead := hSid sid' st' (List.Mem.head _)
            constructor
            · simpa [SessionState.update_type_sid, hsid] using hHead.1.trans hsid
            ·
              simpa [SessionState.updateType, hsid] using hHead.2
        | inr hTail =>
            have hTailSid : ∀ sid st, (sid, st) ∈ tl →
                st.sid = sid ∧ (∀ e ∈ st.endpoints, e.sid = sid) := by
              intro sid'' st'' hMem
              exact hSid sid'' st'' (List.Mem.tail _ hMem)
            exact hTailSid sid st hTail
      · simp only [SessionStore.updateType, hsid, ↓reduceIte, List.mem_cons] at hIn
        cases hIn with
        | inl hEq =>
            cases hEq
            simpa using (hSid _ _ (List.Mem.head _))
        | inr hTail =>
            have hTailSid : ∀ sid st, (sid, st) ∈ tl →
                st.sid = sid ∧ (∀ e ∈ st.endpoints, e.sid = sid) := by
              intro sid'' st'' hMem
              exact hSid sid'' st'' (List.Mem.tail _ hMem)
            exact ih hTailSid hTail

/-! ### `updateTrace` session-consistency helper -/

/-- Helper: session consistency is preserved by updateTrace. -/
theorem update_trace_preserves_session_consistency {store : SessionStore ν} {edge : Edge} {ts : List ValType}
    (hSid : ∀ sid st, (sid, st) ∈ store → st.sid = sid ∧ (∀ e ∈ st.endpoints, e.sid = sid)) :
    ∀ sid st, (sid, st) ∈ store.updateTrace edge ts → st.sid = sid ∧ (∀ e ∈ st.endpoints, e.sid = sid) := by
  -- updateTrace only modifies traces, not sid or endpoints
  intro sid st hIn
  induction store with
  | nil =>
      simp [SessionStore.updateTrace] at hIn
  | cons hd tl ih =>
      obtain ⟨sid', st'⟩ := hd
      by_cases hsid : sid' = edge.sid
      · simp only [SessionStore.updateTrace, hsid, ↓reduceIte, List.mem_cons] at hIn
        cases hIn with
        | inl hEq =>
            cases hEq
            have hHead := hSid sid' st' (List.Mem.head _)
            constructor
            · simpa [SessionState.update_trace_sid, hsid] using hHead.1.trans hsid
            ·
              simpa [SessionState.updateTrace, hsid] using hHead.2
        | inr hTail =>
            have hTailSid : ∀ sid st, (sid, st) ∈ tl →
                st.sid = sid ∧ (∀ e ∈ st.endpoints, e.sid = sid) := by
              intro sid'' st'' hMem
              exact hSid sid'' st'' (List.Mem.tail _ hMem)
            exact hTailSid sid st hTail
      · simp only [SessionStore.updateTrace, hsid, ↓reduceIte, List.mem_cons] at hIn
        cases hIn with
        | inl hEq =>
            cases hEq
            simpa using (hSid _ _ (List.Mem.head _))
        | inr hTail =>
            have hTailSid : ∀ sid st, (sid, st) ∈ tl →
                st.sid = sid ∧ (∀ e ∈ st.endpoints, e.sid = sid) := by
              intro sid'' st'' hMem
              exact hSid sid'' st'' (List.Mem.tail _ hMem)
            exact ih hTailSid hTail

/-! ## WF Refinement Preservation for `updateType` -/

/-- Type update preserves WFSessionStore. -/
theorem SessionStore.update_type_preserves_wf_session_store {store : SessionStore ν} {e : Endpoint} {L : LocalType}
    (hWF : sessionStore_refines_envs store)
    (hMem : ∃ st, (e.sid, st) ∈ store)
    (hCons : store.consistent) :
    sessionStore_refines_envs (store.updateType e L) := by
  obtain ⟨hSid, hG, hD, hBuf⟩ := hWF
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Session consistency preserved
    exact update_type_preserves_session_consistency hSid
  · -- Type lookups agree: lookupG (toGEnv store') e' = lookupType store' e'
    intro e'
    -- We have: lookupG (toGEnv store) e' = lookupType store e' (from hG)
    -- Need: lookupG (toGEnv store') e' = lookupType store' e'
    -- where store' = store.updateType e L
    -- Case split on whether e' = e
    by_cases he : e' = e
    · -- e' = e: both sides give some L
      have hBridge := SessionStore.to_g_env_update_type (store := store) (e := e) (L := L) hMem hCons e'
      have hLookup' : SessionStore.lookupType (store.updateType e L) e' = some L := by
        simpa [he] using (SessionStore.lookup_type_update_type_eq (store := store) (e := e) (L := L) hMem)
      have hRight : lookupG (updateG (SessionStore.toGEnv store) e L) e' = some L := by
        rw [he]
        exact lookup_g_update_g_eq (env := SessionStore.toGEnv store) (e := e) (L := L)
      rw [hLookup']
      exact hBridge.trans hRight
    · -- e' ≠ e: both sides unchanged
      rw [SessionStore.lookup_type_update_type_ne he]
      rw [← hG e']
      calc
        lookupG (SessionStore.toGEnv (store.updateType e L)) e'
            = lookupG (updateG (SessionStore.toGEnv store) e L) e' :=
              SessionStore.to_g_env_update_type (store := store) (e := e) (L := L) hMem hCons e'
        _ = lookupG (SessionStore.toGEnv store) e' :=
              lookup_g_update_g_ne he
  · -- Trace lookups agree (toGEnv update doesn't affect toDEnv)
    intro edge
    rw [SessionStore.lookup_trace_update_type]
    rw [← hD edge]
    congr 1
    exact SessionStore.to_d_env_update_type
  · -- Buffer lookups agree (unchanged by type update)
    intro edge
    rw [SessionStore.to_buffers_update_type]
    rw [SessionStore.lookup_buffer_update_type]
    exact hBuf edge

/-! ## WF Refinement Preservation for `updateTrace` -/

/-- Trace update preserves WFSessionStore. -/
theorem SessionStore.update_trace_preserves_wf_session_store {store : SessionStore ν} {edge : Edge} {ts : List ValType}
    (hWF : sessionStore_refines_envs store)
    (hMem : ∃ st, (edge.sid, st) ∈ store)
    (hCons : store.consistent) :
    sessionStore_refines_envs (store.updateTrace edge ts) := by
  obtain ⟨hSid, hG, hD, hBuf⟩ := hWF
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Session consistency preserved
    exact update_trace_preserves_session_consistency hSid
  · -- Type lookups agree (unchanged by trace update)
    intro e
    rw [SessionStore.lookup_type_update_trace]
    rw [← hG e]
    congr 1
    exact SessionStore.to_g_env_update_trace
  · -- Trace lookups agree
    intro edge'
    by_cases he : edge' = edge
    · -- edge' = edge: both sides give ts
      have hLookup' : SessionStore.lookupTrace (store.updateTrace edge ts) edge' = ts := by
        simpa [he] using (SessionStore.lookup_trace_update_trace_eq (store := store) (edge := edge) (ts := ts) hMem)
      rw [hLookup']
      calc
        lookupD (SessionStore.toDEnv (store.updateTrace edge ts)) edge'
            = lookupD (updateD (SessionStore.toDEnv store) edge ts) edge' :=
              SessionStore.to_d_env_update_trace (store := store) (edge := edge) (ts := ts) hMem hCons edge'
        _ = ts :=
              by simpa [he] using (lookup_d_update_eq (SessionStore.toDEnv store) edge ts)
    · -- edge' ≠ edge: both sides unchanged
      rw [SessionStore.lookup_trace_update_trace_ne he]
      rw [← hD edge']
      calc
        lookupD (SessionStore.toDEnv (store.updateTrace edge ts)) edge'
            = lookupD (updateD (SessionStore.toDEnv store) edge ts) edge' :=
              SessionStore.to_d_env_update_trace (store := store) (edge := edge) (ts := ts) hMem hCons edge'
        _ = lookupD (SessionStore.toDEnv store) edge' :=
              lookup_d_update_neq (SessionStore.toDEnv store) edge edge' ts (Ne.symm he)
  · -- Buffer lookups agree (unchanged by trace update)
    intro edge'
    rw [SessionStore.to_buffers_update_trace]
    rw [SessionStore.lookup_buffer_update_trace]
    exact hBuf edge'
