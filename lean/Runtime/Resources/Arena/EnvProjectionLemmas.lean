import Runtime.Resources.Arena.LookupUpdateLemmas

/-! # Environment Projection Lemmas

Lemmas relating SessionStore projections (toGEnv, toDEnv) to direct
environment operations, enabling proof transfer between representations. -/

/-
The Problem. The VM uses a structured `SessionStore` representation,
but proofs often work with flat `GEnv` and `DEnv`. We need lemmas
relating the two, especially for fold-based projections.

Solution Structure. Prove `DEnv_foldl_append_comm` for trace accumulation.
Prove `lookupG_append_left/right` for GEnv composition. These enable
lifting proofs between representations.
-/

set_option autoImplicit false

universe u

variable {ν : Type u} [VerificationModel ν]

/-! ## DEnv Fold Commutativity -/

theorem DEnv_foldl_append_comm {ν : Type u} [VerificationModel ν]
    (D : DEnv) (store : SessionStore ν) :
    List.foldl (fun acc p => acc ++ p.snd.traces) D store =
    D ++ List.foldl (fun acc p => acc ++ p.snd.traces) (∅ : DEnv) store := by
  induction store generalizing D with
  | nil =>
    simp only [List.foldl]
    -- D ++ ∅ = D
    have h : D ++ (∅ : DEnv) = D := DEnvUnion_empty_right D
    exact h.symm
  | cons hd tl ih =>
    simp only [List.foldl]
    rw [ih (D ++ hd.snd.traces)]
    -- rewrite the RHS foldl using IH at (∅ ++ hd.snd.traces)
    rw [ih (∅ ++ hd.snd.traces)]
    -- reassociate and eliminate ∅ on the right
    -- (D ++ hd.traces) ++ X = D ++ ((∅ ++ hd.traces) ++ X)
    -- -> D ++ (hd.traces ++ X) = D ++ (∅ ++ (hd.traces ++ X))
    -- -> D ++ (hd.traces ++ X) = D ++ (hd.traces ++ X)
    rw [DEnvUnion_assoc D hd.snd.traces (List.foldl (fun acc p => acc ++ p.snd.traces) ∅ tl)]
    rw [DEnvUnion_assoc (∅ : DEnv) hd.snd.traces
      (List.foldl (fun acc p => acc ++ p.snd.traces) ∅ tl)]
    change
      D ++ (hd.snd.traces ++ List.foldl (fun acc p => acc ++ p.snd.traces) ∅ tl) =
        D ++ (DEnvUnion (∅ : DEnv)
          (hd.snd.traces ++ List.foldl (fun acc p => acc ++ p.snd.traces) ∅ tl))
    rw [DEnvUnion_empty_left]

/-! ### `lookupG`/`updateG` append behavior -/

/-- lookupG in appended GEnv: searches left first. -/
theorem lookupG_append_left {G1 G2 : GEnv} {e : Endpoint} {L : LocalType}
    (h : lookupG G1 e = some L) :
    lookupG (G1 ++ G2) e = some L := by
  induction G1 with
  | nil =>
      simp [lookupG] at h
  | cons hd tl ih =>
      cases hEq : (e == hd.1) with
      | true =>
          have hL : hd.2 = L := by
            simpa [lookupG, List.lookup, hEq] using h
          simp [lookupG, List.lookup, hEq, hL]
      | false =>
          have h' : lookupG tl e = some L := by
            simpa [lookupG, List.lookup, hEq] using h
          have ih' := ih h'
          simpa [lookupG, List.lookup, hEq] using ih'

/-! #### Right lookup fallback -/

/-- lookupG in appended GEnv: if not in left, search right. -/
theorem lookupG_append_right {G1 G2 : GEnv} {e : Endpoint}
    (h : lookupG G1 e = none) :
    lookupG (G1 ++ G2) e = lookupG G2 e := by
  induction G1 with
  | nil =>
      simp [lookupG] at h ⊢
  | cons hd tl ih =>
      cases hEq : (e == hd.1) with
      | true =>
          have : False := by
            simp [lookupG, List.lookup, hEq] at h
          exact this.elim
      | false =>
          have h' : lookupG tl e = none := by
            simpa [lookupG, List.lookup, hEq] using h
          have ih' := ih h'
          simpa [lookupG, List.lookup, hEq] using ih'

/-! #### Right-biased update distribution -/

/-- updateG distributes over append (right) when not in left. -/
theorem updateG_append_right {G1 G2 : GEnv} {e : Endpoint} {L : LocalType}
    (hNotMem : lookupG G1 e = none) :
    updateG (G1 ++ G2) e L = G1 ++ updateG G2 e L := by
  induction G1 with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨e', L'⟩ := hd
    by_cases he : e = e'
    · have : False := by
        have hbeq : (e == e') = true := by
          simp [he]
        simp [lookupG, List.lookup, hbeq] at hNotMem
      exact this.elim
    · have hNotMem' : lookupG tl e = none := by
        have hbeq : (e == e') = false := by
          exact beq_eq_false_iff_ne.mpr he
        simpa [lookupG, List.lookup, hbeq] using hNotMem
      have ih' := ih hNotMem'
      simp [updateG, he, ih', List.cons_append]

/-! ## toGEnv/toDEnv commute with updates -/

/-- Helper: GEnv foldl append comm. -/
theorem GEnv_foldl_append_comm {ν : Type u} [VerificationModel ν]
    (G : GEnv) (store : SessionStore ν) :
    List.foldl (fun acc p => acc ++ p.snd.localTypes) G store =
    G ++ List.foldl (fun acc p => acc ++ p.snd.localTypes) [] store := by
  induction store generalizing G with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl]
    rw [ih (G ++ hd.snd.localTypes)]
    simp only [List.nil_append]
    rw [ih hd.snd.localTypes]
    simp only [List.append_assoc]

/-- Helper: Buffers foldl append comm. -/
theorem Buffers_foldl_append_comm {ν : Type u} [VerificationModel ν]
    (B : Buffers) (store : SessionStore ν) :
    List.foldl (fun acc p => acc ++ SignedBuffers.payloads p.snd.buffers) B store =
    B ++ List.foldl (fun acc p => acc ++ SignedBuffers.payloads p.snd.buffers) [] store := by
  induction store generalizing B with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl]
    rw [ih (B ++ SignedBuffers.payloads hd.snd.buffers)]
    simp only [List.nil_append]
    rw [ih (SignedBuffers.payloads hd.snd.buffers)]
    simp only [List.append_assoc]

/-! ### `toGEnv` Extensional Update Bridge -/

/-- Key bridge for `updateType` at lookup level.
    This captures the extensional behavior of `toGEnv` under updates. -/
theorem SessionStore.toGEnv_updateType {store : SessionStore ν} {e : Endpoint} {L : LocalType}
    (hMem : ∃ st, (e.sid, st) ∈ store)
    (hCons : store.consistent) :
    ∀ e', lookupG (store.updateType e L).toGEnv e' = lookupG (updateG (store.toGEnv) e L) e' := by
  intro e'
  induction store with
  | nil =>
      cases hMem with
      | intro _ h => cases h
  | cons hd tl ih =>
      obtain ⟨sid, st⟩ := hd
      by_cases hsid : sid = e.sid

      -- `toGEnv_updateType`: matching session-id case

      · simp only [SessionStore.updateType, hsid, ↓reduceIte]
        simp only [SessionStore.toGEnv, List.foldl]
        have hFoldUpd :
            List.foldl (fun acc p => acc ++ p.snd.localTypes) (st.updateType e L).localTypes tl =
              (st.updateType e L).localTypes ++ SessionStore.toGEnv tl := by
          unfold SessionStore.toGEnv
          exact GEnv_foldl_append_comm (G := (st.updateType e L).localTypes) (store := tl)
        have hFoldOrig :
            List.foldl (fun acc p => acc ++ p.snd.localTypes) st.localTypes tl =
              st.localTypes ++ SessionStore.toGEnv tl := by
          unfold SessionStore.toGEnv
          exact GEnv_foldl_append_comm (G := st.localTypes) (store := tl)
        simp only [List.nil_append]
        rw [hFoldUpd, hFoldOrig]
        simp only [SessionState.updateType]
        by_cases he' : e' = e

        -- `toGEnv_updateType`: matched endpoint

        · have hLeft : lookupG (updateG st.localTypes e L ++ SessionStore.toGEnv tl) e' = some L := by
            rw [he']
            exact lookupG_append_left
              (G1 := updateG st.localTypes e L)
              (G2 := SessionStore.toGEnv tl)
              (e := e)
              (L := L)
              (lookupG_updateG_eq (env := st.localTypes) (e := e) (L := L))
          have hRight : lookupG (updateG (st.localTypes ++ SessionStore.toGEnv tl) e L) e' = some L := by
            rw [he']
            exact lookupG_updateG_eq (env := st.localTypes ++ SessionStore.toGEnv tl) (e := e) (L := L)
          exact hLeft.trans hRight.symm
        · have hR :
            lookupG (updateG (st.localTypes ++ SessionStore.toGEnv tl) e L) e' =
              lookupG (st.localTypes ++ SessionStore.toGEnv tl) e' :=
              lookupG_updateG_ne (env := st.localTypes ++ SessionStore.toGEnv tl) (e := e) (e' := e') (L := L) he'
          have hL :
              lookupG (updateG st.localTypes e L ++ SessionStore.toGEnv tl) e' =
                lookupG (st.localTypes ++ SessionStore.toGEnv tl) e' := by
            by_cases hLeft : lookupG st.localTypes e' = none
            · have hLeftUpd : lookupG (updateG st.localTypes e L) e' = none := by
                simpa [hLeft] using
                  (lookupG_updateG_ne (env := st.localTypes) (e := e) (e' := e') (L := L) he')
              rw [lookupG_append_right (G1 := updateG st.localTypes e L) (G2 := SessionStore.toGEnv tl)
                (e := e') hLeftUpd]
              rw [lookupG_append_right (G1 := st.localTypes) (G2 := SessionStore.toGEnv tl) (e := e') hLeft]
            · obtain ⟨T, hSome⟩ := Option.ne_none_iff_exists.mp hLeft
              have hSome' : lookupG st.localTypes e' = some T := by
                simpa using hSome.symm
              have hLeftUpd : lookupG (updateG st.localTypes e L) e' = some T := by
                simpa [hSome'] using
                  (lookupG_updateG_ne (env := st.localTypes) (e := e) (e' := e') (L := L) he')
              rw [lookupG_append_left (G1 := updateG st.localTypes e L) (G2 := SessionStore.toGEnv tl)
                (e := e') (L := T) hLeftUpd]
              rw [lookupG_append_left (G1 := st.localTypes) (G2 := SessionStore.toGEnv tl)
                (e := e') (L := T) hSome']
          exact hL.trans (by simpa using hR.symm)

        -- `toGEnv_updateType`: unmatched endpoint

      · have hMem' : ∃ st', (e.sid, st') ∈ tl := by
          obtain ⟨st', hst'⟩ := hMem
          simp only [List.mem_cons] at hst'
          cases hst' with
          | inl hEq =>
              simp only [Prod.mk.injEq] at hEq
              exact (hsid hEq.1.symm).elim
          | inr hTail =>
              exact ⟨st', hTail⟩
        have hCons' : SessionStore.consistent tl := by
          intro sid' st' hIn
          exact hCons sid' st' (List.Mem.tail _ hIn)
        have hHead := hCons sid st (List.Mem.head _)
        have hSidNe : e.sid ≠ st.sid := by
          intro hEq
          exact hsid (hHead.1.symm.trans hEq.symm)
        have hNotMemLeft : lookupG st.localTypes e = none :=
          SessionState.lookupG_none_of_sid_ne hHead.2 hSidNe
        simp only [SessionStore.updateType, hsid, ↓reduceIte]
        simp only [SessionStore.toGEnv, List.foldl]
        have hFoldLeft :
            List.foldl (fun acc p => acc ++ p.snd.localTypes) st.localTypes (SessionStore.updateType tl e L) =
              st.localTypes ++ SessionStore.toGEnv (SessionStore.updateType tl e L) := by
          unfold SessionStore.toGEnv
          exact GEnv_foldl_append_comm (G := st.localTypes) (store := SessionStore.updateType tl e L)
        have hFoldOrig :
            List.foldl (fun acc p => acc ++ p.snd.localTypes) st.localTypes tl =
              st.localTypes ++ SessionStore.toGEnv tl := by
          unfold SessionStore.toGEnv
          exact GEnv_foldl_append_comm (G := st.localTypes) (store := tl)
        simp only [List.nil_append]
        rw [hFoldLeft, hFoldOrig]
        rw [updateG_append_right (G1 := st.localTypes) (G2 := SessionStore.toGEnv tl) (e := e) (L := L) hNotMemLeft]
        by_cases hLeft : lookupG st.localTypes e' = none
        · rw [lookupG_append_right (G1 := st.localTypes) (G2 := SessionStore.toGEnv (SessionStore.updateType tl e L))
            (e := e') hLeft]
          rw [lookupG_append_right (G1 := st.localTypes) (G2 := updateG (SessionStore.toGEnv tl) e L)
            (e := e') hLeft]
          exact ih hMem' hCons'
        · obtain ⟨T, hSome⟩ := Option.ne_none_iff_exists.mp hLeft
          have hSome' : lookupG st.localTypes e' = some T := by
            simpa using hSome.symm
          rw [lookupG_append_left (G1 := st.localTypes) (G2 := SessionStore.toGEnv (SessionStore.updateType tl e L))
            (e := e') (L := T) hSome']
          rw [lookupG_append_left (G1 := st.localTypes) (G2 := updateG (SessionStore.toGEnv tl) e L)
            (e := e') (L := T) hSome']

/-! ### `DEnv` Union Lookup Helpers -/

/-- Key lemma: toDEnv commutes with updateTrace.
    Stated extensionally at lookup level. -/
theorem lookupD_DEnvUnion_left {D1 D2 : DEnv} {e : Edge} {ts : Trace}
    (h : D1.find? e = some ts) :
    lookupD (D1 ++ D2) e = ts := by
  unfold lookupD
  have h' := DEnvUnion_find?_left (D1 := D1) (D2 := D2) (e := e) (ts := ts) h
  simp [h']

theorem lookupD_DEnvUnion_right {D1 D2 : DEnv} {e : Edge}
    (h : D1.find? e = none) :
    lookupD (D1 ++ D2) e = lookupD D2 e := by
  unfold lookupD
  have h' := DEnvUnion_find?_right (D1 := D1) (D2 := D2) (e := e) h
  simp [h']

theorem lookupD_updateD_union {D1 D2 : DEnv} {edge edge' : Edge} {ts : Trace} :
    lookupD (updateD D1 edge ts ++ D2) edge' =
      lookupD (updateD (D1 ++ D2) edge ts) edge' := by
  by_cases heq : edge' = edge
  · have hLeftFind : (updateD D1 edge ts).find? edge' = some ts := by
      rw [heq]
      exact find?_updateD_eq D1 edge ts
    have hLeft : lookupD (updateD D1 edge ts ++ D2) edge' = ts :=
      lookupD_DEnvUnion_left hLeftFind
    have hRightEq : lookupD (updateD (D1 ++ D2) edge ts) edge' = ts := by
      rw [heq]
      exact lookupD_update_eq (D1 ++ D2) edge ts
    calc
      lookupD (updateD D1 edge ts ++ D2) edge' = ts := hLeft
      _ = lookupD (updateD (D1 ++ D2) edge ts) edge' := hRightEq.symm
  · have hRight :
        lookupD (updateD (D1 ++ D2) edge ts) edge' = lookupD (D1 ++ D2) edge' :=
        lookupD_update_neq (D1 ++ D2) edge edge' ts (Ne.symm heq)
    have hLeft :
        lookupD (updateD D1 edge ts ++ D2) edge' = lookupD (D1 ++ D2) edge' := by
      by_cases hFind : D1.find? edge' = none
      · have hFindUpd : (updateD D1 edge ts).find? edge' = none := by
          rw [find?_updateD_neq D1 edge edge' ts (Ne.symm heq)]
          exact hFind
        rw [lookupD_DEnvUnion_right hFindUpd]
        rw [lookupD_DEnvUnion_right hFind]
      · obtain ⟨ts', hSomeRaw⟩ := Option.ne_none_iff_exists.mp hFind
        have hSome : D1.find? edge' = some ts' := by
          simpa using hSomeRaw.symm
        have hSomeUpd : (updateD D1 edge ts).find? edge' = some ts' := by
          rw [find?_updateD_neq D1 edge edge' ts (Ne.symm heq)]
          exact hSome
        rw [lookupD_DEnvUnion_left hSomeUpd]
        rw [lookupD_DEnvUnion_left hSome]
    exact hLeft.trans (by simpa using hRight.symm)

/-! ### `toDEnv` Extensional Update Bridge -/

theorem SessionStore.toDEnv_updateTrace {store : SessionStore ν} {edge : Edge} {ts : List ValType}
    (hMem : ∃ st, (edge.sid, st) ∈ store)
    (hCons : store.consistent) :
    ∀ edge', lookupD (store.updateTrace edge ts).toDEnv edge' =
      lookupD (updateD (store.toDEnv) edge ts) edge' := by
  intro edge'
  induction store with
  | nil =>
      cases hMem with
      | intro _ h => cases h
  | cons hd tl ih =>
      obtain ⟨sid, st⟩ := hd
      by_cases hsid : sid = edge.sid

      -- `toDEnv_updateTrace`: matching session-id case

      · simp only [SessionStore.updateTrace, hsid, ↓reduceIte]
        simp only [SessionStore.toDEnv, List.foldl]
        have hFoldUpd :
            List.foldl (fun acc p => acc ++ p.snd.traces) (st.updateTrace edge ts).traces tl =
              (st.updateTrace edge ts).traces ++ SessionStore.toDEnv tl := by
          simpa [SessionStore.toDEnv] using
            (DEnv_foldl_append_comm (D := (st.updateTrace edge ts).traces) (store := tl))
        have hFoldOrig :
            List.foldl (fun acc p => acc ++ p.snd.traces) st.traces tl =
              st.traces ++ SessionStore.toDEnv tl := by
          simpa [SessionStore.toDEnv] using
            (DEnv_foldl_append_comm (D := st.traces) (store := tl))
        have hSeedUpd : (∅ : DEnv) ++ (st.updateTrace edge ts).traces = (st.updateTrace edge ts).traces :=
          DEnvUnion_empty_left (D := (st.updateTrace edge ts).traces)
        have hSeed : (∅ : DEnv) ++ st.traces = st.traces := DEnvUnion_empty_left (D := st.traces)
        rw [hSeedUpd, hSeed]
        rw [hFoldUpd, hFoldOrig]
        simp only [SessionState.updateTrace]
        exact lookupD_updateD_union (D1 := st.traces) (D2 := SessionStore.toDEnv tl)
          (edge := edge) (edge' := edge') (ts := ts)

      -- `toDEnv_updateTrace`: non-matching session-id case

      · have hMem' : ∃ st', (edge.sid, st') ∈ tl := by
          obtain ⟨st', hst'⟩ := hMem
          simp only [List.mem_cons] at hst'
          cases hst' with
          | inl hEq =>
              simp only [Prod.mk.injEq] at hEq
              exact (hsid hEq.1.symm).elim
          | inr hTail =>
              exact ⟨st', hTail⟩
        have hCons' : SessionStore.consistent tl := by
          intro sid' st' hIn
          exact hCons sid' st' (List.Mem.tail _ hIn)
        have hHead := hCons sid st (List.Mem.head _)
        have hSidNe : edge.sid ≠ st.sid := by
          intro hEq
          exact hsid (hHead.1.symm.trans hEq.symm)
        have hNoneLeft : st.traces.find? edge = none :=
          SessionState.traces_find?_none_of_sid_ne hHead.2 hSidNe
        simp only [SessionStore.updateTrace, hsid, ↓reduceIte]
        simp only [SessionStore.toDEnv, List.foldl]
        have hFoldLeft :
            List.foldl (fun acc p => acc ++ p.snd.traces) ((∅ : DEnv) ++ st.traces) (SessionStore.updateTrace tl edge ts) =
              ((∅ : DEnv) ++ st.traces) ++ SessionStore.toDEnv (SessionStore.updateTrace tl edge ts) := by
          simpa [SessionStore.toDEnv] using
            (DEnv_foldl_append_comm (D := ((∅ : DEnv) ++ st.traces)) (store := SessionStore.updateTrace tl edge ts))
        have hFoldOrig :
            List.foldl (fun acc p => acc ++ p.snd.traces) ((∅ : DEnv) ++ st.traces) tl =
              ((∅ : DEnv) ++ st.traces) ++ SessionStore.toDEnv tl := by
          simpa [SessionStore.toDEnv] using
            (DEnv_foldl_append_comm (D := ((∅ : DEnv) ++ st.traces)) (store := tl))
        rw [hFoldLeft, hFoldOrig]
        have hEqLeft : ((∅ : DEnv) ++ st.traces) = st.traces := DEnvUnion_empty_left (D := st.traces)
        have hNoneLeft' : ((∅ : DEnv) ++ st.traces).find? edge = none := by
          simpa [hEqLeft] using hNoneLeft
        rw [updateD_DEnvUnion_right (D1 := ((∅ : DEnv) ++ st.traces)) (D2 := SessionStore.toDEnv tl)
          (e := edge) (ts := ts) hNoneLeft']
        by_cases hFind : st.traces.find? edge' = none
        · have hFind' : ((∅ : DEnv) ++ st.traces).find? edge' = none := by
            simpa [hEqLeft] using hFind
          rw [lookupD_DEnvUnion_right hFind']
          rw [lookupD_DEnvUnion_right hFind']
          exact ih hMem' hCons'
        · obtain ⟨ts', hSomeRaw⟩ := Option.ne_none_iff_exists.mp hFind
          have hSome : st.traces.find? edge' = some ts' := by
            simpa using hSomeRaw.symm
          have hSome' : ((∅ : DEnv) ++ st.traces).find? edge' = some ts' := by
            simpa [hEqLeft] using hSome
          rw [lookupD_DEnvUnion_left hSome']
          rw [lookupD_DEnvUnion_left hSome']

/-! ### Projection Invariance Under Orthogonal Updates -/

/-- toDEnv is unchanged by updateType (type update doesn't affect traces). -/
theorem SessionStore.toDEnv_updateType {store : SessionStore ν} {e : Endpoint} {L : LocalType} :
    (store.updateType e L).toDEnv = store.toDEnv := by
  -- Type updates only modify localTypes, not traces
  induction store with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨sid, st⟩ := hd
      by_cases hsid : sid = e.sid
      · simp [SessionStore.updateType, SessionStore.toDEnv, hsid, SessionState.updateType]
      · simp only [SessionStore.updateType, hsid, ↓reduceIte]
        simp only [SessionStore.toDEnv, List.foldl]
        have hSeed : (∅ : DEnv) ++ st.traces = st.traces := DEnvUnion_empty_left (D := st.traces)
        rw [hSeed]
        rw [DEnv_foldl_append_comm (D := st.traces) (store := SessionStore.updateType tl e L)]
        rw [DEnv_foldl_append_comm (D := st.traces) (store := tl)]
        simpa [SessionStore.toDEnv] using congrArg (fun D => st.traces ++ D) ih

/-! ## `toGEnv` Invariance Under Trace Updates -/

/-- toGEnv is unchanged by updateTrace (trace update doesn't affect types). -/
theorem SessionStore.toGEnv_updateTrace {store : SessionStore ν} {edge : Edge} {ts : List ValType} :
    (store.updateTrace edge ts).toGEnv = store.toGEnv := by
  -- Trace updates only modify traces, not localTypes
  induction store with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨sid, st⟩ := hd
      by_cases hsid : sid = edge.sid
      · simp [SessionStore.updateTrace, SessionStore.toGEnv, hsid, SessionState.updateTrace]
      · simp only [SessionStore.updateTrace, hsid, ↓reduceIte]
        simp only [SessionStore.toGEnv, List.foldl, List.nil_append]
        rw [GEnv_foldl_append_comm (G := st.localTypes) (store := SessionStore.updateTrace tl edge ts)]
        rw [GEnv_foldl_append_comm (G := st.localTypes) (store := tl)]
        simpa [SessionStore.toGEnv] using congrArg (fun G => st.localTypes ++ G) ih

/-! ## `toBuffers` Invariance Under Type Updates -/

/-- toBuffers is unchanged by updateType (type update doesn't affect buffers). -/
theorem SessionStore.toBuffers_updateType {store : SessionStore ν} {e : Endpoint} {L : LocalType} :
    (store.updateType e L).toBuffers = store.toBuffers := by
  -- Type updates only modify localTypes, not buffers
  induction store with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨sid, st⟩ := hd
      by_cases hsid : sid = e.sid
      · simp [SessionStore.updateType, SessionStore.toBuffers, hsid, SessionState.updateType]
      · simp only [SessionStore.updateType, hsid, ↓reduceIte]
        simp only [SessionStore.toBuffers, List.foldl, List.nil_append]
        rw [Buffers_foldl_append_comm (B := SignedBuffers.payloads st.buffers)
          (store := SessionStore.updateType tl e L)]
        rw [Buffers_foldl_append_comm (B := SignedBuffers.payloads st.buffers) (store := tl)]
        simpa [SessionStore.toBuffers] using
          congrArg (fun B => SignedBuffers.payloads st.buffers ++ B) ih

/-! ## `toBuffers` Invariance Under Trace Updates -/

/-- toBuffers is unchanged by updateTrace (trace update doesn't affect buffers). -/
theorem SessionStore.toBuffers_updateTrace {store : SessionStore ν} {edge : Edge} {ts : List ValType} :
    (store.updateTrace edge ts).toBuffers = store.toBuffers := by
  -- Trace updates only modify traces, not buffers
  induction store with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨sid, st⟩ := hd
      by_cases hsid : sid = edge.sid
      · simp [SessionStore.updateTrace, SessionStore.toBuffers, hsid, SessionState.updateTrace]
      · simp only [SessionStore.updateTrace, hsid, ↓reduceIte]
        simp only [SessionStore.toBuffers, List.foldl, List.nil_append]
        rw [Buffers_foldl_append_comm (B := SignedBuffers.payloads st.buffers)
          (store := SessionStore.updateTrace tl edge ts)]
        rw [Buffers_foldl_append_comm (B := SignedBuffers.payloads st.buffers) (store := tl)]
        simpa [SessionStore.toBuffers] using
          congrArg (fun B => SignedBuffers.payloads st.buffers ++ B) ih

/-! ## WFSessionStore Preservation

WFSessionStore-specific lemmas are in `Runtime.Resources.Arena.WFSessionStore`.
-/
