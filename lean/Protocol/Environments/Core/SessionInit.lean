import Protocol.Environments.Core.DEnv

/-! # Protocol.Environments.Core.SessionInit

Session/buffer initialization and environment-union lemmas.
-/

/-
The Problem. Session initialization and environment unions must preserve lookup
behavior required by protocol semantics.

Solution Structure. Proves initialization and union/associativity lemmas.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical
open Batteries

section

/-! ## Session Management -/

/-- Initialize empty buffers for all directed edges between roles. -/
def initBuffers (sid : SessionId) (roles : RoleSet) : Buffers :=
  (RoleSet.allEdges sid roles).map fun e => (e, [])

/-- Initialize empty type traces for all directed edges. -/
def initDEnv (_sid : SessionId) (_roles : RoleSet) : DEnv :=
  ∅

/-- Empty DEnv lookup via `find?` always returns none. -/
@[simp] theorem DEnv_find?_empty (e : Edge) :
    (∅ : DEnv).find? e = none := by
  simp [DEnv.find?, DEnv_map_find?_empty]

/-! ## DEnvUnion Identity Laws -/
theorem DEnvUnion_empty_right (D : DEnv) : DEnvUnion D (∅ : DEnv) = D := by
  apply DEnv_eq_of_find?_eq
  intro e
  simp only [DEnvUnion, DEnv_find?_ofMap]
  rw [RBMap.foldl_eq_foldl_toList]
  have : (∅ : DEnv).map.toList = [] := rfl
  rw [this, List.foldl_nil]
  simp [DEnv.find?]

theorem DEnvUnion_empty_left (D : DEnv) : DEnvUnion (∅ : DEnv) D = D := by
  apply DEnv_eq_of_find?_eq
  intro e
  -- (DEnvUnion ∅ D).find? e = D.find? e
  -- DEnvUnion folds D.map into (∅).map with conditional insert.
  -- Starting from empty, every key is new, so all inserts happen.
  -- The result has the same find? as D.map.
  simp only [DEnvUnion, DEnv_find?_ofMap]
  rw [RBMap.foldl_eq_foldl_toList]
  -- Goal: (DEnv.ofMap (D.map.toList.foldl f (∅).map)).find? e = D.find? e
  -- where f is the conditional insert.
  -- Suffices to show the foldl equals rbmapOfList D.map.toList
  suffices hFold :
    D.map.toList.foldl (fun acc (p : Edge × Trace) =>
      match acc.find? p.1 with
      | some _ => acc
      | none => acc.insert p.1 p.2) (∅ : DEnv).map =
    rbmapOfList D.map.toList by
    have hFoldFind :
        (D.map.toList.foldl (fun acc (p : Edge × Trace) =>
          match acc.find? p.1 with
          | some _ => acc
          | none => acc.insert p.1 p.2) (∅ : DEnv).map).find? e =
          (rbmapOfList D.map.toList).find? e := by
      exact congrArg (fun m => m.find? e) hFold
    exact hFoldFind.trans (rbmapOfList_toList_find? D.map e)
  -- Empty-Left Proof: Pairwise Fold Alignment
  -- Since we start from empty, acc.find? is always none for unseen keys.
  -- With unique keys (from sorted), every key is unseen.
  have hSorted : D.map.toList.Pairwise edgeCmpLT := by
    simpa [edgeCmpLT] using RBMap.toList_sorted (t := D.map)
  unfold rbmapOfList
  generalize D.map.toList = pairs at hSorted
  suffices h : ∀ (acc : RBMap Edge Trace compare) (ps : List (Edge × Trace)),
    ps.Pairwise edgeCmpLT →
    (∀ p ∈ ps, acc.find? p.1 = none) →
    ps.foldl (fun acc (p : Edge × Trace) =>
      match acc.find? p.1 with
      | some _ => acc
      | none => acc.insert p.1 p.2) acc =
    ps.foldl (fun r (p : Edge × Trace) => r.insert p.1 p.2) acc from
    h _ pairs hSorted (fun p _ => rbmap_find?_empty p.1)
  intro acc ps hPW
  induction ps generalizing acc with
  | nil => intro _; rfl
  | cons p ps ih =>
    intro hNone
    simp only [List.foldl_cons]
    have hNoneP := hNone p (by simp)
    rw [hNoneP]
    have hPW' := (List.pairwise_cons.1 hPW)
    refine ih (acc := acc.insert p.1 p.2) hPW'.2 ?_
/- ## Structured Block 1 -/
    intro q hq
    have hNoneQ := hNone q (List.mem_cons_of_mem p hq)
    have hLT := hPW'.1 q hq
    have hCmpLT := edgeCmpLT_eq_lt hLT
    have hNe : compare q.1 p.1 ≠ .eq := by
      intro heq
      have := Std.OrientedCmp.eq_swap (cmp := compare) (a := q.1) (b := p.1)
      simp [heq, hCmpLT] at this
    have := RBMap.find?_insert_of_ne (t := acc) (k := p.1) (v := p.2) (k' := q.1) hNe
    simpa [this] using hNoneQ

/-! ## DEnvUnion Lookup when Key is in Left -/
/-- DEnvUnion find? when key is in left. -/
theorem DEnvUnion_find?_left {D1 D2 : DEnv} {e : Edge} {ts : Trace}
    (h : D1.find? e = some ts) :
    (D1 ++ D2).find? e = some ts := by
  -- Key in D1.map means conditional fold won't overwrite it
  have h0 : D1.map.find? e = some ts := by
    simpa [DEnv.find?] using h
  change (DEnvUnion D1 D2).find? e = some ts
  simp only [DEnvUnion, DEnv_find?_ofMap]
  rw [RBMap.foldl_eq_foldl_toList]
  -- Fold over D2.map.toList preserves existing keys in D1.map.
  let f := fun (acc : RBMap Edge Trace compare) (p : Edge × Trace) =>
    match acc.find? p.1 with
    | some _ => acc
    | none => acc.insert p.1 p.2
  have hfold :
      ∀ (ps : List (Edge × Trace)) (acc : RBMap Edge Trace compare),
        acc.find? e = some ts →
        (ps.foldl f acc).find? e = some ts := by
    intro ps acc hacc
    induction ps generalizing acc with
    | nil =>
        simpa using hacc
    | cons p ps ih =>
        cases hfind : acc.find? p.1 with
        | some v =>
            simpa [List.foldl_cons, f, hfind] using ih (acc := acc) hacc
        | none =>
            have hne : e ≠ p.1 := by
              intro hEq
              subst hEq
              have : (none : Option Trace) = some ts := by
                exact hfind.symm.trans hacc
              cases this
            have hne' : compare e p.1 ≠ .eq := by
              intro hEq
              exact hne ((Edge.compare_eq_iff_eq e p.1).1 hEq)
            have hinsert :
                (acc.insert p.1 p.2).find? e = acc.find? e := by
              simpa using
                (RBMap.find?_insert_of_ne (t := acc) (k := p.1) (v := p.2) (k' := e) hne')
            have hacc' : (acc.insert p.1 p.2).find? e = some ts := by
              simpa [hinsert] using hacc
            simpa [List.foldl_cons, f, hfind] using
              ih (acc := acc.insert p.1 p.2) hacc'
  simpa [f] using hfold (ps := D2.map.toList) (acc := D1.map) h0

/-! ## DEnvUnion Lookup when Key is Absent from Left -/
/-- DEnvUnion find? when key not in left. -/
theorem DEnvUnion_find?_right {D1 D2 : DEnv} {e : Edge}
    (h : D1.find? e = none) :
    (D1 ++ D2).find? e = D2.find? e := by
  -- Key not in D1.map means it can only come from D2
  have h0 : D1.map.find? e = none := by
    simpa [DEnv.find?] using h
  change (DEnvUnion D1 D2).find? e = D2.find? e
  simp only [DEnvUnion, DEnv_find?_ofMap]
  rw [RBMap.foldl_eq_foldl_toList]
  let f := fun (acc : RBMap Edge Trace compare) (p : Edge × Trace) =>
    match acc.find? p.1 with
    | some _ => acc
    | none => acc.insert p.1 p.2
  -- Folding preserves equality of find? at e when the initial maps agree on e.
  have hfold :
      ∀ (ps : List (Edge × Trace)) (acc1 acc2 : RBMap Edge Trace compare),
        acc1.find? e = acc2.find? e →
        (ps.foldl f acc1).find? e = (ps.foldl f acc2).find? e := by
    intro ps acc1 acc2 hEq
    induction ps generalizing acc1 acc2 with
    | nil =>
        simpa [f] using hEq
    | cons p ps ih =>
        by_cases hkey : p.1 = e
        · cases h1 : acc1.find? e with
          | some v =>
              have h2 : acc2.find? e = some v := by
                simpa [h1] using hEq.symm
              simpa [List.foldl_cons, f, hkey, h1, h2] using
                ih (acc1 := acc1) (acc2 := acc2) hEq
          | none =>
              have h2 : acc2.find? e = none := by
                simpa [h1] using hEq.symm
              have hEq1 : (acc1.insert e p.2).find? e = some p.2 := by
                have hcmp : compare e e = .eq := by simp
                simpa using
                  (RBMap.find?_insert_of_eq (t := acc1) (k := e) (v := p.2) (k' := e) hcmp)
              have hEq2 : (acc2.insert e p.2).find? e = some p.2 := by
                have hcmp : compare e e = .eq := by simp
                simpa using
                  (RBMap.find?_insert_of_eq (t := acc2) (k := e) (v := p.2) (k' := e) hcmp)
              have hEq' :
                  (acc1.insert e p.2).find? e = (acc2.insert e p.2).find? e := by
                simp [hEq1, hEq2]
              simpa [List.foldl_cons, f, hkey, h1, h2] using
                ih (acc1 := acc1.insert e p.2) (acc2 := acc2.insert e p.2) hEq'
        -- Empty-Left Lookup: Non-target Key Case
        · have hne' : compare e p.1 ≠ .eq := by
            intro hEq
            apply hkey
            exact (Edge.compare_eq_iff_eq e p.1).1 hEq |>.symm
          have hstep1 : (f acc1 p).find? e = acc1.find? e := by
            cases h1 : acc1.find? p.1 with
/- ## Structured Block 2 -/
            | some v =>
                simp [f, h1]
            | none =>
                have hfind :=
                  RBMap.find?_insert_of_ne (t := acc1) (k := p.1) (v := p.2) (k' := e) hne'
                simpa [f, h1] using hfind
          have hstep2 : (f acc2 p).find? e = acc2.find? e := by
            cases h2 : acc2.find? p.1 with
            | some v =>
                simp [f, h2]
            | none =>
                have hfind :=
                  RBMap.find?_insert_of_ne (t := acc2) (k := p.1) (v := p.2) (k' := e) hne'
                simpa [f, h2] using hfind
          have hEq' : (f acc1 p).find? e = (f acc2 p).find? e := by
            simpa [hstep1, hstep2] using hEq
          simpa [List.foldl_cons, f] using
            ih (acc1 := f acc1 p) (acc2 := f acc2 p) hEq'
  have hEqFold :
      (D2.map.toList.foldl f D1.map).find? e =
      (D2.map.toList.foldl f (∅ : RBMap Edge Trace compare)).find? e := by
    have hEmpty : (∅ : RBMap Edge Trace compare).find? e = none := by
      simp
    exact hfold (ps := D2.map.toList) (acc1 := D1.map) (acc2 := (∅ : RBMap Edge Trace compare))
      (by simpa [hEmpty] using h0)
  have hEmptyUnion :
      (DEnvUnion (∅ : DEnv) D2).find? e = D2.find? e := by
    simpa using congrArg (fun D => D.find? e) (DEnvUnion_empty_left (D := D2))
  have hEmptyFold :
      (D2.map.toList.foldl f (∅ : RBMap Edge Trace compare)).find? e = D2.find? e := by
    have hEmptyUnion' :
        (RBMap.foldl (fun acc k v =>
          match acc.find? k with
          | some _ => acc
          | none => acc.insert k v) (∅ : RBMap Edge Trace compare) D2.map).find? e =
        D2.find? e := by
      simpa [DEnvUnion, DEnv_find?_ofMap] using hEmptyUnion
    simpa [RBMap.foldl_eq_foldl_toList] using hEmptyUnion'
  exact hEqFold.trans hEmptyFold

/-! ## updateD Distribution over DEnvUnion -/
/-- updateD distributes over DEnvUnion when key not in left. -/
theorem updateD_DEnvUnion_right {D1 D2 : DEnv} {e : Edge} {ts : List ValType}
    (h : D1.find? e = none) :
    updateD (D1 ++ D2) e ts = D1 ++ updateD D2 e ts := by
  apply DEnv_eq_of_find?_eq
  intro e'
  by_cases he' : e' = e
  · subst e'
    -- updated key
    have hLeft : (updateD (D1 ++ D2) e ts).find? e = some ts := by
      have hEq : compare e e = .eq := by simp
      have hfind : ((D1 ++ D2).map.insert e ts).find? e = some ts := by
        simpa using
          (RBMap.find?_insert_of_eq (t := (D1 ++ D2).map) (k := e) (v := ts) (k' := e) hEq)
      simpa [updateD, DEnv_find?_ofMap] using hfind
    have hRight :
        (D1 ++ updateD D2 e ts).find? e = some ts := by
      have hnone : D1.find? e = none := h
      have hRight' := DEnvUnion_find?_right (D1 := D1) (D2 := updateD D2 e ts) (e := e) hnone
      -- reduce to updateD on right
      have hEq : compare e e = .eq := by simp
      have hUpd : (updateD D2 e ts).find? e = some ts := by
        have hfind : (D2.map.insert e ts).find? e = some ts := by
          simpa using
            (RBMap.find?_insert_of_eq (t := D2.map) (k := e) (v := ts) (k' := e) hEq)
        simpa [updateD, DEnv_find?_ofMap] using hfind
      simpa [hUpd] using hRight'
    simp [hLeft, hRight]
  -- updateD Distribution: Non-updated Keys
  · -- other keys unchanged
    have hLeft :
        (updateD (D1 ++ D2) e ts).find? e' = (D1 ++ D2).find? e' := by
      have hne' : compare e' e ≠ .eq := by
        intro hEq
        exact he' ((Edge.compare_eq_iff_eq e' e).1 hEq)
      have hfind :
          ((D1 ++ D2).map.insert e ts).find? e' = (D1 ++ D2).map.find? e' := by
        simpa using
          (RBMap.find?_insert_of_ne (t := (D1 ++ D2).map) (k := e) (v := ts) (k' := e') hne')
      simpa [updateD, DEnv_find?_ofMap] using hfind
    cases hfind : D1.find? e' with
    | some ts' =>
        -- key in left; both unions agree on left value
        have hLeftUnion := DEnvUnion_find?_left (D1 := D1) (D2 := D2) (e := e') (ts := ts') hfind
        have hRightUnion :=
          DEnvUnion_find?_left (D1 := D1) (D2 := updateD D2 e ts) (e := e') (ts := ts') hfind
        simp [hLeft, hLeftUnion, hRightUnion]
    | none =>
        -- key not in left; reduce to right
        have hLeftUnion := DEnvUnion_find?_right (D1 := D1) (D2 := D2) (e := e') hfind
        have hRightUnion :=
          DEnvUnion_find?_right (D1 := D1) (D2 := updateD D2 e ts) (e := e') hfind
        -- updateD doesn't affect e' (since e' ≠ e)
        have hUpd :
            (updateD D2 e ts).find? e' = D2.find? e' := by
          have hne' : compare e' e ≠ .eq := by
            intro hEq
/- ## Structured Block 3 -/
            exact he' ((Edge.compare_eq_iff_eq e' e).1 hEq)
          have hfind :
              (D2.map.insert e ts).find? e' = D2.map.find? e' := by
            simpa using
              (RBMap.find?_insert_of_ne (t := D2.map) (k := e) (v := ts) (k' := e') hne')
          simpa [updateD, DEnv_find?_ofMap] using hfind
        simp [hLeft, hLeftUnion, hRightUnion, hUpd]

/-! ## DEnvUnion Associativity -/
/-- DEnvUnion is associative. -/
theorem DEnvUnion_assoc (D1 D2 D3 : DEnv) : (D1 ++ D2) ++ D3 = D1 ++ (D2 ++ D3) := by
  apply DEnv_eq_of_find?_eq
  intro e
  cases h1 : D1.find? e with
  | some ts =>
      -- in left, both sides pick left
      have hLeft :=
        DEnvUnion_find?_left (D1 := D1 ++ D2) (D2 := D3) (e := e) (ts := ts)
          (DEnvUnion_find?_left (D1 := D1) (D2 := D2) (e := e) (ts := ts) h1)
      have hRight :=
        DEnvUnion_find?_left (D1 := D1) (D2 := D2 ++ D3) (e := e) (ts := ts) h1
      simp [hLeft, hRight]
  | none =>
      -- not in left; reduce to D2/D3
      have hD1none : D1.find? e = none := by simpa using h1
      have hD12 : (D1 ++ D2).find? e = D2.find? e :=
        DEnvUnion_find?_right (D1 := D1) (D2 := D2) (e := e) hD1none
      cases h2 : D2.find? e with
      | some ts =>
          have hLeft :=
            DEnvUnion_find?_left (D1 := D1 ++ D2) (D2 := D3) (e := e) (ts := ts) (by simp [hD12, h2])
          have hRight1 :=
            DEnvUnion_find?_right (D1 := D1) (D2 := D2 ++ D3) (e := e) hD1none
          have hRight2 :=
            DEnvUnion_find?_left (D1 := D2) (D2 := D3) (e := e) (ts := ts) h2
          simp [hLeft, hRight1, hRight2]
      | none =>
          have hLeft :=
            DEnvUnion_find?_right (D1 := D1 ++ D2) (D2 := D3) (e := e) (by simp [hD12, h2])
          have hRight1 :=
            DEnvUnion_find?_right (D1 := D1) (D2 := D2 ++ D3) (e := e) hD1none
          have hRight2 :=
            DEnvUnion_find?_right (D1 := D2) (D2 := D3) (e := e) h2
          simp [hLeft, hRight1, hRight2]

/-! ## initBuffers Membership Lookup -/
/-- Looking up an edge in initBuffers returns empty if edge is in allEdges. -/
theorem initBuffers_lookup_mem (sid : SessionId) (roles : RoleSet) (e : Edge)
    (hMem : e ∈ RoleSet.allEdges sid roles) :
    (initBuffers sid roles).lookup e = some [] := by
  simp only [initBuffers]
  generalize hEdges : RoleSet.allEdges sid roles = edges at hMem
  clear hEdges
  induction edges with
  | nil => simp only [List.mem_nil_iff] at hMem
  | cons hd tl ih =>
    simp only [List.map, List.lookup]
    simp only [List.mem_cons] at hMem
    cases hMem with
    | inl heq =>
      subst heq
      simp only [beq_self_eq_true]
    | inr hTl =>
      by_cases heq : e = hd
      · subst heq; simp only [beq_self_eq_true]
      · have hNeq : (e == hd) = false := beq_eq_false_iff_ne.mpr heq
        simp only [hNeq]
        exact ih hTl

/-! ## initDEnv Trivial Lookup Lemmas -/
/-- Looking up an edge in initDEnv returns empty if edge is in allEdges. -/
theorem initDEnv_lookup_mem (sid : SessionId) (roles : RoleSet) (e : Edge)
    (_hMem : e ∈ RoleSet.allEdges sid roles) :
    lookupD (initDEnv sid roles) e = [] := by
  simp [initDEnv, lookupD]

/-- Looking up an edge with a different sid in initDEnv returns none. -/
theorem initDEnv_lookup_none (sid : SessionId) (roles : RoleSet) (e : Edge)
    (_hne : e.sid ≠ sid) :
    lookupD (initDEnv sid roles) e = [] := by
  simp [initDEnv, lookupD]

/-! ## initBuffers Non-membership from Lookup None -/
/-- If initBuffers returns none, the edge is not in the role edges. -/
theorem initBuffers_not_mem_of_lookup_none (sid : SessionId) (roles : RoleSet) (e : Edge)
    (h : (initBuffers sid roles).lookup e = none) :
    e ∉ RoleSet.allEdges sid roles := by
  -- Any edge in allEdges would be found with an empty buffer.
  intro hMem
  have hSome := initBuffers_lookup_mem sid roles e hMem
  exact Option.noConfusion (hSome.symm.trans h)

/-! ## initBuffers Lookup None for Non-members -/
/-- initBuffers returns none for edges not in allEdges. -/
theorem initBuffers_lookup_none_of_notin (sid : SessionId) (roles : RoleSet) (e : Edge)
    (hNot : e ∉ RoleSet.allEdges sid roles) :
    (initBuffers sid roles).lookup e = none := by
  simp only [initBuffers]
  generalize hEdges : RoleSet.allEdges sid roles = edges at hNot
  clear hEdges
  induction edges with
  | nil =>
      simp
  | cons hd tl ih =>
      simp only [List.mem_cons, not_or] at hNot
      simp only [List.map, List.lookup]
      have hne : (e == hd) = false := beq_eq_false_iff_ne.mpr hNot.1
      simp only [hne]
      exact ih hNot.2

/-! ## initBuffers Session-Mismatch Lookup None -/
/-- Looking up an edge with a different sid in initBuffers returns none. -/
theorem initBuffers_lookup_none (sid : SessionId) (roles : RoleSet) (e : Edge)
    (hne : e.sid ≠ sid) :
    (initBuffers sid roles).lookup e = none := by
  simp only [initBuffers]
  -- Every edge in allEdges has .sid = sid, so e cannot be in the list
  have hNotIn : e ∉ RoleSet.allEdges sid roles := by
    intro hmem
    exact hne (RoleSet.allEdges_sid sid roles e hmem)
  -- Use induction with the membership constraint carried through
  generalize hlist : RoleSet.allEdges sid roles = edges at hNotIn
  clear hlist
  induction edges with
  | nil => simp only [List.map, List.lookup]
  | cons hd tl ih =>
    simp only [List.mem_cons, not_or] at hNotIn
    simp only [List.map, List.lookup]
    have hNeEdge : e ≠ hd := hNotIn.1
    have hBeqFalse : (e == hd) = false := beq_eq_false_iff_ne.mpr hNeEdge
    simp only [hBeqFalse]
    exact ih hNotIn.2

/-! ## initDEnv Non-membership Lookup None -/
/-- initDEnv has no entry for edges outside allEdges. -/
theorem initDEnv_find?_none_of_notin (sid : SessionId) (roles : RoleSet) (e : Edge)
    (_hNot : e ∉ RoleSet.allEdges sid roles) :
    (initDEnv sid roles).find? e = none := by
  simp [initDEnv, DEnv.find?, DEnv_map_find?_empty]


end
