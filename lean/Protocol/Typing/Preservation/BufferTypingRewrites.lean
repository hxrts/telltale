import Protocol.Typing.Preservation.StoreTypingFrames

/-! # Buffer Typing Rewrites

Rewriting lemmas for `BuffersTyped`, allowing DEnv substitution when
trace lookups are equivalent, and update lemmas for RBMap-based DEnv. -/

/-
The Problem. `BuffersTyped G D bufs` depends on trace lookups in D.
When we restructure D (e.g., through updates or appends), we need to
show the rewritten D still yields the same lookups.

Solution Structure. Prove `BuffersTyped_rewriteD` for trace-equivalent
substitution. Provide `findD_update_eq` and `findD_update_neq` for
RBMap-based DEnv update semantics.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical
open Batteries

section

/-! ## GEnv Weakening -/

theorem BuffersTyped_weakenG
    {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} {bufs : Buffers} :
    BuffersTyped (G₁ ++ G₂) (D₁ ++ D₂) bufs →
    (∀ e L, lookupG (G₁ ++ G₂) e = some L → lookupG (G₁ ++ G₂) e = some L) →
    BuffersTyped (G₁ ++ G₂) (D₁ ++ D₂) bufs := by
  intro hBT _; exact hBT

theorem BuffersTyped_rewriteD
    {G : GEnv} {D D' : DEnv} {bufs : Buffers} :
    (∀ e, lookupD D e = lookupD D' e) →
    BuffersTyped G D bufs →
    BuffersTyped G D' bufs := by
  intro hEq hBT e
  rcases hBT e with ⟨hLen, hTyping⟩
  refine ⟨?_, ?_⟩
  · simpa [hEq e] using hLen
  · intro i hi
    simpa [hEq e] using hTyping i hi

lemma findD_update_eq (env : DEnv) (e : Edge) (ts : List ValType) :
    (updateD env e ts).find? e = some ts := by
  have hEq : compare e e = .eq := by
    simp
  simpa [updateD] using
    (RBMap.find?_insert_of_eq (t := env.map) (k := e) (v := ts) (k' := e) hEq)

lemma findD_update_neq (env : DEnv) (e e' : Edge) (ts : List ValType) (hne : e ≠ e') :
    (updateD env e ts).find? e' = env.find? e' := by
  have hne' : compare e' e ≠ .eq := by
    intro hEq
    exact hne ((Edge.compare_eq_iff_eq e' e).1 hEq).symm
  have h' : (env.map.insert e ts).find? e' = env.map.find? e' := by
    simpa using
      (RBMap.find?_insert_of_ne (t := env.map) (k := e) (v := ts) (k' := e') hne')
  have h'' : (updateD env e ts).find? e' = env.map.find? e' := by
    simpa [updateD] using h'
  simpa [DEnv.find?] using h''

lemma lookupD_append_left_of_find {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType} :
    D₁.find? e = some ts →
    lookupD (D₁ ++ D₂) e = ts := by
  intro hFind
  have hLeft := findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) hFind
  simp [lookupD, hLeft]

lemma lookupD_updateD_append_left {D D₂ : DEnv} {e e' : Edge} {ts : List ValType} :
    lookupD (updateD (D ++ D₂) e ts) e' = lookupD (updateD D e ts ++ D₂) e' := by
  by_cases hEq : e' = e
  · cases hEq
    -- Both sides update e to ts.
    have hFind : (updateD D e ts).find? e = some ts := findD_update_eq (env:=D) (e:=e) (ts:=ts)
    have hRight : lookupD (updateD D e ts ++ D₂) e = ts :=
      lookupD_append_left_of_find (D₁:=updateD D e ts) (D₂:=D₂) (e:=e) hFind
    simp [lookupD_update_eq, hRight]
  · have hLeftEq :
        lookupD (updateD (D ++ D₂) e ts) e' = lookupD (D ++ D₂) e' :=
        lookupD_update_neq (env:=D ++ D₂) (e:=e) (e':=e') (ts:=ts) (by
          intro hEq'; exact hEq hEq'.symm)
    have hfind : (updateD D e ts).find? e' = D.find? e' :=
      findD_update_neq (env:=D) (e:=e) (e':=e') (ts:=ts) (by
        intro hEq'; exact hEq hEq'.symm)
    cases hLeft : D.find? e' with
    | some ts' =>
        have hLeft' : (updateD D e ts).find? e' = some ts' := by
          simpa [hLeft] using hfind
        have hA :=
          findD_append_left (D₁:=updateD D e ts) (D₂:=D₂) (e:=e') (ts:=ts') hLeft'
        have hB :=
          findD_append_left (D₁:=D) (D₂:=D₂) (e:=e') (ts:=ts') hLeft
        have hfind_union :
            (updateD D e ts ++ D₂).find? e' = (D ++ D₂).find? e' := by
          simpa [hA, hB]
        have hRightEq : lookupD (updateD D e ts ++ D₂) e' = lookupD (D ++ D₂) e' := by
          simp [lookupD, hfind_union]
        simpa [hLeftEq, hRightEq]
    | none =>
        have hLeft' : (updateD D e ts).find? e' = none := by
          simpa [hLeft] using hfind
        have hA := findD_append_right (D₁:=updateD D e ts) (D₂:=D₂) (e:=e') hLeft'
        have hB := findD_append_right (D₁:=D) (D₂:=D₂) (e:=e') hLeft
        have hfind_union :
            (updateD D e ts ++ D₂).find? e' = (D ++ D₂).find? e' := by
          simpa [hA, hB]
        have hRightEq : lookupD (updateD D e ts ++ D₂) e' = lookupD (D ++ D₂) e' := by
          simp [lookupD, hfind_union]
        simpa [hLeftEq, hRightEq]

lemma lookupD_updateD_append_right {D₁ D : DEnv} {e e' : Edge} {ts : List ValType}
    (hNone : D₁.find? e = none) :
    lookupD (updateD (D₁ ++ D) e ts) e' = lookupD (D₁ ++ updateD D e ts) e' := by
  by_cases hEq : e' = e
  · cases hEq
    -- Left updates e directly; right uses append-right since left has none.
    have hRight :
        lookupD (D₁ ++ updateD D e ts) e = lookupD (updateD D e ts) e :=
      lookupD_append_right (D₁:=D₁) (D₂:=updateD D e ts) (e:=e) hNone
    simp [lookupD_update_eq, hRight]
  · have hLeftEq :
        lookupD (updateD (D₁ ++ D) e ts) e' = lookupD (D₁ ++ D) e' :=
        lookupD_update_neq (env:=D₁ ++ D) (e:=e) (e':=e') (ts:=ts) (by
          intro hEq'; exact hEq hEq'.symm)
    have hfind : (updateD D e ts).find? e' = D.find? e' :=
      findD_update_neq (env:=D) (e:=e) (e':=e') (ts:=ts) (by
        intro hEq'; exact hEq hEq'.symm)
    cases hLeft : D₁.find? e' with
    | some ts' =>
        have hA := findD_append_left (D₁:=D₁) (D₂:=updateD D e ts) (e:=e') (ts:=ts') hLeft
        have hB := findD_append_left (D₁:=D₁) (D₂:=D) (e:=e') (ts:=ts') hLeft
        have hfind_union :
            (D₁ ++ updateD D e ts).find? e' = (D₁ ++ D).find? e' := by
          simpa [hA, hB]
        have hRightEq : lookupD (D₁ ++ updateD D e ts) e' = lookupD (D₁ ++ D) e' := by
          simp [lookupD, hfind_union]
        simpa [hLeftEq, hRightEq]
    | none =>
        have hA := findD_append_right (D₁:=D₁) (D₂:=updateD D e ts) (e:=e') hLeft
        have hB := findD_append_right (D₁:=D₁) (D₂:=D) (e:=e') hLeft
        have hfind_union :
            (D₁ ++ updateD D e ts).find? e' = (D₁ ++ D).find? e' := by
          -- use hfind to rewrite right find?
          simpa [hA, hB, hfind]
        have hRightEq : lookupD (D₁ ++ updateD D e ts) e' = lookupD (D₁ ++ D) e' := by
          simp [lookupD, hfind_union]
        simpa [hLeftEq, hRightEq]

lemma lookupD_append_assoc {D₁ D₂ D₃ : DEnv} :
    ∀ e, lookupD ((D₁ ++ D₂) ++ D₃) e = lookupD (D₁ ++ (D₂ ++ D₃)) e := by
  intro e
  cases h1 : D₁.find? e with
  | some ts =>
      have h12 : (D₁ ++ D₂).find? e = some ts :=
        findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) h1
      have hLeft : ((D₁ ++ D₂) ++ D₃).find? e = some ts :=
        findD_append_left (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) (ts:=ts) h12
      have hRight : (D₁ ++ (D₂ ++ D₃)).find? e = some ts :=
        findD_append_left (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) (ts:=ts) h1
      simp [lookupD, hLeft, hRight]
  | none =>
      have h12 : (D₁ ++ D₂).find? e = D₂.find? e :=
        findD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) h1
      cases h2 : D₂.find? e with
      | some ts =>
          have h12' : (D₁ ++ D₂).find? e = some ts := by
            simpa [h2] using h12
          have hLeft : ((D₁ ++ D₂) ++ D₃).find? e = some ts :=
            findD_append_left (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) (ts:=ts) h12'
          have h23 : (D₂ ++ D₃).find? e = some ts :=
            findD_append_left (D₁:=D₂) (D₂:=D₃) (e:=e) (ts:=ts) h2
          have hRight : (D₁ ++ (D₂ ++ D₃)).find? e = some ts := by
            have hRight0 := findD_append_right (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) h1
            simpa [h23] using hRight0
          simp [lookupD, hLeft, hRight]
      | none =>
          have h12' : (D₁ ++ D₂).find? e = none := by
            simpa [h2] using h12
          have hLeft := findD_append_right (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) h12'
          have h23 : (D₂ ++ D₃).find? e = D₃.find? e :=
            findD_append_right (D₁:=D₂) (D₂:=D₃) (e:=e) h2
          have hRight : (D₁ ++ (D₂ ++ D₃)).find? e = D₃.find? e := by
            have hRight0 := findD_append_right (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) h1
            simpa [h23] using hRight0
          simp [lookupD, hLeft, hRight]

lemma BuffersTyped_append_assoc
    {G : GEnv} {D₁ D₂ D₃ : DEnv} {bufs : Buffers} :
    BuffersTyped G ((D₁ ++ D₂) ++ D₃) bufs →
    BuffersTyped G (D₁ ++ (D₂ ++ D₃)) bufs := by
  intro hBT
  exact BuffersTyped_rewriteD (lookupD_append_assoc (D₁:=D₁) (D₂:=D₂) (D₃:=D₃)) hBT

lemma BuffersTyped_append_assoc_symm
    {G : GEnv} {D₁ D₂ D₃ : DEnv} {bufs : Buffers} :
    BuffersTyped G (D₁ ++ (D₂ ++ D₃)) bufs →
    BuffersTyped G ((D₁ ++ D₂) ++ D₃) bufs := by
  intro hBT
  refine BuffersTyped_rewriteD ?_ hBT
  intro e
  symm
  exact lookupD_append_assoc (D₁:=D₁) (D₂:=D₂) (D₃:=D₃) e

lemma DConsistent_append {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    DConsistent G₁ D₁ →
    DConsistent G₂ D₂ →
    DConsistent (G₁ ++ G₂) (D₁ ++ D₂) := by
  intro h1 h2 s hs
  have hs' : s ∈ SessionsOfD D₁ ∪ SessionsOfD D₂ :=
    SessionsOfD_append_subset (D₁:=D₁) (D₂:=D₂) hs
  cases hs' with
  | inl hL =>
      exact SessionsOf_append_left (G₂:=G₂) (h1 hL)
  | inr hR =>
      exact SessionsOf_append_right (G₁:=G₁) (h2 hR)

lemma DEnv_find_none_of_disjoint_left {D₁ D₂ : DEnv} (hDisj : DisjointD D₁ D₂)
    {e : Edge} {ts : List ValType} (hFind : D₁.find? e = some ts) :
    D₂.find? e = none := by
  exact DisjointD_lookup_left (D₁:=D₁) (D₂:=D₂) hDisj hFind

lemma findD_comm_of_disjoint {D₁ D₂ : DEnv} (hDisj : DisjointD D₁ D₂) :
    ∀ e, (D₁ ++ D₂).find? e = (D₂ ++ D₁).find? e := by
  intro e
  cases hLeft : D₁.find? e with
  | some ts =>
      have hRightNone : D₂.find? e = none :=
        DEnv_find_none_of_disjoint_left hDisj (e:=e) (ts:=ts) hLeft
      have hA := findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) hLeft
      have hB := findD_append_right (D₁:=D₂) (D₂:=D₁) (e:=e) hRightNone
      simpa [hA, hB, hLeft]
  | none =>
      have hA := findD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hLeft
      cases hRight : D₂.find? e with
      | some ts =>
          have hB := findD_append_left (D₁:=D₂) (D₂:=D₁) (e:=e) (ts:=ts) hRight
          simpa [hA, hB, hRight]
      | none =>
          have hB := findD_append_right (D₁:=D₂) (D₂:=D₁) (e:=e) hRight
          simpa [hA, hB, hRight, hLeft]

lemma BuffersTyped_mono {G G' : GEnv} {D : DEnv} {bufs : Buffers} :
    (∀ e L, lookupG G e = some L → lookupG G' e = some L) →
    BuffersTyped G D bufs →
    BuffersTyped G' D bufs := by
  intro hMono hBT e
  rcases hBT e with ⟨hLen, hTyping⟩
  refine ⟨hLen, ?_⟩
  intro i hi
  exact HasTypeVal_mono G G' _ _ (hTyping i hi) hMono

lemma lookupG_comm_of_disjoint {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂) :
    ∀ e, lookupG (G₁ ++ G₂) e = lookupG (G₂ ++ G₁) e := by
  intro e
  cases hLeft : lookupG G₁ e with
  | some L =>
      have hNone : lookupG G₂ e = none :=
        lookupG_none_of_disjoint (G₁:=G₂) (G₂:=G₁) (DisjointG_symm hDisj) (e:=e) (L:=L) hLeft
      have hA := lookupG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hLeft
      have hB := lookupG_append_right (G₁:=G₂) (G₂:=G₁) (e:=e) hNone
      simpa [hA, hB, hLeft]
  | none =>
      have hA := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hLeft
      cases hRight : lookupG G₂ e with
      | some L =>
          have hB := lookupG_append_left (G₁:=G₂) (G₂:=G₁) (e:=e) (L:=L) hRight
          simpa [hA, hB, hRight]
      | none =>
          have hB := lookupG_append_right (G₁:=G₂) (G₂:=G₁) (e:=e) hRight
          simpa [hA, hB, hRight, hLeft]

lemma BuffersTyped_swap_G_left {G₁ G₂ G₃ : GEnv} {D : DEnv} {bufs : Buffers}
    (hDisj : DisjointG G₁ G₂) :
    BuffersTyped ((G₁ ++ G₂) ++ G₃) D bufs →
    BuffersTyped (G₂ ++ (G₁ ++ G₃)) D bufs := by
  intro hBT
  have hBT' : BuffersTyped ((G₂ ++ G₁) ++ G₃) D bufs := by
    apply BuffersTyped_mono (G:=((G₁ ++ G₂) ++ G₃)) (G':=((G₂ ++ G₁) ++ G₃))
    · intro ep L hLookup
      have hInv := lookupG_append_inv (G₁:=G₁ ++ G₂) (G₂:=G₃) (e:=ep) hLookup
      cases hInv with
      | inl hLeft =>
          have hSwap := lookupG_comm_of_disjoint hDisj ep
          have hLeft' : lookupG (G₂ ++ G₁) ep = some L := by
            simpa [hSwap] using hLeft
          exact lookupG_append_left (G₁:=G₂ ++ G₁) (G₂:=G₃) hLeft'
      | inr hRight =>
          have hSwap := lookupG_comm_of_disjoint hDisj ep
          have hNone : lookupG (G₂ ++ G₁) ep = none := by
            simpa [hSwap] using hRight.1
          have hRight' : lookupG (G₂ ++ (G₁ ++ G₃)) ep = lookupG G₃ ep := by
            have hRight0 :=
              lookupG_append_right (G₁:=G₂ ++ G₁) (G₂:=G₃) (e:=ep) hNone
            simpa [List.append_assoc] using hRight0
          have hRight'' : lookupG (G₂ ++ (G₁ ++ G₃)) ep = some L := by
            simpa [hRight'] using hRight.2
          have hRight''' : lookupG ((G₂ ++ G₁) ++ G₃) ep = some L := by
            simpa [List.append_assoc] using hRight''
          exact hRight'''
    · exact hBT
  simpa [List.append_assoc] using hBT'

lemma BuffersTyped_swap_D_left {G : GEnv} {D₁ D₂ D₃ : DEnv} {bufs : Buffers}
    (hDisj : DisjointD D₁ D₂) :
    BuffersTyped G ((D₁ ++ D₂) ++ D₃) bufs →
    BuffersTyped G ((D₂ ++ D₁) ++ D₃) bufs := by
  intro hBT
  have hEq : ∀ e, lookupD ((D₁ ++ D₂) ++ D₃) e = lookupD ((D₂ ++ D₁) ++ D₃) e := by
    intro e
    have hInv := findD_comm_of_disjoint hDisj e
    cases hLeft : (D₁ ++ D₂).find? e with
    | some ts =>
        have hA := findD_append_left (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) (ts:=ts) hLeft
        have hLeft' : (D₂ ++ D₁).find? e = some ts := by
          simpa [hInv] using hLeft
        have hB := findD_append_left (D₁:=D₂ ++ D₁) (D₂:=D₃) (e:=e) (ts:=ts) hLeft'
        simp [lookupD, hA, hB]
    | none =>
        have hA := findD_append_right (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) hLeft
        have hLeft' : (D₂ ++ D₁).find? e = none := by
          simpa [hInv] using hLeft
        have hB := findD_append_right (D₁:=D₂ ++ D₁) (D₂:=D₃) (e:=e) hLeft'
        simp [lookupD, hA, hB]
  exact BuffersTyped_rewriteD hEq hBT

lemma lookupG_swap_right {G₁ G₂ G₃ : GEnv} (hDisj : DisjointG G₂ G₃) :
    ∀ e, lookupG (G₁ ++ (G₂ ++ G₃)) e = lookupG (G₁ ++ (G₃ ++ G₂)) e := by
  intro e
  cases hLeft : lookupG G₁ e with
  | some L =>
      have hA := lookupG_append_left (G₁:=G₁) (G₂:=G₂ ++ G₃) (e:=e) (L:=L) hLeft
      have hB := lookupG_append_left (G₁:=G₁) (G₂:=G₃ ++ G₂) (e:=e) (L:=L) hLeft
      simpa [hA, hB]
  | none =>
      have hA := lookupG_append_right (G₁:=G₁) (G₂:=G₂ ++ G₃) (e:=e) hLeft
      have hB := lookupG_append_right (G₁:=G₁) (G₂:=G₃ ++ G₂) (e:=e) hLeft
      have hComm := lookupG_comm_of_disjoint hDisj e
      simpa [hA, hB, hComm]

lemma BuffersTyped_swap_G_right {G₁ G₂ G₃ : GEnv} {D : DEnv} {bufs : Buffers}
    (hDisj : DisjointG G₂ G₃) :
    BuffersTyped (G₁ ++ (G₂ ++ G₃)) D bufs →
    BuffersTyped (G₁ ++ (G₃ ++ G₂)) D bufs := by
  intro hBT
  apply BuffersTyped_mono (G:=G₁ ++ (G₂ ++ G₃)) (G':=G₁ ++ (G₃ ++ G₂))
  · intro ep L hLookup
    have hEq := lookupG_swap_right (G₁:=G₁) (G₂:=G₂) (G₃:=G₃) hDisj ep
    simpa [hEq] using hLookup
  · exact hBT

lemma lookupD_swap_right {D₁ D₂ D₃ : DEnv} (hDisj : DisjointD D₂ D₃) :
    ∀ e, lookupD (D₁ ++ (D₂ ++ D₃)) e = lookupD (D₁ ++ (D₃ ++ D₂)) e := by
  intro e
  cases hLeft : D₁.find? e with
  | some ts =>
      have hA := findD_append_left (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) (ts:=ts) hLeft
      have hB := findD_append_left (D₁:=D₁) (D₂:=D₃ ++ D₂) (e:=e) (ts:=ts) hLeft
      simp [lookupD, hA, hB]
  | none =>
      have hA := findD_append_right (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) hLeft
      have hB := findD_append_right (D₁:=D₁) (D₂:=D₃ ++ D₂) (e:=e) hLeft
      have hComm := findD_comm_of_disjoint hDisj e
      simp [lookupD, hA, hB, hComm]

lemma BuffersTyped_swap_D_right {G : GEnv} {D₁ D₂ D₃ : DEnv} {bufs : Buffers}
    (hDisj : DisjointD D₂ D₃) :
    BuffersTyped G (D₁ ++ (D₂ ++ D₃)) bufs →
    BuffersTyped G (D₁ ++ (D₃ ++ D₂)) bufs := by
  intro hBT
  have hEq : ∀ e, lookupD (D₁ ++ (D₂ ++ D₃)) e = lookupD (D₁ ++ (D₃ ++ D₂)) e :=
    lookupD_swap_right (D₁:=D₁) (D₂:=D₂) (D₃:=D₃) hDisj
  exact BuffersTyped_rewriteD hEq hBT


end
