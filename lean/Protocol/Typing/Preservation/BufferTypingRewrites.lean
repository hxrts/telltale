import Protocol.Typing.Preservation.StoreTypingFrames

/-! # Buffer Typing Rewrites

Rewriting lemmas for `BuffersTyped`, allowing DEnv substitution when
trace lookups are equivalent, and update lemmas for RBMap-based DEnv. -/

/-
The Problem. `BuffersTyped G D bufs` depends on trace lookups in D.
When we restructure D (e.g., through updates or appends), we need to
show the rewritten D still yields the same lookups.

Solution Structure. Prove `buffers_typed_rewrite_d` for trace-equivalent
substitution. Provide `find_d_update_eq` and `find_d_update_neq` for
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

theorem buffers_typed_weaken_g
    {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} {bufs : Buffers} :
    BuffersTyped (G₁ ++ G₂) (D₁ ++ D₂) bufs →
    (∀ e L, lookupG (G₁ ++ G₂) e = some L → lookupG (G₁ ++ G₂) e = some L) →
    BuffersTyped (G₁ ++ G₂) (D₁ ++ D₂) bufs := by
  intro hBT _; exact hBT

theorem buffers_typed_rewrite_d
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

/-! ## DEnv Lookup Rewrites -/

lemma lookup_d_append_left_of_find {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType} :
    D₁.find? e = some ts →
    lookupD (D₁ ++ D₂) e = ts := by
  intro hFind
  have hLeft := find_d_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) hFind
  simp [lookupD, hLeft]

lemma lookup_d_update_d_append_left {D D₂ : DEnv} {e e' : Edge} {ts : List ValType} :
    lookupD (updateD (D ++ D₂) e ts) e' = lookupD (updateD D e ts ++ D₂) e' := by
  by_cases hEq : e' = e
  · cases hEq
    -- Both sides update e to ts.
    have hFind : (updateD D e ts).find? e = some ts := find_d_update_eq (env:=D) (e:=e) (ts:=ts)
    have hRight : lookupD (updateD D e ts ++ D₂) e = ts :=
      lookup_d_append_left_of_find (D₁:=updateD D e ts) (D₂:=D₂) (e:=e) hFind
    simp [lookup_d_update_eq, hRight]
  · have hLeftEq :
        lookupD (updateD (D ++ D₂) e ts) e' = lookupD (D ++ D₂) e' :=
        lookup_d_update_neq (env:=D ++ D₂) (e:=e) (e':=e') (ts:=ts) (by
          intro hEq'; exact hEq hEq'.symm)
    have hfind : (updateD D e ts).find? e' = D.find? e' :=
      find_d_update_neq (env:=D) (e:=e) (e':=e') (ts:=ts) (by
        intro hEq'; exact hEq hEq'.symm)
    cases hLeft : D.find? e' with
    | some ts' =>
        have hLeft' : (updateD D e ts).find? e' = some ts' := by
          simpa [hLeft] using hfind
        have hA :=
          find_d_append_left (D₁:=updateD D e ts) (D₂:=D₂) (e:=e') (ts:=ts') hLeft'
        have hB :=
          find_d_append_left (D₁:=D) (D₂:=D₂) (e:=e') (ts:=ts') hLeft
        have hfind_union :
            (updateD D e ts ++ D₂).find? e' = (D ++ D₂).find? e' := by
          simpa [hA, hB]
        have hRightEq : lookupD (updateD D e ts ++ D₂) e' = lookupD (D ++ D₂) e' := by
          simp [lookupD, hfind_union]
        simpa [hLeftEq, hRightEq]
    | none =>
        have hLeft' : (updateD D e ts).find? e' = none := by
          simpa [hLeft] using hfind
        have hA := find_d_append_right (D₁:=updateD D e ts) (D₂:=D₂) (e:=e') hLeft'
        have hB := find_d_append_right (D₁:=D) (D₂:=D₂) (e:=e') hLeft
        have hfind_union :
            (updateD D e ts ++ D₂).find? e' = (D ++ D₂).find? e' := by
          simpa [hA, hB]
        have hRightEq : lookupD (updateD D e ts ++ D₂) e' = lookupD (D ++ D₂) e' := by
          simp [lookupD, hfind_union]
        simpa [hLeftEq, hRightEq]

/-! ## Right-Append Update Rewrites -/

lemma lookup_d_update_d_append_right {D₁ D : DEnv} {e e' : Edge} {ts : List ValType}
    (hNone : D₁.find? e = none) :
    lookupD (updateD (D₁ ++ D) e ts) e' = lookupD (D₁ ++ updateD D e ts) e' := by
  by_cases hEq : e' = e
  · cases hEq
    -- Left updates e directly; right uses append-right since left has none.
    have hRight :
        lookupD (D₁ ++ updateD D e ts) e = lookupD (updateD D e ts) e :=
      lookup_d_append_right (D₁:=D₁) (D₂:=updateD D e ts) (e:=e) hNone
    simp [lookup_d_update_eq, hRight]
  · have hLeftEq :
        lookupD (updateD (D₁ ++ D) e ts) e' = lookupD (D₁ ++ D) e' :=
        lookup_d_update_neq (env:=D₁ ++ D) (e:=e) (e':=e') (ts:=ts) (by
          intro hEq'; exact hEq hEq'.symm)
    have hfind : (updateD D e ts).find? e' = D.find? e' :=
      find_d_update_neq (env:=D) (e:=e) (e':=e') (ts:=ts) (by
        intro hEq'; exact hEq hEq'.symm)
    cases hLeft : D₁.find? e' with
    | some ts' =>
        have hA := find_d_append_left (D₁:=D₁) (D₂:=updateD D e ts) (e:=e') (ts:=ts') hLeft
        have hB := find_d_append_left (D₁:=D₁) (D₂:=D) (e:=e') (ts:=ts') hLeft
        have hfind_union :
            (D₁ ++ updateD D e ts).find? e' = (D₁ ++ D).find? e' := by
          simpa [hA, hB]
        have hRightEq : lookupD (D₁ ++ updateD D e ts) e' = lookupD (D₁ ++ D) e' := by
          simp [lookupD, hfind_union]
        simpa [hLeftEq, hRightEq]
    | none =>
        have hA := find_d_append_right (D₁:=D₁) (D₂:=updateD D e ts) (e:=e') hLeft
        have hB := find_d_append_right (D₁:=D₁) (D₂:=D) (e:=e') hLeft
        have hfind_union :
            (D₁ ++ updateD D e ts).find? e' = (D₁ ++ D).find? e' := by
          -- use hfind to rewrite right find?
          simpa [hA, hB, hfind]
        have hRightEq : lookupD (D₁ ++ updateD D e ts) e' = lookupD (D₁ ++ D) e' := by
          simp [lookupD, hfind_union]
        simpa [hLeftEq, hRightEq]

/-! ## Append Associativity Rewrites -/

lemma lookup_d_append_assoc {D₁ D₂ D₃ : DEnv} :
    ∀ e, lookupD ((D₁ ++ D₂) ++ D₃) e = lookupD (D₁ ++ (D₂ ++ D₃)) e := by
  intro e
  cases h1 : D₁.find? e with
  | some ts =>
      have h12 : (D₁ ++ D₂).find? e = some ts :=
        find_d_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) h1
      have hLeft : ((D₁ ++ D₂) ++ D₃).find? e = some ts :=
        find_d_append_left (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) (ts:=ts) h12
      have hRight : (D₁ ++ (D₂ ++ D₃)).find? e = some ts :=
        find_d_append_left (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) (ts:=ts) h1
      simp [lookupD, hLeft, hRight]
  | none =>
      /- For the right-biased path, inspect `D₂` to align both append associations. -/
      have h12 : (D₁ ++ D₂).find? e = D₂.find? e :=
        find_d_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) h1
      cases h2 : D₂.find? e with
      | some ts =>
          have h12' : (D₁ ++ D₂).find? e = some ts := by
            simpa [h2] using h12
          have hLeft : ((D₁ ++ D₂) ++ D₃).find? e = some ts :=
            find_d_append_left (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) (ts:=ts) h12'
          have h23 : (D₂ ++ D₃).find? e = some ts :=
            find_d_append_left (D₁:=D₂) (D₂:=D₃) (e:=e) (ts:=ts) h2
          have hRight : (D₁ ++ (D₂ ++ D₃)).find? e = some ts := by
            have hRight0 := find_d_append_right (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) h1
            simpa [h23] using hRight0
          simp [lookupD, hLeft, hRight]
      | none =>
          have h12' : (D₁ ++ D₂).find? e = none := by
            simpa [h2] using h12
          have hLeft := find_d_append_right (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) h12'
          have h23 : (D₂ ++ D₃).find? e = D₃.find? e :=
            find_d_append_right (D₁:=D₂) (D₂:=D₃) (e:=e) h2
          have hRight : (D₁ ++ (D₂ ++ D₃)).find? e = D₃.find? e := by
            have hRight0 := find_d_append_right (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) h1
            simpa [h23] using hRight0
          simp [lookupD, hLeft, hRight]

/-! ## Buffer-Typing Transport Over Associativity -/

lemma buffers_typed_append_assoc
    {G : GEnv} {D₁ D₂ D₃ : DEnv} {bufs : Buffers} :
    BuffersTyped G ((D₁ ++ D₂) ++ D₃) bufs →
    BuffersTyped G (D₁ ++ (D₂ ++ D₃)) bufs := by
  intro hBT
  exact buffers_typed_rewrite_d (lookup_d_append_assoc (D₁:=D₁) (D₂:=D₂) (D₃:=D₃)) hBT

lemma buffers_typed_append_assoc_symm
    {G : GEnv} {D₁ D₂ D₃ : DEnv} {bufs : Buffers} :
    BuffersTyped G (D₁ ++ (D₂ ++ D₃)) bufs →
    BuffersTyped G ((D₁ ++ D₂) ++ D₃) bufs := by
  intro hBT
  refine buffers_typed_rewrite_d ?_ hBT
  intro e
  symm
  exact lookup_d_append_assoc (D₁:=D₁) (D₂:=D₂) (D₃:=D₃) e

/-! ## Session Consistency Under Append -/

lemma d_consistent_append {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    DConsistent G₁ D₁ →
    DConsistent G₂ D₂ →
    DConsistent (G₁ ++ G₂) (D₁ ++ D₂) := by
  intro h1 h2 s hs
  have hs' : s ∈ SessionsOfD D₁ ∪ SessionsOfD D₂ :=
    sessions_of_d_append_subset (D₁:=D₁) (D₂:=D₂) hs
  cases hs' with
  | inl hL =>
      exact sessions_of_append_left (G₂:=G₂) (h1 hL)
  | inr hR =>
      exact sessions_of_append_right (G₁:=G₁) (h2 hR)

/-! ## Disjoint Lookup Commutation -/

lemma d_env_find_none_of_disjoint_left {D₁ D₂ : DEnv} (hDisj : DisjointD D₁ D₂)
    {e : Edge} {ts : List ValType} (hFind : D₁.find? e = some ts) :
    D₂.find? e = none := by
  exact disjoint_d_lookup_left (D₁:=D₁) (D₂:=D₂) hDisj hFind

lemma find_d_comm_of_disjoint {D₁ D₂ : DEnv} (hDisj : DisjointD D₁ D₂) :
    ∀ e, (D₁ ++ D₂).find? e = (D₂ ++ D₁).find? e := by
  intro e
  cases hLeft : D₁.find? e with
  | some ts =>
      have hRightNone : D₂.find? e = none :=
        d_env_find_none_of_disjoint_left hDisj (e:=e) (ts:=ts) hLeft
      have hA := find_d_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) hLeft
      have hB := find_d_append_right (D₁:=D₂) (D₂:=D₁) (e:=e) hRightNone
      simpa [hA, hB, hLeft]
  | none =>
      have hA := find_d_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hLeft
      cases hRight : D₂.find? e with
      | some ts =>
          have hB := find_d_append_left (D₁:=D₂) (D₂:=D₁) (e:=e) (ts:=ts) hRight
          simpa [hA, hB, hRight]
      | none =>
          have hB := find_d_append_right (D₁:=D₂) (D₂:=D₁) (e:=e) hRight
          simpa [hA, hB, hRight, hLeft]

lemma buffers_typed_mono {G G' : GEnv} {D : DEnv} {bufs : Buffers} :
    (∀ e L, lookupG G e = some L → lookupG G' e = some L) →
    BuffersTyped G D bufs →
    BuffersTyped G' D bufs := by
  intro hMono hBT e
  rcases hBT e with ⟨hLen, hTyping⟩
  refine ⟨hLen, ?_⟩
  intro i hi
  exact has_type_val_mono G G' _ _ (hTyping i hi) hMono

/-! ## Global Environment Swap Rewrites -/

lemma lookup_g_comm_of_disjoint {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂) :
    ∀ e, lookupG (G₁ ++ G₂) e = lookupG (G₂ ++ G₁) e := by
  intro e
  cases hLeft : lookupG G₁ e with
  | some L =>
      have hNone : lookupG G₂ e = none :=
        lookup_g_none_of_disjoint (G₁:=G₂) (G₂:=G₁) (disjoint_g_symm hDisj) (e:=e) (L:=L) hLeft
      have hA := lookup_g_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hLeft
      have hB := lookup_g_append_right (G₁:=G₂) (G₂:=G₁) (e:=e) hNone
      simpa [hA, hB, hLeft]
  | none =>
      have hA := lookup_g_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hLeft
      cases hRight : lookupG G₂ e with
      | some L =>
          have hB := lookup_g_append_left (G₁:=G₂) (G₂:=G₁) (e:=e) (L:=L) hRight
          simpa [hA, hB, hRight]
      | none =>
          have hB := lookup_g_append_right (G₁:=G₂) (G₂:=G₁) (e:=e) hRight
          simpa [hA, hB, hRight, hLeft]

/-! ## Left-Swap Transport for Buffer Typing -/

lemma buffers_typed_swap_g_left {G₁ G₂ G₃ : GEnv} {D : DEnv} {bufs : Buffers}
    (hDisj : DisjointG G₁ G₂) :
    BuffersTyped ((G₁ ++ G₂) ++ G₃) D bufs →
    BuffersTyped (G₂ ++ (G₁ ++ G₃)) D bufs := by
  intro hBT
  have hBT' : BuffersTyped ((G₂ ++ G₁) ++ G₃) D bufs := by
    apply buffers_typed_mono (G:=((G₁ ++ G₂) ++ G₃)) (G':=((G₂ ++ G₁) ++ G₃))
    · intro ep L hLookup
      have hInv := lookup_g_append_inv (G₁:=G₁ ++ G₂) (G₂:=G₃) (e:=ep) hLookup
      cases hInv with
      | inl hLeft =>
          have hSwap := lookup_g_comm_of_disjoint hDisj ep
          have hLeft' : lookupG (G₂ ++ G₁) ep = some L := by
            simpa [hSwap] using hLeft
          exact lookup_g_append_left (G₁:=G₂ ++ G₁) (G₂:=G₃) hLeft'
      | inr hRight =>
          /- If the hit comes from `G₃`, first show `(G₂ ++ G₁)` is empty at `ep`. -/
          have hSwap := lookup_g_comm_of_disjoint hDisj ep
          have hNone : lookupG (G₂ ++ G₁) ep = none := by
            simpa [hSwap] using hRight.1
          have hRight' : lookupG (G₂ ++ (G₁ ++ G₃)) ep = lookupG G₃ ep := by
            have hRight0 :=
              lookup_g_append_right (G₁:=G₂ ++ G₁) (G₂:=G₃) (e:=ep) hNone
            simpa [List.append_assoc] using hRight0
          have hRight'' : lookupG (G₂ ++ (G₁ ++ G₃)) ep = some L := by
            simpa [hRight'] using hRight.2
          have hRight''' : lookupG ((G₂ ++ G₁) ++ G₃) ep = some L := by
            simpa [List.append_assoc] using hRight''
          exact hRight'''
    · exact hBT
  simpa [List.append_assoc] using hBT'

/-! ## Left DEnv Swap Transport -/

lemma buffers_typed_swap_d_left {G : GEnv} {D₁ D₂ D₃ : DEnv} {bufs : Buffers}
    (hDisj : DisjointD D₁ D₂) :
    BuffersTyped G ((D₁ ++ D₂) ++ D₃) bufs →
    BuffersTyped G ((D₂ ++ D₁) ++ D₃) bufs := by
  intro hBT
  have hEq : ∀ e, lookupD ((D₁ ++ D₂) ++ D₃) e = lookupD ((D₂ ++ D₁) ++ D₃) e := by
    intro e
    have hInv := find_d_comm_of_disjoint hDisj e
    cases hLeft : (D₁ ++ D₂).find? e with
    | some ts =>
        have hA := find_d_append_left (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) (ts:=ts) hLeft
        have hLeft' : (D₂ ++ D₁).find? e = some ts := by
          simpa [hInv] using hLeft
        have hB := find_d_append_left (D₁:=D₂ ++ D₁) (D₂:=D₃) (e:=e) (ts:=ts) hLeft'
        simp [lookupD, hA, hB]
    | none =>
        have hA := find_d_append_right (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) hLeft
        have hLeft' : (D₂ ++ D₁).find? e = none := by
          simpa [hInv] using hLeft
        have hB := find_d_append_right (D₁:=D₂ ++ D₁) (D₂:=D₃) (e:=e) hLeft'
        simp [lookupD, hA, hB]
  exact buffers_typed_rewrite_d hEq hBT

/-! ## Right-Swap Transport for Buffer Typing -/

lemma lookup_g_swap_right {G₁ G₂ G₃ : GEnv} (hDisj : DisjointG G₂ G₃) :
    ∀ e, lookupG (G₁ ++ (G₂ ++ G₃)) e = lookupG (G₁ ++ (G₃ ++ G₂)) e := by
  intro e
  cases hLeft : lookupG G₁ e with
  | some L =>
      have hA := lookup_g_append_left (G₁:=G₁) (G₂:=G₂ ++ G₃) (e:=e) (L:=L) hLeft
      have hB := lookup_g_append_left (G₁:=G₁) (G₂:=G₃ ++ G₂) (e:=e) (L:=L) hLeft
      simpa [hA, hB]
  | none =>
      have hA := lookup_g_append_right (G₁:=G₁) (G₂:=G₂ ++ G₃) (e:=e) hLeft
      have hB := lookup_g_append_right (G₁:=G₁) (G₂:=G₃ ++ G₂) (e:=e) hLeft
      have hComm := lookup_g_comm_of_disjoint hDisj e
      simpa [hA, hB, hComm]

lemma buffers_typed_swap_g_right {G₁ G₂ G₃ : GEnv} {D : DEnv} {bufs : Buffers}
    (hDisj : DisjointG G₂ G₃) :
    BuffersTyped (G₁ ++ (G₂ ++ G₃)) D bufs →
    BuffersTyped (G₁ ++ (G₃ ++ G₂)) D bufs := by
  intro hBT
  apply buffers_typed_mono (G:=G₁ ++ (G₂ ++ G₃)) (G':=G₁ ++ (G₃ ++ G₂))
  · intro ep L hLookup
    have hEq := lookup_g_swap_right (G₁:=G₁) (G₂:=G₂) (G₃:=G₃) hDisj ep
    simpa [hEq] using hLookup
  · exact hBT

lemma lookup_d_swap_right {D₁ D₂ D₃ : DEnv} (hDisj : DisjointD D₂ D₃) :
    ∀ e, lookupD (D₁ ++ (D₂ ++ D₃)) e = lookupD (D₁ ++ (D₃ ++ D₂)) e := by
  intro e
  cases hLeft : D₁.find? e with
  | some ts =>
      have hA := find_d_append_left (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) (ts:=ts) hLeft
      have hB := find_d_append_left (D₁:=D₁) (D₂:=D₃ ++ D₂) (e:=e) (ts:=ts) hLeft
      simp [lookupD, hA, hB]
  | none =>
      have hA := find_d_append_right (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) hLeft
      have hB := find_d_append_right (D₁:=D₁) (D₂:=D₃ ++ D₂) (e:=e) hLeft
      have hComm := find_d_comm_of_disjoint hDisj e
      simp [lookupD, hA, hB, hComm]

lemma buffers_typed_swap_d_right {G : GEnv} {D₁ D₂ D₃ : DEnv} {bufs : Buffers}
    (hDisj : DisjointD D₂ D₃) :
    BuffersTyped G (D₁ ++ (D₂ ++ D₃)) bufs →
    BuffersTyped G (D₁ ++ (D₃ ++ D₂)) bufs := by
  intro hBT
  have hEq : ∀ e, lookupD (D₁ ++ (D₂ ++ D₃)) e = lookupD (D₁ ++ (D₃ ++ D₂)) e :=
    lookup_d_swap_right (D₁:=D₁) (D₂:=D₂) (D₃:=D₃) hDisj
  exact buffers_typed_rewrite_d hEq hBT


end
