import Protocol.Environments.Renaming.CoreLookup

/-! # Session Renaming: Inverse and Update Lemmas

Inverse lookup theorems and environment update lemmas for session renaming,
enabling proof transport across renamed protocol configurations. -/

/-
The Problem. When verifying renamed configurations, we need to invert
renamed lookups (find the preimage endpoint/edge) and show that updates
commute with renaming. These lemmas are scattered across case analyses
on list membership.

Solution Structure. Prove `lookupG_rename_inv` and `lookupD_rename_inv`
for inverse lookups. Provide update commutativity lemmas for GEnv and
DEnv. Structure proofs by case analysis on list membership with preimage
edge reasoning.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

/-! ## Inverse Lookup Lemmas -/

/-- If lookup succeeds in renamed GEnv, the preimage endpoint exists. -/
theorem lookupG_rename_inv (ρ : SessionRenaming) (G : GEnv) (e : Endpoint) (L : LocalType) :
    lookupG (renameGEnv ρ G) e = some L →
    ∃ e' L', e = renameEndpoint ρ e' ∧ L = renameLocalType ρ L' ∧ lookupG G e' = some L' := by
  intro h
  induction G with
  | nil =>
    simp only [renameGEnv, lookupG, List.lookup, List.map] at h
    exact Option.noConfusion h
  | cons hd tl ih =>
    simp only [renameGEnv, List.map, lookupG, List.lookup] at h
    by_cases heq : e = renameEndpoint ρ hd.1
    case pos =>
      simp only [heq, beq_self_eq_true, Option.some.injEq] at h
      refine ⟨hd.1, hd.2, heq, h.symm, ?_⟩
      simp only [lookupG, List.lookup, beq_self_eq_true]
    case neg =>
      have hbeq : (e == renameEndpoint ρ hd.1) = false := beq_eq_false_iff_ne.mpr heq
      simp only [hbeq] at h
      obtain ⟨e', L', he', hL', hLookup⟩ := ih h
      refine ⟨e', L', he', hL', ?_⟩
      simp only [lookupG, List.lookup]
      have hne : e' ≠ hd.1 := by
        intro heq'
        subst heq'
        exact heq he'
      simp only [beq_eq_false_iff_ne.mpr hne]
      exact hLookup

/-! ## Inverse DEnv Lookup under Renaming -/
/-- If lookup succeeds (non-empty) in renamed DEnv, the preimage edge exists. -/
theorem lookupD_rename_inv (ρ : SessionRenaming) (D : DEnv) (e : Edge) :
    lookupD (renameDEnv ρ D) e ≠ [] →
    ∃ e', e = renameEdge ρ e' ∧
      lookupD (renameDEnv ρ D) e = (lookupD D e').map (renameValType ρ) := by
  intro h
  cases hpre : preimageEdge ρ e with
  | none =>
      have hno : ∀ p ∈ D.list, renameEdge ρ p.1 ≠ e := by
        intro p hp hEq
        have hsome : preimageEdge ρ e = some p.1 := by
          simpa [hEq] using (preimageEdge_rename ρ p.1)
        exact Option.noConfusion (hpre ▸ hsome)
      have hlookup :
          lookupD (renameDEnv ρ D) e = lookupD (∅ : DEnv) e := by
        simpa [renameDEnv] using
          (lookupD_foldl_update_neq (ρ := ρ) (l := D.list) (acc := (∅ : DEnv))
            (edge := e) hno)
      have hlookup' : lookupD (∅ : DEnv) e = [] := by
        simp [lookupD_empty]
      exact (h (by simp [hlookup, hlookup'])).elim
  | some e' =>
      have heq : e = renameEdge ρ e' := by
        exact (preimageEdge_spec (ρ:=ρ) (e:=e) (e':=e') (by simp [hpre])).symm
      refine ⟨e', heq, ?_⟩
      simpa [heq] using (lookupD_rename (ρ:=ρ) (D:=D) (e:=e'))

/-! ## Inverse Buffer Lookup under Renaming -/
/-- If lookup succeeds (non-empty) in renamed buffers, the preimage edge exists. -/
theorem lookupBuf_rename_inv (ρ : SessionRenaming) (bufs : Buffers) (e : Edge) :
    lookupBuf (renameBufs ρ bufs) e ≠ [] →
    ∃ e', e = renameEdge ρ e' ∧
      lookupBuf (renameBufs ρ bufs) e = (lookupBuf bufs e').map (renameValue ρ) := by
  intro h
  induction bufs with
  | nil =>
    simp only [renameBufs, lookupBuf, List.lookup, List.map, Option.getD, ne_eq,
               not_true_eq_false] at h
  | cons hd tl ih =>
    simp only [renameBufs, List.map, lookupBuf, List.lookup, Option.getD] at h ⊢
    by_cases heq : e = renameEdge ρ hd.1
    case pos =>
      refine ⟨hd.1, heq, ?_⟩
      subst heq
      simp only [beq_self_eq_true]
    case neg =>
      have hbeq : (e == renameEdge ρ hd.1) = false := beq_eq_false_iff_ne.mpr heq
      simp only [hbeq] at h ⊢
      obtain ⟨e', he', hLookup⟩ := ih h
      have hne : e' ≠ hd.1 := by
        intro heq'
        subst heq'
        exact heq he'
      refine ⟨e', he', ?_⟩
      simp only [beq_eq_false_iff_ne.mpr hne]
      exact hLookup

/-! ## Update Commutes with Renaming

These lemmas are essential for proving that instruction specs are equivariant
under session renaming (R.6 in implementation.md). -/

/-- Renaming commutes with GEnv update.

    This is the key infrastructure lemma for proving instruction equivariance.
    It states that updating then renaming equals renaming then updating. -/
theorem renameGEnv_updateG (ρ : SessionRenaming) (G : GEnv) (ep : Endpoint) (L : LocalType) :
    renameGEnv ρ (updateG G ep L) =
      updateG (renameGEnv ρ G) (renameEndpoint ρ ep) (renameLocalType ρ L) := by
  induction G with
  | nil =>
    simp [renameGEnv, updateG]
  | cons hd tl ih =>
    simp only [updateG, renameGEnv, List.map]
    by_cases heq : ep = hd.1
    case pos =>
      subst heq
      -- After substitution: ep = hd.1, so if_true applies
      simp only [ite_true, List.map]
    case neg =>
      have hne : renameEndpoint ρ ep ≠ renameEndpoint ρ hd.1 := fun h =>
        heq (renameEndpoint_inj ρ _ _ h)
      -- Unfold the if-then-else for the non-equal case
      simp only [if_neg heq, if_neg hne, List.map, List.cons.injEq, true_and]
      exact ih

/-! ## renameDEnv/updateD Commutation -/
/-- Renaming commutes with DEnv update.

    This lemma handles the map-based DEnv structure. The proof relies on
    the fact that renameEdge is injective (via renameEdge_inj).

    The key insight is that for any edge e':
    - If e' = renameEdge ρ e: both sides have find? = some (ts.map f)
    - If e' is not in the image of renameEdge: both sides have find? = none
    - If e' = renameEdge ρ e'' for e'' ≠ e: both sides have the same lookup as D at e''

    The proof uses DEnv_eq_of_find?_eq and case analysis on the preimage of e'. -/
theorem renameDEnv_updateD (ρ : SessionRenaming) (D : DEnv) (e : Edge) (ts : Trace) :
    renameDEnv ρ (updateD D e ts) =
      updateD (renameDEnv ρ D) (renameEdge ρ e) (ts.map (renameValType ρ)) := by
  apply DEnv_eq_of_find?_eq
  intro e'
  -- DEnv Update Commutation: Target Edge Case
  by_cases heq : e' = renameEdge ρ e
  case pos =>
    subst heq
    have hFold :=
      find?_rename_foldl (ρ := ρ) (l := (updateD D e ts).list)
        (sorted := (updateD D e ts).sorted) (acc := (∅ : DEnv)) (e := e)
    have hFind := find?_updateD_eq D e ts
    have hLookup : (updateD D e ts).list.lookup e = some ts := by
      calc
        (updateD D e ts).list.lookup e
            = (updateD D e ts).find? e := by
                symm; exact DEnv_find?_eq_lookup (env := updateD D e ts) (e := e)
        _ = some ts := hFind
    have hLhs :
        (renameDEnv ρ (updateD D e ts)).find? (renameEdge ρ e) =
          some (ts.map (renameValType ρ)) := by
      simpa [renameDEnv, hLookup] using hFold
    have hRhs :
        (updateD (renameDEnv ρ D) (renameEdge ρ e) (ts.map (renameValType ρ))).find?
          (renameEdge ρ e) = some (ts.map (renameValType ρ)) :=
      find?_updateD_eq (renameDEnv ρ D) (renameEdge ρ e) (ts.map (renameValType ρ))
    rw [hLhs, hRhs]
  -- DEnv Update Commutation: Non-target Edge Case
  case neg =>
    have hrhs :
        (updateD (renameDEnv ρ D) (renameEdge ρ e) (ts.map (renameValType ρ))).find? e' =
          (renameDEnv ρ D).find? e' :=
      find?_updateD_neq (renameDEnv ρ D) (renameEdge ρ e) e' (ts.map (renameValType ρ))
        (fun h => heq h.symm)
    cases hpre : preimageEdge ρ e' with
    -- Non-target Edge: No Preimage Branch
    | none =>
        have hno_lhs : ∀ p ∈ (updateD D e ts).list, renameEdge ρ p.1 ≠ e' := by
          intro p hp hEq
          have hsome : preimageEdge ρ e' = some p.1 := by
            simpa [hEq] using (preimageEdge_rename ρ p.1)
          exact Option.noConfusion (hpre ▸ hsome)
        have hLhs : (renameDEnv ρ (updateD D e ts)).find? e' = none := by
          simpa [renameDEnv] using
            (find?_foldl_update_neq (ρ := ρ) (l := (updateD D e ts).list)
              (acc := (∅ : DEnv)) (edge := e') hno_lhs)
        have hno_rhs : ∀ p ∈ D.list, renameEdge ρ p.1 ≠ e' := by
          intro p hp hEq
          have hsome : preimageEdge ρ e' = some p.1 := by
            simpa [hEq] using (preimageEdge_rename ρ p.1)
          exact Option.noConfusion (hpre ▸ hsome)
        have hRhsBase : (renameDEnv ρ D).find? e' = none := by
          simpa [renameDEnv] using
            (find?_foldl_update_neq (ρ := ρ) (l := D.list)
              (acc := (∅ : DEnv)) (edge := e') hno_rhs)
        rw [hLhs, hrhs, hRhsBase]
    -- Non-target Edge: Existing Preimage Branch
    | some e'' =>
        have he'_eq : e' = renameEdge ρ e'' :=
          (preimageEdge_spec (by simp [hpre])).symm
        have hne : e'' ≠ e := by
          intro hc
          subst hc
          exact heq he'_eq
        have hL :=
          find?_rename_foldl (ρ := ρ) (l := (updateD D e ts).list)
            (sorted := (updateD D e ts).sorted) (acc := (∅ : DEnv)) (e := e'')
        have hEqUpd : (updateD D e ts).list.lookup e'' = (updateD D e ts).find? e'' := by
          symm
          exact DEnv_find?_eq_lookup (env := updateD D e ts) (e := e'')
        have hL' :
            (renameDEnv ρ (updateD D e ts)).find? e' =
              match (updateD D e ts).find? e'' with
              | some ts' => some (ts'.map (renameValType ρ))
              | none => none := by
          simpa [renameDEnv, he'_eq, hEqUpd] using hL
        have hFindUpd : (updateD D e ts).find? e'' = D.find? e'' :=
          find?_updateD_neq D e e'' ts hne.symm
        have hR :=
          find?_rename_foldl (ρ := ρ) (l := D.list) (sorted := D.sorted)
            (acc := (∅ : DEnv)) (e := e'')
        have hEqD : D.list.lookup e'' = D.find? e'' := by
          symm
          exact DEnv_find?_eq_lookup (env := D) (e := e'')
        have hR' :
            (renameDEnv ρ D).find? e' =
              match D.find? e'' with
              | some ts' => some (ts'.map (renameValType ρ))
              | none => none := by
          simpa [renameDEnv, he'_eq, hEqD] using hR
        have hL'' :
            (renameDEnv ρ (updateD D e ts)).find? e' =
              match D.find? e'' with
              | some ts' => some (ts'.map (renameValType ρ))
              | none => none := by
          simpa [hFindUpd] using hL'
        have hEqLR :
            (renameDEnv ρ (updateD D e ts)).find? e' = (renameDEnv ρ D).find? e' := by
          simpa [hR'] using hL''
        rw [hEqLR, hrhs]

/-! ## Renamed updateG Lookup Corollaries -/
/-- Lookup after updateG at the same endpoint (renamed version). -/
theorem lookupG_updateG_rename_eq (ρ : SessionRenaming) (G : GEnv) (ep : Endpoint) (L : LocalType) :
    lookupG (renameGEnv ρ (updateG G ep L)) (renameEndpoint ρ ep) =
      some (renameLocalType ρ L) := by
  rw [renameGEnv_updateG]
  exact lookupG_updateG_eq

/-- Lookup after updateG at a different endpoint (renamed version). -/
theorem lookupG_updateG_rename_neq (ρ : SessionRenaming) (G : GEnv) (ep ep' : Endpoint) (L : LocalType)
    (hne : ep ≠ ep') :
    lookupG (renameGEnv ρ (updateG G ep L)) (renameEndpoint ρ ep') =
      lookupG (renameGEnv ρ G) (renameEndpoint ρ ep') := by
  rw [renameGEnv_updateG]
  have hne' : renameEndpoint ρ ep ≠ renameEndpoint ρ ep' := fun h =>
    hne (renameEndpoint_inj ρ _ _ h)
  exact lookupG_update_neq (renameGEnv ρ G) (renameEndpoint ρ ep) (renameEndpoint ρ ep')
    (renameLocalType ρ L) hne'

/-! ## Renamed updateD Lookup Corollaries -/
/-- Lookup after updateD at the same edge (renamed version). -/
theorem lookupD_updateD_rename_eq (ρ : SessionRenaming) (D : DEnv) (e : Edge) (ts : Trace) :
    lookupD (renameDEnv ρ (updateD D e ts)) (renameEdge ρ e) =
      ts.map (renameValType ρ) := by
  rw [renameDEnv_updateD]
  exact lookupD_update_eq (renameDEnv ρ D) (renameEdge ρ e) (ts.map (renameValType ρ))

/-- Lookup after updateD at a different edge (renamed version). -/
theorem lookupD_updateD_rename_neq (ρ : SessionRenaming) (D : DEnv) (e e' : Edge) (ts : Trace)
    (hne : e ≠ e') :
    lookupD (renameDEnv ρ (updateD D e ts)) (renameEdge ρ e') =
      lookupD (renameDEnv ρ D) (renameEdge ρ e') := by
  rw [renameDEnv_updateD]
  have hne' : renameEdge ρ e ≠ renameEdge ρ e' := fun h =>
    hne (renameEdge_inj ρ _ _ h)
  exact lookupD_update_neq (renameDEnv ρ D) (renameEdge ρ e) (renameEdge ρ e')
    (ts.map (renameValType ρ)) hne'

end
