import Protocol.Typing.Compatibility.Core

/-! # Protocol.Typing.Compatibility.DEnvLemmas

DEnv/SEnv fold and lookup compatibility lemmas.
-/

/-
The Problem. Preservation proofs require robust lookup facts for fold-based
DEnv/SEnv constructions.

Solution Structure. Proves fold/lookup lemmas for DEnv/SEnv utilities.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical
open Batteries

section

/-! ## Fold and Lookup Compatibility -/

private theorem lookupSEnv_foldl_insertPairS
    {L : List (Var × ValType)} {env : SEnv} {x : Var} {v : Option ValType}
    (hlookup : lookupSEnv env x = v)
    (hNot : ∀ T, (x, T) ∈ L → False) :
    lookupSEnv (L.foldl insertPairS env) x = v := by
  induction L generalizing env with
  | nil =>
      simpa using hlookup
  | cons p L ih =>
      cases p with
      | mk x' T' =>
          have hNot' : ∀ T, (x, T) ∈ L → False := by
            intro T hmem
            exact hNot T (List.mem_cons_of_mem _ hmem)
          have hneq : x' ≠ x := by
            intro hEq
            exact hNot T' (by simpa [hEq])
          have hlookup' : lookupSEnv (updateSEnv env x' T') x = v := by
            have h := lookupSEnv_update_neq (env:=env) (x:=x') (y:=x) (T:=T') hneq
            simpa [hlookup] using h
          simpa [List.foldl, insertPairS] using
            (ih (env := updateSEnv env x' T') (hlookup := hlookup') (hNot := hNot'))

/-! ## RBMap Insert-If-Missing Folds -/

def insertIfMissing (acc : RBMap Edge Trace compare) (k : Edge) (v : Trace) :
    RBMap Edge Trace compare :=
  match acc.find? k with
  | some _ => acc
  | none => acc.insert k v

theorem rbmap_foldl_preserve
    (L : List (Edge × Trace)) (acc : RBMap Edge Trace compare) (e : Edge) (ts : Trace)
    (hfind : acc.find? e = some ts) :
    (L.foldl (fun acc p => insertIfMissing acc p.1 p.2) acc).find? e = some ts := by
  induction L generalizing acc with
  | nil =>
      simpa [hfind]
  | cons hd tl ih =>
      cases hd with
      | mk k v =>
          cases hacc : acc.find? k with
          | some _ =>
              simpa [List.foldl, insertIfMissing, hacc] using (ih (acc := acc) hfind)
          | none =>
              have hkne : k ≠ e := by
                intro hEq
                subst hEq
                simpa [hfind] using hacc
              have hne : compare e k ≠ .eq := by
                intro hEq
                exact hkne (by symm; exact (Edge.compare_eq_iff_eq e k).1 hEq)
              have hacc' : (acc.insert k v).find? e = acc.find? e := by
                simpa using (RBMap.find?_insert_of_ne (t := acc) (k := k) (v := v) (k' := e) hne)
              have hfind' : (acc.insert k v).find? e = some ts := by
                simpa [hfind] using hacc'
              simpa [List.foldl, insertIfMissing, hacc] using
                (ih (acc := acc.insert k v) hfind')

/-! ## RBMap Fold Lookup-None Case -/

theorem rbmap_foldl_none
    (L : List (Edge × Trace)) (acc : RBMap Edge Trace compare) (e : Edge)
    (hfind : acc.find? e = none) :
    (L.foldl (fun acc p => insertIfMissing acc p.1 p.2) acc).find? e = L.lookup e := by
  induction L generalizing acc with
  | nil =>
      simpa [List.lookup, hfind]
  | cons hd tl ih =>
      cases hd with
      | mk k v =>
          by_cases hEq : e = k
          · subst hEq
            have hEq' : compare e e = .eq := by
              simp
            have hfind' : (acc.insert e v).find? e = some v := by
              simpa using (RBMap.find?_insert_of_eq (t := acc) (k := e) (v := v) (k' := e) hEq')
            have hpreserve :
                (tl.foldl (fun acc p => insertIfMissing acc p.1 p.2) (acc.insert e v)).find? e =
                  some v :=
              rbmap_foldl_preserve (L := tl) (acc := acc.insert e v) (e := e) (ts := v) hfind'
            simpa [List.lookup, beq_self_eq_true, insertIfMissing, hfind] using hpreserve
          · have hbeq : (e == k) = false := beq_eq_false_iff_ne.mpr hEq
            cases hacc : acc.find? k with
            | some _ =>
                have ih' := ih (acc := acc) hfind
                simpa [List.foldl, insertIfMissing, hacc, List.lookup, hbeq] using ih'
            | none =>
                have hne : compare e k ≠ .eq := by
                  intro hEq'
                  exact hEq ((Edge.compare_eq_iff_eq e k).1 hEq')
                have hacc' : (acc.insert k v).find? e = acc.find? e := by
                  simpa using (RBMap.find?_insert_of_ne (t := acc) (k := k) (v := v) (k' := e) hne)
                have hfind' : (acc.insert k v).find? e = none := by
                  simpa [hfind] using hacc'
                have ih' := ih (acc := acc.insert k v) hfind'
                simpa [List.foldl, insertIfMissing, hacc, List.lookup, hbeq] using ih'

/-! ## DEnv Append Lookup -/

theorem findD_append_left {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType} :
    D₁.find? e = some ts →
    (D₁ ++ D₂).find? e = some ts := by
  intro hfind
  have hfind_map : D₁.map.find? e = some ts := by
    simpa [DEnv.find?] using hfind
  have hfold_list :
      (D₂.map.toList.foldl (fun acc p => insertIfMissing acc p.1 p.2) D₁.map).find? e = some ts :=
    rbmap_foldl_preserve (L := D₂.map.toList) (acc := D₁.map) (e := e) (ts := ts) hfind_map
  have hfold :
      (RBMap.foldl (fun acc k v => insertIfMissing acc k v) D₁.map D₂.map).find? e = some ts := by
    simpa [RBMap.foldl_eq_foldl_toList] using hfold_list
  change (DEnvUnion D₁ D₂).find? e = some ts
  simpa [DEnvUnion, insertIfMissing] using hfold

theorem findD_append_right {D₁ D₂ : DEnv} {e : Edge} :
    D₁.find? e = none →
    (D₁ ++ D₂).find? e = D₂.find? e := by
  intro hfind
  have hfind_map : D₁.map.find? e = none := by
    simpa [DEnv.find?] using hfind
  have hfold_list :
      (D₂.map.toList.foldl (fun acc p => insertIfMissing acc p.1 p.2) D₁.map).find? e =
        D₂.map.toList.lookup e :=
    rbmap_foldl_none (L := D₂.map.toList) (acc := D₁.map) (e := e) hfind_map
  have hfold :
      (RBMap.foldl (fun acc k v => insertIfMissing acc k v) D₁.map D₂.map).find? e =
        D₂.map.toList.lookup e := by
    simpa [RBMap.foldl_eq_foldl_toList] using hfold_list
  have hlookup : D₂.map.toList.lookup e = D₂.map.find? e :=
    lookup_toList_eq_find? (m := D₂.map) (e := e)
  have hfold' :
      (RBMap.foldl (fun acc k v => insertIfMissing acc k v) D₁.map D₂.map).find? e =
        D₂.map.find? e := by
    simpa [hlookup] using hfold
  change (DEnvUnion D₁ D₂).find? e = D₂.map.find? e
  simpa [DEnvUnion, insertIfMissing] using hfold'

/-! ## DEnv Session-Set Consequences -/

theorem SessionsOfD_append_left {D₁ D₂ : DEnv} :
    SessionsOfD D₁ ⊆ SessionsOfD (D₁ ++ D₂) := by
  intro s hs
  rcases hs with ⟨e, ts, hFind, hSid⟩
  exact ⟨e, ts, findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) hFind, hSid⟩

theorem SessionsOfD_append_right {D₁ D₂ : DEnv} :
    SessionsOfD D₂ ⊆ SessionsOfD (D₁ ++ D₂) := by
  intro s hs
  rcases hs with ⟨e, ts, hFind, hSid⟩
  cases hLeft : D₁.find? e with
  | some ts₁ =>
      exact ⟨e, ts₁, findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts₁) hLeft, hSid⟩
  | none =>
      have hFind' := findD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hLeft
      exact ⟨e, ts, by simpa [hFind'] using hFind, hSid⟩

theorem SessionsOfD_append_subset {D₁ D₂ : DEnv} :
    SessionsOfD (D₁ ++ D₂) ⊆ SessionsOfD D₁ ∪ SessionsOfD D₂ := by
  intro s hs
  rcases hs with ⟨e, ts, hFind, hSid⟩
  cases hLeft : D₁.find? e with
  | some ts₁ =>
      have hIn : s ∈ SessionsOfD D₁ := ⟨e, ts₁, hLeft, hSid⟩
      exact Or.inl hIn
  | none =>
      have hRight := findD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hLeft
      have hFind' : D₂.find? e = some ts := by
        simpa [hRight] using hFind
      have hIn : s ∈ SessionsOfD D₂ := ⟨e, ts, hFind', hSid⟩
      exact Or.inr hIn

/-! ## DEnv Session-Set Under updateD -/

theorem SessionsOfD_updateD_subset {D : DEnv} {e : Edge} {ts : List ValType} :
    SessionsOfD (updateD D e ts) ⊆ SessionsOfD D ∪ {e.sid} := by
  intro s hs
  rcases hs with ⟨e', ts', hFind, hSid⟩
  by_cases hEq : e' = e
  · subst hEq
    right
    simpa [hSid]
  · left
    have hFind' : D.find? e' = some ts' := by
      have h' : (updateD D e ts).find? e' = D.find? e' :=
        findD_update_neq D e e' ts (Ne.symm hEq)
      simpa [h'] using hFind
    exact ⟨e', ts', hFind', hSid⟩

theorem lookupD_entry_of_nonempty {D : DEnv} {e : Edge} :
    lookupD D e ≠ [] →
    ∃ ts, D.find? e = some ts := by
  intro hne
  cases hFind : D.find? e with
  | none =>
      have hlookup : lookupD D e = [] := by
        simp [lookupD, hFind]
      exact (hne hlookup).elim
  | some ts =>
      exact ⟨ts, by simpa [hFind]⟩

/-! ## GEnv Append Lookup -/

/-- Lookup in appended GEnv prefers the left. -/
theorem lookupG_append_left {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType} :
    lookupG G₁ e = some L →
    lookupG (G₁ ++ G₂) e = some L := by
  intro hLookup
  induction G₁ with
  | nil =>
      simp [lookupG] at hLookup
  | cons hd tl ih =>
      cases hEq : (e == hd.1) with
      | true =>
          have hL : hd.2 = L := by
            simpa [lookupG, List.lookup, hEq] using hLookup
          simp [lookupG, List.lookup, hEq, hL]
      | false =>
          have hLookup' : lookupG tl e = some L := by
            simpa [lookupG, List.lookup, hEq] using hLookup
          have ih' := ih hLookup'
          simpa [lookupG, List.lookup, hEq] using ih'

/-- Lookup in appended GEnv falls back to the right when left is missing. -/
theorem lookupG_append_right {G₁ G₂ : GEnv} {e : Endpoint} :
    lookupG G₁ e = none →
    lookupG (G₁ ++ G₂) e = lookupG G₂ e := by
  intro hLookup
  induction G₁ with
  | nil =>
      simp [lookupG] at hLookup ⊢
  | cons hd tl ih =>
      cases hEq : (e == hd.1) with
      | true =>
          have : False := by
            simpa [lookupG, List.lookup, hEq] using hLookup
          exact this.elim
      | false =>
          have hLookup' : lookupG tl e = none := by
            simpa [lookupG, List.lookup, hEq] using hLookup
          have ih' := ih hLookup'
          simpa [lookupG, List.lookup, hEq] using ih'

/-! ## GEnv Append Lookup Inversion -/

/-- Invert lookup in an appended GEnv. -/
theorem lookupG_append_inv {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType} :
    lookupG (G₁ ++ G₂) e = some L →
    lookupG G₁ e = some L ∨ (lookupG G₁ e = none ∧ lookupG G₂ e = some L) := by
  intro hLookup
  cases hLeft : lookupG G₁ e with
  | some L₁ =>
      left
      have hLeft' := lookupG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L₁) hLeft
      have hEq : L₁ = L := by
        have : some L₁ = some L := by simpa [hLeft'] using hLookup
        cases this
        rfl
      simpa [hEq] using hLeft
  | none =>
      right
      have hRight := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hLeft
      have hLookup' : lookupG G₂ e = some L := by
        simpa [hRight] using hLookup
      exact ⟨by simpa [hLeft], hLookup'⟩

/-! ## GEnv Session-Set Consequences -/

theorem SessionsOf_append_right_subset {G₁ G₂ : GEnv} :
    SessionsOf G₂ ⊆ SessionsOf (G₁ ++ G₂) := by
  intro s hs
  rcases hs with ⟨e, L, hLookup, hSid⟩
  cases hLeft : lookupG G₁ e with
  | some L₁ =>
      exact ⟨e, L₁, lookupG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L₁) hLeft, hSid⟩
  | none =>
      have hRight := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hLeft
      exact ⟨e, L, by simpa [hRight] using hLookup, hSid⟩

/-- Sessions in an appended GEnv are contained in the union of sessions. -/
theorem SessionsOf_append_subset {G₁ G₂ : GEnv} :
    SessionsOf (G₁ ++ G₂) ⊆ SessionsOf G₁ ∪ SessionsOf G₂ := by
  intro s hs
  rcases hs with ⟨e, L, hLookup, hSid⟩
  cases hLeft : lookupG G₁ e with
  | some L₁ =>
      exact Or.inl ⟨e, L₁, hLeft, hSid⟩
  | none =>
      have hRight := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hLeft
      have hLookup' : lookupG G₂ e = some L := by
        simpa [hRight] using hLookup
      exact Or.inr ⟨e, L, hLookup', hSid⟩

/-- Left sessions embed into appended GEnv sessions. -/
theorem SessionsOf_append_left {G₁ G₂ : GEnv} :
    SessionsOf G₁ ⊆ SessionsOf (G₁ ++ G₂) := by
  intro s hs
  rcases hs with ⟨e, L, hLookup, hSid⟩
  exact ⟨e, L, lookupG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hLookup, hSid⟩

end
