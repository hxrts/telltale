import Protocol.Environments.Core.SessionInit

/-! # Protocol.Environments.Core.LookupLemmas

Final lookup/update lemmas for VarStore/SEnv/GEnv/Buffers.
-/

/-
The Problem. Downstream typing/coherence proofs rely on small algebraic lookup
facts over all runtime environments.

Solution Structure. Collects final lookup/update helper theorems.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical
open Batteries

section

/-! ## Environment Lemmas -/

theorem lookupStr_update_eq (store : VarStore) (x : Var) (v : Value) :
    lookupStr (updateStr store x v) x = some v := by
  induction store with
  | nil =>
    simp only [updateStr, lookupStr, List.lookup, beq_self_eq_true]
  | cons hd tl ih =>
    by_cases h : x = hd.1
    · simp [updateStr, lookupStr, h]
    · have hne : (x == hd.1) = false := beq_eq_false_iff_ne.mpr h
      simp [updateStr, lookupStr, List.lookup, h, hne]
      simpa [lookupStr] using ih

theorem lookupStr_update_neq (store : VarStore) (x y : Var) (v : Value) (hne : x ≠ y) :
    lookupStr (updateStr store x v) y = lookupStr store y := by
  induction store with
  | nil =>
    simp only [updateStr, lookupStr, List.lookup]
    have h : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
    simp only [h]
  | cons hd tl ih =>
    by_cases h : x = hd.1
    · have hyx : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
      have hyh : (y == hd.1) = false := beq_eq_false_iff_ne.mpr (h ▸ Ne.symm hne)
      simp [updateStr, lookupStr, List.lookup, h, hyh]
    · by_cases hy : y = hd.1
      · simp [updateStr, lookupStr, List.lookup, h, hy]
      · have hne' : (y == hd.1) = false := beq_eq_false_iff_ne.mpr hy
        simp [updateStr, lookupStr, List.lookup, h, hne']
        simpa [lookupStr] using ih

theorem lookupSEnv_update_eq (env : SEnv) (x : Var) (T : ValType) :
    lookupSEnv (updateSEnv env x T) x = some T := by
  induction env with
  | nil =>
      simp [lookupSEnv, updateSEnv]
  | cons hd tl ih =>
      by_cases h : x = hd.1
      · simp [lookupSEnv, updateSEnv, h]
      · have hne : (x == hd.1) = false := beq_eq_false_iff_ne.mpr h
        simp [lookupSEnv, updateSEnv, List.lookup, h, hne]
        simpa [lookupSEnv] using ih

theorem lookupSEnv_update_neq (env : SEnv) (x y : Var) (T : ValType) (hne : x ≠ y) :
    lookupSEnv (updateSEnv env x T) y = lookupSEnv env y := by
  induction env with
  | nil =>
      by_cases hy : y = x
      · exact (hne hy.symm).elim
      · have hbeq : (y == x) = false := beq_eq_false_iff_ne.mpr hy
        simp [lookupSEnv, updateSEnv, List.lookup, hbeq]
  | cons hd tl ih =>
      by_cases h : x = hd.1
      · have hy : y ≠ hd.1 := by
          intro hy
          exact hne (h.trans hy.symm)
        have hy' : (y == hd.1) = false := beq_eq_false_iff_ne.mpr hy
        simp [updateSEnv, lookupSEnv, List.lookup, h, hy']
      · simp [updateSEnv, lookupSEnv, List.lookup, h] at *
        by_cases hy : y = hd.1
        · simp [hy]
        · have hy' : (y == hd.1) = false := beq_eq_false_iff_ne.mpr hy
          simp [hy', ih]

/-- When x is already in S₁, updateSEnv finds and replaces it before reaching S₂. -/
theorem updateSEnv_append_left_of_mem {S₁ S₂ : SEnv} {x : Var} {T : ValType}
    (h : ∃ T', lookupSEnv S₁ x = some T') :
    updateSEnv (S₁ ++ S₂) x T = updateSEnv S₁ x T ++ S₂ := by
  induction S₁ with
  | nil => obtain ⟨_, hT'⟩ := h; simp [lookupSEnv] at hT'
  | cons hd tl ih =>
      by_cases heq : x = hd.1
      · -- Found at head: replace and we're done
        simp only [updateSEnv, heq, ↓reduceIte, List.cons_append]
      · -- Not at head: recurse
        simp only [updateSEnv, heq, ↓reduceIte, List.cons_append]
        obtain ⟨T', hT'⟩ := h
        have hT'' : lookupSEnv tl x = some T' := by
          simp only [lookupSEnv, List.lookup] at hT'
          have hne : (x == hd.1) = false := beq_eq_false_iff_ne.mpr heq
          simpa [hne] using hT'
        rw [ih ⟨T', hT''⟩]

theorem lookupG_update_eq (env : GEnv) (e : Endpoint) (L : LocalType) :
    lookupG (updateG env e L) e = some L := by
  exact lookupG_updateG_eq (env := env) (e := e) (L := L)

theorem lookupG_update_neq (env : GEnv) (e e' : Endpoint) (L : LocalType) (hne : e ≠ e') :
    lookupG (updateG env e L) e' = lookupG env e' := by
  simpa using (lookupG_updateG_ne (env := env) (e := e) (e' := e') (L := L) (Ne.symm hne))

/-- If (e', S') ∈ updateG env e L, then either (e' = e and S' = L), or (e', S') was in env. -/
theorem updateG_mem_of (env : GEnv) (e : Endpoint) (L : LocalType) (e' : Endpoint) (S' : LocalType)
    (h : (e', S') ∈ updateG env e L) :
    (e' = e ∧ S' = L) ∨ (e', S') ∈ env := by
  induction env with
  | nil =>
      simp only [updateG, List.mem_singleton] at h
      exact Or.inl (Prod.mk.inj h)
  | cons hd tl ih =>
      by_cases heq : e = hd.1
      · have h' : (e', S') = (e, L) ∨ (e', S') ∈ tl := by
          simpa [updateG, heq, List.mem_cons] using h
        cases h' with
        | inl hhead =>
            exact Or.inl (by simpa using hhead)
        | inr htl =>
            exact Or.inr (List.mem_cons_of_mem _ htl)
      · have h' : (e', S') = hd ∨ (e', S') ∈ updateG tl e L := by
          simpa [updateG, heq, List.mem_cons] using h
        cases h' with
        | inl hhead =>
            exact Or.inr (List.mem_cons.mpr (Or.inl hhead))
        | inr htl =>
            cases ih htl with
            | inl heq' => exact Or.inl heq'
            | inr hmem => exact Or.inr (List.mem_cons.mpr (Or.inr hmem))

/-- updateG preserves supply_fresh: if all endpoints in env have sid < supply,
    and e.sid < supply, then all endpoints in (updateG env e L) have sid < supply. -/
theorem updateG_preserves_supply_fresh (env : GEnv) (e : Endpoint) (L : LocalType)
    (supply : SessionId)
    (hFresh : ∀ e' S', (e', S') ∈ env → e'.sid < supply)
    (heFresh : e.sid < supply) :
    ∀ e' S', (e', S') ∈ updateG env e L → e'.sid < supply := by
  intro e' S' hMem
  cases updateG_mem_of env e L e' S' hMem with
  | inl heq =>
    rw [heq.1]
    exact heFresh
  | inr hmem =>
    exact hFresh e' S' hmem

/-- If lookupG returns some L, then (e, L) is in the list. -/
theorem lookupG_mem (env : GEnv) (e : Endpoint) (L : LocalType)
    (h : lookupG env e = some L) :
    (e, L) ∈ env := by
  simp only [lookupG] at h
  induction env with
  | nil =>
    simp only [List.lookup] at h
    exact Option.noConfusion h
  | cons hd tl ih =>
    simp only [List.lookup] at h
    split at h
    · simp only [Option.some.injEq] at h
      rename_i heq
      simp only [beq_iff_eq] at heq
      simp only [List.mem_cons]
      left
      exact Prod.ext heq h.symm
    · simp only [List.mem_cons]
      right
      exact ih h

/-- If lookupG returns some L, then e.sid < supply (using supply_fresh_G). -/
theorem lookupG_supply_fresh (env : GEnv) (e : Endpoint) (L : LocalType)
    (supply : SessionId)
    (hFresh : ∀ e' S', (e', S') ∈ env → e'.sid < supply)
    (h : lookupG env e = some L) :
    e.sid < supply := by
  have hMem := lookupG_mem env e L h
  exact hFresh e L hMem

theorem lookupBuf_update_eq (bufs : Buffers) (e : Edge) (buf : Buffer) :
    lookupBuf (updateBuf bufs e buf) e = buf := by
  exact lookupBuf_updateBuf_eq (bufs := bufs) (e := e) (buf := buf)

theorem lookupBuf_update_neq (bufs : Buffers) (e e' : Edge) (buf : Buffer) (hne : e ≠ e') :
    lookupBuf (updateBuf bufs e buf) e' = lookupBuf bufs e' := by
  simpa using (lookupBuf_updateBuf_ne (bufs := bufs) (e := e) (e' := e') (buf := buf) (Ne.symm hne))

-- lookupD lemmas are defined above near DEnv.



end
