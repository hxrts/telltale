import SessionTypes.GlobalType.Closedness.CorePredicates

/-! # SessionTypes.GlobalType.Closedness.SubstitutionLemmas

Substitution and free-variable subset lemmas for closed global types.
-/

/-
The Problem. Closedness reasoning must survive substitution and branch-level
manipulations used by projection and unfolding proofs.

Solution Structure. Proves subset and preservation lemmas for free variables
under substitution across global types and branch lists.
-/

set_option linter.dupNamespace false

namespace SessionTypes.GlobalType

/-! ## Substitution and Free-Variable Lemmas -/

/-! ## Branch Helper: Head Case -/

/-- Helper for freeVars_substitute_subset: branches case with explicit IH.

Free variables of a substituted term are bounded by original free vars (minus t) plus repl's free vars.
This is the key structural lemma for closedness preservation.

**Coq reference:** `gType_fv_subst` in `coGlobal.v` (line 753). -/
private theorem freeVars_substituteBranches_subset_aux_head
    {n : Nat} {t : String} {repl : GlobalType}
    (ih : ∀ g' : GlobalType, sizeOf g' < n →
          ∀ v, v ∈ (g'.substitute t repl).freeVars →
          (v ∈ g'.freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars)
    (head : Label × GlobalType) (tail : List (Label × GlobalType))
    (hsize : sizeOf head.2 < n) (v : String)
    (hv : v ∈ (head.2.substitute t repl).freeVars) :
    (v ∈ freeVarsOfBranches (head :: tail) ∧ v ≠ t) ∨ v ∈ repl.freeVars := by
  -- Head case: push IH result into the full branch list.
  have hsub := ih head.2 hsize v hv
  cases hsub with
  | inl hcase =>
      left
      have hmem : v ∈ freeVarsOfBranches (head :: tail) := by
        simp [freeVarsOfBranches, List.mem_append, hcase.1]
      exact ⟨hmem, hcase.2⟩
  | inr hmem =>
      right
      exact hmem

/- Helper: tail case for freeVars_substituteBranches_subset_aux. -/
/-! ## Branch Helper: Tail Case -/

private theorem freeVars_substituteBranches_subset_aux_tail
    {n : Nat} {t : String} {repl : GlobalType}
    (_ih : ∀ g' : GlobalType, sizeOf g' < n →
          ∀ v, v ∈ (g'.substitute t repl).freeVars →
          (v ∈ g'.freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars)
    (head : Label × GlobalType) (tail : List (Label × GlobalType))
    (v : String)
    (hsub : (v ∈ freeVarsOfBranches tail ∧ v ≠ t) ∨ v ∈ repl.freeVars) :
    (v ∈ freeVarsOfBranches (head :: tail) ∧ v ≠ t) ∨ v ∈ repl.freeVars := by
  -- Tail case: lift membership from tail to full branch list.
  cases hsub with
  | inl hcase =>
      left
      have hmem : v ∈ freeVarsOfBranches (head :: tail) := by
        simp [freeVarsOfBranches, List.mem_append, hcase.1]
      exact ⟨hmem, hcase.2⟩
  | inr hmem =>
      right
      exact hmem

/-! ## Branch Helper: Recursive Auxiliary -/

private def freeVars_substituteBranches_subset_aux
    {n : Nat} {t : String} {repl : GlobalType}
    (ih : ∀ g' : GlobalType, sizeOf g' < n →
          ∀ v, v ∈ (g'.substitute t repl).freeVars →
          (v ∈ g'.freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars)
    (branches : List (Label × GlobalType))
    (hsize : ∀ p ∈ branches, sizeOf p.2 < n)
    (v : String)
    (hv : v ∈ freeVarsOfBranches (substituteBranches branches t repl)) :
    (v ∈ freeVarsOfBranches branches ∧ v ≠ t) ∨ v ∈ repl.freeVars := by
  -- Split on whether the free var comes from the head or tail branch.
  match branches with
  | [] =>
      simp only [substituteBranches, freeVarsOfBranches, List.not_mem_nil] at hv
  | head :: tail =>
      simp only [substituteBranches, freeVarsOfBranches, List.mem_append] at hv
      cases hv with
      | inl hv_head =>
          have hsize_head : sizeOf head.2 < n := hsize head List.mem_cons_self
          exact freeVars_substituteBranches_subset_aux_head ih head tail hsize_head v hv_head
      | inr hv_tail =>
          have hsize_tail : ∀ p ∈ tail, sizeOf p.2 < n := fun p hp =>
            hsize p (List.mem_cons_of_mem head hp)
          have hsub := freeVars_substituteBranches_subset_aux ih tail hsize_tail v hv_tail
          exact freeVars_substituteBranches_subset_aux_tail ih head tail v hsub

/-! ## Strong-Induction Size Bounds -/

/-- Strong induction principle for freeVars_substitute_subset. -/
private theorem sizeOf_snd_lt_comm_of_mem (sender receiver : String)
    {branches : List (Label × GlobalType)} {p : Label × GlobalType} (hp : p ∈ branches) :
    sizeOf p.2 < sizeOf (GlobalType.comm sender receiver branches) := by
  -- Size decreases from comm to any continuation.
  have h1 : sizeOf p.2 < sizeOf p := by
    cases p with
    | mk l g => simp; omega
  have h2 : sizeOf p < 1 + sizeOf branches := by
    have := List.sizeOf_lt_of_mem hp
    omega
  have h3 : 1 + sizeOf branches < sizeOf (GlobalType.comm sender receiver branches) := by
    simp [GlobalType.comm.sizeOf_spec]
    have hs : 0 < sizeOf sender := by
      have : sizeOf sender = 1 + sizeOf sender.bytes + sizeOf sender.isValidUTF8 := rfl
      omega
    have hr : 0 < sizeOf receiver := by
      have : sizeOf receiver = 1 + sizeOf receiver.bytes + sizeOf receiver.isValidUTF8 := rfl
      omega
    omega
  exact Nat.lt_trans h1 (Nat.lt_trans h2 h3)

/-! ## Strong-Induction Cases: end/var/mu-shadowed -/

private theorem freeVars_substitute_subset_strong_end
    {t : String} {repl : GlobalType} {v : String}
    (hv : v ∈ (GlobalType.end.substitute t repl).freeVars) :
    (v ∈ GlobalType.end.freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars := by
  -- end has no free vars, so the hypothesis is impossible.
  simp [GlobalType.substitute, GlobalType.freeVars] at hv

private theorem freeVars_substitute_subset_strong_var
    {t : String} {repl : GlobalType} {v w : String}
    (hv : v ∈ ((GlobalType.var w).substitute t repl).freeVars) :
    (v ∈ (GlobalType.var w).freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars := by
  -- var case splits on whether the variable is substituted.
  by_cases hwt : w = t
  · right
    simpa [GlobalType.substitute, hwt] using hv
  · have hv' : v = w := by
      simpa [GlobalType.substitute, hwt, GlobalType.freeVars] using hv
    left
    refine ⟨?_, ?_⟩
    · simp [hv', GlobalType.freeVars]
    · simpa [hv'] using hwt

private theorem freeVars_substitute_subset_strong_mu_shadowed
    {t : String} {repl : GlobalType} {v : String}
    (s : String) (inner : GlobalType) (hst : s = t)
    (hv : v ∈ ((GlobalType.mu s inner).substitute t repl).freeVars) :
    (v ∈ (GlobalType.mu s inner).freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars := by
  -- Shadowed substitution keeps the mu body unchanged.
  have hv' : v ∈ inner.freeVars ∧ v ≠ s := by
    simpa [GlobalType.substitute, GlobalType.freeVars, hst, List.mem_filter,
      bne_iff_ne, ne_eq] using hv
  left
  have hmem : v ∈ (GlobalType.mu s inner).freeVars := by
    simpa [GlobalType.freeVars, List.mem_filter, bne_iff_ne, ne_eq, hst] using hv'
  have hne : v ≠ t := by simpa [hst] using hv'.2
  exact ⟨hmem, hne⟩

/-! ## Strong-Induction Cases: mu/comm -/

private theorem freeVars_substitute_subset_strong_mu_unshadowed
    {n : Nat} {t : String} {repl : GlobalType} {v : String}
    (ih : ∀ g' : GlobalType, sizeOf g' < n →
          ∀ v, v ∈ (g'.substitute t repl).freeVars →
          (v ∈ g'.freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars)
    (s : String) (inner : GlobalType) (hsize : sizeOf (GlobalType.mu s inner) ≤ n)
    (hst : s ≠ t)
    (hv : v ∈ ((GlobalType.mu s inner).substitute t repl).freeVars) :
    (v ∈ (GlobalType.mu s inner).freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars := by
  -- Unshadowed substitution recurses into the body.
  have hv' : v ∈ (inner.substitute t repl).freeVars ∧ v ≠ s := by
    simpa [GlobalType.substitute, GlobalType.freeVars, hst, List.mem_filter,
      bne_iff_ne, ne_eq] using hv
  have hinner_lt : sizeOf inner < n := by
    have hlt : sizeOf inner < sizeOf (GlobalType.mu s inner) := by
      simp [GlobalType.mu.sizeOf_spec]; omega
    exact Nat.lt_of_lt_of_le hlt hsize
  have hsub := ih inner hinner_lt v hv'.1
  cases hsub with
  | inl hcase =>
      left
      have hmem : v ∈ (GlobalType.mu s inner).freeVars := by
        simp [GlobalType.freeVars, List.mem_filter, bne_iff_ne, ne_eq, hcase.1, hv'.2]
      exact ⟨hmem, hcase.2⟩
  | inr hmem =>
      right
      exact hmem

private theorem freeVars_substitute_subset_strong_mu
    {n : Nat} {t : String} {repl : GlobalType} {v : String}
    (ih : ∀ g' : GlobalType, sizeOf g' < n →
          ∀ v, v ∈ (g'.substitute t repl).freeVars →
          (v ∈ g'.freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars)
    (s : String) (inner : GlobalType) (hsize : sizeOf (GlobalType.mu s inner) ≤ n)
    (hv : v ∈ ((GlobalType.mu s inner).substitute t repl).freeVars) :
    (v ∈ (GlobalType.mu s inner).freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars := by
  -- mu case splits on whether substitution is shadowed.
  by_cases hst : s = t
  · exact freeVars_substitute_subset_strong_mu_shadowed s inner hst hv
  · exact freeVars_substitute_subset_strong_mu_unshadowed ih s inner hsize hst hv

/-! ## Strong-Induction Case: comm -/

private theorem freeVars_substitute_subset_strong_comm
    {n : Nat} {t : String} {repl : GlobalType} {v : String}
    (ih : ∀ g' : GlobalType, sizeOf g' < n →
          ∀ v, v ∈ (g'.substitute t repl).freeVars →
          (v ∈ g'.freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars)
    (sender receiver : String) (branches : List (Label × GlobalType))
    (hsize : sizeOf (GlobalType.comm sender receiver branches) ≤ n)
    (hv : v ∈ freeVarsOfBranches (substituteBranches branches t repl)) :
    (v ∈ (GlobalType.comm sender receiver branches).freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars := by
  -- comm case reduces to the branch helper.
  have hbranch_sizes : ∀ p ∈ branches, sizeOf p.2 < n := by
    intro p hp
    exact Nat.lt_of_lt_of_le (sizeOf_snd_lt_comm_of_mem sender receiver hp) hsize
  have hsub := freeVars_substituteBranches_subset_aux ih branches hbranch_sizes v hv
  cases hsub with
  | inl hcase =>
      left
      simpa [GlobalType.freeVars] using hcase
  | inr hmem =>
      right
      exact hmem

/-! ## Strong-Induction Driver -/

private theorem freeVars_substitute_subset_strong (n : Nat) :
    ∀ body : GlobalType, sizeOf body ≤ n →
    ∀ t repl v, v ∈ (body.substitute t repl).freeVars →
    (v ∈ body.freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars := by
  -- Strong induction on size, splitting by constructor.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro body hsize t repl v hv
      have ih' : ∀ g' : GlobalType, sizeOf g' < n →
            ∀ v, v ∈ (g'.substitute t repl).freeVars →
            (v ∈ g'.freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars := by
        intro g' hg' v' hv'
        exact ih (sizeOf g') hg' g' (Nat.le_refl _) t repl v' hv'
      match body with
      | .end => exact freeVars_substitute_subset_strong_end (t:=t) (repl:=repl) (v:=v) hv
      | .var w => exact freeVars_substitute_subset_strong_var (t:=t) (repl:=repl) (v:=v) (w:=w) hv
      | .mu s inner =>
          exact freeVars_substitute_subset_strong_mu ih' s inner hsize (t:=t) (repl:=repl) (v:=v) hv
      | .comm sender receiver branches =>
          simp [GlobalType.substitute, GlobalType.freeVars] at hv
          exact freeVars_substitute_subset_strong_comm ih' sender receiver branches hsize hv
      | .delegate p q sid r cont =>
          -- Delegate case: freeVars of delegate = freeVars of cont
          simp [GlobalType.substitute, GlobalType.freeVars] at hv
          have hcont_size : sizeOf cont < sizeOf (GlobalType.delegate p q sid r cont) := by
            simp only [GlobalType.delegate.sizeOf_spec]
            omega
          have hcont_lt : sizeOf cont < n := Nat.lt_of_lt_of_le hcont_size hsize
          exact ih' cont hcont_lt v hv

/-! ## Substitution Free-Variable Subset Corollaries -/

/-- Main theorem: free vars of substituted type are bounded. -/
theorem freeVars_substitute_subset (body : GlobalType) (t : String) (repl : GlobalType)
    (v : String) (hv : v ∈ (body.substitute t repl).freeVars) :
    (v ∈ body.freeVars ∧ v ≠ t) ∨ v ∈ repl.freeVars :=
  freeVars_substitute_subset_strong (sizeOf body) body (Nat.le_refl _) t repl v hv

private theorem freeVars_substituteBranches_subset_head
    (head : Label × GlobalType) (tail : List (Label × GlobalType))
    (t : String) (repl : GlobalType) (v : String)
    (hv : v ∈ (head.2.substitute t repl).freeVars) :
    (v ∈ freeVarsOfBranches (head :: tail) ∧ v ≠ t) ∨ v ∈ repl.freeVars := by
  -- Head case: lift the single-type lemma into the branch list.
  have hsub := freeVars_substitute_subset head.2 t repl v hv
  cases hsub with
  | inl hcase =>
      left
      have hmem : v ∈ freeVarsOfBranches (head :: tail) := by
        simp [freeVarsOfBranches, List.mem_append, hcase.1]
      exact ⟨hmem, hcase.2⟩
  | inr hmem =>
      right
      exact hmem

/-- Corollary for branches: free vars of substituted branches are bounded. -/
theorem freeVars_substituteBranches_subset (branches : List (Label × GlobalType))
    (t : String) (repl : GlobalType) (v : String)
    (hv : v ∈ freeVarsOfBranches (substituteBranches branches t repl)) :
    (v ∈ freeVarsOfBranches branches ∧ v ≠ t) ∨ v ∈ repl.freeVars := by
  -- Dispatch to the head/tail helpers.
  match branches with
  | [] =>
      simp only [substituteBranches, freeVarsOfBranches, List.not_mem_nil] at hv
  | head :: tail =>
      simp only [substituteBranches, freeVarsOfBranches, List.mem_append] at hv
      cases hv with
      | inl hv_head =>
          exact freeVars_substituteBranches_subset_head head tail t repl v hv_head
      | inr hv_tail =>
          have hsub := freeVars_substituteBranches_subset tail t repl v hv_tail
          cases hsub with
          | inl hcase =>
              left
              have hmem : v ∈ freeVarsOfBranches (head :: tail) := by
                simp [freeVarsOfBranches, List.mem_append, hcase.1]
              exact ⟨hmem, hcase.2⟩
          | inr hmem =>
              right
              exact hmem

/-! ## Closedness under Substitution -/

/-- Substitution preserves closedness when both repl is closed AND body has no free vars other than t.

This is the precise property needed for mu-unfolding: if `(mu t body).isClosed`, then:
1. `repl = mu t body` is closed
2. `body.freeVars ⊆ [t]` (body has no free vars other than t)
Therefore `(body.substitute t repl).isClosed`.

**Coq reference:** Follows from `gType_fv_subst` in `coGlobal.v`. -/
theorem GlobalType.isClosed_substitute_of_closed' (body : GlobalType) (t : String) (repl : GlobalType)
    (hrepl_closed : repl.isClosed = true)
    (hbody_only_t : ∀ v ∈ body.freeVars, v = t) :
    (body.substitute t repl).isClosed = true := by
  simp only [GlobalType.isClosed, List.isEmpty_iff]
  simp only [GlobalType.isClosed, List.isEmpty_iff] at hrepl_closed
  by_contra hne
  have ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hne
  have hsub := freeVars_substitute_subset body t repl v hv
  cases hsub with
  | inl h =>
      -- v is in body.freeVars and v ≠ t
      -- But hbody_only_t says all vars in body.freeVars equal t
      -- Contradiction!
      have heq := hbody_only_t v h.1
      exact h.2 heq
  | inr hmem =>
      simp only [hrepl_closed, List.not_mem_nil] at hmem

/-! ## Closed μ-Body Free-Variable Characterization -/

/-- Mu type closedness implies body has only the bound variable free.

If `(mu t body).isClosed = true`, then `body.freeVars ⊆ [t]`. -/
theorem GlobalType.isClosed_mu_body_freeVars (t : String) (body : GlobalType)
    (hclosed : (GlobalType.mu t body).isClosed = true) :
    ∀ v ∈ body.freeVars, v = t := by
  simp only [GlobalType.isClosed, GlobalType.freeVars, List.isEmpty_iff] at hclosed
  intro v hv
  -- hclosed : body.freeVars.filter (· != t) = []
  -- hv : v ∈ body.freeVars
  -- Goal: v = t
  by_contra hne
  have hfilter : v ∈ body.freeVars.filter (fun x => x != t) := by
    simp only [List.mem_filter, bne_iff_ne]
    exact ⟨hv, hne⟩
  simp only [hclosed, List.not_mem_nil] at hfilter

/-! ## Closedness of μ-Unfold Substitution -/

/-- Mu-unfolding preserves closedness: if `(mu t body).isClosed`, then `(body.substitute t (mu t body)).isClosed`.

This is the key property needed for the mu case in step induction.
It combines:
1. `(mu t body).isClosed` → `mu t body` has no free vars
2. `(mu t body).isClosed` → body has only `t` as free var (`isClosed_mu_body_freeVars`)
3. Substitution doesn't add free vars beyond repl's vars (`isClosed_substitute_of_closed'`)

**Coq reference:** Follows from `gType_fv_subst` in `coGlobal.v`. -/
theorem GlobalType.isClosed_substitute_mu (t : String) (body : GlobalType)
    (hclosed : (GlobalType.mu t body).isClosed = true) :
    (body.substitute t (GlobalType.mu t body)).isClosed = true := by
  apply isClosed_substitute_of_closed' body t (.mu t body) hclosed
  exact isClosed_mu_body_freeVars t body hclosed


end SessionTypes.GlobalType
