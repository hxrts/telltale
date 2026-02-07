import SessionTypes.GlobalType.Semantics

set_option linter.dupNamespace false

/-! # SessionTypes.GlobalType.WellFormedLemmas

Well-formedness preservation under mu-unfolding (allVarsBound, allCommsNonEmpty,
noSelfComm, isProductive monotonicity).
-/

namespace SessionTypes.GlobalType
/-! ## Well-formedness Preservation under Mu-Unfolding

These lemmas show that unfolding a mu-type preserves well-formedness.
Key property: if `mu t body` is well-formed, then `body.substitute t (mu t body)` is well-formed. -/

/-! ## Helper lemmas for allVarsBound -/

/-- If t is in (x :: xs) and t ≠ x, then t is in xs. -/
theorem contains_cons_ne' {t x : String} {xs : List String}
    (hcontains : (x :: xs).contains t = true)
    (hne : t ≠ x) :
    xs.contains t = true := by
  rw [List.contains_cons] at hcontains
  simp only [Bool.or_eq_true] at hcontains
  cases hcontains with
  | inl heq =>
      simp only [beq_iff_eq] at heq
      exact absurd heq hne
  | inr hmem => exact hmem

-- allVarsBound is monotonic: if vars are bound with bound1, they're bound with any superset.
mutual
  theorem allVarsBound_mono (g : GlobalType) (bound₁ bound₂ : List String)
      (hsub : ∀ x, bound₁.contains x = true → bound₂.contains x = true)
      (hbound : g.allVarsBound bound₁ = true) :
      g.allVarsBound bound₂ = true := by
    match g with
    | .end => simp [GlobalType.allVarsBound]
    | .var t =>
        simp only [GlobalType.allVarsBound] at hbound ⊢
        exact hsub t hbound
    | .mu t body =>
        simp only [GlobalType.allVarsBound] at hbound ⊢
        apply allVarsBound_mono body (t :: bound₁) (t :: bound₂)
        · intro x hx
          rw [List.contains_cons] at hx ⊢
          simp only [Bool.or_eq_true] at hx ⊢
          cases hx with
          | inl heq => left; exact heq
          | inr hmem => right; exact hsub x hmem
        · exact hbound
    | .comm _ _ branches =>
        simp only [GlobalType.allVarsBound] at hbound ⊢
        exact allVarsBoundBranches_mono branches bound₁ bound₂ hsub hbound
    | .delegate _ _ _ _ cont =>
        simp only [GlobalType.allVarsBound] at hbound ⊢
        exact allVarsBound_mono cont bound₁ bound₂ hsub hbound

  theorem allVarsBoundBranches_mono (branches : List (Label × GlobalType))
      (bound₁ bound₂ : List String)
      (hsub : ∀ x, bound₁.contains x = true → bound₂.contains x = true)
      (hbound : allVarsBoundBranches branches bound₁ = true) :
      allVarsBoundBranches branches bound₂ = true := by
    match branches with
    | [] => rfl
    | (_, g) :: rest =>
        simp only [allVarsBoundBranches, Bool.and_eq_true] at hbound ⊢
        exact ⟨allVarsBound_mono g bound₁ bound₂ hsub hbound.1,
               allVarsBoundBranches_mono rest bound₁ bound₂ hsub hbound.2⟩
end

/-- Adding a duplicate element to bound doesn't change allVarsBound. -/
theorem allVarsBound_cons_dup (g : GlobalType) (x : String) (bound : List String)
    (hbound : g.allVarsBound (x :: bound) = true) :
    g.allVarsBound (x :: x :: bound) = true := by
  apply allVarsBound_mono g (x :: bound) (x :: x :: bound)
  · intro y hy
    rw [List.contains_cons] at hy ⊢
    simp only [Bool.or_eq_true] at hy ⊢
    cases hy with
    | inl heq => left; exact heq
    | inr hmem =>
        right
        rw [List.contains_cons]
        simp only [Bool.or_eq_true]
        right; exact hmem
  · exact hbound

/-- Removing a duplicate from bound preserves allVarsBound. -/
theorem allVarsBound_cons_dedup (g : GlobalType) (x : String) (bound : List String)
    (hbound : g.allVarsBound (x :: x :: bound) = true) :
    g.allVarsBound (x :: bound) = true := by
  apply allVarsBound_mono g (x :: x :: bound) (x :: bound)
  · intro y hy
    rw [List.contains_cons] at hy ⊢
    simp only [Bool.or_eq_true] at hy ⊢
    cases hy with
    | inl heq => left; exact heq
    | inr hmem =>
        rw [List.contains_cons] at hmem
        simp only [Bool.or_eq_true] at hmem
        cases hmem with
        | inl heq => left; exact heq
        | inr hmem' => right; exact hmem'
  · exact hbound

private theorem contains_cons_swap (x y z : String) (bound : List String)
    (hz : (x :: y :: bound).contains z = true) :
    (y :: x :: bound).contains z = true := by
  -- Move membership across the swapped head.
  rw [List.contains_cons] at hz ⊢
  simp only [Bool.or_eq_true] at hz ⊢
  cases hz with
  | inl heq =>
      right
      rw [List.contains_cons]
      simp only [Bool.or_eq_true]
      left; exact heq
  | inr hmem =>
      rw [List.contains_cons] at hmem
      simp only [Bool.or_eq_true] at hmem
      cases hmem with
      | inl heq => left; exact heq
      | inr hmem' =>
          right
          rw [List.contains_cons]
          simp only [Bool.or_eq_true]
          right; exact hmem'

/-- Swapping adjacent elements in bound preserves allVarsBound. -/
theorem allVarsBound_swap (g : GlobalType) (x y : String) (bound : List String)
    (hbound : g.allVarsBound (x :: y :: bound) = true) :
    g.allVarsBound (y :: x :: bound) = true := by
  -- Use contains_cons_swap to transfer membership across the swap.
  apply allVarsBound_mono g (x :: y :: bound) (y :: x :: bound)
  · intro z hz; exact contains_cons_swap x y z bound hz
  · exact hbound

mutual
  private theorem allVarsBound_substitute_var (t varName : String) (repl : GlobalType)
      (bound : List String)
      (hg : (GlobalType.var t).allVarsBound (varName :: bound) = true)
      (hrepl : repl.allVarsBound bound = true) :
      ((GlobalType.var t).substitute varName repl).allVarsBound bound = true := by
    -- Var case: either substitute repl or keep var t.
    simp only [GlobalType.substitute]
    split
    · exact hrepl
    · rename_i hne
      simp only [GlobalType.allVarsBound] at hg ⊢
      have hne' : t ≠ varName := by
        intro heq
        simp only [heq, beq_self_eq_true] at hne
        exact absurd trivial hne
      exact contains_cons_ne' hg hne'

  private theorem allVarsBound_substitute_mu_shadow (t varName : String) (inner : GlobalType)
      (bound : List String)
      (hg : inner.allVarsBound (t :: varName :: bound) = true)
      (heq : (t == varName) = true) :
      inner.allVarsBound (t :: bound) = true := by
    -- Shadowed binder: dedup the bound list.
    have heq' : t = varName := by simpa [beq_iff_eq] using heq
    subst heq'
    exact allVarsBound_cons_dedup inner t bound hg

  private theorem allVarsBound_substitute_mu_noshadow (t : String) (inner : GlobalType)
      (varName : String) (repl : GlobalType) (bound : List String)
      (hg : inner.allVarsBound (t :: varName :: bound) = true)
      (hrepl : repl.allVarsBound bound = true) :
      (inner.substitute varName repl).allVarsBound (t :: bound) = true := by
    -- Use swap+mono to align bound lists, then apply IH.
    have hg' : inner.allVarsBound (varName :: t :: bound) = true :=
      allVarsBound_swap inner t varName bound hg
    have hrepl' : repl.allVarsBound (t :: bound) = true := by
      apply allVarsBound_mono repl bound (t :: bound)
      · intro x hx
        rw [List.contains_cons]
        simp only [Bool.or_eq_true]
        right; exact hx
      · exact hrepl
    exact allVarsBound_substitute inner varName repl (t :: bound) hg' hrepl'

  /-- allVarsBound is preserved when substituting a closed type for a bound variable.

  **Key insight**: When we substitute `mu t body` for occurrences of `var t` in body,
  the result is still closed because `mu t body` binds t. -/
  theorem allVarsBound_substitute (g : GlobalType) (varName : String) (repl : GlobalType)
      (bound : List String)
      (hg : g.allVarsBound (varName :: bound) = true)
      (hrepl : repl.allVarsBound bound = true) :
      (g.substitute varName repl).allVarsBound bound = true := by
    match g with
    | .end => simp [GlobalType.substitute, GlobalType.allVarsBound]
    | .var t => exact allVarsBound_substitute_var t varName repl bound hg hrepl
    | .mu t inner =>
        simp only [GlobalType.substitute]
        split
        · -- t = varName, shadowed, so no substitution in inner
          rename_i heq
          simp only [GlobalType.allVarsBound] at hg ⊢
          exact allVarsBound_substitute_mu_shadow t varName inner bound hg heq
        · -- t ≠ varName
          simp only [GlobalType.allVarsBound] at hg ⊢
          exact allVarsBound_substitute_mu_noshadow t inner varName repl bound hg hrepl
    | .comm sender receiver branches =>
        simp only [GlobalType.substitute, GlobalType.allVarsBound] at hg ⊢
        exact allVarsBoundBranches_substitute branches varName repl bound hg hrepl
    | .delegate p q sid r cont =>
        simp only [GlobalType.substitute, GlobalType.allVarsBound] at hg ⊢
        exact allVarsBound_substitute cont varName repl bound hg hrepl

  theorem allVarsBoundBranches_substitute (branches : List (Label × GlobalType))
      (varName : String) (repl : GlobalType) (bound : List String)
      (hg : allVarsBoundBranches branches (varName :: bound) = true)
      (hrepl : repl.allVarsBound bound = true) :
      allVarsBoundBranches (substituteBranches branches varName repl) bound = true := by
    match branches with
    | [] => rfl
    | (label, cont) :: rest =>
        simp only [substituteBranches, allVarsBoundBranches, Bool.and_eq_true] at hg ⊢
        exact ⟨allVarsBound_substitute cont varName repl bound hg.1 hrepl,
               allVarsBoundBranches_substitute rest varName repl bound hg.2 hrepl⟩
end

mutual
  /-- allCommsNonEmpty is preserved by substitution. -/
  theorem allCommsNonEmpty_substitute (g : GlobalType) (varName : String) (repl : GlobalType)
      (hg : g.allCommsNonEmpty = true)
      (hrepl : repl.allCommsNonEmpty = true) :
      (g.substitute varName repl).allCommsNonEmpty = true := by
    match g with
    | .end => simp [GlobalType.substitute, GlobalType.allCommsNonEmpty]
    | .var t =>
        simp only [GlobalType.substitute]
        split
        · exact hrepl
        · simp [GlobalType.allCommsNonEmpty]
    | .mu t inner =>
        simp only [GlobalType.substitute]
        split
        · exact hg
        · simp only [GlobalType.allCommsNonEmpty] at hg ⊢
          exact allCommsNonEmpty_substitute inner varName repl hg hrepl
    | .comm sender receiver branches =>
        simp only [GlobalType.substitute, GlobalType.allCommsNonEmpty, Bool.and_eq_true] at hg ⊢
        constructor
        · -- Need: substituteBranches preserves non-emptiness
          -- substituteBranches preserves length, so if branches is non-empty, result is too
          match hb : branches with
          | [] => simp [List.isEmpty] at hg
          | _ :: _ => simp [substituteBranches, List.isEmpty]
        · exact allCommsNonEmptyBranches_substitute branches varName repl hg.2 hrepl
    | .delegate p q sid r cont =>
        simp only [GlobalType.substitute, GlobalType.allCommsNonEmpty] at hg ⊢
        exact allCommsNonEmpty_substitute cont varName repl hg hrepl

  theorem allCommsNonEmptyBranches_substitute (branches : List (Label × GlobalType))
      (varName : String) (repl : GlobalType)
      (hg : allCommsNonEmptyBranches branches = true)
      (hrepl : repl.allCommsNonEmpty = true) :
      allCommsNonEmptyBranches (substituteBranches branches varName repl) = true := by
    match branches with
    | [] => rfl
    | (label, cont) :: rest =>
        simp only [substituteBranches, allCommsNonEmptyBranches, Bool.and_eq_true] at hg ⊢
        exact ⟨allCommsNonEmpty_substitute cont varName repl hg.1 hrepl,
               allCommsNonEmptyBranches_substitute rest varName repl hg.2 hrepl⟩
end

mutual
  /-- noSelfComm is preserved by substitution. -/
  theorem noSelfComm_substitute (g : GlobalType) (varName : String) (repl : GlobalType)
      (hg : g.noSelfComm = true)
      (hrepl : repl.noSelfComm = true) :
      (g.substitute varName repl).noSelfComm = true := by
    match g with
    | .end => simp [GlobalType.substitute, GlobalType.noSelfComm]
    | .var t =>
        simp only [GlobalType.substitute]
        split
        · exact hrepl
        · simp [GlobalType.noSelfComm]
    | .mu t inner =>
        simp only [GlobalType.substitute]
        split
        · exact hg
        · simp only [GlobalType.noSelfComm] at hg ⊢
          exact noSelfComm_substitute inner varName repl hg hrepl
    | .comm sender receiver branches =>
        simp only [GlobalType.substitute, GlobalType.noSelfComm, Bool.and_eq_true] at hg ⊢
        exact ⟨hg.1, noSelfCommBranches_substitute branches varName repl hg.2 hrepl⟩
    | .delegate p q sid r cont =>
        simp only [GlobalType.substitute, GlobalType.noSelfComm, Bool.and_eq_true] at hg ⊢
        exact ⟨hg.1, noSelfComm_substitute cont varName repl hg.2 hrepl⟩

  theorem noSelfCommBranches_substitute (branches : List (Label × GlobalType))
      (varName : String) (repl : GlobalType)
      (hg : noSelfCommBranches branches = true)
      (hrepl : repl.noSelfComm = true) :
      noSelfCommBranches (substituteBranches branches varName repl) = true := by
    match branches with
    | [] => rfl
    | (label, cont) :: rest =>
        simp only [substituteBranches, noSelfCommBranches, Bool.and_eq_true] at hg ⊢
        exact ⟨noSelfComm_substitute cont varName repl hg.1 hrepl,
               noSelfCommBranches_substitute rest varName repl hg.2 hrepl⟩
end

-- Helper lemmas for isProductive monotonicity with respect to unguarded list

-- isProductive is monotonic: adding elements to unguarded can only make it false, not true.
-- Equivalently, if productive with more elements in unguarded, productive with fewer.
mutual
  theorem isProductive_mono (g : GlobalType) (ug1 ug2 : List String)
      (hsub : ∀ x, ug1.contains x = true → ug2.contains x = true)
      (hprod : g.isProductive ug2 = true) :
      g.isProductive ug1 = true := by
    match g with
    | .end => rfl
    | .var t =>
        simp only [GlobalType.isProductive, Bool.not_eq_true'] at hprod ⊢
        -- hprod: ug2.contains t = false
        -- Goal: ug1.contains t = false
        -- Proof by contrapositive: if ug1.contains t = true, then ug2.contains t = true
        by_contra hug1
        simp only [Bool.not_eq_false] at hug1
        have h := hsub t hug1
        rw [hprod] at h
        exact Bool.false_ne_true h
    | .mu t body =>
        simp only [GlobalType.isProductive] at hprod ⊢
        apply isProductive_mono body (t :: ug1) (t :: ug2)
        · intro x hx
          rw [List.contains_cons] at hx ⊢
          simp only [Bool.or_eq_true] at hx ⊢
          cases hx with
          | inl heq => left; exact heq
          | inr hmem => right; exact hsub x hmem
        · exact hprod
    | .comm _ _ branches =>
        simp only [GlobalType.isProductive] at hprod ⊢
        exact hprod  -- comm resets unguarded to [], so independent of ug1/ug2
    | .delegate _ _ _ _ cont =>
        simp only [GlobalType.isProductive] at hprod ⊢
        exact hprod  -- delegate resets unguarded to [], so independent of ug1/ug2

  theorem isProductiveBranches_mono (branches : List (Label × GlobalType))
      (ug1 ug2 : List String)
      (hsub : ∀ x, ug1.contains x = true → ug2.contains x = true)
      (hprod : isProductiveBranches branches ug2 = true) :
      isProductiveBranches branches ug1 = true := by
    match branches with
    | [] => rfl
    | (_, g) :: rest =>
        simp only [isProductiveBranches, Bool.and_eq_true] at hprod ⊢
        exact ⟨isProductive_mono g ug1 ug2 hsub hprod.1,
               isProductiveBranches_mono rest ug1 ug2 hsub hprod.2⟩
end
end SessionTypes.GlobalType
