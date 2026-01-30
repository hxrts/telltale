import SessionTypes.GlobalType.Part3

set_option linter.dupNamespace false

/-! # GlobalType Part 4

isProductive preservation under substitution and wellFormed_mu_unfold theorem.
-/

namespace SessionTypes.GlobalType
/-- Removing a duplicate from unguarded preserves isProductive. -/
theorem isProductive_cons_dedup (g : GlobalType) (x : String) (unguarded : List String)
    (hprod : g.isProductive (x :: x :: unguarded) = true) :
    g.isProductive (x :: unguarded) = true := by
  apply isProductive_mono g (x :: unguarded) (x :: x :: unguarded)
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
  · exact hprod

/-- Swapping adjacent elements in unguarded preserves isProductive. -/
theorem isProductive_swap (g : GlobalType) (x y : String) (unguarded : List String)
    (hprod : g.isProductive (x :: y :: unguarded) = true) :
    g.isProductive (y :: x :: unguarded) = true := by
  -- Reduce to monotonicity and commutativity of contains.
  apply isProductive_mono g (y :: x :: unguarded) (x :: y :: unguarded)
  · intro z hz
    simpa [List.contains_cons, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm] using hz
  · exact hprod

-- isProductive is unaffected by extending unguarded with variables not in the type.
-- If a variable x is not used in g (i.e., x is not in any var constructor), then
-- adding x to unguarded doesn't affect isProductive.

-- Key lemma: if body.allVarsBound bound = true and body.isProductive bound = true,
-- then body.isProductive (bound ++ extra) = true for any extra.
-- This is because extra vars don't appear in body (due to allVarsBound).

mutual
  /-- If a type has all its vars bound and is productive, adding extra elements to
      unguarded preserves productivity (since those vars don't appear in the type). -/
  theorem isProductive_extend (g : GlobalType) (bound extra : List String)
      (hbound : g.allVarsBound bound = true)
      (hprod : g.isProductive bound = true) :
      g.isProductive (bound ++ extra) = true := by
    match g with
    | .end => rfl
    | .var t =>
        simp only [GlobalType.allVarsBound] at hbound
        simp only [GlobalType.isProductive, Bool.not_eq_true'] at hprod ⊢
        -- hbound says t is contained, hprod says it is not.
        rw [hbound] at hprod
        exact (Bool.false_ne_true hprod.symm).elim
    | .mu t body =>
        simp only [GlobalType.allVarsBound] at hbound
        simp only [GlobalType.isProductive] at hprod ⊢
        -- hbound: body.allVarsBound (t :: bound) = true
        -- hprod: body.isProductive (t :: bound) = true
        -- Goal: body.isProductive (t :: (bound ++ extra)) = true
        have h : t :: (bound ++ extra) = (t :: bound) ++ extra := rfl
        rw [h]
        exact isProductive_extend body (t :: bound) extra hbound hprod
    | .comm _ _ branches =>
        simp only [GlobalType.allVarsBound] at hbound
        simp only [GlobalType.isProductive] at hprod ⊢
        -- Comm resets unguarded to [], so hprod suffices.
        exact hprod

  theorem isProductiveBranches_extend (branches : List (Label × GlobalType))
      (bound extra : List String)
      (hbound : allVarsBoundBranches branches bound = true)
      (hprod : isProductiveBranches branches bound = true) :
      isProductiveBranches branches (bound ++ extra) = true := by
    match branches with
    | [] => rfl
    | (_, g) :: rest =>
        simp only [allVarsBoundBranches, Bool.and_eq_true] at hbound
        simp only [isProductiveBranches, Bool.and_eq_true] at hprod ⊢
        exact ⟨isProductive_extend g bound extra hbound.1 hprod.1,
               isProductiveBranches_extend rest bound extra hbound.2 hprod.2⟩
end

/-- Corollary: If (mu t body) is productive, then it's productive for any unguarded list. -/
theorem mu_isProductive_forall (t : String) (body : GlobalType)
    (hbound : body.allVarsBound [t] = true)
    (hprod : body.isProductive [t] = true) :
    ∀ ug, (GlobalType.mu t body).isProductive ug = true := by
  intro ug
  simp only [GlobalType.isProductive]
  -- Goal: body.isProductive (t :: ug) = true
  -- We have: body.allVarsBound [t] = true and body.isProductive [t] = true
  -- Use isProductive_extend with bound = [t] and extra = ug
  have h : [t] ++ ug = t :: ug := rfl
  rw [← h]
  exact isProductive_extend body [t] ug hbound hprod

-- isProductive preservation under substitution
--
-- Key insight: When g.isProductive (varName :: unguarded) = true, any occurrence of
-- var varName in g must be after a comm (which resets unguarded to []). So the replacement
-- only needs to be productive with [].

mutual
  private theorem isProductive_substitute_var (t varName : String) (repl : GlobalType)
      (unguarded : List String)
      (hg : (GlobalType.var t).isProductive (varName :: unguarded) = true)
      (hrepl : ∀ ug, repl.isProductive ug = true) :
      ((GlobalType.var t).substitute varName repl).isProductive unguarded = true := by
    -- Var case: either substitute repl or keep var t.
    simp only [GlobalType.substitute]
    split
    · exact hrepl unguarded
    · rename_i _hne
      simp only [GlobalType.isProductive, Bool.not_eq_true'] at hg ⊢
      by_contra hunguarded
      simp only [Bool.not_eq_false] at hunguarded
      have h : (varName :: unguarded).contains t = true := by
        rw [List.contains_cons]
        simp only [Bool.or_eq_true]
        right; exact hunguarded
      rw [hg] at h
      exact Bool.false_ne_true h

  private theorem isProductive_substitute_mu_shadow (t varName : String) (inner : GlobalType)
      (unguarded : List String)
      (hg : inner.isProductive (t :: varName :: unguarded) = true)
      (heq : (t == varName) = true) :
      inner.isProductive (t :: unguarded) = true := by
    -- Shadowed binder: dedup the unguarded list.
    have heq' : t = varName := by simpa [beq_iff_eq] using heq
    subst heq'
    exact isProductive_cons_dedup inner t unguarded hg

  /-- isProductive is preserved under substitution.

  The replacement must be productive for any unguarded list it might encounter.
  This is satisfied when repl.isProductive [] = true, because comm resets unguarded. -/
  theorem isProductive_substitute (g : GlobalType) (varName : String) (repl : GlobalType)
      (unguarded : List String)
      (hg : g.isProductive (varName :: unguarded) = true)
      (hrepl : ∀ ug, repl.isProductive ug = true) :
      (g.substitute varName repl).isProductive unguarded = true := by
    match g with
    | .end => simp [GlobalType.substitute, GlobalType.isProductive]
    | .var t => exact isProductive_substitute_var t varName repl unguarded hg hrepl
    | .mu t inner =>
        simp only [GlobalType.substitute]
        split
        · -- t = varName, shadowed - no substitution
          rename_i heq
          simp only [GlobalType.isProductive] at hg ⊢
          exact isProductive_substitute_mu_shadow t varName inner unguarded hg heq
        · -- t ≠ varName
          simp only [GlobalType.isProductive] at hg ⊢
          have hg' : inner.isProductive (varName :: t :: unguarded) = true :=
            isProductive_swap inner t varName unguarded hg
          exact isProductive_substitute inner varName repl (t :: unguarded) hg' hrepl
    | .comm sender receiver branches =>
        simp only [GlobalType.substitute, GlobalType.isProductive] at hg ⊢
        -- comm resets unguarded to [], so hg : isProductiveBranches branches [] = true
        -- Goal: isProductiveBranches (substituteBranches branches varName repl) [] = true
        exact isProductiveBranches_substitute_any branches varName repl [] hg hrepl

  -- For branches, if replacement is always productive, substitution preserves productivity
  -- regardless of whether varName is in unguarded
  theorem isProductiveBranches_substitute_any (branches : List (Label × GlobalType))
      (varName : String) (repl : GlobalType) (unguarded : List String)
      (hg : isProductiveBranches branches unguarded = true)
      (hrepl : ∀ ug, repl.isProductive ug = true) :
      isProductiveBranches (substituteBranches branches varName repl) unguarded = true := by
    match branches with
    | [] => rfl
    | (label, cont) :: rest =>
        simp only [substituteBranches, isProductiveBranches, Bool.and_eq_true] at hg ⊢
        exact ⟨isProductive_substitute_any cont varName repl unguarded hg.1 hrepl,
               isProductiveBranches_substitute_any rest varName repl unguarded hg.2 hrepl⟩

  -- If replacement is always productive, substitution preserves productivity
  -- This is a more general version that doesn't require varName in unguarded
  theorem isProductive_substitute_any (g : GlobalType) (varName : String) (repl : GlobalType)
      (unguarded : List String)
      (hg : g.isProductive unguarded = true)
      (hrepl : ∀ ug, repl.isProductive ug = true) :
      (g.substitute varName repl).isProductive unguarded = true := by
    -- Dispatch on g.
    match g with
    | .end => simp [GlobalType.substitute, GlobalType.isProductive]
    | .var t =>
        simp only [GlobalType.substitute]
        split
        · exact hrepl unguarded
        · exact hg
    | .mu t inner =>
        simp only [GlobalType.substitute]
        split
        · exact hg
        · simp only [GlobalType.isProductive] at hg ⊢
          exact isProductive_substitute_any inner varName repl (t :: unguarded) hg hrepl
    | .comm sender receiver branches =>
        simp only [GlobalType.substitute, GlobalType.isProductive] at hg ⊢
        exact isProductiveBranches_substitute_any branches varName repl [] hg hrepl
end

/-- Mu-unfolding preserves well-formedness components that don't depend on variable binding.

This is a simplified version that shows noSelfComm and allCommsNonEmpty are preserved.
The full wellFormed preservation requires more sophisticated reasoning about allVarsBound
and isProductive. -/
theorem wellFormed_mu_unfold_partial (t : String) (body : GlobalType)
    (hwf : (GlobalType.mu t body).wellFormed = true) :
    (body.substitute t (GlobalType.mu t body)).noSelfComm = true ∧
    (body.substitute t (GlobalType.mu t body)).allCommsNonEmpty = true := by
  unfold GlobalType.wellFormed at hwf
  simp only [Bool.and_eq_true] at hwf
  -- hwf : (((_.allVarsBound ∧ _.allCommsNonEmpty) ∧ _.noSelfComm) ∧ _.isProductive)
  have hne := hwf.1.1.2  -- allCommsNonEmpty
  have hns := hwf.1.2    -- noSelfComm
  simp only [GlobalType.allCommsNonEmpty, GlobalType.noSelfComm] at hne hns
  exact ⟨noSelfComm_substitute body t (GlobalType.mu t body) hns hns,
         allCommsNonEmpty_substitute body t (GlobalType.mu t body) hne hne⟩

/-- Mu-unfolding preserves allVarsBound for closed types.

**Key insight**: If `mu t body` is closed (allVarsBound [] = true),
then `body.substitute t (mu t body)` is also closed.

This works because:
1. body.allVarsBound [t] = true (from mu's definition)
2. Substituting (mu t body) for t in body removes the t dependency
3. (mu t body).allVarsBound [] = true, so substituted vars are still bound -/
theorem allVarsBound_mu_unfold (t : String) (body : GlobalType)
    (hbound : (GlobalType.mu t body).allVarsBound [] = true) :
    (body.substitute t (GlobalType.mu t body)).allVarsBound [] = true := by
  -- hbound: (mu t body).allVarsBound [] = true
  -- which unfolds to: body.allVarsBound [t] = true
  simp only [GlobalType.allVarsBound] at hbound
  -- Now hbound: body.allVarsBound [t] = true
  -- Apply allVarsBound_substitute with bound = []
  -- Need: body.allVarsBound (t :: []) = body.allVarsBound [t] = true ✓
  -- Need: (mu t body).allVarsBound [] = true
  have hrepl : (GlobalType.mu t body).allVarsBound [] = true := by
    simp only [GlobalType.allVarsBound]
    exact hbound
  exact allVarsBound_substitute body t (GlobalType.mu t body) [] hbound hrepl

/-- Mu-unfolding preserves isProductive.

**Key insight**: If `mu t body` is productive AND has all vars bound,
then `body.substitute t (mu t body)` is also productive.

This requires both productivity (for guarded recursion) and allVarsBound
(so we know the replacement (mu t body) is productive for any unguarded list). -/
theorem isProductive_mu_unfold (t : String) (body : GlobalType)
    (hbound : (GlobalType.mu t body).allVarsBound [] = true)
    (hprod : (GlobalType.mu t body).isProductive = true) :
    (body.substitute t (GlobalType.mu t body)).isProductive = true := by
  simp only [GlobalType.allVarsBound] at hbound
  simp only [GlobalType.isProductive] at hprod
  -- hbound: body.allVarsBound [t] = true
  -- hprod: body.isProductive [t] = true
  -- Goal: (body.substitute t (mu t body)).isProductive [] = true
  -- Use isProductive_substitute with hrepl from mu_isProductive_forall
  have hrepl : ∀ ug, (GlobalType.mu t body).isProductive ug = true :=
    mu_isProductive_forall t body hbound hprod
  exact isProductive_substitute body t (GlobalType.mu t body) [] hprod hrepl

/-- Mu-unfolding preserves full well-formedness.

Main theorem: if `mu t body` is well-formed, then unfolding it
(substituting the whole mu-type for its bound variable) is also well-formed. -/
theorem wellFormed_mu_unfold (t : String) (body : GlobalType)
    (hwf : (GlobalType.mu t body).wellFormed = true) :
    (body.substitute t (GlobalType.mu t body)).wellFormed = true := by
  unfold GlobalType.wellFormed at hwf ⊢
  simp only [Bool.and_eq_true] at hwf ⊢
  obtain ⟨⟨⟨hbound, hne⟩, hns⟩, hprod⟩ := hwf
  simp only [GlobalType.allVarsBound, GlobalType.allCommsNonEmpty,
             GlobalType.noSelfComm, GlobalType.isProductive] at hbound hne hns hprod ⊢
  constructor
  constructor
  constructor
  · exact allVarsBound_mu_unfold t body hbound
  · exact allCommsNonEmpty_substitute body t (GlobalType.mu t body) hne hne
  · exact noSelfComm_substitute body t (GlobalType.mu t body) hns hns
  · exact isProductive_mu_unfold t body hbound hprod

end SessionTypes.GlobalType
