import SessionTypes.LocalTypeR.Unfolding

set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

/-
The Problem. Substitution must preserve closedness, guardedness, and contractiveness for
well-formedness to propagate through unfolding. The mu case is delicate: substituting into
a mu body requires the replacement to be closed to avoid introducing unguarded variables.

Solution Structure. Proves `substitute_not_free` for idempotence when variable not present.
`muHeight_substitute_guarded` shows mu-height doesn't increase under guarded substitution.
`isGuarded_substitute` and `isContractive_substitute` prove preservation with closed replacements.
`iterate_unfold_bounded_contractive` shows contractive types reach observable form.
-/

/-! # SessionTypes.LocalTypeR.Substitution

Closed types and substitution, muHeight properties, guardedness and contractiveness preservation.
-/

namespace SessionTypes.LocalTypeR
open SessionTypes.GlobalType
/-! ## Closed Types and Substitution -/

theorem isFreeIn_false_of_closed (lt : LocalTypeR) (v : String) :
    lt.isClosed → lt.isFreeIn v = false := by
  intro hclosed
  cases hfree : lt.isFreeIn v with
  | true =>
      have hmem := isFreeIn_mem_freeVars lt v hfree
      have hnil : lt.freeVars = [] := by
        have : lt.freeVars.isEmpty = true := by
          simpa [LocalTypeR.isClosed] using hclosed
        exact (List.isEmpty_eq_true _).1 this
      have : False := by
        simpa [hnil] using hmem
      exact this.elim
  | false =>
      simpa using hfree

/-! ## Substitute-Not-Free Idempotence -/

mutual
  theorem substitute_not_free (e : LocalTypeR) (x : String) (rx : LocalTypeR)
      (hnot_free : LocalTypeR.isFreeIn x e = false) :
      e.substitute x rx = e := by
    match e with
    | .end => rfl
    | .var w =>
        by_cases hwt : w = x
        · subst hwt
          have : False := by
            simpa [LocalTypeR.isFreeIn] using hnot_free
          exact this.elim
        · have hbeq : (w == x) = false := beq_eq_false_iff_ne.mpr hwt
          simp [LocalTypeR.substitute, hbeq]
    | .send p bs =>
        have hbs : isFreeInBranches' x bs = false := by
          simpa [LocalTypeR.isFreeIn] using hnot_free
        have hbs' := substituteBranches_not_free bs x rx hbs
        simpa [LocalTypeR.substitute, hbs', -substituteBranches_eq_map]
    | .recv p bs =>
        have hbs : isFreeInBranches' x bs = false := by
          simpa [LocalTypeR.isFreeIn] using hnot_free
        have hbs' := substituteBranches_not_free bs x rx hbs
        simpa [LocalTypeR.substitute, hbs', -substituteBranches_eq_map]
    | .mu t body =>
        by_cases hxt : t = x
        · have hbeq : (t == x) = true := by
            simpa [beq_iff_eq] using hxt
          simp [LocalTypeR.substitute, hbeq]
        · have hbeq : (t == x) = false := beq_eq_false_iff_ne.mpr hxt
          have hxt' : x ≠ t := by
            intro hx
            exact hxt hx.symm
          have hxtbeq : (x == t) = false := beq_eq_false_iff_ne.mpr hxt'
          have hbody : LocalTypeR.isFreeIn x body = false := by
            simpa [LocalTypeR.isFreeIn, hxtbeq] using hnot_free
          have hbody' := substitute_not_free body x rx hbody
          simp [LocalTypeR.substitute, hbeq, hbody']
  termination_by sizeOf e

  /-! ## Substitute-Not-Free on Branch Lists -/

  theorem substituteBranches_not_free (bs : List BranchR) (x : String) (rx : LocalTypeR)
      (hnot_free : isFreeInBranches' x bs = false) :
      LocalTypeR.substituteBranches bs x rx = bs := by
    match bs with
    | [] => rfl
    | (label, _vt, cont) :: rest =>
        have hsplit : cont.isFreeIn x = false ∧ isFreeInBranches' x rest = false := by
          simpa [isFreeInBranches', Bool.or_eq_false_iff] using hnot_free
        have h1 : cont.substitute x rx = cont :=
          substitute_not_free cont x rx hsplit.1
        have h2 : LocalTypeR.substituteBranches rest x rx = rest :=
          substituteBranches_not_free rest x rx hsplit.2
        simp [LocalTypeR.substituteBranches, h1, h2, -substituteBranches_eq_map]
  termination_by sizeOf bs
end

/-! ## Environment Application on Closed Types -/

theorem apply_env_of_closed (env : Env) (lt : LocalTypeR) :
    lt.isClosed → Env.apply env lt = lt := by
  intro hclosed
  induction env generalizing lt with
  | nil =>
      simp [Env.apply]
  | cons head rest ih =>
      cases head with
      | mk v u =>
          have hnot : lt.isFreeIn v = false := isFreeIn_false_of_closed lt v hclosed
          have hsubst : lt.substitute v u = lt := substitute_not_free lt v u hnot
          have ih' := ih (lt := lt) hclosed
          simpa [Env.apply, hsubst] using ih'

theorem applyActiveEnv_eq_of_closed (lt : LocalTypeR) :
    lt.isClosed → applyActiveEnv lt = lt := by
  intro hclosed
  simpa [applyActiveEnv] using apply_env_of_closed ActiveEnv lt hclosed

/-! ## Full-Unfold Free-Variable Consequences -/

/-- If `fullUnfold lt = .var v`, then `v` is free in `lt`. -/
theorem fullUnfold_var_is_free (lt : LocalTypeR) (v : String) :
    lt.fullUnfold = .var v → lt.isFreeIn v = true := by
  intro h
  -- v is free in fullUnfold, so v is free in lt by iterated unfold subset
  have hv_mem_full : v ∈ lt.fullUnfold.freeVars := by
    -- fullUnfold = var v, whose freeVars is [v]
    simpa [h, LocalTypeR.freeVars] using (List.mem_cons_self v [])
  have hv_mem : v ∈ lt.freeVars := by
    have hsubset := freeVars_iter_unfold_subset (k := lt.muHeight) (lt := lt) (v := v) hv_mem_full
    simpa [LocalTypeR.fullUnfold] using hsubset
  exact mem_freeVars_isFreeIn lt v hv_mem

theorem LocalTypeR.fullUnfold_not_var_of_closed {lt : LocalTypeR}
    (hclosed : lt.isClosed) : ∀ v, lt.fullUnfold ≠ .var v := by
  intro v h
  have hfree : lt.isFreeIn v = true := fullUnfold_var_is_free lt v h
  have hmem : v ∈ lt.freeVars := isFreeIn_mem_freeVars lt v hfree
  have hnil : lt.freeVars = [] := by
    have : lt.freeVars.isEmpty = true := by
      simpa [LocalTypeR.isClosed] using hclosed
    exact (List.isEmpty_eq_true _).1 this
  have : False := by
    simpa [hnil] using hmem
  exact this.elim

/-! ## muHeight Under Guarded Substitution -/

/-- Substituting a term for a guarded variable does not increase `muHeight`.

    Contractiveness ensures that after muHeight iterations of unfold,
    we reach a communication (send/recv) or end, not another mu. -/
theorem muHeight_substitute_guarded (t : String) (body e : LocalTypeR) :
    body.isGuarded t = true → (body.substitute t e).muHeight ≤ body.muHeight := by
  intro hguard
  cases body with
  | «end» =>
      simp [LocalTypeR.substitute, LocalTypeR.muHeight]
  | var w =>
      by_cases hw : w = t
      · subst hw
        have : False := by
          simpa [LocalTypeR.isGuarded] using hguard
        exact this.elim
      · have hbeq : (w == t) = false := beq_eq_false_iff_ne.mpr hw
        simp [LocalTypeR.substitute, LocalTypeR.muHeight, hbeq]
  | send _ _ | recv _ _ =>
      -- Send/recv have identical muHeight behavior.
      simp [LocalTypeR.substitute, LocalTypeR.muHeight]
  | mu s body =>
      by_cases hs : s = t
      · have hbeq : (s == t) = true := by
          simpa [beq_iff_eq] using hs
        -- Shadowed: no substitution under mu
        simp [LocalTypeR.substitute, LocalTypeR.muHeight, hbeq]
      · have hbeq_st : (s == t) = false := beq_eq_false_iff_ne.mpr hs
        have hbeq_ts : (t == s) = false := beq_eq_false_iff_ne.mpr (by intro h; exact hs h.symm)
        -- Substitute under mu; use recursion on body
        have hguard' : body.isGuarded t = true := by
          simpa [LocalTypeR.isGuarded, hbeq_ts] using hguard
        have ih := muHeight_substitute_guarded t body e hguard'
        have := Nat.add_le_add_left ih 1
        simpa [LocalTypeR.substitute, LocalTypeR.muHeight, hbeq_st] using this
termination_by sizeOf body

/-! ## Guardedness Under Substitution -/

/-- Guardedness is preserved by substitution when the replacement is closed. -/
theorem isGuarded_substitute (body : LocalTypeR) (t v : String) (e : LocalTypeR) :
    body.isGuarded v = true → e.isClosed →
    (body.substitute t e).isGuarded v = true := by
  intro hguard hclosed
  cases body with
  | «end» =>
      simp [LocalTypeR.substitute, LocalTypeR.isGuarded]
  | var w =>
      by_cases hw : w = t
      · subst hw
        have hguard_e : e.isGuarded v = true := isGuarded_of_closed e v hclosed
        simpa [LocalTypeR.substitute] using hguard_e
      · have hbeq : (w == t) = false := beq_eq_false_iff_ne.mpr hw
        simpa [LocalTypeR.substitute, LocalTypeR.isGuarded, hbeq] using hguard
  | send _ _ | recv _ _ =>
      -- Send and recv cases are identical (symmetric under duality)
      simp [LocalTypeR.substitute, LocalTypeR.isGuarded]
  | mu s body =>
      by_cases hs : s = t
      · have hbeq : (s == t) = true := by
          simpa [beq_iff_eq] using hs
        simpa [LocalTypeR.substitute, hbeq] using hguard
      · have hbeq_st : (s == t) = false := beq_eq_false_iff_ne.mpr hs
        by_cases hvs : v = s
        · subst hvs
          simp [LocalTypeR.substitute, LocalTypeR.isGuarded, hbeq_st]
        · have hvbeq : (v == s) = false := beq_eq_false_iff_ne.mpr hvs
          have hguard' : body.isGuarded v = true := by
            simpa [LocalTypeR.isGuarded, hvbeq] using hguard
          have ih := isGuarded_substitute body t v e hguard' hclosed
          simp [LocalTypeR.substitute, LocalTypeR.isGuarded, hbeq_st, hvbeq, ih]
termination_by sizeOf body

/-- Guardedness of `v` is preserved when substituting for a different variable `t`.
    Requires closed replacement to avoid introducing unguarded occurrences of `v`. -/
theorem isGuarded_substitute_other (body : LocalTypeR) (t v : String) (e : LocalTypeR) :
    v ≠ t → body.isGuarded v = true →
    e.isClosed → (body.substitute t e).isGuarded v = true := by
  intro _ hguard hclosed
  exact isGuarded_substitute body t v e hguard hclosed

-- NOTE: isContractive_substitute_mu is proved in LocalTypeRDBBridge.lean

/-! ## Contractiveness Under Substitution -/

mutual
  /-- Substitution preserves contractiveness when the replacement is closed and contractive.
      The mu case requires closedness to avoid introducing unguarded variables. -/
  theorem isContractive_substitute (body : LocalTypeR) (t : String) (e : LocalTypeR) :
      body.isContractive = true → e.isContractive = true → e.isClosed →
      (body.substitute t e).isContractive = true := by
    intro hbody hcontr hclosed
    cases body with
    | «end» =>
        simp [LocalTypeR.substitute, LocalTypeR.isContractive]
    | var w =>
        by_cases hw : w = t
        · subst hw
          simpa [LocalTypeR.substitute] using hcontr
        · have hbeq : (w == t) = false := beq_eq_false_iff_ne.mpr hw
          simp [LocalTypeR.substitute, LocalTypeR.isContractive, hbeq]
    | send p bs | recv p bs =>
        -- Send and recv cases are identical (symmetric under duality)
        have hbs : isContractiveBranches bs = true := by
          simpa [LocalTypeR.isContractive] using hbody
        have hbs' : isContractiveBranches (substituteBranches bs t e) = true :=
          isContractiveBranches_substitute bs t e hbs hcontr hclosed
        simp [LocalTypeR.substitute, LocalTypeR.isContractive, hbs', -substituteBranches_eq_map]
    | mu s body =>
        by_cases hs : s = t
        · have hbeq : (s == t) = true := by
            simpa [beq_iff_eq] using hs
          simpa [LocalTypeR.substitute, LocalTypeR.isContractive, hbeq] using hbody
        · have hbeq : (s == t) = false := beq_eq_false_iff_ne.mpr hs
          have hpair : body.isGuarded s = true ∧ body.isContractive = true := by
            simpa [LocalTypeR.isContractive, Bool.and_eq_true] using hbody
          have hguard : body.isGuarded s = true := hpair.1
          have hbody_contr : body.isContractive = true := hpair.2
          have hguard' : (body.substitute t e).isGuarded s = true :=
            isGuarded_substitute body t s e hguard hclosed
          have hbody' : (body.substitute t e).isContractive = true :=
            isContractive_substitute body t e hbody_contr hcontr hclosed
          simp [LocalTypeR.substitute, LocalTypeR.isContractive, hbeq, hguard', hbody']
  termination_by sizeOf body

  /-! ## Contractiveness on Branch Substitution -/

  theorem isContractiveBranches_substitute (bs : List BranchR) (t : String) (e : LocalTypeR) :
      isContractiveBranches bs = true → e.isContractive = true → e.isClosed →
      isContractiveBranches (substituteBranches bs t e) = true := by
    intro hbs hcontr hclosed
    cases bs with
    | nil =>
        simp [isContractiveBranches]
    | cons head tail =>
        cases head with
        | mk label rest => cases rest with | mk _vt cont =>
            have hpair : cont.isContractive = true ∧ isContractiveBranches tail = true := by
              simpa [isContractiveBranches, Bool.and_eq_true] using hbs
            have hcont' : (cont.substitute t e).isContractive = true :=
              isContractive_substitute cont t e hpair.1 hcontr hclosed
            have htail' : isContractiveBranches (substituteBranches tail t e) = true :=
              isContractiveBranches_substitute tail t e hpair.2 hcontr hclosed
            simp [isContractiveBranches, LocalTypeR.substituteBranches, hcont', htail', -substituteBranches_eq_map]
  termination_by sizeOf bs
end

/-! ## ClosedUnder through substitution/apply -/

theorem LocalTypeR.isClosed_substitute_mu {t : String} {body : LocalTypeR}
    (hclosed : (LocalTypeR.mu t body).isClosed) :
    (body.substitute t (LocalTypeR.mu t body)).isClosed := by
  -- Convert isClosed to freeVars = []
  have hmu_nil : (LocalTypeR.mu t body).freeVars = [] := by
    have : (LocalTypeR.mu t body).freeVars.isEmpty = true := by
      simpa [LocalTypeR.isClosed] using hclosed
    exact (List.isEmpty_eq_true _).1 this
  have hfilter_nil : body.freeVars.filter (· != t) = [] := by
    simpa [LocalTypeR.freeVars] using hmu_nil
  -- Show substituted freeVars is empty
  simp [LocalTypeR.isClosed, List.isEmpty_eq_true, List.eq_nil_iff_forall_not_mem]
  intro v hv
  have hres := freeVars_substitute_closed body t (.mu t body) hclosed v hv
  have hmem_filter : v ∈ body.freeVars.filter (· != t) := by
    apply List.mem_filter.mpr
    exact ⟨hres.1, (bne_iff_ne).2 hres.2⟩
  -- Contradiction with hfilter_nil
  simpa [hfilter_nil] using hmem_filter

/-! ## ClosedUnder Preservation Through Env.apply -/

theorem closedUnder_substitute_closed {env : Env} {t : LocalTypeR}
    (v : String) (u : LocalTypeR) :
    u.isClosed → ClosedUnder ((v, u) :: env) t → ClosedUnder env (t.substitute v u) := by
  intro hclosed hcu x hx
  have hres := freeVars_substitute_closed t v u hclosed x hx
  have hx_in : x ∈ t.freeVars := hres.1
  have hxne : x ≠ v := hres.2
  have hx_dom : x ∈ Env.dom ((v, u) :: env) := hcu x hx_in
  have hx_dom' : x = v ∨ x ∈ Env.dom env := by
    simpa [Env.dom] using (List.mem_cons.mp hx_dom)
  cases hx_dom' with
  | inl hx_eq => exact (hxne hx_eq).elim
  | inr hx_rest => exact hx_rest

/-! ## Closedness Through Env.apply -/

theorem isClosed_apply_of_closed_env (env : Env) (t : LocalTypeR) :
    EnvWellFormed env → ClosedUnder env t → (Env.apply env t).isClosed := by
  intro hWF hclosed
  induction env generalizing t with
  | nil =>
      have hclosed' : t.isClosed := (closedUnder_nil_iff_isClosed t).1 hclosed
      simpa [Env.apply] using hclosed'
  | cons head rest ih =>
      cases head with
      | mk v u =>
          rcases hWF with ⟨hu_closed, _hu_contr, hWF_rest⟩
          have hclosed_subst : ClosedUnder rest (t.substitute v u) :=
            closedUnder_substitute_closed (env := rest) (t := t) v u hu_closed hclosed
          have hclosed_apply := ih (t := t.substitute v u) hWF_rest hclosed_subst
          simpa [Env.apply] using hclosed_apply

/-! ## Contractiveness Through Env.apply -/

theorem isContractive_apply_of_closed_env (env : Env) (t : LocalTypeR) :
    EnvWellFormed env → t.isContractive = true → (Env.apply env t).isContractive = true := by
  intro hWF hcontr
  induction env generalizing t with
  | nil =>
      simpa [Env.apply] using hcontr
  | cons head rest ih =>
      cases head with
      | mk v u =>
          rcases hWF with ⟨hu_closed, hu_contr, hWF_rest⟩
          have hcontr_subst : (t.substitute v u).isContractive = true :=
            isContractive_substitute t v u hcontr hu_contr hu_closed
          have hcontr_apply := ih (t := t.substitute v u) hWF_rest hcontr_subst
          simpa [Env.apply] using hcontr_apply

/-! ## Iterated Unfold Bound for Closed Contractive Types -/

/-- Iterating `unfold` at least `muHeight` times on a closed, contractive type yields `muHeight = 0`. -/
theorem iterate_unfold_bounded_contractive (k : Nat) (e : LocalTypeR)
    (hcontr : e.isContractive = true) (hclosed : e.isClosed) (h : e.muHeight ≤ k) :
    ((LocalTypeR.unfold)^[k] e).muHeight = 0 := by
  induction k generalizing e with
  | zero =>
      have hmh : e.muHeight = 0 := Nat.le_zero.mp h
      simp [Function.iterate_zero, hmh]
  | succ k ih =>
      cases e with
      | «end» =>
          have hiter := Function.iterate_fixed (f := LocalTypeR.unfold) (x := LocalTypeR.end) rfl (n := Nat.succ k)
          simpa [LocalTypeR.muHeight] using congrArg LocalTypeR.muHeight hiter
      | var w =>
          have hiter := Function.iterate_fixed (f := LocalTypeR.unfold) (x := LocalTypeR.var w) rfl (n := Nat.succ k)
          simpa [LocalTypeR.muHeight] using congrArg LocalTypeR.muHeight hiter
      | send p bs =>
          have hiter := Function.iterate_fixed (f := LocalTypeR.unfold) (x := LocalTypeR.send p bs) rfl (n := Nat.succ k)
          simpa [LocalTypeR.muHeight] using congrArg LocalTypeR.muHeight hiter
      | recv p bs =>
          have hiter := Function.iterate_fixed (f := LocalTypeR.unfold) (x := LocalTypeR.recv p bs) rfl (n := Nat.succ k)
          simpa [LocalTypeR.muHeight] using congrArg LocalTypeR.muHeight hiter
      | mu t body =>
          -- Extract guardness and contractiveness of body
          have hpair : body.isGuarded t = true ∧ body.isContractive = true := by
            simpa [LocalTypeR.isContractive, Bool.and_eq_true] using hcontr
          have hguarded : body.isGuarded t = true := hpair.1
          have hbody_contr : body.isContractive = true := hpair.2
          have hle : body.muHeight ≤ k := by
            -- muHeight (.mu t body) = 1 + body.muHeight
            have h' : 1 + body.muHeight ≤ 1 + k := by
              simpa [LocalTypeR.muHeight, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
            exact Nat.le_of_add_le_add_left h'
          -- Substitution preserves contractiveness (needed for IH)
          have hsubst_contr : (body.substitute t (.mu t body)).isContractive = true :=
            isContractive_substitute body t (.mu t body) hbody_contr hcontr hclosed
          have hsubst_closed : (body.substitute t (.mu t body)).isClosed :=
            LocalTypeR.isClosed_substitute_mu hclosed
          -- Mu-height does not increase under guarded substitution
          have hsubst_h : (body.substitute t (.mu t body)).muHeight ≤ k := by
            have hle' : (body.substitute t (.mu t body)).muHeight ≤ body.muHeight :=
              muHeight_substitute_guarded t body (.mu t body) hguarded
            exact le_trans hle' hle
          have ih' := ih (e := body.substitute t (.mu t body)) hsubst_contr hsubst_closed hsubst_h
          -- unfold^[k+1] (.mu t body) = unfold^[k] (body.substitute t (.mu t body))
          simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using ih'

/-! ## fullUnfold Non-Recursive Shape Corollary -/

theorem LocalTypeR.fullUnfold_non_mu_of_contractive {lt : LocalTypeR}
    (hcontr : lt.isContractive = true) (hclosed : lt.isClosed) : lt.fullUnfold.muHeight = 0 := by
  simp [fullUnfold]
  apply iterate_unfold_bounded_contractive
  · exact hcontr
  · exact hclosed
  · simp

end SessionTypes.LocalTypeR
