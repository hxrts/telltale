import SessionTypes.LocalTypeR.Environments

set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

/-
The Problem. Recursive types need iterative unfolding to reach observable form (send/recv/end).
The number of unfold steps depends on nesting depth. Guardedness determines whether variables
appear at head position or inside communications.

Solution Structure. Defines `muHeight` counting nested mus at head. `fullUnfold` iterates
`unfold` muHeight-many times (Coq's `full_eunf` pattern). Proves `fullUnfold_mu` relating
mu-unfolding to body substitution. `isFreeIn_mem_freeVars` and `isGuarded_of_closed` connect
membership predicates. Closed types have all variables guarded (vacuously).
-/

/-! # SessionTypes.LocalTypeR.Unfolding

Full unfolding, guardedness/contractiveness properties, and contractive types reaching observable form.
-/

namespace SessionTypes.LocalTypeR
open SessionTypes.GlobalType
/-! ## Full Unfolding (Coq-style `full_eunf`)

Iterate mu-unfolding until reaching a non-mu form.
This is the Coq pattern where predicates work on fully unfolded types. -/

/-- Height for mu unfolding - counts nested mus at the head. -/
def LocalTypeR.muHeight : LocalTypeR → Nat
  | .mu _ body => 1 + body.muHeight
  | _ => 0

/-- Fully unfold a local type by iterating unfold until non-mu form.
    Corresponds to Coq's `full_eunf`. -/
def LocalTypeR.fullUnfold (lt : LocalTypeR) : LocalTypeR :=
  (LocalTypeR.unfold)^[lt.muHeight] lt

/-- If a type has no leading `mu`, then `fullUnfold` cannot be a `mu`.

    This is the only unconditional statement we can make without assuming
    guardedness/contractiveness. -/
theorem LocalTypeR.fullUnfold_not_mu (lt : LocalTypeR) :
    lt.muHeight = 0 → ∀ t body, lt.fullUnfold ≠ .mu t body := by
  intro h t body
  cases lt <;> simp [fullUnfold, muHeight] at h ⊢

/-- fullUnfold is idempotent when its result has no leading `mu`. -/
theorem LocalTypeR.fullUnfold_idemp (lt : LocalTypeR) :
    lt.fullUnfold.muHeight = 0 → lt.fullUnfold.fullUnfold = lt.fullUnfold := by
  intro h
  have h' : ((LocalTypeR.unfold)^[lt.muHeight] lt).muHeight = 0 := by
    simpa [fullUnfold] using h
  simp [fullUnfold, h']


/-! ## Guardedness and muHeight Properties -/

/-- For non-mu types, unfold is identity. -/
theorem LocalTypeR.unfold_non_mu (lt : LocalTypeR) :
    (∀ t body, lt ≠ .mu t body) → lt.unfold = lt := by
  intro h
  match lt with
  | «end» | var _ | send _ _ | recv _ _ => rfl
  | .mu t body => exact absurd rfl (h t body)

/-- The result of unfold on a mu is the substituted body. -/
theorem LocalTypeR.unfold_mu (t : String) (body : LocalTypeR) :
    (.mu t body : LocalTypeR).unfold = body.substitute t (.mu t body) := rfl

/-- fullUnfold of mu unfolds via one step of unfold then iterate.

    This follows from the definition: fullUnfold (.mu t body) = unfold^[1 + body.muHeight] (.mu t body)
    and Function.iterate_succ_apply: f^[n+1] x = f^[n] (f x).

    Corresponds to Coq's `full_eunf_subst`. -/
theorem LocalTypeR.fullUnfold_mu (t : String) (body : LocalTypeR) :
    (.mu t body : LocalTypeR).fullUnfold =
      LocalTypeR.unfold^[body.muHeight] (body.substitute t (.mu t body)) := by
  -- fullUnfold (.mu t body) = unfold^[(.mu t body).muHeight] (.mu t body)
  --                         = unfold^[1 + body.muHeight] (.mu t body)
  --                         = unfold^[body.muHeight] (unfold (.mu t body))
  --                         = unfold^[body.muHeight] (body.substitute t (.mu t body))
  simp only [fullUnfold, muHeight]
  -- Goal: unfold^[1 + body.muHeight] (.mu t body) = unfold^[body.muHeight] (body.substitute ...)
  rw [Nat.add_comm, Function.iterate_succ_apply]
  -- Goal: unfold^[body.muHeight] (unfold (.mu t body)) = unfold^[body.muHeight] (body.substitute ...)
  rfl

/-! ## Key Property: Contractive types reach observable form

For closed, contractive types, fullUnfold always reaches a non-mu form.
This is because:
1. Contractive means all bound variables are guarded
2. Guarded variables only appear inside send/recv
3. So fullUnfold reaches send/recv/end (not var since closed) -/

/-! ## Observable-Form Classification -/

/-- Classification of fully unfolded types. -/
inductive FullUnfoldResult where
  | is_end : FullUnfoldResult
  | is_var (v : String) : FullUnfoldResult
  | is_send (p : String) (bs : List BranchR) : FullUnfoldResult
  | is_recv (p : String) (bs : List BranchR) : FullUnfoldResult

/-- Classify the result of full unfolding a non-mu type. -/
def LocalTypeR.classifyNonMu : LocalTypeR → FullUnfoldResult
  | .end => .is_end
  | .var v => .is_var v
  | .send p bs => .is_send p bs
  | .recv p bs => .is_recv p bs
  | .mu _ _ => .is_end  -- Shouldn't be called on mu, but need total function

/-- For a type with muHeight 0 (non-mu at head), fullUnfold returns the type itself. -/
theorem LocalTypeR.fullUnfold_muHeight_zero {lt : LocalTypeR} (h : lt.muHeight = 0) :
    lt.fullUnfold = lt := by
  simp [fullUnfold, h]

/-- Non-mu types have muHeight 0. -/
theorem LocalTypeR.muHeight_non_mu :
    ∀ (lt : LocalTypeR), (∀ t body, lt ≠ .mu t body) → lt.muHeight = 0 := by
  intro lt h
  cases lt with
  | «end» => rfl
  | var _ => rfl
  | send _ _ => rfl
  | recv _ _ => rfl
  | mu t body => exact absurd rfl (h t body)

/-! ## freeVars/isFreeIn Bridge for Unfolding -/

/- For closed types (no free variables), fullUnfold cannot produce a variable.

    This is a useful auxiliary lemma (though not strictly needed for observable_of_closed_contractive
    since we prove it directly by induction).

    Intuition:
    - Closed means freeVars = []
    - If fullUnfold = .var v, then v would be free in the original type
    - But closed types have no free variables, contradiction

    Proof sketch: By contrapositive of unguarded_unfolds_to_var.
    If fullUnfold = .var v, then by unguarded_unfolds_to_var, v is free and unguarded.
    But isClosed means no free variables, contradiction.

    Note: This doesn't require contractiveness! Closedness alone ensures fullUnfold ≠ .var. -/
-- Helper: isFreeIn v = true implies v ∈ freeVars
mutual
  theorem isFreeIn_mem_freeVars (lt : LocalTypeR) (v : String) :
      lt.isFreeIn v = true → v ∈ lt.freeVars := by
    intro h
    cases hlt : lt with
    | «end» =>
        simp [LocalTypeR.isFreeIn, LocalTypeR.freeVars, hlt] at h
    | var w =>
        have hv : v = w := by
          simpa [LocalTypeR.isFreeIn, beq_iff_eq, hlt] using h
        subst hv
        simp [LocalTypeR.freeVars, hlt]
    | send _ bs =>
        have h' : isFreeInBranches' v bs = true := by
          simpa [LocalTypeR.isFreeIn, hlt] using h
        have hmem := isFreeInBranches'_mem_freeVarsOfBranches bs v h'
        simpa [LocalTypeR.freeVars, hlt] using hmem
    | recv _ bs =>
        have h' : isFreeInBranches' v bs = true := by
          simpa [LocalTypeR.isFreeIn, hlt] using h
        have hmem := isFreeInBranches'_mem_freeVarsOfBranches bs v h'
        simpa [LocalTypeR.freeVars, hlt] using hmem
    | mu t body =>
        by_cases hvt : v = t
        · have hbeq : (v == t) = true := by
            simpa [beq_iff_eq] using hvt
          have hfalse : False := by
            simpa [LocalTypeR.isFreeIn, hbeq, hlt] using h
          exact False.elim hfalse
        · have hvne : (v == t) = false := beq_eq_false_iff_ne.mpr hvt
          have h' : body.isFreeIn v = true := by
            simpa [LocalTypeR.isFreeIn, hvne, hlt] using h
          have hmem : v ∈ body.freeVars := isFreeIn_mem_freeVars body v h'
          apply (List.mem_filter).2
          exact ⟨hmem, (bne_iff_ne).2 hvt⟩
  termination_by sizeOf lt
  decreasing_by
    classical
    all_goals
      simp [*] <;> omega

  /-! ## Branch freeVars/isFreeIn Bridge -/

  theorem isFreeInBranches'_mem_freeVarsOfBranches (bs : List BranchR) (v : String) :
      isFreeInBranches' v bs = true → v ∈ freeVarsOfBranches bs := by
    intro h
    cases hbs : bs with
    | nil =>
        simp [isFreeInBranches', freeVarsOfBranches, hbs] at h
    | cons head tail =>
        cases hhead : head with
        | mk label rest =>
          cases rest with
          | mk _vt cont =>
            have h' : cont.isFreeIn v = true ∨ isFreeInBranches' v tail = true := by
              simpa [isFreeInBranches', hbs, hhead, Bool.or_eq_true] using h
            cases h' with
            | inl hcont =>
                have hmem : v ∈ cont.freeVars := isFreeIn_mem_freeVars cont v hcont
                simp [freeVarsOfBranches, hbs, hmem]
            | inr htail =>
                have hmem := isFreeInBranches'_mem_freeVarsOfBranches tail v htail
                simp [freeVarsOfBranches, hbs, hmem]
  termination_by sizeOf bs
  decreasing_by
    classical
    all_goals
      simp [*] <;> omega
end

/-! ## Guardedness from Non-Freeness -/

/-- If `v` is not free in `lt`, then `v` is guarded in `lt`. -/
theorem isGuarded_of_isFreeIn_false (lt : LocalTypeR) (v : String) :
    lt.isFreeIn v = false → lt.isGuarded v = true := by
  intro h
  cases lt with
  | «end» =>
      simp [LocalTypeR.isGuarded]
  | var w =>
      have hv : v ≠ w := by
        have hbeq : (v == w) = false := by
          simpa [LocalTypeR.isFreeIn] using h
        exact (beq_eq_false_iff_ne).1 hbeq
      have hvb : (v != w) = true := (bne_iff_ne).2 hv
      simp [LocalTypeR.isGuarded, hvb]
  | send _ _ =>
      simp [LocalTypeR.isGuarded]
  | recv _ _ =>
      simp [LocalTypeR.isGuarded]
  | mu t body =>
      by_cases hvt : v = t
      · subst hvt
        simp [LocalTypeR.isGuarded]
      · have hvne : (v == t) = false := beq_eq_false_iff_ne.mpr hvt
        have hbody : body.isFreeIn v = false := by
          simpa [LocalTypeR.isFreeIn, hvne] using h
        have hbody' := isGuarded_of_isFreeIn_false body v hbody
        simp [LocalTypeR.isGuarded, hvne, hbody']
termination_by sizeOf lt

/-! ## Guardedness from Closedness -/

/-- Closed types have all variables guarded (vacuously, since they have no free variables). -/
theorem isGuarded_of_closed (lt : LocalTypeR) (v : String) :
    lt.isClosed → lt.isGuarded v = true := by
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
      exact isGuarded_of_isFreeIn_false lt v hfree

end SessionTypes.LocalTypeR
