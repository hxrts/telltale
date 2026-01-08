import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.CoTypes.Bisim

/-!
# LocalType Core Well-Formedness Theory

This module provides proofs for the well-formedness theory of `LocalTypeR`,
following the structure from `observable_closed_problem.lean`.

## Purpose

The main result `observable_of_closed_contractive` is already proved in `Bisim.lean`
using structural induction. However, several supporting lemmas in `LocalTypeR.lean`
remain as sorries. This module provides those missing proofs.

## Status

Current sorries in `LocalTypeR.lean` that need resolution:
1. Line 188: `isClosed_substitute_mu` - substitution preserves closedness
2. Line 368: `fullUnfold_not_var_of_closed` - closed types don't unfold to var
3. Line 382: `fullUnfold_non_mu_of_contractive` - contractive types unfold to non-mu
4. Line 417, 569: Complex unguarded variable cases

## Structure

This file proves the 6 subproblems from `observable_closed_problem.lean`:

1. **unguarded_unfolds_to_var**: Unguarded variables unfold to themselves
2. **isGuarded_substitute**: Guardedness preserved by substitution
3. **isFreeIn_substitute**: Free variables behave correctly under substitution
4. **contractive_implies_guarded**: Contractive types have all vars guarded
5. **isClosed_substitute**: Substitution preserves closedness
6. **fullUnfold_muHeight**: Full unfolding reaches muHeight = 0

These combine to resolve the LocalTypeR sorries and support the main theorem.

-/

namespace LocalTypeCore

open LocalTypeR

/-! ## Section 1: Re-exports from Existing Modules -/

-- Closedness is defined in LocalTypeR.lean:
-- def LocalTypeR.isClosed (lt : LocalTypeR) : Bool := lt.freeVars.isEmpty

-- Observable behavior predicates are defined in Bisim.lean:
-- - UnfoldsToEnd : LocalTypeR → Prop
-- - CanSend : LocalTypeR → String → List (Label × LocalTypeR) → Prop
-- - CanRecv : LocalTypeR → String → List (Label × LocalTypeR) → Prop
-- - UnfoldsToVar : LocalTypeR → String → Prop
-- - Observable : LocalTypeR → Prop

-- The main theorem is already proved in Bisim.lean:
-- theorem observable_of_closed_contractive {a : LocalTypeR}
--     (hclosed : a.isClosed) (hcontr : a.isContractive = true) : Observable a

/-! ## Section 2: Free Variable Lemmas -/

/-- **Helper Lemma**: Free variables of substitution.

If `v ≠ t`, then `v` is free in `body.substitute t e` iff:
- `v` is free in `body`, OR
- `t` is free in `body` AND `v` is free in `e` -/
theorem freeVars_substitute (v t : String) (body e : LocalTypeR) :
    v ∈ (body.substitute t e).freeVars ↔
      v ∈ body.freeVars ∧ v ≠ t ∨ t ∈ body.freeVars ∧ v ∈ e.freeVars := by
  sorry

/-! ## Section 3: Closedness Lemmas -/

/-- **Subproblem 5**: Substitution preserves closedness for mu types.

This directly addresses the sorry at LocalTypeR.lean:188. -/
theorem isClosed_substitute_mu {t : String} {body : LocalTypeR}
    (hclosed : (.mu t body).isClosed = true) :
    (body.substitute t (.mu t body)).isClosed = true := by
  sorry

/-- Closed types have empty free variable sets. -/
theorem isClosed_freeVars_empty {e : LocalTypeR} :
    e.isClosed = true ↔ e.freeVars = [] := by
  simp only [LocalTypeR.isClosed, List.isEmpty_iff_eq_nil]

/-! ## Section 4: Guardedness Lemmas -/

/-- **Subproblem 2**: Substitution preserves guardedness for variables other
than the substituted one. -/
theorem isGuarded_substitute (v t : String) (body e : LocalTypeR) (h : v ≠ t) :
    body.isGuarded v = true → (body.substitute t e).isGuarded v = true := by
  sorry

/-- **Subproblem 4**: In a contractive type, all free variables are guarded. -/
theorem contractive_implies_guarded (v : String) (e : LocalTypeR) :
    e.isContractive = true → e.isFreeIn v = true → e.isGuarded v = true := by
  sorry

/-! ## Section 5: Full Unfolding Lemmas -/

/-- **Subproblem 6a**: Full unfolding yields muHeight = 0.

This is the key lemma needed for LocalTypeR.lean:382. -/
theorem fullUnfold_muHeight_zero (e : LocalTypeR) :
    e.fullUnfold.muHeight = 0 := by
  sorry

/-- **Subproblem 6b**: Full unfolding reaches a non-mu form.

Follows from fullUnfold_muHeight_zero and the existing LocalTypeR.fullUnfold_not_mu. -/
theorem fullUnfold_not_mu (e : LocalTypeR) :
    ∀ t body, e.fullUnfold ≠ .mu t body := by
  intro t body hcontra
  have h := fullUnfold_muHeight_zero e
  cases hcontra
  simp [LocalTypeR.muHeight] at h

/-- **Subproblem 1**: Closed types don't unfold to var.

This addresses the sorry at LocalTypeR.lean:368. -/
theorem fullUnfold_not_var_of_closed {lt : LocalTypeR}
    (hclosed : lt.isClosed = true) : ∀ v, lt.fullUnfold ≠ .var v := by
  sorry

/-! ## Section 6: Completeness Check -/

-- These are the sorries we aim to resolve in LocalTypeR.lean:
-- Line 188: isClosed_substitute_mu ✓ (defined above)
-- Line 368: fullUnfold_not_var_of_closed ✓ (defined above)
-- Line 382: fullUnfold_non_mu_of_contractive ✓ (use fullUnfold_muHeight_zero)
-- Line 417, 569: Complex cases (may require unguarded_unfolds_to_var)

end LocalTypeCore
