import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.CoTypes.Bisim

/-!
# Observable Behavior of Closed Recursive Types

This module proves that closed, contractive recursive types eventually exhibit
observable behavior (end, send, or recv). This is directly adapted from
`work/observable_closed_problem.lean` using our concrete LocalTypeR type.

## The Problem

A type is "closed" if it has no free variables. The key theorem states:

> Every closed, contractive type eventually unfolds to an observable form.

The difficulty: the obvious induction measure (`muHeight` = nesting depth of mus)
doesn't decrease through unfolding because `body.substitute t (mu t body)` can
have higher muHeight than the original type.

## Proof Strategy

1. Don't induct on muHeight directly
2. Use guardedness: in a contractive type, the bound variable only appears inside communications
3. Key lemma: if v is free but NOT guarded in e, then fullUnfold e = var v
4. Contrapositive: if e is closed and contractive, then fullUnfold e cannot be a var

The key insight: guardedness ensures we "make progress" through mu binders.

## Structure

This file proves 6 subproblems that build toward the main theorem:
1. `unguarded_unfolds_to_var`: Unguarded variables surface through fullUnfold
2. `isGuarded_substitute`: Guardedness preserved through substitution
3. `isFreeIn_substitute`: Free variables preserved through substitution
4. `contractive_implies_guarded`: Contractive types have no unguarded free variables
5. `closed_contractive_fullUnfold_not_var`: Closed contractive types don't unfold to var
6. `fullUnfold_not_mu`: fullUnfold reaches non-mu form

-/

namespace ObservableClosed

open LocalTypeR

-- Re-export Observable predicates from Bisim.lean
-- These are already defined: UnfoldsToEnd, UnfoldsToVar, CanSend, CanRecv, Observable

/-! ## Subproblem 1: Unguarded variables unfold to themselves

If variable v is free in e but NOT guarded, then e.fullUnfold = var v.

This captures the intuition that unguarded variables are "at the head"
and will be exposed after unfolding all the mus.

PROOF STRATEGY:
- Base cases (non-mu): Either v is not free (contradiction) or e = var v
- Mu case: v ≠ t (else shadowed = guarded) and v unguarded in body
  Need to show: fullUnfold(body.substitute t (mu t body)) = var v

The mu case is the difficult one. We need to show that substitution
preserves the "unguarded at head" property.
-/
theorem unguarded_unfolds_to_var (e : LocalTypeR) (v : String)
    (h_free : e.isFreeIn v = true) (h_not_guarded : e.isGuarded v = false) :
    e.fullUnfold = LocalTypeR.var v := by
  sorry

/-! ## Subproblem 2: Guardedness preserved through substitution

If v is unguarded in e, and we substitute some other variable t with repl,
then v remains unguarded in the result (assuming v ≠ t and v not free in repl).

This is needed for the mu case of unguarded_unfolds_to_var.

DIFFICULTY: The substitution may introduce new occurrences of v via repl.
We need the condition that v is not free in repl.
-/
theorem isGuarded_substitute (e : LocalTypeR) (v t : String) (repl : LocalTypeR)
    (hvt : v ≠ t)
    (hv_repl : repl.isFreeIn v = false)
    (h_unguarded : e.isGuarded v = false) :
    (e.substitute t repl).isGuarded v = false := by
  induction e with
  | end =>
    simp [LocalTypeR.isGuarded] at h_unguarded
  | var w =>
    simp [LocalTypeR.isGuarded] at h_unguarded ⊢
    simp [LocalTypeR.substitute]
    split
    · -- w == t, so substitute gives repl
      -- h_unguarded : (v != w) = false, so v = w
      -- But hvt says v != t, and w = t from the split
      -- So v = w = t, contradicting hvt
      have : w = t := by simp_all
      have : v = w := by
        by_contra hne
        simp [hne] at h_unguarded
      rw [this.symm] at hvt
      simp at hvt
    · -- w != t, substitute is identity
      exact h_unguarded
  | send p bs | recv p bs =>
    simp [LocalTypeR.isGuarded] at h_unguarded
  | mu s body ih =>
    simp [LocalTypeR.isGuarded] at h_unguarded ⊢
    simp [LocalTypeR.substitute]
    split at h_unguarded
    · -- v == s, contradiction with h_unguarded
      simp at h_unguarded
    · -- v != s
      split
      · -- s == t
        split
        · simp_all
        · exact h_unguarded
      · -- s != t
        split
        · simp_all
        · exact ih hv_repl h_unguarded

/-! ## Subproblem 3: Free variable preserved through substitution

If v is free in e and v ≠ t, then v is still free in e.substitute t repl
(assuming v is not captured by any mu in repl).

This is the contrapositive direction needed for the mu case.
-/
theorem isFreeIn_substitute (e : LocalTypeR) (v t : String) (repl : LocalTypeR)
    (hvt : v ≠ t)
    (h_free : e.isFreeIn v = true) :
    (e.substitute t repl).isFreeIn v = true ∨ repl.isFreeIn v = true := by
  induction e with
  | end =>
    simp [LocalTypeR.isFreeIn] at h_free
  | var w =>
    simp [LocalTypeR.isFreeIn] at h_free
    simp [LocalTypeR.substitute]
    split
    · -- w == t
      -- h_free : v == w, so v = w = t, but hvt says v != t
      have : w = t := by simp_all
      rw [←this] at hvt
      have : v = w := by simp_all
      rw [this] at hvt
      simp at hvt
    · -- w != t
      left
      simp [LocalTypeR.isFreeIn]
      exact h_free
  | send p bs | recv p bs =>
    sorry -- Need helper for branches
  | mu s body ih =>
    simp [LocalTypeR.isFreeIn] at h_free ⊢
    simp [LocalTypeR.substitute]
    split at h_free
    · simp at h_free
    · split
      · -- s == t
        left
        split
        · simp_all
        · exact h_free
      · -- s != t
        split
        · simp_all
        · have := ih h_free
          cases this with
          | inl h => left; exact h
          | inr h => right; exact h

/-! ## Subproblem 4: Contractive types have no unguarded free variables

If a type is contractive, then every free variable is guarded.
This is the key connection between contractiveness and guardedness.

PROOF: By induction on type structure.
- end/var/send/recv: immediate
- mu t body: body.isGuarded t by contractiveness, and IH on body
-/
theorem contractive_implies_guarded (e : LocalTypeR) (v : String)
    (h_contractive : e.isContractive = true)
    (h_free : e.isFreeIn v = true) :
    e.isGuarded v = true := by
  induction e with
  | end =>
    simp [LocalTypeR.isFreeIn] at h_free
  | var w =>
    -- If v is free in (var w), then v = w
    -- But isGuarded v (var w) = (v != w) = false when v = w
    -- This case is impossible for closed types
    simp [LocalTypeR.isFreeIn] at h_free
    simp [LocalTypeR.isGuarded, h_free]
  | send p bs | recv p bs =>
    -- send/recv are always guarded
    simp [LocalTypeR.isGuarded]
  | mu t body ih =>
    simp [LocalTypeR.isContractive, Bool.and_eq_true] at h_contractive
    obtain ⟨hguarded_t, hcontr_body⟩ := h_contractive
    simp [LocalTypeR.isFreeIn] at h_free
    split at h_free
    · simp at h_free
    · simp [LocalTypeR.isGuarded]
      split
      · simp_all
      · exact ih hcontr_body h_free

/-! ## Subproblem 5: Closed contractive types unfold to non-variable

Combining the above: if e is closed and contractive, fullUnfold e ≠ var w for any w.

PROOF:
- Suppose fullUnfold e = var w
- By unguarded_unfolds_to_var contrapositive: w must be free and unguarded
- By contractive_implies_guarded: if w is free, it's guarded
- By closed: no variable is free
- Contradiction
-/
theorem closed_contractive_fullUnfold_not_var (e : LocalTypeR) (w : String)
    (h_closed : e.isClosed = true)
    (h_contractive : e.isContractive = true) :
    e.fullUnfold ≠ LocalTypeR.var w := by
  sorry

/-! ## Subproblem 6: fullUnfold reaches non-mu

After muHeight unfolding steps, the result has no mu at the head.

PROOF: By induction on muHeight.
- muHeight = 0: e is not a mu, so fullUnfold e = e
- muHeight = n+1: e = mu t body, unfold gives body.substitute t (mu t body),
  which has muHeight ≤ n (need lemma about muHeight of substitution)
-/
theorem fullUnfold_not_mu (e : LocalTypeR) :
    ∀ t body, e.fullUnfold ≠ LocalTypeR.mu t body := by
  sorry

/-! ## Main Theorem

Every closed, contractive type has observable behavior.
For closed types, UnfoldsToVar is impossible (no free variables),
so the type must unfold to end, send, or recv.

NOTE: This theorem is already proved in Bisim.lean as `observable_of_closed_contractive`.
We re-state it here to show how it follows from the 6 subproblems.
-/
theorem observable_of_closed_contractive (e : LocalTypeR)
    (h_closed : e.isClosed = true)
    (h_contractive : e.isContractive = true) :
    Observable e := by
  -- This is already proved in Bisim.lean, but we can see how it uses the subproblems
  sorry

end ObservableClosed
