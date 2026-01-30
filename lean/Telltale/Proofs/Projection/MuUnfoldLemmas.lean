import Telltale.Protocol.GlobalType
import Telltale.Protocol.LocalTypeR
import Telltale.Protocol.Projection.Trans
import Telltale.Protocol.Projection.ProjSubst
import Telltale.Protocol.CoTypes.EQ2

/-! # Mu-Unfold Lemmas for Harmony

This module proves the 4 mu-unfold lemmas in Harmony.lean using the `proj_subst` lemma.

## Main Results

1. `EQ2_mu_crossed_unfold_left`: Crossed mu-unfold (left) for mu-mu case
2. `EQ2_mu_crossed_unfold_right`: Crossed mu-unfold (right) for mu-mu case
3. `EQ2_mu_unguarded_to_end`: Mismatched guardedness (guarded → mu, unguarded → end)
4. `EQ2_end_to_mu_unguarded`: Mismatched guardedness (unguarded → end, guarded → mu)

## Proof Strategy

The key insight is that `proj_subst` gives us:
```
trans (inner.substitute t G) role = (trans inner role).substitute t (trans G role)
```

This allows us to rewrite the LHS of the crossed-unfold lemmas, and then apply
`EQ2_unfold_left`/`EQ2_unfold_right` which handle mu-unfolding via EQ2.
-/

namespace Telltale.Proofs.Projection.MuUnfoldLemmas

open Telltale.Protocol.GlobalType (GlobalType Label)
open Telltale.Protocol.LocalTypeR (LocalTypeR)
open Telltale.Protocol.LocalTypeR (isGuarded_of_closed isGuarded_substitute)
open Telltale.Protocol.CoTypes.EQ2
open Telltale.Protocol.Projection.ProjSubst (projTrans proj_subst)

/-! ## Core Helper: Unfold Reflexivity

The key observation is that `EQ2_unfold_left (EQ2_refl (.mu s X))` gives us:
  EQ2 (X.substitute s (.mu s X)) (.mu s X)

because `unfold (.mu s X) = X.substitute s (.mu s X)`. -/

/-- Mu self-unfold: the unfolding of a mu is EQ2-equivalent to the mu itself.

    This is the core lemma that powers the crossed-unfold proofs. -/
theorem EQ2_mu_self_unfold (s : String) (body : LocalTypeR) :
    EQ2 (body.substitute s (.mu s body)) (.mu s body) := by
  have h := EQ2_unfold_left (EQ2_refl (.mu s body))
  simp only [LocalTypeR.unfold] at h
  exact h

/-- Symmetric version: mu is EQ2-equivalent to its unfolding. -/
theorem EQ2_mu_to_unfold (s : String) (body : LocalTypeR) :
    EQ2 (.mu s body) (body.substitute s (.mu s body)) := by
  -- Symmetry of EQ2 flips the direction of mu self-unfold.
  exact EQ2_symm (EQ2_mu_self_unfold s body)

/-! ## Crossed Unfold Lemmas -/

/-- Mu-mu crossed unfold: right unfold relates to left mu.

    Given both sides are guarded for s, we have:
    - LHS: `(trans (inner.substitute t G) role).substitute s (.mu s ...)`
    - RHS: `.mu s ((trans inner role).substitute t (trans G role))`

    Using `proj_subst`, both occurrences of `trans (inner.substitute t G) role`
    become `(trans inner role).substitute t (trans G role)`, so:
    - LHS becomes: `X.substitute s (.mu s X)`
    - RHS is: `.mu s X`

    And `EQ2_mu_self_unfold` gives us `EQ2 (X.substitute s (.mu s X)) (.mu s X)`.
-/
theorem EQ2_mu_crossed_unfold_left'
    {s t : String} {inner G : GlobalType} {role : String}
    (hGclosed : G.isClosed = true)
    (_hL : (projTrans (inner.substitute t G) role).isGuarded s = true)
    (_hR_pre : (projTrans inner role).isGuarded s = true) :
    EQ2 ((projTrans (inner.substitute t G) role).substitute s
           (.mu s (projTrans (inner.substitute t G) role)))
        (.mu s ((projTrans inner role).substitute t (projTrans G role))) := by
  -- proj_subst: trans (inner.substitute t G) role = (trans inner role).substitute t (trans G role)
  -- Use simp to rewrite all occurrences
  simp only [proj_subst _ _ _ _ hGclosed]
  -- Now goal is: EQ2 (X.substitute s (.mu s X)) (.mu s X)
  exact EQ2_mu_self_unfold s _

/-- Mu-mu crossed unfold: left mu relates to right unfold.

    Symmetric to `EQ2_mu_crossed_unfold_left'`. -/
theorem EQ2_mu_crossed_unfold_right'
    {s t : String} {inner G : GlobalType} {role : String}
    (hGclosed : G.isClosed = true)
    (_hL : (projTrans (inner.substitute t G) role).isGuarded s = true)
    (_hR_pre : (projTrans inner role).isGuarded s = true) :
    EQ2 (.mu s (projTrans (inner.substitute t G) role))
        (((projTrans inner role).substitute t (projTrans G role)).substitute s
          (.mu s ((projTrans inner role).substitute t (projTrans G role)))) := by
  -- Use simp to rewrite all occurrences
  simp only [proj_subst _ _ _ _ hGclosed]
  -- Now goal is: EQ2 (.mu s X) (X.substitute s (.mu s X))
  exact EQ2_mu_to_unfold s _

/-! ## Guardedness Preservation Through Substitution

Unguardedness is preserved when substituting a different variable `u ≠ v`.
This rules out the mismatched guardedness cases in Harmony.lean for `s ≠ t`. -/

/- Key lemma: Unguardedness is preserved when substituting a different variable.

   If `t.isGuarded v = false` (v appears unguarded) and `u ≠ v`,
   then `(t.substitute u repl).isGuarded v = false`.

   Proof: The `.var v` that caused unguardedness is unchanged by substituting `u`. -/
/-- Unguardedness preservation: `.end` case is impossible. -/
private theorem isGuarded_false_substitute_preserved_end (u v : String) (repl : LocalTypeR)
    (hunguarded : LocalTypeR.end.isGuarded v = false) :
    (LocalTypeR.end.substitute u repl).isGuarded v = false := by
  -- isGuarded v .end = true, contradicting hunguarded.
  simp only [LocalTypeR.isGuarded] at hunguarded
  exact absurd hunguarded (by decide)

/-- Unguardedness preservation: variable case. -/
private theorem isGuarded_false_substitute_preserved_var (w u v : String) (repl : LocalTypeR)
    (hneq : u ≠ v) (hunguarded : (LocalTypeR.var w).isGuarded v = false) :
    ((LocalTypeR.var w).substitute u repl).isGuarded v = false := by
  -- Unguardedness forces w = v, then substitution with u ≠ v leaves .var v.
  simp only [LocalTypeR.isGuarded, bne_eq_false_iff_eq] at hunguarded
  subst hunguarded
  simp only [LocalTypeR.substitute]
  split
  · rename_i hvu
    simp only [beq_iff_eq] at hvu
    exact absurd hvu.symm hneq
  · simp only [LocalTypeR.isGuarded, bne_self_eq_false]

/-- Unguardedness preservation: `.send` case is impossible. -/
private theorem isGuarded_false_substitute_preserved_send (p : String) (bs : List (Label × LocalTypeR))
    (u v : String) (repl : LocalTypeR) (hunguarded : (LocalTypeR.send p bs).isGuarded v = false) :
    ((LocalTypeR.send p bs).substitute u repl).isGuarded v = false := by
  -- isGuarded v (.send p bs) = true, contradicts hunguarded.
  simp only [LocalTypeR.isGuarded] at hunguarded
  exact absurd hunguarded (by decide)

/-- Unguardedness preservation: `.recv` case is impossible. -/
private theorem isGuarded_false_substitute_preserved_recv (p : String) (bs : List (Label × LocalTypeR))
    (u v : String) (repl : LocalTypeR) (hunguarded : (LocalTypeR.recv p bs).isGuarded v = false) :
    ((LocalTypeR.recv p bs).substitute u repl).isGuarded v = false := by
  -- isGuarded v (.recv p bs) = true, contradicts hunguarded.
  simp only [LocalTypeR.isGuarded] at hunguarded
  exact absurd hunguarded (by decide)

/-- Unguardedness preservation: mu case uses the induction hypothesis. -/
private theorem isGuarded_false_substitute_preserved_mu (s : String) (body : LocalTypeR)
    (u v : String) (repl : LocalTypeR) (_hneq : u ≠ v)
    (hunguarded : (LocalTypeR.mu s body).isGuarded v = false)
    (ih : body.isGuarded v = false → (body.substitute u repl).isGuarded v = false) :
    ((LocalTypeR.mu s body).substitute u repl).isGuarded v = false := by
  -- Split on v == s, then on s == u to account for shadowing.
  simp only [LocalTypeR.isGuarded] at hunguarded
  split at hunguarded
  · contradiction
  · rename_i hvs
    simp only [LocalTypeR.substitute]
    split
    · simp only [LocalTypeR.isGuarded, hvs]
      exact hunguarded
    · simp only [LocalTypeR.isGuarded, hvs]
      exact ih hunguarded

/-- Key lemma: Unguardedness is preserved when substituting a different variable. -/
theorem isGuarded_false_substitute_preserved (t : LocalTypeR) (u v : String) (repl : LocalTypeR)
    (hneq : u ≠ v) (hunguarded : t.isGuarded v = false) :
    (t.substitute u repl).isGuarded v = false := by
  -- Structural recursion on the local type (avoid `induction` on nested inductive).
  refine (LocalTypeR.rec
    (motive_1 := fun t => t.isGuarded v = false → (t.substitute u repl).isGuarded v = false)
    (motive_2 := fun _ => True) (motive_3 := fun _ => True)
    (by intro h; exact isGuarded_false_substitute_preserved_end u v repl h)
    (by intro p bs _ h; exact isGuarded_false_substitute_preserved_send p bs u v repl h)
    (by intro p bs _ h; exact isGuarded_false_substitute_preserved_recv p bs u v repl h)
    (by intro s body ih h; exact isGuarded_false_substitute_preserved_mu s body u v repl hneq h ih)
    (by intro w h; exact isGuarded_false_substitute_preserved_var w u v repl hneq h)
    (by exact True.intro) (by intro _ _ _ _; exact True.intro) (by intro _ _ _; exact True.intro) t) hunguarded

/-- Corollary: Unguardedness is preserved in the forward direction.
    (The reverse direction is more complex and not needed.) -/
theorem isGuarded_substitute_forward (lt : LocalTypeR) (u v : String) (repl : LocalTypeR)
    (hneq : u ≠ v) (hunguarded : lt.isGuarded v = false) :
    (lt.substitute u repl).isGuarded v = false := by
  -- Reuse the preservation lemma directly.
  exact isGuarded_false_substitute_preserved lt u v repl hneq hunguarded

/-! ## Mismatched Guardedness Lemmas

These handle the case where one side is guarded and the other is not.

**Key Insight:** For `EQ2_mu_unguarded_to_end'`, the hypotheses are contradictory!

By `proj_subst`:
  `projTrans (inner.substitute t G) role = (projTrans inner role).substitute t (projTrans G role)`

So if `(projTrans inner role).isGuarded s = false` and `s ≠ t`, then by
`isGuarded_false_substitute_preserved`, the LHS also has `isGuarded s = false`.

But `hL` claims `isGuarded s = true`, contradiction! -/

/-- Mismatched guardedness: guarded mu unfold relates to end. -/
theorem EQ2_mu_unguarded_to_end'
    {s t : String} {inner G : GlobalType} {role : String}
    (hst : s ≠ t)
    (hGclosed : G.isClosed = true)
    (hL : (projTrans (inner.substitute t G) role).isGuarded s = true)
    (hR_pre : (projTrans inner role).isGuarded s = false) :
    EQ2 ((projTrans (inner.substitute t G) role).substitute s
           (.mu s (projTrans (inner.substitute t G) role)))
        .end := by
  -- By proj_subst: projTrans (inner.substitute t G) role = (projTrans inner role).substitute t (projTrans G role)
  rw [proj_subst inner t G role hGclosed] at hL
  -- Now hL says: ((projTrans inner role).substitute t (projTrans G role)).isGuarded s = true
  -- But since (projTrans inner role).isGuarded s = false and s ≠ t,
  -- by isGuarded_false_substitute_preserved, the substituted term also has isGuarded s = false.
  have hcontra := isGuarded_false_substitute_preserved
    (projTrans inner role) t s (projTrans G role) (Ne.symm hst) hR_pre
  -- hcontra: ((projTrans inner role).substitute t (projTrans G role)).isGuarded s = false
  -- hL: ((projTrans inner role).substitute t (projTrans G role)).isGuarded s = true
  -- Contradiction!
  rw [hcontra] at hL
  simp at hL

/-- Mismatched guardedness: end relates to guarded mu unfold. -/
theorem EQ2_end_to_mu_unguarded'
    {s t : String} {inner G : GlobalType} {role : String}
    (hGclosed : G.isClosed = true)
    (hL_pre : (projTrans (inner.substitute t G) role).isGuarded s = false)
    (hR : (projTrans inner role).isGuarded s = true) :
    EQ2 .end
        (((projTrans inner role).substitute t (projTrans G role)).substitute s
          (.mu s ((projTrans inner role).substitute t (projTrans G role)))) := by
  -- The hypothesis hL_pre is vacuously false for closed G.
  -- By proj_subst: projTrans (inner.substitute t G) role = (projTrans inner role).substitute t (projTrans G role)
  rw [proj_subst inner t G role hGclosed] at hL_pre
  -- projTrans G role is closed (since G is closed)
  have hProjGclosed : (projTrans G role).isClosed = true :=
    Telltale.Protocol.Projection.Trans.trans_isClosed_of_isClosed G role hGclosed
  -- For closed local types, all variables are guarded
  have hProjGguarded : (projTrans G role).isGuarded s = true :=
    isGuarded_of_closed (projTrans G role) s hProjGclosed
  -- By isGuarded_substitute (LocalTypeR.lean:1242), guardedness is preserved under substitution
  -- when the replacement is closed.
  have hSubstGuarded : ((projTrans inner role).substitute t (projTrans G role)).isGuarded s = true :=
    isGuarded_substitute (projTrans inner role) t s (projTrans G role) hR hProjGclosed
  -- Contradiction: hL_pre says isGuarded s = false, but hSubstGuarded says it's true
  rw [hSubstGuarded] at hL_pre
  simp at hL_pre

end Telltale.Proofs.Projection.MuUnfoldLemmas
