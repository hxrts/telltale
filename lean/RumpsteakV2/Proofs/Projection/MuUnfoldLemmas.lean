import RumpsteakV2.Protocol.GlobalType
import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.Projection.Trans
import RumpsteakV2.Protocol.Projection.ProjSubst
import RumpsteakV2.Protocol.CoTypes.EQ2

/-! # Mu-Unfold Lemmas for Harmony

This module proves the 4 mu-unfold axioms in Harmony.lean using the `proj_subst` lemma.

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

This allows us to rewrite the LHS of the crossed-unfold axioms, and then apply
`EQ2_unfold_left`/`EQ2_unfold_right` which handle mu-unfolding via EQ2.
-/

namespace RumpsteakV2.Proofs.Projection.MuUnfoldLemmas

open RumpsteakV2.Protocol.GlobalType (GlobalType Label)
open RumpsteakV2.Protocol.LocalTypeR (LocalTypeR)
open RumpsteakV2.Protocol.LocalTypeR (isGuarded_of_closed isGuarded_substitute)
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.Projection.ProjSubst (projTrans proj_subst)

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
    EQ2 (.mu s body) (body.substitute s (.mu s body)) :=
  EQ2_symm (EQ2_mu_self_unfold s body)

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
    (_hL : (projTrans (inner.substitute t G) role).isGuarded s = true)
    (_hR_pre : (projTrans inner role).isGuarded s = true) :
    EQ2 ((projTrans (inner.substitute t G) role).substitute s
           (.mu s (projTrans (inner.substitute t G) role)))
        (.mu s ((projTrans inner role).substitute t (projTrans G role))) := by
  -- proj_subst: trans (inner.substitute t G) role = (trans inner role).substitute t (trans G role)
  -- Use simp to rewrite all occurrences
  simp only [proj_subst]
  -- Now goal is: EQ2 (X.substitute s (.mu s X)) (.mu s X)
  exact EQ2_mu_self_unfold s _

/-- Mu-mu crossed unfold: left mu relates to right unfold.

    Symmetric to `EQ2_mu_crossed_unfold_left'`. -/
theorem EQ2_mu_crossed_unfold_right'
    {s t : String} {inner G : GlobalType} {role : String}
    (_hL : (projTrans (inner.substitute t G) role).isGuarded s = true)
    (_hR_pre : (projTrans inner role).isGuarded s = true) :
    EQ2 (.mu s (projTrans (inner.substitute t G) role))
        (((projTrans inner role).substitute t (projTrans G role)).substitute s
          (.mu s ((projTrans inner role).substitute t (projTrans G role)))) := by
  -- Use simp to rewrite all occurrences
  simp only [proj_subst]
  -- Now goal is: EQ2 (.mu s X) (X.substitute s (.mu s X))
  exact EQ2_mu_to_unfold s _

/-! ## Guardedness Preservation Through Substitution

The key insight for the mismatched guardedness cases is that guardedness
is preserved in a specific way through substitution:

1. If `v` is unguarded in `t`, and we substitute a *different* variable `u ≠ v`,
   then `v` remains unguarded (the `.var v` is still there).

2. If `v` is guarded in `t`, substitution can only make `v` unguarded if the
   replacement term has unguarded `v` and we replace at an unguarded position.

This means the "mismatched guardedness" cases in Harmony.lean are actually
impossible when `s ≠ t` (the non-shadowed mu case). -/

/-- Key lemma: Unguardedness is preserved when substituting a different variable.

    If `t.isGuarded v = false` (v appears unguarded) and `u ≠ v`,
    then `(t.substitute u repl).isGuarded v = false`.

    Proof: The `.var v` that caused unguardedness is unchanged by substituting `u`. -/
theorem isGuarded_false_substitute_preserved (t : LocalTypeR) (u v : String) (repl : LocalTypeR)
    (hneq : u ≠ v) (hunguarded : t.isGuarded v = false) :
    (t.substitute u repl).isGuarded v = false := by
  cases t with
  | «end» =>
      -- isGuarded v .end = true, contradicts hunguarded
      simp only [LocalTypeR.isGuarded] at hunguarded
      -- hunguarded : true = false, contradiction
      exact absurd hunguarded (by decide)
  | var w =>
      -- isGuarded v (.var w) = (v != w), so hunguarded means v = w
      simp only [LocalTypeR.isGuarded] at hunguarded
      -- hunguarded : (v != w) = false, which means v = w
      simp only [bne_eq_false_iff_eq] at hunguarded
      subst hunguarded
      -- Now w = v, and we substitute u for v where u ≠ v
      -- Goal: (.var v).substitute u repl).isGuarded v = false
      simp only [LocalTypeR.substitute]
      -- Now goal involves: if v == u then repl else .var v
      -- Since v ≠ u, the condition v == u is false
      split
      · -- v == u case: impossible since hneq says u ≠ v
        rename_i hvu
        simp only [beq_iff_eq] at hvu
        exact absurd hvu.symm hneq
      · -- v != u case: result is .var v, so isGuarded v (.var v) = (v != v) = false
        simp only [LocalTypeR.isGuarded, bne_self_eq_false]
  | send p bs =>
      -- isGuarded v (.send p bs) = true, contradicts hunguarded
      simp only [LocalTypeR.isGuarded] at hunguarded
      exact absurd hunguarded (by decide)
  | recv p bs =>
      -- isGuarded v (.recv p bs) = true, contradicts hunguarded
      simp only [LocalTypeR.isGuarded] at hunguarded
      exact absurd hunguarded (by decide)
  | mu s body =>
      -- isGuarded v (.mu s body) = if v == s then true else body.isGuarded v
      simp only [LocalTypeR.isGuarded] at hunguarded
      split at hunguarded
      · -- v == s case: isGuarded = true, contradicts hunguarded
        contradiction
      · -- v != s case: body.isGuarded v = false
        rename_i hvs
        simp only [LocalTypeR.substitute]
        split
        · -- s == u: substitution shadowed, result is .mu s body unchanged
          simp only [LocalTypeR.isGuarded, hvs]
          exact hunguarded
        · -- s != u: result is .mu s (body.substitute u repl)
          simp only [LocalTypeR.isGuarded, hvs]
          -- IH: body.substitute has isGuarded v = false
          exact isGuarded_false_substitute_preserved body u v repl hneq hunguarded

/-- Corollary: Unguardedness is preserved in the forward direction.
    (The reverse direction is more complex and not needed.) -/
theorem isGuarded_substitute_forward (lt : LocalTypeR) (u v : String) (repl : LocalTypeR)
    (hneq : u ≠ v) (hunguarded : lt.isGuarded v = false) :
    (lt.substitute u repl).isGuarded v = false :=
  isGuarded_false_substitute_preserved lt u v repl hneq hunguarded

/-! ## Mismatched Guardedness Lemmas

These handle the case where one side is guarded and the other is not.

**Key Insight:** For `EQ2_mu_unguarded_to_end'`, the hypotheses are contradictory!

By `proj_subst`:
  `projTrans (inner.substitute t G) role = (projTrans inner role).substitute t (projTrans G role)`

So if `(projTrans inner role).isGuarded s = false` and `s ≠ t`, then by
`isGuarded_false_substitute_preserved`, the LHS also has `isGuarded s = false`.

But `hL` claims `isGuarded s = true`, contradiction! -/

/-- Mismatched guardedness: guarded mu unfold relates to end.

    **PROVEN**: This case is vacuously true because the hypotheses are contradictory.

    By `proj_subst`, both sides have the same isGuarded value when `s ≠ t`.
    So if RHS is unguarded (`hR_pre`), LHS cannot be guarded (`hL`).

    Note: Requires `s ≠ t` hypothesis, which holds in Harmony.lean (non-shadowed branch). -/
theorem EQ2_mu_unguarded_to_end'
    {s t : String} {inner G : GlobalType} {role : String}
    (hst : s ≠ t)
    (hL : (projTrans (inner.substitute t G) role).isGuarded s = true)
    (hR_pre : (projTrans inner role).isGuarded s = false) :
    EQ2 ((projTrans (inner.substitute t G) role).substitute s
           (.mu s (projTrans (inner.substitute t G) role)))
        .end := by
  -- By proj_subst: projTrans (inner.substitute t G) role = (projTrans inner role).substitute t (projTrans G role)
  rw [proj_subst] at hL
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

/-- Mismatched guardedness: end relates to guarded mu unfold.

    **Analysis from Coq reference (coLocal.v):**

    In Coq, EQ2 is defined as `paco2 ((ApplyF full_eunf full_eunf) ∘ EQ2_gen)`, meaning
    both sides are fully unfolded before comparison. The key lemma `eguarded_unfv` shows:
    ```
    eguarded n g = false → full_eunf g = EVar n
    ```
    So unguarded mu types unfold to `EVar n`, NOT `EEnd`. Since `EQ2_gen` has no case
    matching `EEnd` with `EVar n`, Coq considers `.end` and unguarded mu to be **NOT**
    EQ2-equivalent. Instead, Coq uses well-formedness predicates (`lInvPred`) to exclude
    non-contractive types from the EQ2 domain entirely.

    **Our approach:** Following Coq's strategy, we require the global type `G` to be closed.
    For closed types, `isGuarded_of_closed` shows all variables are guarded, making the
    hypothesis `hL_pre : isGuarded s = false` vacuously false. This makes the theorem
    trivially true by contradiction.

    **Why this works:** In real protocol verification, global types are closed (no free
    variables). By `trans_isClosed_of_isClosed`, projections of closed global types are
    closed local types. Therefore, the unguardedness hypothesis never holds in practice.

    Note: Requires `s ≠ t` hypothesis, which holds in Harmony.lean (non-shadowed branch). -/
theorem EQ2_end_to_mu_unguarded'
    {s t : String} {inner G : GlobalType} {role : String}
    (hst : s ≠ t)
    (hGclosed : G.isClosed = true)
    (hL_pre : (projTrans (inner.substitute t G) role).isGuarded s = false)
    (hR : (projTrans inner role).isGuarded s = true) :
    EQ2 .end
        (((projTrans inner role).substitute t (projTrans G role)).substitute s
          (.mu s ((projTrans inner role).substitute t (projTrans G role)))) := by
  -- The hypothesis hL_pre is vacuously false for closed G.
  -- By proj_subst: projTrans (inner.substitute t G) role = (projTrans inner role).substitute t (projTrans G role)
  rw [proj_subst] at hL_pre
  -- projTrans G role is closed (since G is closed)
  have hProjGclosed : (projTrans G role).isClosed = true :=
    RumpsteakV2.Protocol.Projection.Trans.trans_isClosed_of_isClosed G role hGclosed
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

end RumpsteakV2.Proofs.Projection.MuUnfoldLemmas
