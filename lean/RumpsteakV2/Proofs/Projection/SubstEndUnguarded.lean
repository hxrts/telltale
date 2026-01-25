import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.CoTypes.Observable
import RumpsteakV2.Protocol.CoTypes.Bisim
import RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt

/-! # SubstEndUnguarded: Substituting End for Unguarded Variables

This module proves that substituting `.end` for an unguarded variable produces
a local type that is EQ2-equivalent to `.end`.

## Main Result

`subst_end_unguarded_eq2_end`: If `lt.isGuarded v = false`, then
`EQ2 (lt.substitute v .end) .end`.
-/

namespace RumpsteakV2.Proofs.Projection.SubstEndUnguarded

open RumpsteakV2.Protocol.LocalTypeR (LocalTypeR substituteBranches substitute_send substitute_recv substitute_end)
open RumpsteakV2.Protocol.GlobalType (Label)
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.Observable
open RumpsteakV2.Protocol.CoTypes.Bisim (UnfoldsToEnd.toEQ2)

-- Use the isFreeIn from SubstCommBarendregt
open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt (isFreeIn isFreeInBranches substitute_not_free)

/-! ## Helper lemmas for termination -/

/-- sizeOf of second component is less than sizeOf of the pair. -/
private theorem sizeOf_snd_lt_sizeOf_pair (hd : Label × LocalTypeR) :
    sizeOf hd.2 < sizeOf hd := by
  -- sizeOf (a, b) = 1 + sizeOf a + sizeOf b
  show sizeOf hd.2 < 1 + sizeOf hd.1 + sizeOf hd.2
  omega

/-- sizeOf of element is less than sizeOf of cons list. -/
private theorem sizeOf_snd_lt_sizeOf_cons (hd : Label × LocalTypeR) (tl : List (Label × LocalTypeR)) :
    sizeOf hd.2 < sizeOf (hd :: tl) := by
  have h1 : sizeOf hd.2 < sizeOf hd := sizeOf_snd_lt_sizeOf_pair hd
  -- sizeOf (hd :: tl) = 1 + sizeOf hd + sizeOf tl
  show sizeOf hd.2 < 1 + sizeOf hd + sizeOf tl
  omega

private theorem sizeOf_tl_lt_sizeOf_cons (hd : Label × LocalTypeR) (tl : List (Label × LocalTypeR)) :
    sizeOf tl < sizeOf (hd :: tl) := by
  -- sizeOf (hd :: tl) = 1 + sizeOf hd + sizeOf tl
  show sizeOf tl < 1 + sizeOf hd + sizeOf tl
  omega

/-! ## Key Lemma: Free variables preserved through substitution for other variable -/

/-- Helper: var case for isFreeIn_subst_other. -/
private theorem isFreeIn_subst_other_var (v t w : String) (repl : LocalTypeR)
    (hvt : v ≠ t) (hfree : isFreeIn v (LocalTypeR.var w) = true) :
    isFreeIn v ((LocalTypeR.var w).substitute t repl) = true := by
  -- Reduce to the beq split on w == t.
  by_cases hwt' : w = t
  · have hfree' : v = w := by
      have : (v == w) = true := by simpa [isFreeIn] using hfree
      exact beq_iff_eq.mp this
    exact (hvt (hfree' ▸ hwt')).elim
  · have hwt : (w == t) = false := beq_eq_false_iff_ne.mpr hwt'
    simpa [LocalTypeR.substitute, isFreeIn, hwt] using hfree

mutual
/-- Free variables are preserved through substitution when not the substituted variable. -/
theorem isFreeIn_subst_other (e : LocalTypeR) (v t : String) (repl : LocalTypeR)
    (hvt : v ≠ t) (hfree : isFreeIn v e = true) :
    isFreeIn v (e.substitute t repl) = true := by
  -- Proceed by cases on the local type constructor.
  match e with
  | .end => cases hfree
  | .var w => exact isFreeIn_subst_other_var v t w repl hvt hfree
  | .send _ bs =>
      simp only [substitute_send, isFreeIn] at hfree ⊢
      exact isFreeInBranches_subst_other bs v t repl hvt hfree
  | .recv _ bs =>
      simp only [substitute_recv, isFreeIn] at hfree ⊢
      exact isFreeInBranches_subst_other bs v t repl hvt hfree
  | .mu s body =>
      -- Split on shadowing s == t, then on v == s.
      unfold LocalTypeR.substitute
      by_cases hst : s == t
      · simpa [hst, ↓reduceIte] using hfree
      · simp only [hst, Bool.false_eq_true, ↓reduceIte, isFreeIn] at hfree ⊢
        by_cases hvs : v == s
        · simp only [hvs, ↓reduceIte] at hfree
          cases hfree
        · simp only [hvs, Bool.false_eq_true, ↓reduceIte] at hfree ⊢
          exact isFreeIn_subst_other body v t repl hvt hfree
termination_by sizeOf e

/-- Free variables in branches preserved through substitution. -/
theorem isFreeInBranches_subst_other (bs : List (Label × LocalTypeR)) (v t : String)
    (repl : LocalTypeR) (hvt : v ≠ t) (hfree : isFreeInBranches v bs = true) :
    isFreeInBranches v (substituteBranches bs t repl) = true := by
  -- Recurse over branches, preserving the witness from the head or tail.
  match bs with
  | [] => cases hfree
  | hd :: tl =>
      simp only [substituteBranches, isFreeInBranches]
      simp only [isFreeInBranches] at hfree
      cases Bool.or_eq_true_iff.mp hfree with
      | inl h => exact Bool.or_eq_true_iff.mpr (Or.inl (isFreeIn_subst_other hd.2 v t repl hvt h))
      | inr h => exact Bool.or_eq_true_iff.mpr (Or.inr (isFreeInBranches_subst_other tl v t repl hvt h))
termination_by sizeOf bs
decreasing_by
  all_goals
    first
    | exact sizeOf_snd_lt_sizeOf_cons hd tl
    | exact sizeOf_tl_lt_sizeOf_cons hd tl
end

/-! ## Key Lemma: UnfoldsToEnd implies no free variables -/

/-- Types satisfying UnfoldsToEnd have no free variables. -/
theorem UnfoldsToEnd_no_free_vars (lt : LocalTypeR) (h : UnfoldsToEnd lt) (v : String) :
    isFreeIn v lt = false := by
  induction h with
  | base => rfl
  | @mu t body _ ih =>
      simp only [isFreeIn]
      by_cases hvt : v == t
      · simp only [hvt, ↓reduceIte]
      · simp only [hvt, Bool.false_eq_true, ↓reduceIte]
        by_contra h_free
        simp only [Bool.not_eq_false] at h_free
        -- Convert ¬(v == t) = true to v ≠ t
        simp only [Bool.not_eq_true] at hvt
        have hvt_ne : v ≠ t := beq_eq_false_iff_ne.mp hvt
        have h_still_free : isFreeIn v (body.substitute t (.mu t body)) = true :=
          isFreeIn_subst_other body v t (.mu t body) hvt_ne h_free
        exact absurd h_still_free (ih ▸ Bool.false_ne_true)

/-- Substitution into a term satisfying UnfoldsToEnd is a no-op. -/
theorem substitute_UnfoldsToEnd_eq (lt : LocalTypeR) (h : UnfoldsToEnd lt)
    (v : String) (repl : LocalTypeR) :
    lt.substitute v repl = lt := by
  -- No free variables means substitution is identity.
  have h_no_free := UnfoldsToEnd_no_free_vars lt h v
  exact substitute_not_free lt v repl h_no_free

/-! ## Core Lemma: mu preserves UnfoldsToEnd -/

/-- If X unfolds to .end, then .mu t X also unfolds to .end. -/
theorem mu_preserves_unfolds_to_end (t : String) (body : LocalTypeR)
    (h : UnfoldsToEnd body) : UnfoldsToEnd (.mu t body) := by
  -- Unfold once and reuse the body witness.
  apply UnfoldsToEnd.mu
  rw [substitute_UnfoldsToEnd_eq body h t (.mu t body)]
  exact h

/-! ## Main Theorem -/

/-- Unguarded substitution on `.end` is impossible (guarded by definition). -/
private theorem substitute_end_unguarded_unfolds_to_end_end (v : String)
    (hnotguard : LocalTypeR.end.isGuarded v = false) :
    UnfoldsToEnd (LocalTypeR.end.substitute v .end) := by
  -- isGuarded on `.end` is true, contradicting hnotguard.
  simp only [LocalTypeR.isGuarded] at hnotguard
  cases hnotguard

/-- Unguarded substitution on a variable yields `.end`. -/
private theorem substitute_end_unguarded_unfolds_to_end_var (w v : String)
    (hnotguard : (LocalTypeR.var w).isGuarded v = false) :
    UnfoldsToEnd ((LocalTypeR.var w).substitute v .end) := by
  -- isGuarded false forces w = v; substitution yields `.end`.
  simp only [LocalTypeR.isGuarded, bne_eq_false_iff_eq] at hnotguard
  simp only [LocalTypeR.substitute, hnotguard, beq_self_eq_true, ↓reduceIte]
  exact UnfoldsToEnd.base

/-- Unguarded substitution on `.send` cannot happen. -/
private theorem substitute_end_unguarded_unfolds_to_end_send
    (p : String) (bs : List (Label × LocalTypeR)) (v : String)
    (hnotguard : (LocalTypeR.send p bs).isGuarded v = false) :
    UnfoldsToEnd ((LocalTypeR.send p bs).substitute v .end) := by
  -- isGuarded on send is true, contradiction.
  simp only [LocalTypeR.isGuarded] at hnotguard
  cases hnotguard

/-- Unguarded substitution on `.recv` cannot happen. -/
private theorem substitute_end_unguarded_unfolds_to_end_recv
    (p : String) (bs : List (Label × LocalTypeR)) (v : String)
    (hnotguard : (LocalTypeR.recv p bs).isGuarded v = false) :
    UnfoldsToEnd ((LocalTypeR.recv p bs).substitute v .end) := by
  -- isGuarded on recv is true, contradiction.
  simp only [LocalTypeR.isGuarded] at hnotguard
  cases hnotguard

/-- Unguarded substitution on `.mu` unfolds through the body. -/
private theorem substitute_end_unguarded_unfolds_to_end_mu
    (t : String) (body : LocalTypeR) (v : String)
    (hbeq_tv : (t == v) = false)
    (ih_body : UnfoldsToEnd (body.substitute v .end)) :
    UnfoldsToEnd ((LocalTypeR.mu t body).substitute v .end) := by
  -- Use the non-shadowing equality to reduce substitution.
  simp only [LocalTypeR.substitute, hbeq_tv]
  exact mu_preserves_unfolds_to_end t (body.substitute v .end) ih_body

/-- When `v` is unguarded in `lt`, substituting `.end` for `v` produces a type
    that unfolds to `.end`. -/
theorem substitute_end_unguarded_unfolds_to_end (lt : LocalTypeR) (v : String)
    (hnotguard : lt.isGuarded v = false) :
    UnfoldsToEnd (lt.substitute v .end) := by
  -- Dispatch by constructor to keep each proof block small.
  cases lt with
  | «end» =>
      exact substitute_end_unguarded_unfolds_to_end_end v hnotguard
  | var w =>
      exact substitute_end_unguarded_unfolds_to_end_var w v hnotguard
  | send p bs =>
      exact substitute_end_unguarded_unfolds_to_end_send p bs v hnotguard
  | recv p bs =>
      exact substitute_end_unguarded_unfolds_to_end_recv p bs v hnotguard
  | mu t body =>
      simp only [LocalTypeR.isGuarded] at hnotguard
      split at hnotguard
      · contradiction
      · rename_i hvt
        simp only [Bool.not_eq_true] at hvt
        have hvt_ne : v ≠ t := beq_eq_false_iff_ne.mp hvt
        have hbeq_tv : (t == v) = false := beq_eq_false_iff_ne.mpr (Ne.symm hvt_ne)
        have ih_body : UnfoldsToEnd (body.substitute v .end) :=
          substitute_end_unguarded_unfolds_to_end body v hnotguard
        exact substitute_end_unguarded_unfolds_to_end_mu t body v hbeq_tv ih_body

/-- Substituting `.end` for an unguarded variable produces something EQ2 to `.end`.

    This is the main theorem that removes the extra assumption in Harmony.lean. -/
theorem subst_end_unguarded_eq2_end (lt : LocalTypeR) (v : String)
    (hnotguard : lt.isGuarded v = false) :
    EQ2 (lt.substitute v .end) .end := by
  -- Reduce to UnfoldsToEnd, then convert to EQ2.
  have h := substitute_end_unguarded_unfolds_to_end lt v hnotguard
  exact UnfoldsToEnd.toEQ2 h

end RumpsteakV2.Proofs.Projection.SubstEndUnguarded
