import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.Projection.Trans

/-! # Full Unfolding for LocalTypeR

This module implements the Coq-style approach to mu-unfolding using a termination
measure (height) and iterative unfolding. This provides an alternative to direct
coinductive proofs for substitution commutation.

## Strategy (from Coq `coLocal.v`)

1. Define `muHeight`: count nested mu constructors
2. Define `singleUnfold`: one step of mu-substitution
3. Define `fullUnfold`: iterate singleUnfold height-many times
4. Prove `fullUnfold_mu_subst`: fullUnfold (mu t body) = fullUnfold (body.substitute t (mu t body))
5. Connect to EQ2 via structural equality on fully unfolded terms

## Key Insight

After `muHeight` iterations of unfolding, a term either:
- Has no outer mu (leaf case), or
- Has a guarded mu where further unfolding is stable

This makes the unfolding operation well-defined and allows equational reasoning
without explicit coinduction.

## References

- Coq: `emu_height`, `eunf`, `full_eunf`, `full_eunf_subst` in `coLocal.v`
-/

namespace RumpsteakV2.Protocol.CoTypes.FullUnfold

open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.GlobalType (Label)
open RumpsteakV2.Protocol.CoTypes.EQ2

/-! ## Height Function

Count nested mu constructors. This serves as a termination measure for unfolding. -/

/-- Count the number of nested mu constructors at the top level.
    Corresponds to Coq's `emu_height`. -/
def muHeight : LocalTypeR → Nat
  | .mu _ body => 1 + muHeight body
  | _ => 0

@[simp] theorem muHeight_end : muHeight .end = 0 := rfl
@[simp] theorem muHeight_var (v : String) : muHeight (.var v) = 0 := rfl
@[simp] theorem muHeight_send (p : String) (bs : List (Label × LocalTypeR)) :
    muHeight (.send p bs) = 0 := rfl
@[simp] theorem muHeight_recv (p : String) (bs : List (Label × LocalTypeR)) :
    muHeight (.recv p bs) = 0 := rfl
@[simp] theorem muHeight_mu (t : String) (body : LocalTypeR) :
    muHeight (.mu t body) = 1 + muHeight body := rfl

/-! ## Single Unfold Step

One step of mu-substitution, corresponding to Coq's `eunf`. -/

/-- Single unfold step: substitute mu-body with the mu itself.
    Corresponds to Coq's `eunf`. -/
def singleUnfold : LocalTypeR → LocalTypeR
  | .mu t body => body.substitute t (.mu t body)
  | other => other

@[simp] theorem singleUnfold_end : singleUnfold .end = .end := rfl
@[simp] theorem singleUnfold_var (v : String) : singleUnfold (.var v) = .var v := rfl
@[simp] theorem singleUnfold_send (p : String) (bs : List (Label × LocalTypeR)) :
    singleUnfold (.send p bs) = .send p bs := rfl
@[simp] theorem singleUnfold_recv (p : String) (bs : List (Label × LocalTypeR)) :
    singleUnfold (.recv p bs) = .recv p bs := rfl
@[simp] theorem singleUnfold_mu (t : String) (body : LocalTypeR) :
    singleUnfold (.mu t body) = body.substitute t (.mu t body) := rfl

/-! ## Full Unfold

Iterate singleUnfold height-many times to fully unfold all outer mus.
Corresponds to Coq's `full_eunf`. -/

/-- Iterate a function n times. -/
def iterate (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterate f n (f x)

@[simp] theorem iterate_zero (f : α → α) (x : α) : iterate f 0 x = x := rfl
@[simp] theorem iterate_succ (f : α → α) (n : Nat) (x : α) :
    iterate f (n + 1) x = iterate f n (f x) := rfl

/-- Alternative iteration: apply f first, then iterate.
    `iterateR f n x = f (f (... (f x)))` with n applications. -/
def iterateR (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iterateR f n x)

@[simp] theorem iterateR_zero (f : α → α) (x : α) : iterateR f 0 x = x := rfl
@[simp] theorem iterateR_succ (f : α → α) (n : Nat) (x : α) :
    iterateR f (n + 1) x = f (iterateR f n x) := rfl

/-- iterate and iterateR are related by shifting. -/
theorem iterate_iterateR (f : α → α) (n : Nat) (x : α) :
    iterate f n (f x) = f (iterate f n x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => simp [ih]

/-- Full unfold: iterate singleUnfold muHeight-many times.
    Corresponds to Coq's `full_eunf`. -/
def fullUnfold (t : LocalTypeR) : LocalTypeR :=
  iterate singleUnfold (muHeight t) t

@[simp] theorem fullUnfold_end : fullUnfold .end = .end := rfl
@[simp] theorem fullUnfold_var (v : String) : fullUnfold (.var v) = .var v := rfl
@[simp] theorem fullUnfold_send (p : String) (bs : List (Label × LocalTypeR)) :
    fullUnfold (.send p bs) = .send p bs := rfl
@[simp] theorem fullUnfold_recv (p : String) (bs : List (Label × LocalTypeR)) :
    fullUnfold (.recv p bs) = .recv p bs := rfl

/-! ## Key Lemmas

These lemmas establish the properties needed for the substitution commutation proof. -/

/-- After unfolding, the result is not a mu (or is stable under further unfolding). -/
def isUnfolded : LocalTypeR → Bool
  | .mu _ _ => false
  | _ => true

/-- Height decreases by 1 after single unfold of a mu with guarded body.
    This is the key property for termination. -/
theorem muHeight_singleUnfold_guarded (t : String) (body : LocalTypeR)
    (hguard : body.isGuarded t = true) :
    muHeight (singleUnfold (.mu t body)) = muHeight body := by
  simp only [singleUnfold_mu]
  -- When body is guarded for t, substituting doesn't add new outer mus
  -- The result has the same height as body
  sorry

/-- Height of substituted term when variable is guarded. -/
theorem muHeight_substitute_guarded (body : LocalTypeR) (t : String) (replacement : LocalTypeR)
    (hguard : body.isGuarded t = true) :
    muHeight (body.substitute t replacement) = muHeight body := by
  -- Guarded means no free occurrences of t at top level
  -- So substitution doesn't change the mu structure
  sorry

/-- Height after single unfold of unguarded mu. -/
theorem muHeight_singleUnfold_unguarded (t : String) (body : LocalTypeR)
    (hnotguard : body.isGuarded t = false) :
    muHeight (singleUnfold (.mu t body)) = muHeight body + muHeight (.mu t body) := by
  simp only [singleUnfold_mu]
  -- When body is unguarded, it contains .var t which gets replaced by .mu t body
  sorry

/-! ## Guardedness and Unfolding -/

/-- If body is guarded for t, then unfolding preserves guardedness. -/
theorem isGuarded_singleUnfold (body : LocalTypeR) (t : String) (v : String)
    (hguard : body.isGuarded v = true) :
    (singleUnfold body).isGuarded v = true := by
  cases body with
  | mu s inner =>
      simp only [singleUnfold_mu]
      -- Need to show (inner.substitute s (.mu s inner)).isGuarded v = true
      sorry
  | _ => simp [singleUnfold, hguard]

/-- Guardedness is preserved through substitution when the replacement is guarded. -/
theorem isGuarded_substitute (body : LocalTypeR) (t : String) (replacement : LocalTypeR)
    (v : String) (hbody : body.isGuarded v = true) (hrep : replacement.isGuarded v = true) :
    (body.substitute t replacement).isGuarded v = true := by
  sorry

/-! ## The Key Theorem: Unfolding Commutes with Substitution

This is the Lean equivalent of Coq's `full_eunf_subst`. -/

/-- Single unfold of iterated unfold equals iterated unfold of single unfold.
    Corresponds to Coq's `-iterS iterSr` rewrite pattern. -/
theorem iterate_singleUnfold_comm (n : Nat) (t : LocalTypeR) :
    iterate singleUnfold n (singleUnfold t) = singleUnfold (iterate singleUnfold n t) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
      simp only [iterate_succ]
      rw [ih]

/-- Full unfold of a mu equals full unfold of its unfolded body.
    This is the key lemma corresponding to Coq's `full_eunf_subst`.

    The proof follows Coq's structure:
    1. Case split on guardedness of body for t
    2. Guarded case: heights match, unfold in lockstep
    3. Unguarded case: both reach the same unguarded variable -/
theorem fullUnfold_mu_subst (t : String) (body : LocalTypeR) :
    fullUnfold (.mu t body) = fullUnfold (body.substitute t (.mu t body)) := by
  simp only [fullUnfold, muHeight_mu]
  -- fullUnfold (.mu t body) = iterate singleUnfold (1 + muHeight body) (.mu t body)
  -- Rewrite 1 + n to n + 1 so we can use iterate_succ
  conv_lhs => rw [Nat.add_comm]
  -- Now: iterate singleUnfold (muHeight body + 1) (.mu t body)
  --    = iterate singleUnfold (muHeight body) (singleUnfold (.mu t body))
  simp only [iterate_succ, singleUnfold_mu]
  -- Now need: iterate singleUnfold (muHeight body) (body.substitute t (.mu t body))
  --         = iterate singleUnfold (muHeight (body.substitute t (.mu t body))) (body.substitute t (.mu t body))
  -- i.e., muHeight body = muHeight (body.substitute t (.mu t body))
  by_cases hguard : body.isGuarded t
  · -- Guarded case: heights match
    have hheq : muHeight (body.substitute t (.mu t body)) = muHeight body :=
      muHeight_substitute_guarded body t (.mu t body) hguard
    rw [hheq]
  · -- Unguarded case: need different reasoning
    simp only [Bool.not_eq_true] at hguard
    -- When body is unguarded for t, it contains .var t at top level
    -- Substitution replaces this with (.mu t body), potentially increasing height
    -- But after sufficient unfolding, both reach the same normal form
    sorry

/-! ## Connection to EQ2

Link the computational equality via fullUnfold to the coinductive EQ2. -/

/-- If two terms have the same full unfold, they are EQ2-equivalent.

    This bridges the computational approach (equality via normalization)
    to the coinductive approach (EQ2 relation). -/
theorem EQ2_of_fullUnfold_eq (a b : LocalTypeR)
    (h : fullUnfold a = fullUnfold b) : EQ2 a b := by
  -- The proof uses coinduction: fullUnfold produces the same "observable behavior"
  -- EQ2 captures extensional equality of the infinite trees
  sorry

/-- EQ2 implies equality of full unfolds for well-formed types.

    Note: This may require well-formedness (no infinite mu-chains). -/
theorem fullUnfold_eq_of_EQ2 (a b : LocalTypeR)
    (heq : EQ2 a b) : fullUnfold a = fullUnfold b := by
  -- EQ2 means same observable behavior, so same normal form
  sorry

/-- EQ2 is equivalent to equality of full unfolds (for well-formed types). -/
theorem EQ2_iff_fullUnfold_eq (a b : LocalTypeR) :
    EQ2 a b ↔ fullUnfold a = fullUnfold b := by
  constructor
  · exact fullUnfold_eq_of_EQ2 a b
  · exact EQ2_of_fullUnfold_eq a b

/-! ## Application: Substitution Commutation for Projection

The main application: proving that projection commutes with substitution
using the fullUnfold infrastructure.

Note: The actual projection function `trans : GlobalType → String → LocalTypeR`
is defined in `RumpsteakV2.Protocol.Projection.Trans`. The key theorem to prove
would be that fullUnfold commutes with projection in the appropriate sense. -/

end RumpsteakV2.Protocol.CoTypes.FullUnfold
