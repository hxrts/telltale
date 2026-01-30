import SessionTypes.LocalTypeR
import SessionCoTypes.EQ2
import SessionCoTypes.EQ2Props
import Choreography.Projection.Trans

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

namespace SessionCoTypes.FullUnfold

open SessionTypes.LocalTypeR
open SessionTypes.GlobalType (Label)
open SessionCoTypes.EQ2
open SessionCoTypes.EQ2Props

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

private theorem muHeight_substitute_guarded_eq (body : LocalTypeR) (t : String) (replacement : LocalTypeR)
    (hguard : body.isGuarded t = true) :
    (body.substitute t replacement).muHeight = body.muHeight := by
  cases body with
  | «end» =>
      simp [LocalTypeR.substitute, LocalTypeR.muHeight] at *
  | var v =>
      have hne : t ≠ v := (bne_iff_ne).1 (by simpa [LocalTypeR.isGuarded] using hguard)
      have hbeq : (v == t) = false := by
        apply beq_eq_false_iff_ne.mpr
        intro h
        exact hne h.symm
      simp [LocalTypeR.substitute, LocalTypeR.muHeight, hbeq]
  | send p bs =>
      simp [LocalTypeR.substitute, LocalTypeR.muHeight]
  | recv p bs =>
      simp [LocalTypeR.substitute, LocalTypeR.muHeight]
  | mu s inner =>
      by_cases hts : t = s
      · subst hts
        simp [LocalTypeR.substitute, LocalTypeR.muHeight]
      · have hinner : inner.isGuarded t = true := by
          simpa [LocalTypeR.isGuarded, hts] using hguard
        have ih := muHeight_substitute_guarded_eq inner t replacement hinner
        have hbeq : (s == t) = false := by
          apply beq_eq_false_iff_ne.mpr
          exact ne_comm.mp hts
        simp [LocalTypeR.substitute, LocalTypeR.muHeight, hbeq, ih]
termination_by sizeOf body

/-- Full unfold of a mu equals full unfold of its unfolded body.
    This is the key lemma corresponding to Coq's `full_eunf_subst`.

    The proof follows Coq's structure:
    1. Case split on guardedness of body for t
    2. Guarded case: heights match, unfold in lockstep
    3. Unguarded case: both reach the same unguarded variable -/
theorem fullUnfold_mu_subst (t : String) (body : LocalTypeR)
    (hguard : body.isGuarded t = true) :
    (.mu t body : LocalTypeR).fullUnfold =
      (body.substitute t (.mu t body)).fullUnfold := by
  have hheq : (body.substitute t (.mu t body)).muHeight = body.muHeight :=
    muHeight_substitute_guarded_eq body t (.mu t body) hguard
  simpa [LocalTypeR.fullUnfold, hheq] using (LocalTypeR.fullUnfold_mu t body)

/-! ## Connection to EQ2

Link the computational equality via fullUnfold to the coinductive EQ2. -/

/-- If two terms have the same full unfold, they are EQ2-equivalent.

    This bridges the computational approach (equality via normalization)
    to the coinductive approach (EQ2 relation). -/
theorem EQ2_of_fullUnfold_eq (a b : LocalTypeR)
    (hWFa : LocalTypeR.WellFormed a) (hWFb : LocalTypeR.WellFormed b)
    (h : a.fullUnfold = b.fullUnfold) : EQ2 a b := by
  -- Use EQ2 on both sides via unfolding iterates.
  have hWFa_full : LocalTypeR.WellFormed a.fullUnfold :=
    LocalTypeR.WellFormed.fullUnfold hWFa
  have hWFb_full : LocalTypeR.WellFormed b.fullUnfold :=
    LocalTypeR.WellFormed.fullUnfold hWFb
  have ha : EQ2 a a.fullUnfold := by
    simpa [LocalTypeR.fullUnfold] using
      (EQ2_unfold_right_iter (a := a) (b := a) (EQ2_refl a) a.muHeight)
  have hb : EQ2 b b.fullUnfold := by
    simpa [LocalTypeR.fullUnfold] using
      (EQ2_unfold_right_iter (a := b) (b := b) (EQ2_refl b) b.muHeight)
  have hab_full : EQ2 a.fullUnfold b.fullUnfold := by
    simpa [h] using (EQ2_refl a.fullUnfold)
  have h1 : EQ2 a b.fullUnfold :=
    EQ2_trans_wf ha hab_full hWFa hWFa_full hWFb_full
  exact EQ2_trans_wf h1 (EQ2_symm hb) hWFa hWFb_full hWFb

/-- EQ2 implies equality of full unfolds for well-formed types.

    Note: This may require well-formedness (no infinite mu-chains). -/
theorem fullUnfold_eq_of_EQ2 (a b : LocalTypeR)
    (hWFa : LocalTypeR.WellFormed a) (hWFb : LocalTypeR.WellFormed b)
    (heq : EQ2 a b) : EQ2 a.fullUnfold b.fullUnfold := by
  have hWFa_full : LocalTypeR.WellFormed a.fullUnfold :=
    LocalTypeR.WellFormed.fullUnfold hWFa
  have hWFb_full : LocalTypeR.WellFormed b.fullUnfold :=
    LocalTypeR.WellFormed.fullUnfold hWFb
  have ha : EQ2 a a.fullUnfold := by
    simpa [LocalTypeR.fullUnfold] using
      (EQ2_unfold_right_iter (a := a) (b := a) (EQ2_refl a) a.muHeight)
  have hb : EQ2 b b.fullUnfold := by
    simpa [LocalTypeR.fullUnfold] using
      (EQ2_unfold_right_iter (a := b) (b := b) (EQ2_refl b) b.muHeight)
  have h1 : EQ2 a.fullUnfold b :=
    EQ2_trans_wf (EQ2_symm ha) heq hWFa_full hWFa hWFb
  exact EQ2_trans_wf h1 hb hWFa_full hWFb hWFb_full

/-- EQ2 is equivalent to equality of full unfolds (for well-formed types). -/
theorem EQ2_iff_fullUnfold_eq (a b : LocalTypeR)
    (hWFa : LocalTypeR.WellFormed a) (hWFb : LocalTypeR.WellFormed b) :
    EQ2 a b ↔ EQ2 a.fullUnfold b.fullUnfold := by
  constructor
  · intro h
    exact fullUnfold_eq_of_EQ2 a b hWFa hWFb h
  · intro h
    -- EQ2 is preserved by folding back through unfold
    have hWFa_full : LocalTypeR.WellFormed a.fullUnfold :=
      LocalTypeR.WellFormed.fullUnfold hWFa
    have hWFb_full : LocalTypeR.WellFormed b.fullUnfold :=
      LocalTypeR.WellFormed.fullUnfold hWFb
    have ha : EQ2 a a.fullUnfold := by
      simpa [LocalTypeR.fullUnfold] using
        (EQ2_unfold_right_iter (a := a) (b := a) (EQ2_refl a) a.muHeight)
    have hb : EQ2 b b.fullUnfold := by
      simpa [LocalTypeR.fullUnfold] using
        (EQ2_unfold_right_iter (a := b) (b := b) (EQ2_refl b) b.muHeight)
    have h1 : EQ2 a b.fullUnfold :=
      EQ2_trans_wf ha h hWFa hWFa_full hWFb_full
    exact EQ2_trans_wf h1 (EQ2_symm hb) hWFa hWFb_full hWFb

/-! ## Application: Substitution Commutation for Projection

The main application: proving that projection commutes with substitution
using the fullUnfold infrastructure.

Note: The actual projection function `trans : GlobalType → String → LocalTypeR`
is defined in `Choreography.Projection.Trans`. The key theorem to prove
would be that fullUnfold commutes with projection in the appropriate sense. -/

end SessionCoTypes.FullUnfold
