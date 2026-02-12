import Mathlib.Data.List.Forall2
import Mathlib.Order.FixedPoints
import SessionTypes.GlobalType
import SessionTypes.LocalTypeR
import SessionCoTypes.CoinductiveRel

set_option linter.dupNamespace false
set_option linter.unusedTactic false

/-! # SessionCoTypes.EQ2

Coinductive equality (EQ2) for local types.

## Expose

The following definitions form the semantic interface for proofs:

- `EQ2`: coinductive equality (greatest fixed point of EQ2F)
- `EQ2_refl`: reflexivity of EQ2
- `EQ2_symm`: symmetry of EQ2
- `EQ2_trans_wf`: transitivity of EQ2 (via Bisim, in EQ2Props.lean)
- `EQ2_equiv`: equivalence relation instance
- `EQ2_trans_via_end` / `EQ2_trans_via_var`: constructor-based transitivity helpers
- `EQ2_unfold_left`: left unfolding preserves EQ2
- `EQ2_unfold_right`: right unfolding preserves EQ2
- `EQ2_unfold`: bilateral unfolding preserves EQ2
- `EQ2_coind`: coinduction principle
-/

/-
The Problem. Recursive session types need an equality that identifies types
differing only in their recursion structure (equi-recursive equality). The
standard equality is too strict; we need the greatest fixed point of a
one-step equality functor.

Solution Structure. Defines `EQ2F` as the one-step generator matching constructors
and requiring relation R on continuations. `EQ2` is the greatest fixed point.
Proves reflexivity by structural induction, symmetry by swapping, and provides
unfolding lemmas (EQ2_unfold_left/right) allowing mu-unwrapping.
-/

namespace SessionCoTypes.EQ2

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionCoTypes.CoinductiveRel

/-- Relation on local types. -/
abbrev Rel := LocalTypeR → LocalTypeR → Prop

/-- Branch-wise relation used by EQ2. -/
def BranchesRel (R : Rel) (bs cs : List BranchR) : Prop :=
  List.Forall₂ (fun a b => a.1 = b.1 ∧ R a.2.2 b.2.2) bs cs

private theorem BranchesRel_mono {R S : Rel}
    (h : ∀ a b, R a b → S a b) :
    ∀ {bs cs}, BranchesRel R bs cs → BranchesRel S bs cs := by
  intro bs cs hrel
  exact List.Forall₂.imp (fun a b hab => ⟨hab.1, h _ _ hab.2⟩) hrel

/-- One-step generator for EQ2. -/
def EQ2F (R : Rel) : Rel
  | .end, .end => True
  | .var x, .var y => x = y
  | .send p bs, .send q cs => p = q ∧ BranchesRel R bs cs
  | .recv p bs, .recv q cs => p = q ∧ BranchesRel R bs cs
  | .mu t body, .mu s body' =>
      R (body.substitute t (.mu t body)) (.mu s body') ∧
        R (.mu t body) (body'.substitute s (.mu s body'))
  | .mu t body, b => R (body.substitute t (.mu t body)) b
  | a, .mu t body => R a (body.substitute t (.mu t body))
  | _, _ => False

private theorem EQ2F_mono : Monotone EQ2F := by
  intro R S h a b hrel
  cases a <;> cases b <;> simp [EQ2F] at hrel ⊢
  all_goals
    first
    | exact hrel
    | exact h _ _ hrel
    | cases hrel with
      | intro h1 h2 =>
        first
        | exact ⟨h _ _ h1, h _ _ h2⟩
        | exact ⟨h1, BranchesRel_mono (fun _ _ hr => h _ _ hr) h2⟩
instance : CoinductiveRel Rel EQ2F := ⟨EQ2F_mono⟩


/-- EQ2 as the greatest fixed point of EQ2F. -/
def EQ2 : Rel :=
  (OrderHom.gfp ⟨EQ2F, EQ2F_mono⟩)

/- Shared coinduction aliases (see `CoinductiveRel`). -/
/-- Alias: EQ2 as gfp via CoinductiveRel. -/
theorem EQ2_gfp : EQ2 = SessionCoTypes.CoinductiveRel.gfp (F := EQ2F) := rfl

/-- Alias: coinduction via CoinductiveRel. -/
theorem EQ2_coind' {R : Rel} (h : R ≤ EQ2F R) : R ≤ EQ2 := by
  simpa [EQ2] using (SessionCoTypes.CoinductiveRel.coind (F := EQ2F) h)

/-- Alias: unfold via CoinductiveRel. -/
theorem EQ2_unfold' : EQ2 ≤ EQ2F EQ2 := by
  change (OrderHom.gfp ⟨EQ2F, EQ2F_mono⟩) ≤ EQ2F (OrderHom.gfp ⟨EQ2F, EQ2F_mono⟩)
  exact SessionCoTypes.CoinductiveRel.unfold (F := EQ2F)

/-- Alias: fold via CoinductiveRel. -/
theorem EQ2_fold' : EQ2F EQ2 ≤ EQ2 := by
  change EQ2F (OrderHom.gfp ⟨EQ2F, EQ2F_mono⟩) ≤ (OrderHom.gfp ⟨EQ2F, EQ2F_mono⟩)
  exact SessionCoTypes.CoinductiveRel.fold (F := EQ2F)

theorem EQ2_fixed : EQ2F EQ2 = EQ2 := by
  change EQ2F (OrderHom.gfp ⟨EQ2F, EQ2F_mono⟩) = (OrderHom.gfp ⟨EQ2F, EQ2F_mono⟩)
  exact SessionCoTypes.CoinductiveRel.gfp_fixed (F := EQ2F)

theorem EQ2_destruct {a b : LocalTypeR} (h : EQ2 a b) : EQ2F EQ2 a b := by
  have hfix : EQ2F EQ2 = EQ2 := EQ2_fixed
  exact (Eq.mp (congrArg (fun R => R a b) hfix.symm) h)

/-- Unfold EQ2 on the left. -/
theorem EQ2_unfold_left {a b : LocalTypeR} (h : EQ2 a b) :
    EQ2 (LocalTypeR.unfold a) b := by
  cases a with
  | mu t body =>
      have h' : EQ2F EQ2 (.mu t body) b := EQ2_destruct h
      cases b with
      | mu s body' =>
          have hleft : EQ2 (body.substitute t (.mu t body)) (.mu s body') := by
            simpa [EQ2F] using h'.1
          simpa [LocalTypeR.unfold] using hleft
      | _ =>
          simpa [EQ2F, LocalTypeR.unfold] using h'
  | _ =>
      simpa [LocalTypeR.unfold] using h

/-- Unfold EQ2 on the right. -/
theorem EQ2_unfold_right {a b : LocalTypeR} (h : EQ2 a b) :
    EQ2 a (LocalTypeR.unfold b) := by
  cases b with
  | mu t body =>
      have h' : EQ2F EQ2 a (.mu t body) := EQ2_destruct h
      cases a with
      | mu s body' =>
          have hright : EQ2 (.mu s body') (body.substitute t (.mu t body)) := by
            simpa [EQ2F] using h'.2
          simpa [LocalTypeR.unfold] using hright
      | _ =>
          simpa [EQ2F, LocalTypeR.unfold] using h'
  | _ =>
      simpa [LocalTypeR.unfold] using h

/-- Unfold EQ2 on the right for n steps. -/
theorem EQ2_unfold_right_iter {a : LocalTypeR} :
    ∀ {b : LocalTypeR}, EQ2 a b → ∀ n, EQ2 a ((LocalTypeR.unfold)^[n] b) := by
  intro b h n
  induction n generalizing b with
  | zero =>
      simpa [Function.iterate_zero, id_eq] using h
  | succ n ih =>
      have h' : EQ2 a (LocalTypeR.unfold b) := EQ2_unfold_right h
      have hstep : EQ2 a ((LocalTypeR.unfold)^[n] (LocalTypeR.unfold b)) := ih h'
      simpa [Function.iterate_succ_apply] using hstep

/-- Unfold EQ2 on both sides. -/
theorem EQ2_unfold {a b : LocalTypeR} (h : EQ2 a b) :
    EQ2 (LocalTypeR.unfold a) (LocalTypeR.unfold b) := by
  exact EQ2_unfold_right (EQ2_unfold_left h)

/-! ## Coinduction Principle -/

/-- Coinduction principle for EQ2: if R is a post-fixpoint of EQ2F, then R ⊆ EQ2. -/
theorem EQ2_coind {R : Rel} (h : ∀ a b, R a b → EQ2F R a b) :
    ∀ a b, R a b → EQ2 a b := by
  intro a b hr
  have hle : R ≤ EQ2F R := fun x y hxy => h x y hxy
  exact (EQ2_coind' hle) a b hr

/-! ## Coinduction Up-To

This section provides "coinduction up-to" infrastructure, allowing coinductive proofs
to "borrow" from the EQ2 relation during intermediate steps. This is essential for
proving congruence lemmas like EQ2_substitute and EQ2_dual.

The key insight is that if a relation R is a post-fixpoint of EQ2F when extended
by EQ2, then R is still contained in EQ2. -/

/-- Destruct EQ2 to get EQ2F EQ2 (public version for coinduction up-to proofs). -/
theorem EQ2.destruct {a b : LocalTypeR} (h : EQ2 a b) : EQ2F EQ2 a b :=
  EQ2_destruct h

/-- Construct EQ2 from EQ2F EQ2 (inverse of destruct). -/
theorem EQ2.construct {a b : LocalTypeR} (h : EQ2F EQ2 a b) : EQ2 a b := by
  have hfix : EQ2F EQ2 = EQ2 := EQ2_fixed
  exact Eq.mp (congrArg (fun R => R a b) hfix) h

/-- EQ2F is monotone (public version for coinduction up-to proofs). -/
theorem EQ2F.mono : Monotone EQ2F := EQ2F_mono

/-- EQ2 closure of a relation: pairs in R or pairs in EQ2. -/
def EQ2_closure (R : Rel) : Rel := fun a b => R a b ∨ EQ2 a b

/-- EQ2 closure is monotone. -/
theorem EQ2_closure_mono : Monotone EQ2_closure := by
  intro R S hrs a b h
  cases h with
  | inl hr => exact Or.inl (hrs a b hr)
  | inr heq => exact Or.inr heq

/-- Enhanced coinduction principle: if R is a post-fixpoint of EQ2F up to EQ2 closure,
    then R ⊆ EQ2.

    This allows the step case to appeal to either R or the already-established EQ2.
    Formally: if ∀ a b, R a b → EQ2F (R ∨ EQ2) a b, then R ⊆ EQ2. -/
theorem EQ2_coind_upto {R : Rel} (h : ∀ a b, R a b → EQ2F (EQ2_closure R) a b) :
    ∀ a b, R a b → EQ2 a b := by
  intro a b hr
  -- Define the accumulated relation: R ∪ EQ2
  let S := EQ2_closure R
  -- Show S is a post-fixpoint of EQ2F
  have hS_postfix : ∀ x y, S x y → EQ2F S x y := by
    intro x y hxy
    cases hxy with
    | inl hxr =>
        -- x y in R, so EQ2F (EQ2_closure R) x y by h
        exact h x y hxr
    | inr hxeq =>
        -- x y in EQ2, so EQ2F EQ2 x y by fixed point
        have hf : EQ2F EQ2 x y := EQ2_destruct hxeq
        -- Lift EQ2F EQ2 to EQ2F S using monotonicity
        exact EQ2F_mono (fun a b h => Or.inr h) x y hf
  -- Apply standard coinduction with S
  have hinS : S a b := Or.inl hr
  exact EQ2_coind hS_postfix a b hinS


end SessionCoTypes.EQ2
