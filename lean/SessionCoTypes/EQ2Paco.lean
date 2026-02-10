import Paco
import SessionCoTypes.EQ2
import SessionCoTypes.CoinductiveRelPaco
import SessionCoTypes.Bisim

/-! # EQ2 Integration with Paco

This module connects the EQ2 coinductive equality with paco-lean's parametrized
coinduction framework. This enables:

1. Transitivity proofs via accumulation
2. Up-to techniques with compatible closures
3. Compositional coinductive proofs

## Main Results

- `EQ2FMono`: EQ2F as a Paco.MonoRel
- `EQ2_eq_paco_bot`: EQ2 equals paco EQ2FMono ⊥
- `EQ2_paco_coind`: Parametrized coinduction for EQ2
- `EQ2_paco_coind_acc`: Coinduction with accumulated hypotheses

## Usage

```lean
-- Prove EQ2 a b using paco with witness relation R and accumulator r
theorem my_eq2_proof : EQ2 a b := by
  rw [EQ2_eq_paco_bot]
  apply Paco.paco_coind EQ2FMono MyWitness ⊥
  · intro x y hxy
    -- Show MyWitness is a post-fixpoint of EQ2F
    ...
  · exact ...
```
-/

/-
The Problem. Standard coinduction for EQ2 is limited: we can't accumulate
hypotheses or use up-to techniques. Paco (parametrized coinduction) provides
these features but requires connecting EQ2 to its framework.

Solution Structure. Wraps EQ2F as `EQ2FMono : Paco.MonoRel`. Proves `EQ2_eq_paco_bot`
showing EQ2 equals the paco greatest fixed point. Provides `EQ2_paco_coind` for
parametrized coinduction and `EQ2_paco_coind_acc` for coinduction with accumulated
hypotheses. Enables transitivity via accumulation and compatible closures.
-/

namespace SessionCoTypes.EQ2Paco

open SessionCoTypes.EQ2
open SessionCoTypes.Bisim
open SessionTypes.LocalTypeR
open Paco

/-! ## EQ2F as a Paco MonoRel -/

/-- Convert our Rel to Paco.Rel (they're the same type but in different namespaces). -/
def toPacoRel (R : EQ2.Rel) : Paco.Rel LocalTypeR := R

/-- Convert Paco.Rel back to our Rel. -/
def fromPacoRel (R : Paco.Rel LocalTypeR) : EQ2.Rel := R

/-- EQ2F lifted to operate on Paco.Rel. -/
def EQ2F_paco (R : Paco.Rel LocalTypeR) : Paco.Rel LocalTypeR :=
  EQ2F (fromPacoRel R)

/-- Local copy of BranchesRel_mono (since the original is private). -/
private theorem BranchesRel_mono' {R S : EQ2.Rel}
    (h : ∀ a b, R a b → S a b) :
    ∀ {bs cs}, BranchesRel R bs cs → BranchesRel S bs cs := by
  intro bs cs hrel
  exact List.Forall₂.imp (fun a b hab => ⟨hab.1, h _ _ hab.2⟩) hrel

/-- Monotonicity of EQ2F in the Paco framework. -/
theorem EQ2F_paco_mono : Paco.Monotone2 EQ2F_paco := by
  intro R S hRS x y hxy
  simp only [EQ2F_paco, fromPacoRel] at *
  cases x <;> cases y <;> simp only [EQ2F] at hxy ⊢
  all_goals
    first
    | exact hxy
    | exact hRS _ _ hxy
    | obtain ⟨h1, h2⟩ := hxy
      first
      | exact ⟨hRS _ _ h1, hRS _ _ h2⟩
      | refine ⟨h1, ?_⟩
        exact BranchesRel_mono' (fun _ _ hr => hRS _ _ hr) h2

/-- EQ2F as a bundled monotone relation transformer for paco. -/
def EQ2FMono : Paco.MonoRel LocalTypeR where
  F := EQ2F_paco
  mono := EQ2F_paco_mono

/-! ## Equivalence between EQ2 and paco EQ2FMono ⊥ -/

/-- EQ2 implies paco EQ2FMono ⊥. -/
theorem EQ2_le_paco_bot : EQ2 ≤ paco EQ2FMono ⊥ := by
  intro x y h
  -- We use EQ2 itself as the witness relation
  refine ⟨toPacoRel EQ2, ?_, h⟩
  intro a b hab
  -- hab : EQ2 a b
  -- Need: EQ2FMono.F (EQ2 ⊔ ⊥) a b = EQ2F_paco EQ2 a b = EQ2F EQ2 a b
  simp only [Paco.Rel.sup_bot]
  -- EQ2FMono.F = EQ2F_paco = fun R => EQ2F (fromPacoRel R)
  show EQ2F (fromPacoRel (toPacoRel EQ2)) a b
  simp only [fromPacoRel, toPacoRel]
  exact EQ2.destruct hab

/-- paco EQ2FMono ⊥ implies EQ2. -/
theorem paco_bot_le_EQ2 : paco EQ2FMono ⊥ ≤ EQ2 := by
  intro x y ⟨R, hR, hxy⟩
  -- R is a post-fixpoint: R ⊆ EQ2F_paco (R ⊔ ⊥) = EQ2F_paco R = EQ2F R
  -- By standard coinduction, R ⊆ EQ2
  have hpost : ∀ a b, R a b → EQ2F R a b := by
    intro a b hab
    simp only [Paco.Rel.sup_bot] at hR
    have h := hR a b hab
    -- h : EQ2FMono.F R a b = EQ2F_paco R a b = EQ2F R a b
    exact h
  exact EQ2_coind hpost x y hxy

/-- EQ2 equals paco EQ2FMono ⊥. -/
theorem EQ2_eq_paco_bot : EQ2 = paco EQ2FMono ⊥ :=
  Paco.Rel.le_antisymm EQ2_le_paco_bot paco_bot_le_EQ2

/-! ## Parametrized Coinduction for EQ2

These lemmas provide paco-style coinduction principles specialized for EQ2.
-/

/-- Parametrized coinduction for EQ2.

To prove EQ2 a b, provide a witness relation R and show:
1. R is a post-fixpoint of EQ2F when extended by r
2. R a b holds

The parameter r can accumulate hypotheses during the proof. -/
theorem EQ2_paco_coind (R : EQ2.Rel) (r : EQ2.Rel)
    (hpost : ∀ a b, R a b → EQ2F (fun x y => R x y ∨ r x y) a b)
    {x y : LocalTypeR} (hxy : R x y) :
    paco EQ2FMono (toPacoRel r) x y := by
  apply SessionCoTypes.CoinductiveRelPaco.coind_upto_pointwise EQ2FMono (toPacoRel R) (toPacoRel r)
  · intro a b hab
    -- hab : toPacoRel R a b = R a b
    -- Need: EQ2FMono.F (toPacoRel R ⊔ toPacoRel r) a b
    -- EQ2FMono.F = EQ2F_paco = fun R => EQ2F (fromPacoRel R)
    -- So need: EQ2F (fromPacoRel (toPacoRel R ⊔ toPacoRel r)) a b
    --        = EQ2F (R ⊔ r) a b
    --        = EQ2F (fun x y => R x y ∨ r x y) a b
    exact hpost a b hab
  · exact hxy

/-- Convert paco result back to EQ2 when parameter is empty. -/
theorem paco_to_EQ2 {x y : LocalTypeR} (h : paco EQ2FMono ⊥ x y) : EQ2 x y :=
  paco_bot_le_EQ2 x y h

/-- Coinduction with accumulation: use previously proven facts. -/
theorem EQ2_paco_coind_acc (R : EQ2.Rel) (r : EQ2.Rel)
    (hpost : ∀ a b, R a b → EQ2F (fun x y => R x y ∨ (paco EQ2FMono (toPacoRel r) x y ∨ r x y)) a b)
    {x y : LocalTypeR} (hxy : R x y) :
    paco EQ2FMono (toPacoRel r) x y := by
  apply SessionCoTypes.CoinductiveRelPaco.coind_upto_acc EQ2FMono (toPacoRel R) (toPacoRel r)
  · intro a b hab
    -- hab : toPacoRel R a b = R a b
    -- Need: EQ2FMono.F (toPacoRel R ⊔ upaco EQ2FMono (toPacoRel r)) a b
    -- upaco EQ2FMono (toPacoRel r) = paco EQ2FMono (toPacoRel r) ⊔ toPacoRel r
    -- So the target relation is R ⊔ paco ⊔ r, which matches hpost
    exact hpost a b hab
  · exact hxy

/-- Parametrized coinduction for EQ2 using gpaco (guarded accumulator). -/
theorem EQ2_gpaco_coind (R r g : EQ2.Rel)
    (hpost : ∀ a b, R a b →
      EQ2F (fun x y => R x y ∨ gupaco EQ2FMono (toPacoRel r) (toPacoRel g) x y) a b ∨ r a b)
    {x y : LocalTypeR} (hxy : R x y) :
    gpaco EQ2FMono (toPacoRel r) (toPacoRel g) x y := by
  apply SessionCoTypes.CoinductiveRelPaco.gcoind_upto_pointwise
    EQ2FMono (toPacoRel R) (toPacoRel r) (toPacoRel g)
  · intro a b hab
    -- hab : R a b
    exact hpost a b hab
  · exact hxy

/-- gpaco without base case (R must always make one-step progress). -/
theorem EQ2_gpaco_coind' (R r g : EQ2.Rel)
    (hpost : ∀ a b, R a b →
      EQ2F (fun x y => R x y ∨ gupaco EQ2FMono (toPacoRel r) (toPacoRel g) x y) a b) :
    R ≤ gpaco EQ2FMono (toPacoRel r) (toPacoRel g) := by
  intro x y hxy
  apply SessionCoTypes.CoinductiveRelPaco.gcoind_upto
    EQ2FMono (toPacoRel R) (toPacoRel r) (toPacoRel g)
  · intro a b hab
    exact hpost a b hab
  · exact hxy

/-! ## Transitivity via Paco

The main application: proving transitivity of EQ2 using accumulation.
-/

/-- The relation for transitivity proofs: pairs connected by LocalTypeR.WellFormed intermediate. -/
def TransRelPacoWF : EQ2.Rel := fun a c =>
  ∃ b, EQ2 a b ∧ EQ2 b c ∧
  LocalTypeR.WellFormed a ∧ LocalTypeR.WellFormed b ∧ LocalTypeR.WellFormed c

/-- TransRelPacoWF with LocalTypeR.WellFormed hypotheses can use EQ2_trans_via_Bisim. -/
theorem TransRelPacoWF_to_paco {a c : LocalTypeR} (h : TransRelPacoWF a c) :
    paco EQ2FMono (toPacoRel EQ2) a c := by
  obtain ⟨b, hab, hbc, hWFa, hWFb, hWFc⟩ := h
  have heq : EQ2 a c := EQ2_trans_via_Bisim hab hbc hWFa hWFb hWFc
  refine ⟨toPacoRel EQ2, ?_, heq⟩
  intro x y hxy
  have h' := EQ2.destruct hxy
  show EQ2F_paco (toPacoRel EQ2 ⊔ toPacoRel EQ2) x y
  simp only [EQ2F_paco, fromPacoRel, toPacoRel]
  exact EQ2F.mono (fun _ _ hr => Or.inl hr) x y h'

/-- Transitivity for EQ2 via paco (requires WellFormed).

This version includes explicit LocalTypeR.WellFormed hypotheses and delegates to
EQ2_trans_via_Bisim from Bisim.lean. For transitivity without WellFormed,
use specialized lemmas like EQ2_trans_via_end or EQ2_trans_via_var. -/
theorem EQ2_trans_via_paco {a b c : LocalTypeR}
    (hab : EQ2 a b) (hbc : EQ2 b c)
    (hWFa : LocalTypeR.WellFormed a) (hWFb : LocalTypeR.WellFormed b)
    (hWFc : LocalTypeR.WellFormed c) : EQ2 a c :=
  EQ2_trans_via_Bisim hab hbc hWFa hWFb hWFc

/-! ## Up-To Techniques

Infrastructure for "up-to" coinduction using paco's closure operators.
-/

/-- Reflexive closure for EQ2 relations. -/
def ReflClosure (R : EQ2.Rel) : EQ2.Rel :=
  fun x y => x = y ∨ R x y

/-- Symmetric closure for EQ2 relations. -/
def SymmClosure (R : EQ2.Rel) : EQ2.Rel :=
  fun x y => R x y ∨ R y x

/-- Transitive closure for EQ2 relations. -/
def TransClosure (R : EQ2.Rel) : EQ2.Rel :=
  fun x y => ∃ n, TransClosureN R n x y
where
  TransClosureN (R : EQ2.Rel) : Nat → LocalTypeR → LocalTypeR → Prop
    | 0, x, y => R x y
    | n+1, x, z => ∃ y, R x y ∧ TransClosureN R n y z

/-- Reflexive-symmetric-transitive (equivalence) closure. -/
def EquivClosure (R : EQ2.Rel) : EQ2.Rel :=
  TransClosure (SymmClosure (ReflClosure R))

end SessionCoTypes.EQ2Paco
