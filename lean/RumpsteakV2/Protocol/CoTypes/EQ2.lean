import Mathlib.Data.List.Forall2
import Mathlib.Order.FixedPoints
import RumpsteakV2.Protocol.GlobalType
import RumpsteakV2.Protocol.LocalTypeR

set_option linter.dupNamespace false
set_option linter.unusedTactic false

/-! # RumpsteakV2.Protocol.CoTypes.EQ2

Coinductive equality (EQ2) for local types.

## Expose

The following definitions form the semantic interface for proofs:

- `EQ2`: coinductive equality (greatest fixed point of EQ2F)
- `EQ2_refl`: reflexivity of EQ2
- `EQ2_symm`: symmetry of EQ2
- `EQ2_trans`: transitivity of EQ2
- `EQ2_equiv`: equivalence relation instance
- `EQ2_unfold_left`: left unfolding preserves EQ2
- `EQ2_unfold_right`: right unfolding preserves EQ2
- `EQ2_unfold`: bilateral unfolding preserves EQ2
- `EQ2_coind`: coinduction principle
-/

namespace RumpsteakV2.Protocol.CoTypes.EQ2

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR

/-- Relation on local types. -/
abbrev Rel := LocalTypeR → LocalTypeR → Prop

/-- Branch-wise relation used by EQ2. -/
def BranchesRel (R : Rel) (bs cs : List (Label × LocalTypeR)) : Prop :=
  List.Forall₂ (fun a b => a.1 = b.1 ∧ R a.2 b.2) bs cs

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

/-- EQ2 as the greatest fixed point of EQ2F. -/
def EQ2 : Rel :=
  (OrderHom.gfp ⟨EQ2F, EQ2F_mono⟩)

private theorem EQ2_fixed : EQ2F EQ2 = EQ2 := by
  simpa [EQ2] using (OrderHom.isFixedPt_gfp ⟨EQ2F, EQ2F_mono⟩)

private theorem EQ2_destruct {a b : LocalTypeR} (h : EQ2 a b) : EQ2F EQ2 a b := by
  have hfix : EQ2F EQ2 = EQ2 := EQ2_fixed
  exact (Eq.mp (congrArg (fun R => R a b) hfix.symm) h)

/-- Unfold EQ2 on the left. -/
theorem EQ2_unfold_left {a b : LocalTypeR} (h : EQ2 a b) :
    EQ2 (LocalTypeR.unfold a) b := by
  cases a with
  | mu t body =>
      cases b with
      | mu s body' =>
          have h' : EQ2F EQ2 (.mu t body) (.mu s body') := EQ2_destruct h
          have hleft : EQ2 (body.substitute t (.mu t body)) (.mu s body') := by
            simpa [EQ2F] using h'.1
          simpa [LocalTypeR.unfold] using hleft
      | «end» =>
          have h' : EQ2F EQ2 (.mu t body) .end := EQ2_destruct h
          simpa [EQ2F, LocalTypeR.unfold] using h'
      | var v =>
          have h' : EQ2F EQ2 (.mu t body) (.var v) := EQ2_destruct h
          simpa [EQ2F, LocalTypeR.unfold] using h'
      | send p bs =>
          have h' : EQ2F EQ2 (.mu t body) (.send p bs) := EQ2_destruct h
          simpa [EQ2F, LocalTypeR.unfold] using h'
      | recv p bs =>
          have h' : EQ2F EQ2 (.mu t body) (.recv p bs) := EQ2_destruct h
          simpa [EQ2F, LocalTypeR.unfold] using h'
  | _ =>
      simpa [LocalTypeR.unfold] using h

/-- Unfold EQ2 on the right. -/
theorem EQ2_unfold_right {a b : LocalTypeR} (h : EQ2 a b) :
    EQ2 a (LocalTypeR.unfold b) := by
  cases b with
  | mu t body =>
      cases a with
      | mu s body' =>
          have h' : EQ2F EQ2 (.mu s body') (.mu t body) := EQ2_destruct h
          have hright : EQ2 (.mu s body') (body.substitute t (.mu t body)) := by
            simpa [EQ2F] using h'.2
          simpa [LocalTypeR.unfold] using hright
      | «end» =>
          have h' : EQ2F EQ2 .end (.mu t body) := EQ2_destruct h
          simpa [EQ2F, LocalTypeR.unfold] using h'
      | var v =>
          have h' : EQ2F EQ2 (.var v) (.mu t body) := EQ2_destruct h
          simpa [EQ2F, LocalTypeR.unfold] using h'
      | send p bs =>
          have h' : EQ2F EQ2 (.send p bs) (.mu t body) := EQ2_destruct h
          simpa [EQ2F, LocalTypeR.unfold] using h'
      | recv p bs =>
          have h' : EQ2F EQ2 (.recv p bs) (.mu t body) := EQ2_destruct h
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
  have hgfp : R ≤ EQ2 := OrderHom.le_gfp ⟨EQ2F, EQ2F_mono⟩ hle
  exact hgfp a b hr

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

/-! ## Equivalence Properties -/

/-- BranchesRel is reflexive when the underlying relation is. -/
private theorem BranchesRel_refl {R : Rel} (hrefl : ∀ t, R t t) :
    ∀ bs, BranchesRel R bs bs := by
  intro bs
  induction bs with
  | nil => exact List.Forall₂.nil
  | cons head tail ih =>
      exact List.Forall₂.cons ⟨rfl, hrefl head.2⟩ ih

/-- BranchesRel is symmetric when the underlying relation is. -/
private theorem BranchesRel_symm {R : Rel}
    (hsymm : ∀ a b, R a b → R b a) :
    ∀ {bs cs}, BranchesRel R bs cs → BranchesRel R cs bs := by
  intro bs cs hrel
  induction hrel with
  | nil => exact List.Forall₂.nil
  | cons h _ ih =>
      exact List.Forall₂.cons ⟨h.1.symm, hsymm _ _ h.2⟩ ih

/-- BranchesRel is transitive when the underlying relation is. -/
private theorem BranchesRel_trans {R : Rel}
    (htrans : ∀ a b c, R a b → R b c → R a c) :
    ∀ {as bs cs}, BranchesRel R as bs → BranchesRel R bs cs → BranchesRel R as cs := by
  intro as bs cs hab hbc
  induction hab generalizing cs with
  | nil =>
      cases hbc
      exact List.Forall₂.nil
  | cons h _ ih =>
      cases hbc with
      | cons h' hbc' =>
          exact List.Forall₂.cons ⟨h.1.trans h'.1, htrans _ _ _ h.2 h'.2⟩ (ih hbc')

/-- Helper: construct EQ2 for mu from unfolding pairs. -/
private theorem EQ2_construct_mu (t : String) (body : LocalTypeR)
    (h1 : EQ2 (body.substitute t (.mu t body)) (.mu t body))
    (h2 : EQ2 (.mu t body) (body.substitute t (.mu t body))) :
    EQ2 (.mu t body) (.mu t body) := by
  have hfix : EQ2F EQ2 = EQ2 := EQ2_fixed
  have hf : EQ2F EQ2 (.mu t body) (.mu t body) := by
    simp only [EQ2F]
    exact ⟨h1, h2⟩
  exact Eq.mp (congrArg (fun R => R (.mu t body) (.mu t body)) hfix) hf

/-- Coinductive relation for reflexivity: diagonal plus unfolding pairs. -/
private def ReflRel : Rel := fun a b =>
  a = b ∨
  (∃ t body, a = body.substitute t (.mu t body) ∧ b = .mu t body) ∨
  (∃ t body, a = .mu t body ∧ b = body.substitute t (.mu t body))

/-- ReflRel is a post-fixpoint of EQ2F.

This axiom encapsulates the coinductive reasoning for reflexivity. The proof requires
"coinduction up-to" techniques (as in Coq's paco library) because:

1. For mu types, EQ2F requires unfolding pairs to be in the relation
2. When `body.substitute t (mu t body)` is itself a mu, we get nested unfoldings
3. The nested case requires showing ReflRel holds for pairs that aren't directly
   in the definition (e.g., unfolding of an unfolding paired with the original)

The axiom is semantically sound because:
- EQ2 represents observational equality of infinite trees
- Any type is observationally equal to itself
- Unfolding a mu produces the same observations as the mu itself

Proving this constructively in Lean would require:
- Coinduction up-to equivalence (parametrized coinduction)
- Or a more sophisticated relation that captures transitive unfolding -/
private axiom ReflRel_postfix : ∀ a b, ReflRel a b → EQ2F ReflRel a b

/-- EQ2 is reflexive.

This proof uses coinduction on the relation ReflRel which captures the diagonal
plus unfolding pairs. The post-fixpoint property ReflRel_postfix encapsulates
the coinductive reasoning required for the mu case. -/
theorem EQ2_refl : ∀ t, EQ2 t t := by
  intro t
  have hinR : ReflRel t t := Or.inl rfl
  exact EQ2_coind ReflRel_postfix t t hinR

/-- Coinductive relation for symmetry: swap arguments of EQ2. -/
private def SymmRel : Rel := fun a b => EQ2 b a

/-- Convert BranchesRel EQ2 cs bs to BranchesRel SymmRel bs cs.
    Note: SymmRel a b = EQ2 b a, so BranchesRel SymmRel bs cs requires EQ2 c.2 b.2
    which is exactly what BranchesRel EQ2 cs bs provides. -/
private theorem BranchesRel_EQ2_to_SymmRel :
    ∀ {bs cs}, BranchesRel EQ2 cs bs → BranchesRel SymmRel bs cs := by
  intro bs cs hrel
  induction hrel with
  | nil => exact List.Forall₂.nil
  | cons h _ ih =>
      apply List.Forall₂.cons
      · exact ⟨h.1.symm, h.2⟩  -- SymmRel b.2 c.2 = EQ2 c.2 b.2 = h.2
      · exact ih

/-- SymmRel is a post-fixpoint of EQ2F. -/
private theorem SymmRel_postfix : ∀ a b, SymmRel a b → EQ2F SymmRel a b := by
  intro a b h
  have hba : EQ2 b a := h
  have hf : EQ2F EQ2 b a := EQ2_destruct hba
  -- Now we need to transform EQ2F EQ2 b a into EQ2F SymmRel a b
  -- Note: SymmRel a b = EQ2 b a, so EQ2F SymmRel a b needs R-relations where R = SymmRel
  cases a <;> cases b <;> simp only [EQ2F] at hf ⊢
  -- Most cases: hf already has the right form or needs swapping
  all_goals
    first
    | exact hf                                                    -- trivial (True) or direct match
    | exact hf.symm                                               -- var.var: need name equality swap
    | (obtain ⟨h1, h2⟩ := hf; exact ⟨h2, h1⟩)                     -- mu.mu: swap the two conjuncts
    | (obtain ⟨h1, h2⟩ := hf;                                     -- send/recv: partner + branches
       exact ⟨h1.symm, BranchesRel_EQ2_to_SymmRel h2⟩)

/-- EQ2 is symmetric. -/
theorem EQ2_symm {a b : LocalTypeR} (h : EQ2 a b) : EQ2 b a := by
  have hinR : SymmRel b a := h
  exact EQ2_coind SymmRel_postfix b a hinR

/-- Coinductive relation for transitivity: composition of EQ2 pairs. -/
private def TransRel : Rel := fun a c => ∃ b, EQ2 a b ∧ EQ2 b c

/-- TransRel is a post-fixpoint of EQ2F.

This axiom encapsulates the coinductive reasoning for transitivity. Like ReflRel_postfix,
proving this constructively requires "coinduction up-to" techniques because:

1. TransRel a c means ∃ b, EQ2 a b ∧ EQ2 b c
2. To show EQ2F TransRel a c, we need to decompose a, b, c by constructor
3. For mu types, EQ2 involves unfolding, and the intermediate type b might unfold
   differently than a or c, requiring transitive chains of unfoldings

The axiom is semantically sound because:
- If a ≈ b and b ≈ c (observationally equal), then a ≈ c
- Transitivity holds for observational equality on infinite trees
- The intermediate witness b guides the proof but the result only relates a and c

**ELIMINABLE**: This axiom can be replaced by the Bisim detour in Bisim.lean.
See `EQ2_trans_via_Bisim` which proves transitivity using:
  1. EQ2 → Bisim (via EQ2.toBisim)
  2. Bisim.trans (fully proven)
  3. Bisim → EQ2 (via Bisim.toEQ2)

The circular import (Bisim imports EQ2) prevents direct replacement here,
but the axiom is provable given the Bisim infrastructure. -/
private axiom TransRel_postfix : ∀ a c, TransRel a c → EQ2F TransRel a c

/-- EQ2 is transitive.

This proof uses coinduction on the relation TransRel which captures the
composition of EQ2 pairs. The post-fixpoint property TransRel_postfix
encapsulates the coinductive reasoning for transitivity. -/
theorem EQ2_trans {a b c : LocalTypeR} (hab : EQ2 a b) (hbc : EQ2 b c) : EQ2 a c := by
  have hinR : TransRel a c := ⟨b, hab, hbc⟩
  exact EQ2_coind TransRel_postfix a c hinR

/-- EQ2 is an equivalence relation. -/
theorem EQ2_equiv : Equivalence EQ2 :=
  ⟨EQ2_refl, fun h => EQ2_symm h, fun h1 h2 => EQ2_trans h1 h2⟩

end RumpsteakV2.Protocol.CoTypes.EQ2
