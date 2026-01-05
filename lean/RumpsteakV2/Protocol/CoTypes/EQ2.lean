import Mathlib.Data.List.Forall2
import Mathlib.Order.FixedPoints
import RumpsteakV2.Protocol.GlobalType
import RumpsteakV2.Protocol.LocalTypeR

/-! # RumpsteakV2.Protocol.CoTypes.EQ2

Coinductive equality (EQ2) for local types.

## Expose

The following definitions form the semantic interface for proofs:

- `EQ2`
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

/-- Unfold EQ2 on both sides. -/
theorem EQ2_unfold {a b : LocalTypeR} (h : EQ2 a b) :
    EQ2 (LocalTypeR.unfold a) (LocalTypeR.unfold b) := by
  exact EQ2_unfold_right (EQ2_unfold_left h)

end RumpsteakV2.Protocol.CoTypes.EQ2
