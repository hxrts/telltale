import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Bisim

set_option linter.dupNamespace false

/-!
# Dual for LocalTypeC

Corecursive definition swapping send/recv.
-/

namespace RumpsteakV2.Coinductive

/-- Swap send/recv in the head tag. -/
def dualHead : LocalTypeHead → LocalTypeHead
  | .end => .end
  | .var x => .var x
  | .mu x => .mu x
  | .send p labels => .recv p labels
  | .recv p labels => .send p labels

/-- One-step coalgebra for `dualC`. -/
def dualStep (t : LocalTypeC) : LocalTypeF.Obj LocalTypeC :=
  match h : PFunctor.M.dest t with
  | ⟨.end, _⟩ => ⟨.end, fun x => PEmpty.elim x⟩
  | ⟨.var x, _⟩ => ⟨.var x, fun x => PEmpty.elim x⟩
  | ⟨.mu x, f⟩ => ⟨.mu x, fun _ => f ()⟩
  | ⟨.send p labels, f⟩ => ⟨.recv p labels, fun i => f i⟩
  | ⟨.recv p labels, f⟩ => ⟨.send p labels, fun i => f i⟩

/-- Coinductive duality. -/
def dualC : LocalTypeC → LocalTypeC :=
  PFunctor.M.corec dualStep

/-! ## Involution -/

private theorem dest_dualC (t : LocalTypeC) :
    PFunctor.M.dest (dualC t) =
      match PFunctor.M.dest t with
      | ⟨.end, _⟩ => ⟨.end, fun x => PEmpty.elim x⟩
      | ⟨.var x, _⟩ => ⟨.var x, fun x => PEmpty.elim x⟩
      | ⟨.mu x, f⟩ => ⟨.mu x, fun _ => dualC (f ())⟩
      | ⟨.send p labels, f⟩ => ⟨.recv p labels, fun i => dualC (f i)⟩
      | ⟨.recv p labels, f⟩ => ⟨.send p labels, fun i => dualC (f i)⟩ := by
  -- TODO: Fix after TypeContext refactoring
  sorry

private theorem dest_dualC_twice (t : LocalTypeC) :
    PFunctor.M.dest (dualC (dualC t)) =
      match PFunctor.M.dest t with
      | ⟨.end, _⟩ => ⟨.end, fun x => PEmpty.elim x⟩
      | ⟨.var x, _⟩ => ⟨.var x, fun x => PEmpty.elim x⟩
      | ⟨.mu x, f⟩ => ⟨.mu x, fun _ => dualC (dualC (f ()))⟩
      | ⟨.send p labels, f⟩ => ⟨.send p labels, fun i => dualC (dualC (f i))⟩
      | ⟨.recv p labels, f⟩ => ⟨.recv p labels, fun i => dualC (dualC (f i))⟩ := by
  -- TODO: Fix after TypeContext refactoring
  sorry

/-- Duality is involutive. -/
theorem dualC_involutive (t : LocalTypeC) : dualC (dualC t) = t := by
  -- TODO: Fix after TypeContext refactoring
  sorry

end RumpsteakV2.Coinductive
