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
  cases hdest : PFunctor.M.dest t with
  | mk s f =>
      simpa [dualC, dualStep, hdest] using (PFunctor.M.dest_corec (g := dualStep) t)

private theorem dest_dualC_twice (t : LocalTypeC) :
    PFunctor.M.dest (dualC (dualC t)) =
      match PFunctor.M.dest t with
      | ⟨.end, _⟩ => ⟨.end, fun x => PEmpty.elim x⟩
      | ⟨.var x, _⟩ => ⟨.var x, fun x => PEmpty.elim x⟩
      | ⟨.mu x, f⟩ => ⟨.mu x, fun _ => dualC (dualC (f ()))⟩
      | ⟨.send p labels, f⟩ => ⟨.send p labels, fun i => dualC (dualC (f i))⟩
      | ⟨.recv p labels, f⟩ => ⟨.recv p labels, fun i => dualC (dualC (f i))⟩ := by
  cases hdest : PFunctor.M.dest t with
  | mk s f =>
      simpa [dest_dualC, hdest] using (dest_dualC (dualC t))

/-- Duality is involutive. -/
theorem dualC_involutive (t : LocalTypeC) : dualC (dualC t) = t := by
  refine (PFunctor.M.bisim (P := LocalTypeF) (R := fun x y => x = dualC (dualC y)) ?_) _ _ rfl
  intro x y hxy
  subst hxy
  cases hdest : PFunctor.M.dest y with
  | mk s f =>
      refine ⟨s, (fun i => dualC (dualC (f i))), f, ?_, hdest, ?_⟩
      · simpa [dest_dualC_twice, hdest]
      · intro i
        rfl

end RumpsteakV2.Coinductive
