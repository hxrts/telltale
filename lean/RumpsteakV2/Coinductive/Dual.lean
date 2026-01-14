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
  match PFunctor.M.dest t with
  | ⟨.end, _⟩ => ⟨.end, fun x => PEmpty.elim x⟩
  | ⟨.var x, _⟩ => ⟨.var x, fun x => PEmpty.elim x⟩
  | ⟨.mu x, f⟩ => ⟨.mu x, fun _ => f ()⟩
  | ⟨.send p labels, f⟩ => ⟨.recv p labels, fun i => f i⟩
  | ⟨.recv p labels, f⟩ => ⟨.send p labels, fun i => f i⟩

/-- Coinductive duality. -/
def dualC : LocalTypeC → LocalTypeC :=
  PFunctor.M.corec dualStep

/-! ## Involution -/

/-- Helper: dest of dualC for end. -/
private theorem dest_dualC_end (f : LocalTypeF.B .end → LocalTypeC) :
    PFunctor.M.dest (dualC (PFunctor.M.mk ⟨.end, f⟩)) = ⟨.end, fun x => PEmpty.elim x⟩ := by
  simp only [dualC, PFunctor.M.dest_corec, dualStep, PFunctor.M.dest_mk, PFunctor.map]
  congr 1
  funext x
  cases x

/-- Helper: dest of dualC for var. -/
private theorem dest_dualC_var (x : String) (f : LocalTypeF.B (.var x) → LocalTypeC) :
    PFunctor.M.dest (dualC (PFunctor.M.mk ⟨.var x, f⟩)) = ⟨.var x, fun x => PEmpty.elim x⟩ := by
  simp only [dualC, PFunctor.M.dest_corec, dualStep, PFunctor.M.dest_mk, PFunctor.map]
  congr 1
  funext y
  cases y

/-- Helper: dest of dualC for mu. -/
private theorem dest_dualC_mu (x : String) (f : LocalTypeF.B (.mu x) → LocalTypeC) :
    PFunctor.M.dest (dualC (PFunctor.M.mk ⟨.mu x, f⟩)) = ⟨.mu x, fun _ => dualC (f ())⟩ := by
  simp only [dualC, PFunctor.M.dest_corec, dualStep, PFunctor.M.dest_mk]
  rfl

/-- Helper: dest of dualC for send. -/
private theorem dest_dualC_send (p : String) (labels : List RumpsteakV2.Protocol.GlobalType.Label)
    (f : LocalTypeF.B (.send p labels) → LocalTypeC) :
    PFunctor.M.dest (dualC (PFunctor.M.mk ⟨.send p labels, f⟩)) =
      ⟨.recv p labels, fun i => dualC (f i)⟩ := by
  simp only [dualC, PFunctor.M.dest_corec, dualStep, PFunctor.M.dest_mk]
  rfl

/-- Helper: dest of dualC for recv. -/
private theorem dest_dualC_recv (p : String) (labels : List RumpsteakV2.Protocol.GlobalType.Label)
    (f : LocalTypeF.B (.recv p labels) → LocalTypeC) :
    PFunctor.M.dest (dualC (PFunctor.M.mk ⟨.recv p labels, f⟩)) =
      ⟨.send p labels, fun i => dualC (f i)⟩ := by
  simp only [dualC, PFunctor.M.dest_corec, dualStep, PFunctor.M.dest_mk]
  rfl

/-- Helper: dest of dualC twice for end. -/
private theorem dest_dualC_twice_end (f : LocalTypeF.B .end → LocalTypeC) :
    PFunctor.M.dest (dualC (dualC (PFunctor.M.mk ⟨.end, f⟩))) =
      ⟨.end, fun x => PEmpty.elim x⟩ := by
  -- First, dualC (mk ⟨.end, f⟩) = mk ⟨.end, fun x => PEmpty.elim x⟩
  conv_lhs => arg 1; arg 1; rw [← PFunctor.M.mk_dest (dualC (PFunctor.M.mk ⟨.end, f⟩))]
  rw [dest_dualC_end]
  -- Now have: dualC (mk ⟨.end, fun x => PEmpty.elim x⟩)
  rw [dest_dualC_end]

/-- Helper: dest of dualC twice for var. -/
private theorem dest_dualC_twice_var (x : String) (f : LocalTypeF.B (.var x) → LocalTypeC) :
    PFunctor.M.dest (dualC (dualC (PFunctor.M.mk ⟨.var x, f⟩))) =
      ⟨.var x, fun x => PEmpty.elim x⟩ := by
  conv_lhs => arg 1; arg 1; rw [← PFunctor.M.mk_dest (dualC (PFunctor.M.mk ⟨.var x, f⟩))]
  rw [dest_dualC_var, dest_dualC_var]

/-- Helper: dest of dualC twice for mu. -/
private theorem dest_dualC_twice_mu (x : String) (f : LocalTypeF.B (.mu x) → LocalTypeC) :
    PFunctor.M.dest (dualC (dualC (PFunctor.M.mk ⟨.mu x, f⟩))) =
      ⟨.mu x, fun _ => dualC (dualC (f ()))⟩ := by
  -- First rewrite inner dualC: mk ⟨mu x, f⟩ -> mk ⟨mu x, fun _ => dualC (f ())⟩
  conv_lhs => arg 1; arg 1; rw [← PFunctor.M.mk_dest (dualC (PFunctor.M.mk ⟨.mu x, f⟩))]
  rw [dest_dualC_mu]
  -- Now have: dualC (PFunctor.M.mk ⟨mu x, fun _ => dualC (f ())⟩)
  rw [dest_dualC_mu]

/-- Helper: dest of dualC twice for send. -/
private theorem dest_dualC_twice_send (p : String) (labels : List RumpsteakV2.Protocol.GlobalType.Label)
    (f : LocalTypeF.B (.send p labels) → LocalTypeC) :
    PFunctor.M.dest (dualC (dualC (PFunctor.M.mk ⟨.send p labels, f⟩))) =
      ⟨.send p labels, fun i => dualC (dualC (f i))⟩ := by
  -- First rewrite inner dualC: mk ⟨send p labels, f⟩ -> mk ⟨recv p labels, fun i => dualC (f i)⟩
  conv_lhs => arg 1; arg 1; rw [← PFunctor.M.mk_dest (dualC (PFunctor.M.mk ⟨.send p labels, f⟩))]
  rw [dest_dualC_send]
  -- Now have: dualC (PFunctor.M.mk ⟨recv p labels, fun i => dualC (f i)⟩)
  rw [dest_dualC_recv]

/-- Helper: dest of dualC twice for recv. -/
private theorem dest_dualC_twice_recv (p : String) (labels : List RumpsteakV2.Protocol.GlobalType.Label)
    (f : LocalTypeF.B (.recv p labels) → LocalTypeC) :
    PFunctor.M.dest (dualC (dualC (PFunctor.M.mk ⟨.recv p labels, f⟩))) =
      ⟨.recv p labels, fun i => dualC (dualC (f i))⟩ := by
  -- First rewrite inner dualC: mk ⟨recv p labels, f⟩ -> mk ⟨send p labels, fun i => dualC (f i)⟩
  conv_lhs => arg 1; arg 1; rw [← PFunctor.M.mk_dest (dualC (PFunctor.M.mk ⟨.recv p labels, f⟩))]
  rw [dest_dualC_recv]
  -- Now have: dualC (PFunctor.M.mk ⟨send p labels, fun i => dualC (f i)⟩)
  rw [dest_dualC_send]

/-- Duality is involutive. -/
theorem dualC_involutive (t : LocalTypeC) : dualC (dualC t) = t := by
  refine (PFunctor.M.bisim (P := LocalTypeF) (R := fun x y => x = dualC (dualC y)) ?_) _ _ rfl
  intro x y hxy
  subst hxy
  -- Reconstruct y from its dest
  conv_rhs => rw [← PFunctor.M.mk_dest y]
  cases hdest : PFunctor.M.dest y with
  | mk s f =>
      -- Now y = PFunctor.M.mk ⟨s, f⟩
      cases s with
      | «end» =>
          -- For end: children are PEmpty, so the function equality is trivial
          have heq : (fun i : LocalTypeF.B .end => dualC (dualC (f i))) =
                     (fun x => PEmpty.elim x) := by funext i; cases i
          refine ⟨.end, (fun i => dualC (dualC (f i))), f, ?_, rfl, ?_⟩
          · rw [heq]; exact dest_dualC_twice_end f
          · intro i; cases i
      | var x =>
          -- For var: children are PEmpty, so the function equality is trivial
          have heq : (fun i : LocalTypeF.B (.var x) => dualC (dualC (f i))) =
                     (fun x => PEmpty.elim x) := by funext i; cases i
          refine ⟨.var x, (fun i => dualC (dualC (f i))), f, ?_, rfl, ?_⟩
          · rw [heq]; exact dest_dualC_twice_var x f
          · intro i; cases i
      | mu x =>
          refine ⟨.mu x, (fun _ => dualC (dualC (f ()))), f, dest_dualC_twice_mu x f, rfl, ?_⟩
          intro _; rfl
      | send p labels =>
          refine ⟨.send p labels, (fun i => dualC (dualC (f i))), f, dest_dualC_twice_send p labels f, rfl, ?_⟩
          intro _; rfl
      | recv p labels =>
          refine ⟨.recv p labels, (fun i => dualC (dualC (f i))), f, dest_dualC_twice_recv p labels f, rfl, ?_⟩
          intro _; rfl

end RumpsteakV2.Coinductive
