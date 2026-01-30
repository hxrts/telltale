import Mathlib
import SessionCoTypes.Coinductive.LocalTypeC
import SessionCoTypes.Coinductive.Bisim

set_option linter.dupNamespace false

/-!
The Problem. Session type duality swaps send and recv. For coinductive types,
we need a corecursive definition of duality and a proof that it's involutive
(dual(dual(t)) = t).

The difficulty is that coinductive proofs require bisimulation: we must show
that dual(dual(t)) and t have the same head and their children are related
by the same relation, recursively forever.

Solution Structure.
1. Define dualHead: swap send/recv in the head tag
2. Define dualStep: one-step coalgebra for duality
3. Define dualC: the corecursive dual operation
4. Prove helper lemmas about dest of dualC for each constructor
5. Prove dualC_involutive via bisimulation
-/

namespace SessionCoTypes.Coinductive

/-! ## Duality Definition -/

/-- Swap send and recv in the head tag; leave other constructors unchanged. -/
def dualHead : LocalTypeHead → LocalTypeHead
  | .end         => .end
  | .var x       => .var x
  | .mu x        => .mu x
  | .send p ls   => .recv p ls
  | .recv p ls   => .send p ls

/-- One-step coalgebra for dualC: swap send/recv, keep children. -/
def dualStep (t : LocalTypeC) : LocalTypeF.Obj LocalTypeC :=
  match PFunctor.M.dest t with
  | ⟨.end, _⟩      => ⟨.end, PEmpty.elim⟩
  | ⟨.var x, _⟩    => ⟨.var x, PEmpty.elim⟩
  | ⟨.mu x, f⟩     => ⟨.mu x, fun _ => f ()⟩
  | ⟨.send p ls, f⟩ => ⟨.recv p ls, f⟩
  | ⟨.recv p ls, f⟩ => ⟨.send p ls, f⟩

/-- Coinductive duality: swap send/recv throughout the infinite tree. -/
def dualC : LocalTypeC → LocalTypeC :=
  PFunctor.M.corec dualStep

/-! ## Destructor Lemmas -/

private theorem dest_dualC_end (f : LocalTypeF.B .end → LocalTypeC) :
    PFunctor.M.dest (dualC (PFunctor.M.mk ⟨.end, f⟩)) = ⟨.end, PEmpty.elim⟩ := by
  simp only [dualC, PFunctor.M.dest_corec, dualStep, PFunctor.M.dest_mk, PFunctor.map]
  congr 1; funext x; cases x

private theorem dest_dualC_var (x : String) (f : LocalTypeF.B (.var x) → LocalTypeC) :
    PFunctor.M.dest (dualC (PFunctor.M.mk ⟨.var x, f⟩)) = ⟨.var x, PEmpty.elim⟩ := by
  simp only [dualC, PFunctor.M.dest_corec, dualStep, PFunctor.M.dest_mk, PFunctor.map]
  congr 1; funext y; cases y

private theorem dest_dualC_mu (x : String) (f : LocalTypeF.B (.mu x) → LocalTypeC) :
    PFunctor.M.dest (dualC (PFunctor.M.mk ⟨.mu x, f⟩)) = ⟨.mu x, fun _ => dualC (f ())⟩ := by
  simp only [dualC, PFunctor.M.dest_corec, dualStep, PFunctor.M.dest_mk]; rfl

private theorem dest_dualC_send (p : String) (labels : List SessionTypes.GlobalType.Label)
    (f : LocalTypeF.B (.send p labels) → LocalTypeC) :
    PFunctor.M.dest (dualC (PFunctor.M.mk ⟨.send p labels, f⟩)) =
      ⟨.recv p labels, fun i => dualC (f i)⟩ := by
  simp only [dualC, PFunctor.M.dest_corec, dualStep, PFunctor.M.dest_mk]; rfl

private theorem dest_dualC_recv (p : String) (labels : List SessionTypes.GlobalType.Label)
    (f : LocalTypeF.B (.recv p labels) → LocalTypeC) :
    PFunctor.M.dest (dualC (PFunctor.M.mk ⟨.recv p labels, f⟩)) =
      ⟨.send p labels, fun i => dualC (f i)⟩ := by
  simp only [dualC, PFunctor.M.dest_corec, dualStep, PFunctor.M.dest_mk]; rfl

/-! ## Double Dual Lemmas -/

private theorem dest_dualC_twice_end (f : LocalTypeF.B .end → LocalTypeC) :
    PFunctor.M.dest (dualC (dualC (PFunctor.M.mk ⟨.end, f⟩))) = ⟨.end, PEmpty.elim⟩ := by
  conv_lhs => arg 1; arg 1; rw [← PFunctor.M.mk_dest (dualC (PFunctor.M.mk ⟨.end, f⟩))]
  rw [dest_dualC_end, dest_dualC_end]

private theorem dest_dualC_twice_var (x : String) (f : LocalTypeF.B (.var x) → LocalTypeC) :
    PFunctor.M.dest (dualC (dualC (PFunctor.M.mk ⟨.var x, f⟩))) = ⟨.var x, PEmpty.elim⟩ := by
  conv_lhs => arg 1; arg 1; rw [← PFunctor.M.mk_dest (dualC (PFunctor.M.mk ⟨.var x, f⟩))]
  rw [dest_dualC_var, dest_dualC_var]

private theorem dest_dualC_twice_mu (x : String) (f : LocalTypeF.B (.mu x) → LocalTypeC) :
    PFunctor.M.dest (dualC (dualC (PFunctor.M.mk ⟨.mu x, f⟩))) =
      ⟨.mu x, fun _ => dualC (dualC (f ()))⟩ := by
  conv_lhs => arg 1; arg 1; rw [← PFunctor.M.mk_dest (dualC (PFunctor.M.mk ⟨.mu x, f⟩))]
  rw [dest_dualC_mu, dest_dualC_mu]

private theorem dest_dualC_twice_send (p : String) (labels : List SessionTypes.GlobalType.Label)
    (f : LocalTypeF.B (.send p labels) → LocalTypeC) :
    PFunctor.M.dest (dualC (dualC (PFunctor.M.mk ⟨.send p labels, f⟩))) =
      ⟨.send p labels, fun i => dualC (dualC (f i))⟩ := by
  conv_lhs => arg 1; arg 1; rw [← PFunctor.M.mk_dest (dualC (PFunctor.M.mk ⟨.send p labels, f⟩))]
  rw [dest_dualC_send, dest_dualC_recv]

private theorem dest_dualC_twice_recv (p : String) (labels : List SessionTypes.GlobalType.Label)
    (f : LocalTypeF.B (.recv p labels) → LocalTypeC) :
    PFunctor.M.dest (dualC (dualC (PFunctor.M.mk ⟨.recv p labels, f⟩))) =
      ⟨.recv p labels, fun i => dualC (dualC (f i))⟩ := by
  conv_lhs => arg 1; arg 1; rw [← PFunctor.M.mk_dest (dualC (PFunctor.M.mk ⟨.recv p labels, f⟩))]
  rw [dest_dualC_recv, dest_dualC_send]

/-! ## Involution -/

/-- Duality is involutive: dual(dual(t)) = t.
    Proof by bisimulation with R x y := x = dualC (dualC y). -/
theorem dualC_involutive (t : LocalTypeC) : dualC (dualC t) = t := by
  refine (PFunctor.M.bisim (P := LocalTypeF) (R := fun x y => x = dualC (dualC y)) ?_) _ _ rfl
  intro x y hxy
  subst hxy
  conv_rhs => rw [← PFunctor.M.mk_dest y]
  cases hdest : PFunctor.M.dest y with
  | mk s f =>
      cases s with
      | «end» =>
          have heq : (fun i : LocalTypeF.B .end => dualC (dualC (f i))) = PEmpty.elim := by
            funext i; cases i
          refine ⟨.end, fun i => dualC (dualC (f i)), f, ?_, rfl, fun i => i.elim⟩
          rw [heq]; exact dest_dualC_twice_end f
      | var x =>
          have heq : (fun i : LocalTypeF.B (.var x) => dualC (dualC (f i))) = PEmpty.elim := by
            funext i; cases i
          refine ⟨.var x, fun i => dualC (dualC (f i)), f, ?_, rfl, fun i => i.elim⟩
          rw [heq]; exact dest_dualC_twice_var x f
      | mu x =>
          exact ⟨.mu x, fun _ => dualC (dualC (f ())), f, dest_dualC_twice_mu x f, rfl, fun _ => rfl⟩
      | send p labels =>
          exact ⟨.send p labels, fun i => dualC (dualC (f i)), f,
                 dest_dualC_twice_send p labels f, rfl, fun _ => rfl⟩
      | recv p labels =>
          exact ⟨.recv p labels, fun i => dualC (dualC (f i)), f,
                 dest_dualC_twice_recv p labels f, rfl, fun _ => rfl⟩

end SessionCoTypes.Coinductive
