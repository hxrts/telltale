import Mathlib
import Telltale.Coinductive.LocalTypeC

set_option linter.dupNamespace false

/-!
To build coinductive local types from other data, we need anamorphisms
(unfolds). Mathlib's PFunctor.M provides a corecursor, however, the
interface is low-level.

We therefore wrap PFunctor.M.corec in a friendlier `ana` function
and provide an unfolding equation for reasoning about its behavior.
-/

namespace Telltale.Coinductive

/-! ## Anamorphism -/

/-- Anamorphism (unfold) for LocalTypeC.
    Given a coalgebra `α → LocalTypeF.Obj α`, produces a function `α → LocalTypeC`
    that builds the coinductive type by repeatedly applying the coalgebra. -/
def ana {α : Type} (coalg : α → LocalTypeF.Obj α) : α → LocalTypeC :=
  PFunctor.M.corec coalg

/-- Unfolding equation: destruct after ana equals map ana over coalgebra. -/
theorem dest_ana {α : Type} (coalg : α → LocalTypeF.Obj α) (a : α) :
    PFunctor.M.dest (ana coalg a) = PFunctor.map (P := LocalTypeF) (ana coalg) (coalg a) := by
  simpa [ana] using PFunctor.M.dest_corec (g := coalg) (x := a) (P := LocalTypeF)

end Telltale.Coinductive
