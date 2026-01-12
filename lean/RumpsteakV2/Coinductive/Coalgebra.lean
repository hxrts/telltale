import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC

set_option linter.dupNamespace false

/-!
# Coalgebra helpers for LocalTypeC

Lightweight wrappers around the M-type corecursor.
-/

namespace RumpsteakV2.Coinductive

/-- Anamorphism for `LocalTypeC` (no fuel). -/
def ana {α : Type} (coalg : α → LocalTypeF.Obj α) : α → LocalTypeC :=
  PFunctor.M.corec coalg

/-- Unfolding equation for `ana`. -/
theorem dest_ana {α : Type} (coalg : α → LocalTypeF.Obj α) (a : α) :
    PFunctor.M.dest (ana coalg a) = PFunctor.map (P := LocalTypeF) (ana coalg) (coalg a) := by
  simpa [ana] using (PFunctor.M.dest_corec (g := coalg) (x := a) (P := LocalTypeF))

end RumpsteakV2.Coinductive
