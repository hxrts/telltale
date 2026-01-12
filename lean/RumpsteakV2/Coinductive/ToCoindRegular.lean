import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Bridge
import RumpsteakV2.Coinductive.RegularityLemmas
import RumpsteakV2.Protocol.LocalTypeR

set_option linter.dupNamespace false

/-!
# Regularity of `toCoind`
-/

namespace RumpsteakV2.Coinductive

open RumpsteakV2.Protocol.LocalTypeR

-- These helper lemmas are commented out due to TypeContext refactoring issues
-- TODO: Fix after TypeContext refactoring
-- private lemma child_toCoind_send ...
-- private lemma child_toCoind_recv ...

/-- `toCoind` produces a regular coinductive type. -/
theorem toCoind_regular : ∀ t : LocalTypeR, Regular (toCoind t)
  | .end => by
      apply regular_of_children
      intro i; cases i
  | .var x => by
      apply regular_of_children
      intro i; cases i
  | .mu x body => by
      apply regular_of_children
      intro i
      cases i
      simpa [toCoind] using toCoind_regular body
  | .send _ _ => by
      -- TODO: Fix after TypeContext refactoring
      sorry
  | .recv _ _ => by
      -- TODO: Fix after TypeContext refactoring
      sorry

end RumpsteakV2.Coinductive
