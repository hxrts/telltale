import Mathlib
import SessionCoTypes.Coinductive.Bisim
import SessionCoTypes.Coinductive.Bridge
import SessionCoTypes.Coinductive.ToInductive
import SessionCoTypes.Coinductive.Regularity

set_option linter.dupNamespace false


/-
The Problem. When converting between inductive and coinductive representations,
we need congruence lemmas: if inputs are equal, outputs are equal.
These lemmas enable substitution in proofs about type equivalence.

Solution Structure. Prove congruence for the embedding:
- to_coind_congr: equal inductive types map to equal coinductive types

(`toInductive` is not congruent in its `Regular` witness: generated names depend on
the enumerated state list, so no such lemma is stated.)
-/

namespace SessionCoTypes.Coinductive

/-! ## Congruence Lemmas -/

/-- toCoind is congruent: equal inputs produce equal outputs. -/
lemma to_coind_congr {t u : SessionTypes.LocalTypeR.LocalTypeR} (h : t = u) :
    toCoind t = toCoind u := by
  simp [h]

end SessionCoTypes.Coinductive
