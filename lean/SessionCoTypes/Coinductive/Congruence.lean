import Mathlib
import SessionCoTypes.Coinductive.Bisim
import SessionCoTypes.Coinductive.Bridge
import SessionCoTypes.Coinductive.ToInductive
import SessionCoTypes.Coinductive.Regularity

set_option linter.dupNamespace false


/-
The Problem. When converting between inductive and coinductive representations,
we need congruence lemmas: if inputs are equal (or bisimilar), outputs are equal.
These lemmas enable substitution in proofs about type equivalence.

Solution Structure. Prove congruence for both directions:
- to_coind_congr: equal inductive types map to equal coinductive types
- to_inductive_congr: bisimilar coinductive types map to equal inductive types
-/

namespace SessionCoTypes.Coinductive

/-! ## Congruence Lemmas -/

/-- toCoind is congruent: equal inputs produce equal outputs. -/
lemma to_coind_congr {t u : SessionTypes.LocalTypeR.LocalTypeR} (h : t = u) :
    toCoind t = toCoind u := by
  simp [h]

/-- toInductive is congruent under bisimilarity.
    Since bisimilarity equals equality for M-types, this follows from reflexivity. -/
lemma to_inductive_congr {t u : LocalTypeC} (ht : Regular t) (hu : Regular u)
    (h : Bisim t u) : toInductive t ht = toInductive u hu := by
  have htu : t = u := (bisim_eq_iff t u).1 h
  subst htu
  rfl

end SessionCoTypes.Coinductive
