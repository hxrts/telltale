import Mathlib
import RumpsteakV2.Coinductive.Bisim
import RumpsteakV2.Coinductive.Bridge
import RumpsteakV2.Coinductive.ToInductive
import RumpsteakV2.Coinductive.Regularity

set_option linter.dupNamespace false

/-!
The Problem. When converting between inductive and coinductive representations,
we need congruence lemmas: if inputs are equal (or bisimilar), outputs are equal.
These lemmas enable substitution in proofs about type equivalence.

Solution Structure. Prove congruence for both directions:
- toCoind_congr: equal inductive types map to equal coinductive types
- toInductive_congr: bisimilar coinductive types map to equal inductive types
-/

namespace RumpsteakV2.Coinductive

/-! ## Congruence Lemmas -/

/-- toCoind is congruent: equal inputs produce equal outputs. -/
lemma toCoind_congr {t u : RumpsteakV2.Protocol.LocalTypeR.LocalTypeR} (h : t = u) :
    toCoind t = toCoind u := by
  simp [h]

/-- toInductive is congruent under bisimilarity.
    Since bisimilarity equals equality for M-types, this follows from reflexivity. -/
lemma toInductive_congr {t u : LocalTypeC} (ht : Regular t) (hu : Regular u)
    (h : Bisim t u) : toInductive t ht = toInductive u hu := by
  have htu : t = u := (Bisim_eq_iff t u).1 h
  subst htu
  rfl

end RumpsteakV2.Coinductive
