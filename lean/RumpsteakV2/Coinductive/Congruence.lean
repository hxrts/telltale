import Mathlib
import RumpsteakV2.Coinductive.Bisim
import RumpsteakV2.Coinductive.Bridge
import RumpsteakV2.Coinductive.ToInductive
import RumpsteakV2.Coinductive.Regularity

set_option linter.dupNamespace false

/-!
# Congruence lemmas for toCoind / toInductive
-/

namespace RumpsteakV2.Coinductive

/-- `toCoind` is congruent with equality. -/
lemma toCoind_congr {t u : RumpsteakV2.Protocol.LocalTypeR.LocalTypeR} (h : t = u) :
    toCoind t = toCoind u := by
  simpa [h]

/-- `toInductive` is congruent under bisimilarity (extensionality). -/
lemma toInductive_congr {t u : LocalTypeC} (ht : Regular t) (hu : Regular u)
    (h : Bisim t u) : toInductive t ht = toInductive u hu := by
  have htu : t = u := (Bisim_eq_iff t u).1 h
  subst htu
  rfl

end RumpsteakV2.Coinductive
