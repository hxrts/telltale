import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Observable
import RumpsteakV2.Coinductive.Bridge
import RumpsteakV2.Protocol.LocalTypeR

set_option linter.dupNamespace false

/-!
# WellFormedC preservation

Basic preservation lemmas for `WellFormedC` across core constructors and the
embedding `toCoind`.
-/

namespace RumpsteakV2.Coinductive

open RumpsteakV2.Protocol.LocalTypeR

/-- `mkEnd` is observable. -/
lemma observable_mkEnd : ObservableC mkEnd := by
  apply ObservableC.is_end
  refine ⟨mkEnd, Relation.ReflTransGen.refl, ?_⟩
  simp [head_mkEnd]

/-- `mkVar` is observable as a variable. -/
lemma observable_mkVar (x : String) : ObservableC (mkVar x) := by
  apply ObservableC.is_var x
  refine ⟨mkVar x, Relation.ReflTransGen.refl, ?_⟩
  simp [head_mkVar]

/-- `mkSend` is observable as a send. -/
lemma observable_mkSend (p : String) (bs : List (RumpsteakV2.Protocol.GlobalType.Label × LocalTypeC)) :
    ObservableC (mkSend p bs) := by
  -- TODO: Fix label type mismatch after TypeContext refactoring
  sorry

/-- `mkRecv` is observable as a recv. -/
lemma observable_mkRecv (p : String) (bs : List (RumpsteakV2.Protocol.GlobalType.Label × LocalTypeC)) :
    ObservableC (mkRecv p bs) := by
  -- TODO: Fix label type mismatch after TypeContext refactoring
  sorry

/-- `mkEnd` is well-formed. -/
lemma wellFormed_mkEnd : WellFormedC mkEnd := by
  -- TODO: Fix after TypeContext refactoring
  sorry

/-- `mkVar` is not closed. -/
lemma not_closed_mkVar (x : String) : ¬ ClosedC (mkVar x) := by
  intro h
  have : UnfoldsToVarC (mkVar x) x := by
    refine ⟨mkVar x, Relation.ReflTransGen.refl, ?_⟩
    simp [head_mkVar]
  exact (h x) this

/-- Closedness preserved by `mkMu` if body is closed. -/
lemma closed_mkMu {x : String} {t : LocalTypeC} (hclosed : ClosedC t) : ClosedC (mkMu x t) := by
  -- TODO: Fix after TypeContext refactoring
  sorry

/-- Observability preserved by `mkMu` if body is observable. -/
lemma observable_mkMu {x : String} {t : LocalTypeC} (hobs : ObservableC t) :
    ObservableC (mkMu x t) := by
  -- TODO: Fix after TypeContext refactoring
  sorry

/-- WellFormed preserved by `mkMu`. -/
lemma wellFormed_mkMu {x : String} {t : LocalTypeC} (hWF : WellFormedC t) :
    WellFormedC (mkMu x t) :=
  ⟨closed_mkMu hWF.closed, observable_mkMu hWF.observable⟩

/-- toCoind preserves observability for inductive constructors. -/
lemma observable_toCoind : ∀ t : LocalTypeR, ObservableC (toCoind t)
  | .end => observable_mkEnd
  | .var x => observable_mkVar x
  | .mu x body => observable_mkMu (observable_toCoind body)
  | .send _ _ => by
      -- TODO: Fix label type mismatch after TypeContext refactoring
      sorry
  | .recv _ _ => by
      -- TODO: Fix label type mismatch after TypeContext refactoring
      sorry

end RumpsteakV2.Coinductive
