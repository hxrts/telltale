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
  refine ObservableC.is_send p (branchesOf (mkSend p bs)) ?_
  refine ⟨mkSend p bs, bs.map Prod.fst, Relation.ReflTransGen.refl, ?_, rfl⟩
  simp [head_mkSend]

/-- `mkRecv` is observable as a recv. -/
lemma observable_mkRecv (p : String) (bs : List (RumpsteakV2.Protocol.GlobalType.Label × LocalTypeC)) :
    ObservableC (mkRecv p bs) := by
  refine ObservableC.is_recv p (branchesOf (mkRecv p bs)) ?_
  refine ⟨mkRecv p bs, bs.map Prod.fst, Relation.ReflTransGen.refl, ?_, rfl⟩
  simp [head_mkRecv]

/-- `mkEnd` is well-formed. -/
lemma wellFormed_mkEnd : WellFormedC mkEnd := by
  refine ⟨?_, observable_mkEnd⟩
  intro v hvar
  rcases hvar with ⟨u, hsteps, hhead⟩
  cases (Relation.ReflTransGen.cases_head hsteps) with
  | refl =>
      simp [head_mkEnd] at hhead
  | tail hstep _ =>
      rcases hstep with ⟨x, f, hdest, _⟩
      have hdest' :
          (⟨LocalTypeHead.end, fun x => PEmpty.elim x⟩ : LocalTypeF LocalTypeC) =
            ⟨LocalTypeHead.mu x, f⟩ := by
        simpa [mkEnd] using hdest
      cases hdest'

/-- `mkVar` is not closed. -/
lemma not_closed_mkVar (x : String) : ¬ ClosedC (mkVar x) := by
  intro h
  have : UnfoldsToVarC (mkVar x) x := by
    refine ⟨mkVar x, Relation.ReflTransGen.refl, ?_⟩
    simp [head_mkVar]
  exact (h x) this

/-- Closedness preserved by `mkMu` if body is closed. -/
lemma closed_mkMu {x : String} {t : LocalTypeC} (hclosed : ClosedC t) : ClosedC (mkMu x t) := by
  intro v hvar
  rcases hvar with ⟨u, hsteps, hhead⟩
  cases (Relation.ReflTransGen.cases_head hsteps) with
  | refl =>
      simp [head_mkMu] at hhead
  | tail hstep hrest =>
      rcases hstep with ⟨x', f, hdest, rfl⟩
      have hdest' :
          (⟨LocalTypeHead.mu x, fun _ => t⟩ : LocalTypeF LocalTypeC) =
            ⟨LocalTypeHead.mu x', f⟩ := by
        simpa [mkMu] using hdest
      cases hdest'
      have : UnfoldsToVarC t v := ⟨u, hrest, hhead⟩
      exact hclosed v this

/-- Observability preserved by `mkMu` if body is observable. -/
lemma observable_mkMu {x : String} {t : LocalTypeC} (hobs : ObservableC t) :
    ObservableC (mkMu x t) := by
  have hstep : UnfoldsC (mkMu x t) t := by
    refine ⟨x, fun _ => t, ?_, rfl⟩
    simp [mkMu]
  cases hobs with
  | is_end hend =>
      rcases hend with ⟨u, hsteps, hhead⟩
      apply ObservableC.is_end
      exact ⟨u, Relation.ReflTransGen.tail hstep hsteps, hhead⟩
  | is_var v hvar =>
      rcases hvar with ⟨u, hsteps, hhead⟩
      apply ObservableC.is_var v
      exact ⟨u, Relation.ReflTransGen.tail hstep hsteps, hhead⟩
  | is_send p bs hsend =>
      rcases hsend with ⟨u, labels, hsteps, hhead, hbs⟩
      apply ObservableC.is_send p bs
      exact ⟨u, labels, Relation.ReflTransGen.tail hstep hsteps, hhead, hbs⟩
  | is_recv p bs hrecv =>
      rcases hrecv with ⟨u, labels, hsteps, hhead, hbs⟩
      apply ObservableC.is_recv p bs
      exact ⟨u, labels, Relation.ReflTransGen.tail hstep hsteps, hhead, hbs⟩

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
      simpa [toCoind] using observable_mkSend _ _
  | .recv _ _ => by
      simpa [toCoind] using observable_mkRecv _ _

end RumpsteakV2.Coinductive
