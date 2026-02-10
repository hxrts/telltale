import Mathlib
import SessionCoTypes.Coinductive.LocalTypeC
import SessionCoTypes.Coinductive.Observable
import SessionCoTypes.Coinductive.Bridge
import SessionTypes.LocalTypeR

set_option linter.dupNamespace false

/-! # Well-Formed Coinductive Types

Preservation lemmas for WellFormedC (closed + observable) property. -/

namespace SessionCoTypes.Coinductive

open SessionTypes.LocalTypeR

/-! ## Observability of Smart Constructors -/

/-- mkEnd is immediately observable as end. -/
lemma observable_mkEnd : ObservableC mkEnd := by
  apply ObservableC.is_end
  exact ⟨mkEnd, Relation.ReflTransGen.refl, by simp [head_mkEnd]⟩

/-- mkVar is observable as a variable (but not closed). -/
lemma observable_mkVar (x : String) : ObservableC (mkVar x) := by
  apply ObservableC.is_var x
  exact ⟨mkVar x, Relation.ReflTransGen.refl, by simp [head_mkVar]⟩

/-- mkSend is immediately observable as send. -/
lemma observable_mkSend (p : String) (bs : List (SessionTypes.GlobalType.Label × LocalTypeC)) :
    ObservableC (mkSend p bs) := by
  refine ObservableC.is_send p (branchesOf (mkSend p bs)) ?_
  exact ⟨mkSend p bs, bs.map Prod.fst, Relation.ReflTransGen.refl, by simp [head_mkSend], rfl⟩

/-- mkRecv is immediately observable as recv. -/
lemma observable_mkRecv (p : String) (bs : List (SessionTypes.GlobalType.Label × LocalTypeC)) :
    ObservableC (mkRecv p bs) := by
  refine ObservableC.is_recv p (branchesOf (mkRecv p bs)) ?_
  exact ⟨mkRecv p bs, bs.map Prod.fst, Relation.ReflTransGen.refl, by simp [head_mkRecv], rfl⟩

/-! ## Well-Formedness of End -/

/-- mkEnd is well-formed: closed (trivially) and observable. -/
lemma wellFormed_mkEnd : WellFormedC mkEnd := by
  refine ⟨?_, observable_mkEnd⟩
  intro v ⟨u, hsteps, hhead⟩
  cases Relation.ReflTransGen.cases_head hsteps with
  | inl heq => subst heq; simp [head_mkEnd] at hhead
  | inr hexists =>
      rcases hexists with ⟨y, ⟨x, f, hdest, _⟩, _⟩
      simp only [mkEnd, PFunctor.M.dest_mk] at hdest
      injection hdest with h1 _; cases h1

/-! ## Closedness -/

/-- mkVar is not closed: it unfolds to itself as a variable. -/
lemma not_closed_mkVar (x : String) : ¬ClosedC (mkVar x) := by
  intro h
  have : UnfoldsToVarC (mkVar x) x :=
    ⟨mkVar x, Relation.ReflTransGen.refl, by simp [head_mkVar]⟩
  exact h x this

/-- Closedness is preserved by mkMu if the body is closed.
    Any variable reachable from mkMu x t must be reachable from t. -/
lemma closed_mkMu {x : String} {t : LocalTypeC} (hclosed : ClosedC t) : ClosedC (mkMu x t) := by
  intro v ⟨u, hsteps, hhead⟩
  cases Relation.ReflTransGen.cases_head hsteps with
  | inl heq => subst heq; simp [head_mkMu] at hhead
  | inr hexists =>
      rcases hexists with ⟨y, ⟨x', f, hdest, rfl⟩, hrest⟩
      simp only [mkMu, PFunctor.M.dest_mk] at hdest
      injection hdest with h1 h2
      injection h1 with hx; subst hx
      have hfeq : f = fun _ => t := h2.symm
      simp only [hfeq] at hrest
      exact hclosed v ⟨u, hrest, hhead⟩

/-! ## Observability Preservation -/

/-- Observability is preserved by mkMu: unfold one step and use body's observability. -/
lemma observable_mkMu {x : String} {t : LocalTypeC} (hobs : ObservableC t) :
    ObservableC (mkMu x t) := by
  have hstep : UnfoldsC (mkMu x t) t := ⟨x, fun _ => t, by simp [mkMu], rfl⟩
  cases hobs with
  | is_end hend =>
      rcases hend with ⟨u, hsteps, hhead⟩
      exact ObservableC.is_end ⟨u, Relation.ReflTransGen.head hstep hsteps, hhead⟩
  | is_var v hvar =>
      rcases hvar with ⟨u, hsteps, hhead⟩
      exact ObservableC.is_var v ⟨u, Relation.ReflTransGen.head hstep hsteps, hhead⟩
  | is_send p bs hsend =>
      rcases hsend with ⟨u, labels, hsteps, hhead, hbs⟩
      exact ObservableC.is_send p bs ⟨u, labels, Relation.ReflTransGen.head hstep hsteps, hhead, hbs⟩
  | is_recv p bs hrecv =>
      rcases hrecv with ⟨u, labels, hsteps, hhead, hbs⟩
      exact ObservableC.is_recv p bs ⟨u, labels, Relation.ReflTransGen.head hstep hsteps, hhead, hbs⟩

/-- mkMu preserves well-formedness. -/
lemma wellFormed_mkMu {x : String} {t : LocalTypeC} (hWF : WellFormedC t) :
    WellFormedC (mkMu x t) :=
  ⟨closed_mkMu hWF.closed, observable_mkMu hWF.observable⟩

/-! ## toCoind Preserves Observability -/

/-- The toCoind embedding preserves observability for all inductive types. -/
lemma observable_toCoind : ∀ t : LocalTypeR, ObservableC (toCoind t)
  | .end       => observable_mkEnd
  | .var x     => observable_mkVar x
  | .mu x body => observable_mkMu (observable_toCoind body)
  | .send _ _  => by simpa [toCoind] using observable_mkSend _ _
  | .recv _ _  => by simpa [toCoind] using observable_mkRecv _ _

end SessionCoTypes.Coinductive
