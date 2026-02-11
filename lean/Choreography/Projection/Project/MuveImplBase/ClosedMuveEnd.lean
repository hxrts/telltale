import Choreography.Projection.Project.MuveImplBase.MuveCore

namespace Choreography.Projection.Project

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Project
open Choreography.Projection.Projectb
open SessionTypes.Participation
open SessionCoTypes.EQ2
open SessionCoTypes.EQ2Props

/-- Relation for proving EQ2 .end X for closed muve types.
    ClosedMuveRel a b holds when a = .end and b is a closed muve type. -/
def ClosedMuveRel : LocalTypeR → LocalTypeR → Prop := fun a b =>
  a = .end ∧ isMuve b = true ∧ isClosed b = true

/-- Convert isClosed = true to freeVars = []. -/
theorem isClosed_eq_true_iff (lt : LocalTypeR) :
    isClosed lt = true ↔ lt.freeVars = [] := by
  simp only [isClosed, beq_iff_eq]

/-- For closed muve types, substituting into the body keeps it closed muve.
    This is key for the mu case of the coinduction proof. -/
theorem closed_muve_substitute_mu (t : String) (body : LocalTypeR)
    (hmuve : isMuve (.mu t body) = true)
    (hclosed : isClosed (.mu t body) = true) :
    isMuve (body.substitute t (.mu t body)) = true ∧
    isClosed (body.substitute t (.mu t body)) = true := by
  -- Convert isClosed hypothesis to freeVars = []
  have hclosed_eq : (.mu t body : LocalTypeR).freeVars = [] :=
    (isClosed_eq_true_iff _).mp hclosed
  constructor
  · -- muve preservation
    simp only [isMuve] at hmuve
    apply isMuve_substitute
    · exact hmuve
    · -- isMuve (.mu t body) requires isMuve body
      simp only [isMuve, hmuve]
  · -- closed preservation: use substitute_closed_when_only_var
    rw [isClosed_eq_true_iff]
    -- (.mu t body).freeVars = [] means body.freeVars.filter (· != t) = []
    -- This means all free vars in body are equal to t
    have hbody_fv : ∀ x, x ∈ body.freeVars → x = t := mu_closed_body_freeVars t body hclosed_eq
    -- (.mu t body).freeVars = [] since isClosed
    exact substitute_closed_when_only_var body t (.mu t body) hbody_fv hclosed_eq

/-- ClosedMuveRel is a post-fixpoint of EQ2F.
    This proves: if b is a closed muve type, then EQ2 .end b. -/
theorem ClosedMuveRel_postfix :
    ∀ a b, ClosedMuveRel a b → EQ2F ClosedMuveRel a b := by
  intro a b ⟨ha, hmuve, hclosed⟩
  subst ha  -- a = .end
  cases b with
  | «end» => simp only [EQ2F]  -- EQ2F _ .end .end = True
  | var t =>
      -- var has free vars, contradicts hclosed
      -- hclosed : isClosed (.var t) = true means ([t] == []) = true
      -- But [t] ≠ [], so this is false = true
      simp only [isClosed, LocalTypeR.freeVars, beq_iff_eq] at hclosed
      exact nomatch hclosed
  | mu t body =>
      -- EQ2F ClosedMuveRel .end (.mu t body) = ClosedMuveRel .end (body.substitute t (.mu t body))
      simp only [EQ2F]
      constructor
      · rfl
      · have ⟨hmuve', hclosed'⟩ := closed_muve_substitute_mu t body hmuve hclosed
        exact ⟨hmuve', hclosed'⟩
  | send _ _ => simp [isMuve] at hmuve
  | recv _ _ => simp [isMuve] at hmuve


end Choreography.Projection.Project
