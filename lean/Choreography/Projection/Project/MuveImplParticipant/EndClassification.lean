import Choreography.Projection.Project.MuveImplParticipant.ParticipationCore

namespace Choreography.Projection.Project

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Project
open Choreography.Projection.Projectb
open SessionTypes.Participation
open SessionCoTypes.EQ2
open SessionCoTypes.EQ2Props

/-- Helper relation: closed muve types relate to .end (symmetric form). -/
private def ClosedMuveRelSym : LocalTypeR → LocalTypeR → Prop := fun a b =>
  isMuve a = true ∧ isClosed a = true ∧ b = .end

/-- Helper: ClosedMuveRelSym is a postfixpoint of EQ2F. -/
private theorem ClosedMuveRelSym_postfix :
    ∀ a b, ClosedMuveRelSym a b → EQ2F ClosedMuveRelSym a b := by
  intro a b ⟨hmuve_a, hclosed_a, hb⟩
  -- The relation forces b = .end, then EQ2F reduces by cases on a.
  subst hb
  cases a with
  | «end» => simp [EQ2F]
  | var _ =>
      -- A closed var is impossible, so EQ2F var/end is false.
      have : False := by
        simp [isClosed, LocalTypeR.freeVars] at hclosed_a
      exact this.elim
  | mu t body =>
      simp [EQ2F] at *
      have ⟨hmuve', hclosed'⟩ := closed_muve_substitute_mu t body hmuve_a hclosed_a
      exact ⟨hmuve', hclosed', rfl⟩
  | send _ _ => simp [isMuve] at hmuve_a
  | recv _ _ => simp [isMuve] at hmuve_a

/-- Helper: non-participant case for part_of2_or_end. -/
private theorem part_of2_or_end_nonpart (role : String) (g : GlobalType) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hwf : g.wellFormed = true)
    (hpart : ¬ part_of2 role g) :
    EQ2 lt .end := by
  have hmuve : isMuve lt = true :=
    CProject_muve_of_not_part_of2 g role lt hproj hpart hwf  -- use closed muve coinduction
  have hclosed : isClosed lt = true := CProject_closed_of_not_part_of2 g role lt hproj hpart hwf
  have hinR : ClosedMuveRelSym lt .end := ⟨hmuve, hclosed, rfl⟩
  exact EQ2_coind ClosedMuveRelSym_postfix lt .end hinR

/-- Classification: either participates or projects to EEnd. -/
theorem part_of2_or_end (role : String) (g : GlobalType) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hwf : g.wellFormed = true) :
    part_of_all2 role g ∨ EQ2 lt .end := by
  -- Case split on participation.
  by_cases hpart : part_of2 role g
  · left
    exact CProject_part_of2_implies_part_of_all2 g role lt hproj hpart hwf
  · right
    exact part_of2_or_end_nonpart role g lt hproj hwf hpart



end Choreography.Projection.Project
