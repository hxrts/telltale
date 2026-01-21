import RumpsteakV2.Protocol.Projection.Projectb
import RumpsteakV2.Protocol.Projection.Project
import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.CoTypes.EQ2Props

/-
The Problem. Projection from global to local types is not unique: different
local types may project from the same global type. However, these projections
should be equivalent up to EQ2.

We must prove: if CProject g role e1 and CProject g role e2, then EQ2 e1 e2.
This establishes determinism modulo observational equivalence.

Solution Structure. Use CProject_implies_EQ2_trans to relate both e1 and e2
to trans g role, then compose via WellFormed-gated transitivity and symmetry.
-/

/-! # RumpsteakV2.Protocol.Projection.ProjectProps

Determinism properties for CProject (up to EQ2).
-/

namespace RumpsteakV2.Protocol.Projection.Projectb

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.EQ2Props

/-! ## Determinism Theorems -/

/-- Projection is deterministic up to EQ2 (assuming well-formed global types).

Uses CProject_implies_EQ2_trans twice and composes via EQ2_trans_wf. -/
theorem project_deterministic {g : GlobalType} {role : String} {e1 e2 : LocalTypeR}
    (hp1 : CProject g role e1) (hp2 : CProject g role e2)
    (hwf : g.wellFormed = true) : EQ2 e1 e2 := by
  have hne : g.allCommsNonEmpty = true := by
    have hwf' := hwf
    simp [GlobalType.wellFormed, Bool.and_eq_true] at hwf'
    exact hwf'.1.1.2
  have htrans_eq : Trans.trans g role = e1 :=
    trans_eq_of_CProject g role e1 hp1 hne
  have htrans_eq2 : Trans.trans g role = e2 :=
    trans_eq_of_CProject g role e2 hp2 hne
  have hEq : e1 = e2 := by
    exact htrans_eq.symm.trans htrans_eq2
  subst hEq
  exact EQ2_refl _

/-- Helper: cons case for branches_proj_deterministic. -/
private theorem branches_proj_deterministic_cons
    (lb1 : Label × LocalTypeR) (lbs1' : List (Label × LocalTypeR))
    (lb2 : Label × LocalTypeR) (lbs2' : List (Label × LocalTypeR))
    (gb : Label × GlobalType) (gbs' : List (Label × GlobalType))
    {role : String}
    (hpair1 : gb.1 = lb1.1 ∧ CProject gb.2 role lb1.2)
    (htail1 : BranchesProjRel CProject gbs' role lbs1')
    (hpair2 : gb.1 = lb2.1 ∧ CProject gb.2 role lb2.2)
    (htail2 : BranchesProjRel CProject gbs' role lbs2')
    (hwf : ∀ gb' ∈ (gb :: gbs'), gb'.2.wellFormed = true)
    (branches_det : ∀ {lbs1 lbs2}, BranchesProjRel CProject gbs' role lbs1 →
      BranchesProjRel CProject gbs' role lbs2 →
      (∀ gb'' ∈ gbs', gb''.2.wellFormed = true) → BranchesRel EQ2 lbs1 lbs2) :
    BranchesRel EQ2 (lb1 :: lbs1') (lb2 :: lbs2') := by
  cases gb with
  | mk l gcont =>
      cases lb1 with
      | mk l1 t1 =>
          cases lb2 with
          | mk l2 t2 =>
              rcases hpair1 with ⟨hlabel1, hcont1⟩
              rcases hpair2 with ⟨hlabel2, hcont2⟩
              have hwf_head : gcont.wellFormed = true := hwf (l, gcont) (by simp)
              have hcont_eq : EQ2 t1 t2 := project_deterministic hcont1 hcont2 hwf_head
              have hlabel_eq : l1 = l2 := hlabel1.symm.trans hlabel2
              have hwf_tail : ∀ gb' ∈ gbs', gb'.2.wellFormed = true := by
                intro gb' hmem
                exact hwf gb' (by simp [hmem])
              have htail_eq := branches_det htail1 htail2 hwf_tail
              cases hlabel_eq
              exact List.Forall₂.cons ⟨rfl, hcont_eq⟩ htail_eq

/-- Determinism for branch-wise projection up to EQ2 (assuming well-formed branches). -/
theorem branches_proj_deterministic {gbs : List (Label × GlobalType)} {role : String}
    {lbs1 lbs2 : List (Label × LocalTypeR)}
    (h1 : BranchesProjRel CProject gbs role lbs1)
    (h2 : BranchesProjRel CProject gbs role lbs2)
    (hwf : ∀ gb ∈ gbs, gb.2.wellFormed = true) :
    BranchesRel EQ2 lbs1 lbs2 := by
  cases gbs with
  | nil =>
      cases h1
      cases h2
      exact List.Forall₂.nil
  | cons gb gbs' =>
      cases lbs1 with
      | nil => cases h1
      | cons lb1 lbs1' =>
          cases lbs2 with
          | nil => cases h2
          | cons lb2 lbs2' =>
              cases h1 with
              | cons hpair1 htail1 =>
                  cases h2 with
                  | cons hpair2 htail2 =>
                      exact branches_proj_deterministic_cons lb1 lbs1' lb2 lbs2' gb gbs'
                        hpair1 htail1 hpair2 htail2 hwf
                        (fun h1 h2 hwf' => branches_proj_deterministic h1 h2 hwf')

end RumpsteakV2.Protocol.Projection.Projectb
