import RumpsteakV2.Protocol.Projection.Projectb
import RumpsteakV2.Protocol.Projection.Project
import RumpsteakV2.Protocol.CoTypes.EQ2

/-
The Problem. Projection from global to local types is not unique: different
local types may project from the same global type. However, these projections
should be equivalent up to EQ2.

We must prove: if CProject g role e1 and CProject g role e2, then EQ2 e1 e2.
This establishes determinism modulo observational equivalence.

Solution Structure. Use CProject_implies_EQ2_trans to relate both e1 and e2
to trans g role, then compose via transitivity and symmetry.
-/

/-! # RumpsteakV2.Protocol.Projection.ProjectProps

Determinism properties for CProject (up to EQ2).
-/

namespace RumpsteakV2.Protocol.Projection.Projectb

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.CoTypes.EQ2

/-! ## Determinism Theorems -/

/-- Projection is deterministic up to EQ2 (assuming non-empty comm branches).

Uses CProject_implies_EQ2_trans twice and composes via EQ2 transitivity. -/
theorem project_deterministic {g : GlobalType} {role : String} {e1 e2 : LocalTypeR}
    (hp1 : CProject g role e1) (hp2 : CProject g role e2)
    (hne : g.allCommsNonEmpty = true) : EQ2 e1 e2 := by
  have h1 : EQ2 e1 (trans g role) :=
    RumpsteakV2.Protocol.Projection.Project.CProject_implies_EQ2_trans g role e1 hp1 hne
  have h2 : EQ2 e2 (trans g role) :=
    RumpsteakV2.Protocol.Projection.Project.CProject_implies_EQ2_trans g role e2 hp2 hne
  exact EQ2_trans h1 (EQ2_symm h2)

/-- Determinism for branch-wise projection up to EQ2 (assuming non-empty comm branches). -/
theorem branches_proj_deterministic {gbs : List (Label × GlobalType)} {role : String}
    {lbs1 lbs2 : List (Label × LocalTypeR)}
    (h1 : BranchesProjRel CProject gbs role lbs1)
    (h2 : BranchesProjRel CProject gbs role lbs2)
    (hne : GlobalType.allCommsNonEmptyBranches gbs = true) :
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
                      cases gb with
                      | mk l gcont =>
                          cases lb1 with
                          | mk l1 t1 =>
                              cases lb2 with
                              | mk l2 t2 =>
                                  rcases hpair1 with ⟨hlabel1, hcont1⟩
                                  rcases hpair2 with ⟨hlabel2, hcont2⟩
                                  have hne' : gcont.allCommsNonEmpty = true ∧
                                      GlobalType.allCommsNonEmptyBranches gbs' = true := by
                                    simpa [GlobalType.allCommsNonEmptyBranches] using hne
                                  have hcont_eq : EQ2 t1 t2 :=
                                    project_deterministic hcont1 hcont2 hne'.1
                                  have hlabel_eq : l1 = l2 := hlabel1.symm.trans hlabel2
                                  have htail_eq :=
                                    branches_proj_deterministic htail1 htail2 hne'.2
                                  cases hlabel_eq
                                  exact List.Forall₂.cons ⟨rfl, hcont_eq⟩ htail_eq

end RumpsteakV2.Protocol.Projection.Projectb
