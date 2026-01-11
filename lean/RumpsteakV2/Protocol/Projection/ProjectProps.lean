import RumpsteakV2.Protocol.Projection.Projectb

/-! # RumpsteakV2.Protocol.Projection.ProjectProps

Determinism properties for CProject.
-/

namespace RumpsteakV2.Protocol.Projection.Projectb

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR

mutual
  /-- Projection is deterministic (assuming non-empty comm branches). -/
  theorem project_deterministic {g : GlobalType} {role : String} {e1 e2 : LocalTypeR}
      (hp1 : CProject g role e1) (hp2 : CProject g role e2)
      (hne : g.allCommsNonEmpty = true) : e1 = e2 := by
    have h1F := CProject_destruct hp1
    have h2F := CProject_destruct hp2
    cases g with
    | «end» =>
        cases e1 with
        | «end» =>
            cases e2 with
            | «end» => rfl
            | _ =>
                simp [CProjectF] at h2F
        | _ =>
            simp [CProjectF] at h1F
    | var t =>
        cases e1 with
        | var t1 =>
            cases e2 with
            | var t2 =>
                simp [CProjectF] at h1F h2F
                subst h1F
                subst h2F
                rfl
            | _ =>
                simp [CProjectF] at h2F
        | _ =>
            simp [CProjectF] at h1F
    | mu t body =>
        cases e1 with
        | mu t1 body1 =>
            cases e2 with
            | mu t2 body2 =>
                simp [CProjectF] at h1F h2F
                rcases h1F with ⟨ht1, _, hbody1⟩
                rcases h2F with ⟨ht2, _, hbody2⟩
                subst ht1
                subst ht2
                have hne_body : body.allCommsNonEmpty = true := by
                  simpa [GlobalType.allCommsNonEmpty] using hne
                have hbody := project_deterministic hbody1 hbody2 hne_body
                simp [hbody]
            | _ =>
                simp [CProjectF] at h2F
        | _ =>
            simp [CProjectF] at h1F
    | comm sender receiver gbs =>
        have hne' : gbs.isEmpty = false ∧ GlobalType.allCommsNonEmptyBranches gbs = true := by
          simpa [GlobalType.allCommsNonEmpty, Bool.and_eq_true] using hne
        by_cases hs : role = sender
        · cases e1 with
          | send partner1 lbs1 =>
              cases e2 with
              | send partner2 lbs2 =>
                  simp [CProjectF, hs] at h1F h2F
                  rcases h1F with ⟨hpartner1, hbr1⟩
                  rcases h2F with ⟨hpartner2, hbr2⟩
                  subst hpartner1
                  subst hpartner2
                  have hbs := branches_proj_deterministic hbr1 hbr2 hne'.2
                  simp [hbs]
              | _ =>
                  simp [CProjectF, hs] at h2F
          | _ =>
              simp [CProjectF, hs] at h1F
        · by_cases hr : role = receiver
          · have hns : receiver ≠ sender := by
              intro hEq
              apply hs
              exact hr.trans hEq
            cases e1 with
            | recv partner1 lbs1 =>
                cases e2 with
                | recv partner2 lbs2 =>
                    simp [CProjectF, hr, hns] at h1F h2F
                    rcases h1F with ⟨hpartner1, hbr1⟩
                    rcases h2F with ⟨hpartner2, hbr2⟩
                    subst hpartner1
                    subst hpartner2
                    have hbs := branches_proj_deterministic hbr1 hbr2 hne'.2
                    simp [hbs]
                | _ =>
                    simp [CProjectF, hr, hns] at h2F
            | _ =>
                simp [CProjectF, hr, hns] at h1F
          · simp [CProjectF, hs, hr] at h1F h2F
            cases gbs with
            | nil =>
                -- contradict allCommsNonEmpty
                have : False := by
                  simpa using hne'.1
                cases this
            | cons gb rest =>
                have h1' := h1F gb (by simp)
                have h2' := h2F gb (by simp)
                have hne_br : gb.2.allCommsNonEmpty = true := by
                  have hne'' : gb.2.allCommsNonEmpty = true ∧
                      GlobalType.allCommsNonEmptyBranches rest = true := by
                    simpa [GlobalType.allCommsNonEmptyBranches] using hne'.2
                  exact hne''.1
                exact project_deterministic h1' h2' hne_br

  /-- Determinism for branch-wise projection (assuming non-empty comm branches). -/
  theorem branches_proj_deterministic {gbs : List (Label × GlobalType)} {role : String}
      {lbs1 lbs2 : List (Label × LocalTypeR)}
      (h1 : BranchesProjRel CProject gbs role lbs1)
      (h2 : BranchesProjRel CProject gbs role lbs2)
      (hne : GlobalType.allCommsNonEmptyBranches gbs = true) : lbs1 = lbs2 := by
    cases gbs with
    | nil =>
        cases h1
        cases h2
        rfl
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
                                    have hcont_eq := project_deterministic hcont1 hcont2 hne'.1
                                    have hlabel_eq : l1 = l2 := by
                                      exact hlabel1.symm.trans hlabel2
                                    have htail_eq :=
                                      branches_proj_deterministic htail1 htail2 hne'.2
                                    cases hlabel_eq
                                    cases hcont_eq
                                    simp [htail_eq]
end

end RumpsteakV2.Protocol.Projection.Projectb
