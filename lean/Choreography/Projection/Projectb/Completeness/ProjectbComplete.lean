import Choreography.Projection.Projectb.Completeness.TransEq

/-! # Choreography.Projection.Projectb.Completeness.ProjectbComplete

Completeness lemmas for boolean checker `projectb`.
-/

/-
The Problem. After proving trans-equality from `CProject`, we still need to
show the executable checker accepts all relationally valid projections.

Solution Structure. Contains projectb-specific completeness helper lemmas and
the final completeness theorem.
-/

namespace Choreography.Projection.Projectb
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionTypes.Participation
open SessionCoTypes.CoinductiveRel

/-! ## Completeness Helpers -/

/-- Helper: branch projection for comm sender/receiver cases. -/
theorem projectbBranches_of_CProject_comm
    (gbs : List (Label × GlobalType)) (role : String) (lbs : List BranchR)
    (hbranches : BranchesProjRel CProject gbs role lbs)
    (ih : ∀ gb ∈ gbs, ∀ lb, CProject gb.2 role lb → projectb gb.2 role lb = true) :
    projectbBranches gbs role lbs = true := by
  -- Use branch relation and recurse on continuations.
  exact BranchesProjRel_to_projectbBranches gbs role lbs hbranches
    (fun gb hmem lb hcp => ih gb hmem lb hcp)

/-- Helper: all-branches projection for non-participants. -/
theorem projectbAllBranches_of_CProject_comm
    (gbs : List (Label × GlobalType)) (role : String) (cand : LocalTypeR)
    (hbranches : AllBranchesProj CProject gbs role cand)
    (ih : ∀ gb ∈ gbs, CProject gb.2 role cand → projectb gb.2 role cand = true) :
    projectbAllBranches gbs role cand = true := by
  -- Use all-branches relation and recurse on continuations.
  exact AllBranchesProj_to_projectbAllBranches gbs role cand hbranches
    (fun gb hmem hcp => ih gb hmem hcp)

/-! ## Completeness Helper Cases -/

/-- Helper: completeness for mu cases. -/
theorem projectb_complete_mu_case
    (t : String) (body : GlobalType) (role : String) (cand : LocalTypeR)
    (hproj : CProject (GlobalType.mu t body) role cand)
    (hne : (GlobalType.mu t body).allCommsNonEmpty = true)
    (ih : ∀ candBody, CProject body role candBody → projectb body role candBody = true) :
    projectb (GlobalType.mu t body) role cand = true := by
  -- Extract the body projection and reuse trans equality to pick the branch.
  have hF := CProject_destruct hproj
  simp [CProjectF] at hF
  rcases hF with ⟨candBody, hbody, hcase⟩
  have hne_body : body.allCommsNonEmpty = true := by
    simpa [GlobalType.allCommsNonEmpty] using hne
  have hproj_body : projectb body role candBody = true :=
    ih candBody hbody
  have htrans_body : Trans.trans body role = candBody :=
    trans_eq_of_CProject body role candBody hbody hne_body
  exact projectb_complete_mu t body role cand candBody hcase hproj_body htrans_body

/-! ## Completeness Helper Cases: Comm Participants -/

/-- Helper: completeness for comm sender cases. -/
theorem projectb_complete_comm_sender_case
    (s r role : String) (gbs : List (Label × GlobalType)) (cand : LocalTypeR)
    (hs : role = s) (hproj : CProject (.comm s r gbs) role cand)
    (_hne_branches : ∀ gb ∈ gbs, gb.2.allCommsNonEmpty = true)
    (ih : ∀ gb ∈ gbs, ∀ lb, CProject gb.2 role lb → projectb gb.2 role lb = true) :
    projectb (.comm s r gbs) role cand = true := by
  -- Sender roles must yield send candidates with branch-wise projections.
  have hF := CProject_destruct hproj
  simp [CProjectF, hs] at hF
  cases cand with
  | send partner lbs =>
      rcases hF with ⟨hpartner, hbranches⟩
      have hbranches_proj : projectbBranches gbs role lbs = true :=
        projectbBranches_of_CProject_comm gbs role lbs (by simpa [hs] using hbranches) ih
      exact projectb_complete_comm_sender s r role gbs partner lbs hs hpartner hbranches_proj
  | _ => cases hF

/-- Helper: completeness for comm receiver cases. -/
theorem projectb_complete_comm_receiver_case
    (s r role : String) (gbs : List (Label × GlobalType)) (cand : LocalTypeR)
    (hr : role = r) (hs : role ≠ s) (hproj : CProject (.comm s r gbs) role cand)
    (_hne_branches : ∀ gb ∈ gbs, gb.2.allCommsNonEmpty = true)
    (ih : ∀ gb ∈ gbs, ∀ lb, CProject gb.2 role lb → projectb gb.2 role lb = true) :
    projectb (.comm s r gbs) role cand = true := by
  -- Receiver roles must yield recv candidates with branch-wise projections.
  have hrs : r ≠ s := by simpa [hr] using hs
  have hF := CProject_destruct hproj
  simp [CProjectF, hr, hrs] at hF
  cases cand with
  | recv partner lbs =>
      rcases hF with ⟨hpartner, hbranches⟩
      have hbranches_proj : projectbBranches gbs role lbs = true :=
        projectbBranches_of_CProject_comm gbs role lbs (by simpa [hr] using hbranches) ih
      exact projectb_complete_comm_receiver s r role gbs partner lbs hr hs hpartner hbranches_proj
  | _ => cases hF

/-! ## Completeness Helper Cases: Comm Non-Participant -/

/-- Helper: completeness for comm non-participant cases. -/
theorem projectb_complete_comm_other_case
    (s r role : String) (gbs : List (Label × GlobalType)) (cand : LocalTypeR)
    (hs : role ≠ s) (hr : role ≠ r) (hproj : CProject (.comm s r gbs) role cand)
    (_hne_branches : ∀ gb ∈ gbs, gb.2.allCommsNonEmpty = true)
    (ih : ∀ gb ∈ gbs, CProject gb.2 role cand → projectb gb.2 role cand = true) :
    projectb (.comm s r gbs) role cand = true := by
  -- Non-participants must project all branches to the same candidate.
  have hF := CProject_destruct hproj
  simp [CProjectF, hs, hr] at hF
  have hbranches_proj : projectbAllBranches gbs role cand = true :=
    projectbAllBranches_of_CProject_comm gbs role cand hF ih
  exact projectb_complete_comm_other s r role gbs cand hs hr hbranches_proj

/-! ## Main Completeness Theorem -/

/-- Completeness: every CProject witness satisfies the boolean checker. -/
theorem projectb_complete (g : GlobalType) (role : String) (cand : LocalTypeR)
    (h : CProject g role cand) (hne : g.allCommsNonEmpty = true) :
    projectb g role cand = true := by
  -- Main recursion over the global constructor.
  cases g with
  | «end» => exact projectb_complete_end role cand h
  | var t => exact projectb_complete_var t role cand h
  | mu t body =>
      have hne_body : body.allCommsNonEmpty = true := by
        simpa [GlobalType.allCommsNonEmpty] using hne
      have ih_body : ∀ candBody, CProject body role candBody → projectb body role candBody = true :=
        fun candBody hbody => projectb_complete body role candBody hbody hne_body
      exact projectb_complete_mu_case t body role cand h hne ih_body
  -- projectb_complete: Comm Case
  | comm s r gbs =>
      have hne_branches : ∀ gb ∈ gbs, gb.2.allCommsNonEmpty = true :=
        GlobalType.allCommsNonEmpty_comm_branches _ _ gbs hne
      have ih_branches :
          ∀ gb ∈ gbs, ∀ lb, CProject gb.2 role lb → projectb gb.2 role lb = true :=
        fun gb hmem lb hcp => projectb_complete gb.2 role lb hcp (hne_branches gb hmem)
      have ih_all :
          ∀ gb ∈ gbs, CProject gb.2 role cand → projectb gb.2 role cand = true :=
        fun gb hmem hcp => projectb_complete gb.2 role cand hcp (hne_branches gb hmem)
      by_cases hs : role = s
      · exact projectb_complete_comm_sender_case s r role gbs cand hs h hne_branches ih_branches
      · by_cases hr : role = r
        · exact projectb_complete_comm_receiver_case s r role gbs cand hr hs h hne_branches ih_branches
        · exact projectb_complete_comm_other_case s r role gbs cand hs hr h hne_branches ih_all
  -- projectb_complete: Delegate Case
  | delegate p q sid r cont =>
      have hne_cont : cont.allCommsNonEmpty = true := by
        simpa [GlobalType.allCommsNonEmpty] using hne
      by_cases hp : role = p
      · have hf := CProject_destruct h
        cases cand with
        | send partner lbs =>
            cases lbs with
            | nil =>
                simp [CProjectF, hp] at hf
            | cons b bs =>
                cases bs with
                | nil =>
                    cases b with
                    | mk lbl rest =>
                        cases rest with
                        | mk vt contCand =>
                            simp [CProjectF, hp] at hf
                            rcases hf with ⟨hpartner, hlbl, hvt, hcont⟩
                            have hproj_cont : projectb cont role contCand = true := by
                              simpa [hp] using
                                (projectb_complete cont p contCand hcont hne_cont)
                            subst hpartner
                            subst hlbl
                            subst hvt
                            simp [projectb, hp]
                            refine And.intro ?_ (And.intro ?_ ?_)
                            · simp [reduceBEq]
                            · simp [reduceBEq]
                            · simpa [hp] using hproj_cont
                | cons b2 bs2 =>
                    simp [CProjectF, hp] at hf
        | recv _ _ =>
            simp [CProjectF, hp] at hf
        | «end» =>
            simp [CProjectF, hp] at hf
        | var _ =>
            simp [CProjectF, hp] at hf
        | mu _ _ =>
            simp [CProjectF, hp] at hf
      -- projectb_complete: Delegate Receiver/Other Subcases
      · by_cases hq : role = q
        · have hnp : q ≠ p := by
            intro hqp
            exact hp (hq.trans hqp)
          have hf := CProject_destruct h
          cases cand with
          | recv partner lbs =>
              cases lbs with
              | nil =>
                  simp [CProjectF, hq, hnp] at hf
              | cons b bs =>
                  cases bs with
                  | nil =>
                      cases b with
                      | mk lbl rest =>
                          cases rest with
                          | mk vt contCand =>
                              have hf' :
                                  partner = p ∧ lbl = ⟨"_delegate", .unit⟩ ∧
                                    vt = some (.chan sid r) ∧ CProject cont q contCand := by
                                simpa [CProjectF, hq, hnp] using hf
                              rcases hf' with ⟨hpartner, hlbl, hvt, hcont⟩
                              have hproj_cont : projectb cont role contCand = true := by
                                simpa [hq] using
                                  (projectb_complete cont q contCand hcont hne_cont)
                              subst hpartner
                              subst hlbl
                              subst hvt
                              simp [projectb, hq, hnp]
                              refine And.intro ?_ (And.intro ?_ ?_)
                              · simp [reduceBEq]
                              · simp [reduceBEq]
                              · simpa [hq] using hproj_cont
                  | cons b2 bs2 =>
                      simp [CProjectF, hq, hnp] at hf
          | send _ _ =>
              simp [CProjectF, hq, hnp] at hf
          | «end» =>
              simp [CProjectF, hq, hnp] at hf
          | var _ =>
              simp [CProjectF, hq, hnp] at hf
          | mu _ _ =>
              simp [CProjectF, hq, hnp] at hf
        -- projectb_complete: Delegate Non-Participant Subcase
        · -- non-participant: follow continuation
          have hf := CProject_destruct h
          simp [CProjectF, hp, hq] at hf
          have hproj_cont : projectb cont role cand = true :=
            projectb_complete cont role cand hf hne_cont
          have hpeq : (role == p) = false := beq_eq_false_iff_ne.mpr hp
          have hqeq : (role == q) = false := beq_eq_false_iff_ne.mpr hq
          unfold projectb
          simp [hpeq, hqeq, hproj_cont]
termination_by g
decreasing_by
  all_goals
    -- Now we have context like: hg : g = GlobalType... and hmem : gb ∈ gbs
    -- Use cases to match which termination goal we're in
    first
    -- mu case: sizeOf body < sizeOf g where g = GlobalType.mu t body
    | (subst_vars; exact sizeOf_body_lt_mu _ _)
    -- comm case: sizeOf gb.2 < sizeOf g where g = GlobalType.comm s r gbs and gb ∈ gbs
    | (subst_vars; apply sizeOf_elem_snd_lt_comm; assumption)
    -- delegate case: sizeOf cont < sizeOf g
    | (subst_vars; simp only [sizeOf, GlobalType._sizeOf_1]; omega)

/-! ## Completeness Corollary -/

/-- projectb = true iff CProject holds (for non-empty comms). -/
theorem projectb_iff_CProject (g : GlobalType) (role : String) (cand : LocalTypeR)
    (hne : g.allCommsNonEmpty = true) :
    projectb g role cand = true ↔ CProject g role cand :=
  ⟨projectb_sound g role cand, fun h => projectb_complete g role cand h hne⟩


end Choreography.Projection.Projectb
