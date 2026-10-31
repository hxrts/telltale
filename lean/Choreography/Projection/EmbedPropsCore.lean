import Choreography.Projection.Embed
import Choreography.Projection.DelegateFree
import Choreography.Projection.Projectb
import SessionTypes.Participation

/-! # Choreography.Projection.EmbedPropsCorennEmbedding determinism and embed/project roundtrip properties. Embedding existence lives in `Choreography.Projection.EmbedProps`. -/

/-
The Problem. Establish determinism and roundtrip laws for `CEmbed`/`CProject`.
Solution Structure. Use mutual induction over local types and branch lists for
determinism/roundtrip, then derive embedding existence for well-formed local
types under the usual self-communication exclusions.
-/

/-! # Choreography.Projection.EmbedProps

Determinism and round-trip properties for CEmbed/CProject.
-/

namespace Choreography.Projection.Embed

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Projectb
open SessionTypes.Participation

/-! ## Determinism

Embedding is deterministic: a local type embeds into at most one global type. -/

/-- Helper: determinism for end case. -/
private theorem embed_deterministic_end {role : String} {g1 g2 : GlobalType}
    (h1F : CEmbedF CEmbed LocalTypeR.end role g1)
    (h2F : CEmbedF CEmbed LocalTypeR.end role g2) : g1 = g2 := by
  cases g1 with
  | «end» =>
      cases g2 with
      | «end» => rfl
      | _ => simp [CEmbedF] at h2F
  | _ => simp [CEmbedF] at h1F

/-- Helper: determinism for var case. -/
private theorem embed_deterministic_var {t : String} {role : String} {g1 g2 : GlobalType}
    (h1F : CEmbedF CEmbed (LocalTypeR.var t) role g1)
    (h2F : CEmbedF CEmbed (LocalTypeR.var t) role g2) : g1 = g2 := by
  cases g1 with
  | var t1 =>
      cases g2 with
      | var t2 =>
          simp [CEmbedF] at h1F h2F
          subst h1F h2F
          rfl
      | _ => simp [CEmbedF] at h2F
  | _ => simp [CEmbedF] at h1F
-- Determinism Core
mutual
/-- Determinism for embedding: a local type embeds into at most one global type. -/
theorem embed_deterministic {e : LocalTypeR} {role : String} {g1 g2 : GlobalType}
     (h1 : CEmbed e role g1) (h2 : CEmbed e role g2) : g1 = g2 := by
  -- Reduce to the one-step generators and dispatch on constructors.
  have h1F := c_embed_destruct h1; have h2F := c_embed_destruct h2
  cases e with
  | «end» => exact embed_deterministic_end h1F h2F
  | var t => exact embed_deterministic_var h1F h2F
  | mu t body =>
      cases g1 with
      | mu t1 gbody1 =>
          cases g2 with
          | mu t2 gbody2 =>
              simp [CEmbedF] at h1F h2F
              rcases h1F with ⟨ht1, _, hbody1⟩; rcases h2F with ⟨ht2, _, hbody2⟩
              subst ht1 ht2
              simpa [embed_deterministic hbody1 hbody2]
          | _ => simp [CEmbedF] at h2F
      | _ => simp [CEmbedF] at h1F
  | send receiver lbs =>
      cases g1 with
      | comm sender1 receiver1 gbs1 =>
          cases g2 with
          | comm sender2 receiver2 gbs2 =>
              simp [CEmbedF] at h1F h2F
              rcases h1F with ⟨hrole1, _, hrecv1, hbr1⟩; rcases h2F with ⟨hrole2, _, hrecv2, hbr2⟩
              subst hrole1 hrole2 hrecv1 hrecv2
              simpa [branches_embed_deterministic hbr1 hbr2]
          | _ => simp [CEmbedF] at h2F
      | _ => simp [CEmbedF] at h1F
/- ## Structured Block 1 -/
  | recv sender lbs =>
      cases g1 with
      | comm sender1 receiver1 gbs1 =>
          cases g2 with
          | comm sender2 receiver2 gbs2 =>
              simp [CEmbedF] at h1F h2F
              rcases h1F with ⟨hrole1, _, hsend1, hbr1⟩; rcases h2F with ⟨hrole2, _, hsend2, hbr2⟩
              subst hrole1 hrole2 hsend1 hsend2
              simpa [branches_embed_deterministic hbr1 hbr2]
          | _ => simp [CEmbedF] at h2F
      | _ => simp [CEmbedF] at h1F
termination_by sizeOf e
decreasing_by
  all_goals
    subst_vars
    first
    | exact size_of_body_lt_size_of_mu _ _
    | exact size_of_branches_lt_size_of_send _ _
-- Determinism Branches
/-- Determinism for branch-wise embedding. -/
theorem branches_embed_deterministic {lbs : List BranchR} {role : String}
     {gbs1 gbs2 : List (Label × GlobalType)}
     (h1 : BranchesEmbedRel CEmbed lbs role gbs1)
     (h2 : BranchesEmbedRel CEmbed lbs role gbs2) : gbs1 = gbs2 := by
  -- Induct on gbs1/gbs2 with matching constructors.
  cases gbs1 with
  | nil => cases h1; cases gbs2 with | nil => rfl | cons _ _ => cases h2
  | cons gb1 gbs1' =>
      cases h1 with
      | cons hpair htail =>
          cases gbs2 with
          | nil => cases h2
          | cons gb2 gbs2' =>
              cases h2 with
              | cons hpair2 htail2 =>
                  cases gb1 with
                  | mk l1 g1 => cases gb2 with
                    | mk l2 g2 =>
                        rcases hpair with ⟨hlabel1, _hnone1, hcont1⟩
                        rcases hpair2 with ⟨hlabel2, _hnone2, hcont2⟩
                        have hlabel : l1 = l2 := hlabel1.symm.trans hlabel2
                        have hcont : g1 = g2 := embed_deterministic hcont1 hcont2
                        have htail_eq := branches_embed_deterministic htail htail2
                        cases hlabel; cases hcont; simp [htail_eq]
termination_by sizeOf lbs
decreasing_by
  all_goals
    subst_vars
    first
    | exact size_of_cont_lt_size_of_branches _ _ _ _
    | exact size_of_tail_lt_size_of_branches _ _
end

/-! ## Roundtrip Properties

Embedding and projection are inverses: embed then project yields the original local type. -/

/-- Helper: roundtrip for end case. -/
private theorem embed_project_roundtrip_end {role : String} {g : GlobalType} {e' : LocalTypeR}
    (hF : CEmbedF CEmbed LocalTypeR.end role g)
    (hP : CProjectF CProject g role e') : LocalTypeR.end = e' := by
  cases g with
  | «end» =>
      cases e' with
      | «end» => rfl
      | _ => simp [CProjectF] at hP
  | _ => simp [CEmbedF] at hF

/-- Helper: roundtrip for var case. -/
private theorem embed_project_roundtrip_var {t : String} {role : String} {g : GlobalType} {e' : LocalTypeR}
    (hF : CEmbedF CEmbed (LocalTypeR.var t) role g)
    (hP : CProjectF CProject g role e') : LocalTypeR.var t = e' := by
  cases g with
  | var t' =>
      cases e' with
      | var t'' =>
          simp [CEmbedF] at hF
          simp [CProjectF] at hP
          subst hF hP
          rfl
      | _ => simp [CProjectF] at hP
  | _ => simp [CEmbedF] at hF
-- Roundtrip Core
mutual
/-- Embed then project gives back the same local type. -/
theorem embed_project_roundtrip {e : LocalTypeR} {role : String} {g : GlobalType} {e' : LocalTypeR}
    (he : CEmbed e role g) (hp : CProject g role e') : e = e' := by
  have hF := c_embed_destruct he; have hP := c_project_destruct hp
  cases e with
  | «end» => exact embed_project_roundtrip_end hF hP
  | var t => exact embed_project_roundtrip_var hF hP
  | mu t body =>
      cases g with
      | mu t' gbody =>
          cases e' with
          | mu t'' body' =>
              simp [CEmbedF] at hF; rcases hF with ⟨ht1, hguard, hbody1⟩; subst ht1
              simp [CProjectF] at hP; rcases hP with ⟨hproj, hguard'⟩; rcases hguard' with ⟨_, ht''⟩; subst ht''
              simpa [embed_project_roundtrip hbody1 hproj]
          | «end» =>
              simp [CEmbedF] at hF; rcases hF with ⟨ht1, hguard, hbody1⟩; subst ht1
              simp [CProjectF] at hP; rcases hP with ⟨candBody, hproj, hguard_false⟩
              have heq := embed_project_roundtrip hbody1 hproj
              subst heq
              rw [hguard] at hguard_false
              cases hguard_false
          | _ => simp [CProjectF] at hP
      | _ => simp [CEmbedF] at hF
  | send receiver lbs =>
      cases g with
      | comm sender receiver' gbs =>
          simp [CEmbedF] at hF; rcases hF with ⟨hrole, _, hrecv, hbr⟩; subst hrole
          cases e' with
          | send receiver'' lbs' =>
/- ## Structured Block 2 -/
              simp [CProjectF] at hP; rcases hP with ⟨hrecv', hpr⟩; subst hrecv hrecv'
              simpa [branches_embed_project_roundtrip hbr hpr]
          | _ => simp [CProjectF] at hP
      | _ => simp [CEmbedF] at hF
  | recv sender lbs =>
      cases g with
      | comm sender' receiver gbs =>
          simp [CEmbedF] at hF; rcases hF with ⟨hrole, hneq, hsend, hbr⟩; subst hrole hsend
          have hneq' : role ≠ sender := by intro hrole'; exact hneq hrole'.symm
          cases e' with
          | recv sender'' lbs' =>
              simp [CProjectF, hneq'] at hP; rcases hP with ⟨hsend', hpr⟩; subst hsend'
              simpa [branches_embed_project_roundtrip hbr hpr]
          | _ => simp [CProjectF, hneq'] at hP
      | _ => simp [CEmbedF] at hF
termination_by sizeOf e
decreasing_by
  all_goals
    subst_vars
    first
    | exact size_of_body_lt_size_of_mu _ _
    | exact size_of_branches_lt_size_of_send _ _
-- Roundtrip Branches
/-- Embed/project roundtrip for branches. -/
theorem branches_embed_project_roundtrip {lbs : List BranchR} {role : String}
    {gbs : List (Label × GlobalType)} {lbs' : List BranchR}
    (hbr : BranchesEmbedRel CEmbed lbs role gbs)
    (hpr : BranchesProjRel CProject gbs role lbs') : lbs = lbs' := by
  -- Induct on branch lists.
  cases lbs with
  | nil => cases gbs with | nil => cases hbr; cases hpr; rfl | cons _ _ => cases hbr
  | cons lb lbs_tl =>
      cases gbs with
      | nil => cases hbr
      | cons gb gbs_tl =>
          cases hbr with
          | cons hpair htail =>
              cases lbs' with
              | nil => cases hpr
              | cons lb' lbs'_tl =>
                  cases hpr with
                  | cons hpair2 htail2 =>
                      rcases hpair with ⟨hl1, hvt1, hc1⟩
                      rcases hpair2 with ⟨hl2, hvt2, hc2⟩
                      have hcont_eq := embed_project_roundtrip hc1 hc2
                      have htail_eq := branches_embed_project_roundtrip htail htail2
                      have hl : lb.1 = lb'.1 := hl1.trans hl2
                      have hv : lb.2.1 = lb'.2.1 := hvt1.trans hvt2.symm
                      subst htail_eq
                      obtain ⟨a1, b1, c1⟩ := lb
                      obtain ⟨a2, b2, c2⟩ := lb'
                      simp only at hl hv hcont_eq
                      subst hl hv hcont_eq
                      rfl
termination_by sizeOf lbs
decreasing_by
/- ## Structured Block 3 -/
  all_goals
    subst_vars
    first
    | exact size_of_cont_lt_size_of_branches _ _ _ _
    | exact size_of_tail_lt_size_of_branches _ _
end

/-- Project then embed gives back the same global type (follows from determinism). -/
theorem project_embed_roundtrip {g g' : GlobalType} {role : String} {e : LocalTypeR}
    (_hp : CProject g role e) (he : CEmbed e role g) (he' : CEmbed e role g') : g = g' :=
  embed_deterministic he he'

end Choreography.Projection.Embed
