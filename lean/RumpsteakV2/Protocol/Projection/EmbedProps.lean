import RumpsteakV2.Protocol.Projection.Embed
import RumpsteakV2.Protocol.Projection.Projectb

/-! # RumpsteakV2.Protocol.Projection.EmbedProps

Determinism and round-trip properties for CEmbed/CProject.
-/

namespace RumpsteakV2.Protocol.Projection.Embed

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Projectb

mutual
  /-- Determinism for embedding: a local type embeds into at most one global type. -/
  theorem embed_deterministic {e : LocalTypeR} {role : String} {g1 g2 : GlobalType}
      (h1 : CEmbed e role g1) (h2 : CEmbed e role g2) : g1 = g2 := by
    have h1F := CEmbed_destruct h1
    have h2F := CEmbed_destruct h2
    cases e with
    | «end» =>
        cases g1 with
        | «end» =>
            cases g2 with
            | «end» => rfl
            | _ =>
                simp [CEmbedF] at h2F
        | _ =>
            simp [CEmbedF] at h1F
    | var t =>
        cases g1 with
        | var t1 =>
            cases g2 with
            | var t2 =>
                simp [CEmbedF] at h1F
                simp [CEmbedF] at h2F
                subst h1F
                subst h2F
                rfl
            | _ =>
                simp [CEmbedF] at h2F
        | _ =>
            simp [CEmbedF] at h1F
    | mu t body =>
        cases g1 with
        | mu t1 gbody1 =>
            cases g2 with
            | mu t2 gbody2 =>
                simp [CEmbedF] at h1F
                simp [CEmbedF] at h2F
                rcases h1F with ⟨ht1, _, hbody1⟩
                rcases h2F with ⟨ht2, _, hbody2⟩
                subst ht1
                subst ht2
                have hbody := embed_deterministic hbody1 hbody2
                simp [hbody]
            | _ =>
                simp [CEmbedF] at h2F
        | _ =>
            simp [CEmbedF] at h1F
    | send receiver lbs =>
        cases g1 with
        | comm sender1 receiver1 gbs1 =>
            cases g2 with
            | comm sender2 receiver2 gbs2 =>
                simp [CEmbedF] at h1F
                simp [CEmbedF] at h2F
                rcases h1F with ⟨hrole1, _, hrecv1, hbr1⟩
                rcases h2F with ⟨hrole2, _, hrecv2, hbr2⟩
                subst hrole1
                subst hrole2
                subst hrecv1
                subst hrecv2
                have hbs := branches_embed_deterministic hbr1 hbr2
                simp [hbs]
            | _ =>
                simp [CEmbedF] at h2F
        | _ =>
            simp [CEmbedF] at h1F
    | recv sender lbs =>
        cases g1 with
        | comm sender1 receiver1 gbs1 =>
            cases g2 with
            | comm sender2 receiver2 gbs2 =>
                simp [CEmbedF] at h1F
                simp [CEmbedF] at h2F
                rcases h1F with ⟨hrole1, _, hsend1, hbr1⟩
                rcases h2F with ⟨hrole2, _, hsend2, hbr2⟩
                subst hrole1
                subst hrole2
                subst hsend1
                subst hsend2
                have hbs := branches_embed_deterministic hbr1 hbr2
                simp [hbs]
            | _ =>
                simp [CEmbedF] at h2F
        | _ =>
            simp [CEmbedF] at h1F

  /-- Determinism for branch-wise embedding. -/
  theorem branches_embed_deterministic {lbs : List (Label × LocalTypeR)} {role : String}
      {gbs1 gbs2 : List (Label × GlobalType)}
      (h1 : BranchesEmbedRel CEmbed lbs role gbs1)
      (h2 : BranchesEmbedRel CEmbed lbs role gbs2) : gbs1 = gbs2 := by
    cases gbs1 with
    | nil =>
        cases h1
        cases gbs2 with
        | nil => rfl
        | cons _ _ => cases h2
    | cons gb1 gbs1' =>
        cases h1 with
        | cons hpair htail =>
            cases gbs2 with
            | nil => cases h2
            | cons gb2 gbs2' =>
                cases h2 with
                | cons hpair2 htail2 =>
                    cases gb1 with
                    | mk l1 g1 =>
                        cases gb2 with
                        | mk l2 g2 =>
                            cases hpair with
                            | intro hlabel1 hcont1 =>
                                cases hpair2 with
                                | intro hlabel2 hcont2 =>
                                    have hlabel : l1 = l2 := by
                                      exact hlabel1.symm.trans hlabel2
                                    have hcont : g1 = g2 :=
                                      embed_deterministic hcont1 hcont2
                                    have htail_eq := branches_embed_deterministic htail htail2
                                    cases hlabel
                                    cases hcont
                                    simp [htail_eq]
end

mutual
  /-- Embed then project gives back the same local type. -/
  theorem embed_project_roundtrip {e : LocalTypeR} {role : String} {g : GlobalType} {e' : LocalTypeR}
      (he : CEmbed e role g) (hp : CProject g role e') : e = e' := by
    have hF := CEmbed_destruct he
    have hP := CProject_destruct hp
    cases e with
    | «end» =>
        cases g with
        | «end» =>
            cases e' with
            | «end» => rfl
            | _ =>
                simp [CProjectF] at hP
        | _ =>
            simp [CEmbedF] at hF
    | var t =>
        cases g with
        | var t' =>
            cases e' with
            | var t'' =>
                simp [CEmbedF] at hF
                simp [CProjectF] at hP
                subst hF
                subst hP
                rfl
            | _ =>
                simp [CProjectF] at hP
        | _ =>
            simp [CEmbedF] at hF
    | mu t body =>
        cases g with
        | mu t' gbody =>
            cases e' with
            | mu t'' body' =>
                simp [CEmbedF] at hF
                simp [CProjectF] at hP
                rcases hF with ⟨ht1, _, hbody1⟩
                rcases hP with ⟨ht2, _, hbody2⟩
                subst ht1
                subst ht2
                have hbody := embed_project_roundtrip hbody1 hbody2
                simp [hbody]
            | _ =>
                simp [CProjectF] at hP
        | _ =>
            simp [CEmbedF] at hF
    | send receiver lbs =>
        cases g with
        | comm sender receiver' gbs =>
            simp [CEmbedF] at hF
            rcases hF with ⟨hrole, _, hrecv, hbr⟩
            subst hrole
            cases e' with
            | send receiver'' lbs' =>
                simp [CProjectF] at hP
                rcases hP with ⟨hrecv', hpr⟩
                subst hrecv
                subst hrecv'
                have hbs := branches_embed_project_roundtrip hbr hpr
                simp [hbs]
            | _ =>
                simp [CProjectF] at hP
        | _ =>
            simp [CEmbedF] at hF
    | recv sender lbs =>
        cases g with
        | comm sender' receiver gbs =>
            simp [CEmbedF] at hF
            rcases hF with ⟨hrole, hneq, hsend, hbr⟩
            subst hrole
            subst hsend
            have hneq' : role ≠ sender := by
              intro hrole'
              exact hneq hrole'.symm
            cases e' with
            | recv sender'' lbs' =>
                simp [CProjectF, hneq'] at hP
                rcases hP with ⟨hsend', hpr⟩
                subst hsend'
                have hbs := branches_embed_project_roundtrip hbr hpr
                simp [hbs]
            | _ =>
                simp [CProjectF, hneq'] at hP
        | _ =>
            simp [CEmbedF] at hF

  /-- Embed/project roundtrip for branches. -/
  theorem branches_embed_project_roundtrip {lbs : List (Label × LocalTypeR)} {role : String}
      {gbs : List (Label × GlobalType)} {lbs' : List (Label × LocalTypeR)}
      (hbr : BranchesEmbedRel CEmbed lbs role gbs)
      (hpr : BranchesProjRel CProject gbs role lbs') : lbs = lbs' := by
    cases lbs with
    | nil =>
        cases gbs with
        | nil =>
            cases hbr
            cases hpr
            rfl
        | cons _ _ =>
            cases hbr
    | cons lb lbs_tl =>
        cases gbs with
        | nil =>
            cases hbr
        | cons gb gbs_tl =>
            cases hbr with
            | cons hpair htail =>
                cases lbs' with
                | nil =>
                    cases hpr
                | cons lb' lbs'_tl =>
                    cases hpr with
                    | cons hpair2 htail2 =>
                        cases gb with
                        | mk l gcont =>
                            cases hpair with
                            | intro hlabel hcont =>
                                cases hpair2 with
                                | intro hlabel' hproj =>
                                    have hcont_eq := embed_project_roundtrip hcont hproj
                                    have htail_eq := branches_embed_project_roundtrip htail htail2
                                    cases lb with
                                    | mk l1 t1 =>
                                        cases lb' with
                                        | mk l2 t2 =>
                                            have hlabel_eq : l1 = l2 := by
                                              exact hlabel.trans hlabel'
                                            cases hlabel_eq
                                            cases hcont_eq
                                            simp [htail_eq]
end

/-- Project then embed gives back the same global type (fixed form). -/
theorem project_embed_roundtrip {g g' : GlobalType} {role : String} {e : LocalTypeR}
    (_hp : CProject g role e) (he : CEmbed e role g) (he' : CEmbed e role g') : g = g' :=
  embed_deterministic he he'

end RumpsteakV2.Protocol.Projection.Embed
