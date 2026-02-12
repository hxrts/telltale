import Choreography.Projection.Embed
import Choreography.Projection.Projectb
import SessionTypes.Participation

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
/-! ## Determinism Core -/
mutual
/-- Determinism for embedding: a local type embeds into at most one global type. -/
theorem embed_deterministic {e : LocalTypeR} {role : String} {g1 g2 : GlobalType}
     (h1 : CEmbed e role g1) (h2 : CEmbed e role g2) : g1 = g2 := by
  -- Reduce to the one-step generators and dispatch on constructors.
  have h1F := CEmbed_destruct h1; have h2F := CEmbed_destruct h2
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
    | exact sizeOf_body_lt_sizeOf_mu _ _
    | exact sizeOf_branches_lt_sizeOf_send _ _
/-! ## Determinism Branches -/
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
    | exact sizeOf_cont_lt_sizeOf_branches _ _ _
    | exact sizeOf_tail_lt_sizeOf_branches _ _
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
/-! ## Roundtrip Core -/
mutual
/-- Embed then project gives back the same local type. -/
theorem embed_project_roundtrip {e : LocalTypeR} {role : String} {g : GlobalType} {e' : LocalTypeR}
    (he : CEmbed e role g) (hp : CProject g role e') : e = e' := by
  have hF := CEmbed_destruct he; have hP := CProject_destruct hp
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
              have : False := by simpa [embed_project_roundtrip hbody1 hproj, hguard] using hguard_false
              exact this.elim
          | _ => simp [CProjectF] at hP
      | _ => simp [CEmbedF] at hF
  | send receiver lbs =>
      cases g with
      | comm sender receiver' gbs =>
          simp [CEmbedF] at hF; rcases hF with ⟨hrole, _, hrecv, hbr⟩; subst hrole
          cases e' with
          | send receiver'' lbs' =>
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
    | exact sizeOf_body_lt_sizeOf_mu _ _
    | exact sizeOf_branches_lt_sizeOf_send _ _
/-! ## Roundtrip Branches -/
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
                      cases gb with
                      | mk l gcont => cases lb with
                        | mk l1 t1 => cases lb' with
                          | mk l2 t2 =>
                              have hlabel : l1 = l2 := by exact hpair.1.trans hpair2.1
                              cases hlabel
                              have hcont_eq := embed_project_roundtrip hpair.2.2 hpair2.2.2
                              have htail_eq := branches_embed_project_roundtrip htail htail2
                              cases hcont_eq; simp [htail_eq]
termination_by sizeOf lbs
decreasing_by
  all_goals
    subst_vars
    first
    | exact sizeOf_cont_lt_sizeOf_branches _ _ _
    | exact sizeOf_tail_lt_sizeOf_branches _ _
end

/-- Project then embed gives back the same global type (follows from determinism). -/
theorem project_embed_roundtrip {g g' : GlobalType} {role : String} {e : LocalTypeR}
    (_hp : CProject g role e) (he : CEmbed e role g) (he' : CEmbed e role g') : g = g' :=
  embed_deterministic he he'

/-! ## Embedding Existence

Any well-formed local type can be embedded into some global type. -/

/-! ## Helper Lemmas -/

/-- Helper: contractiveness for mu case of embed_lcontractive_of_local. -/
private lemma embed_lcontractive_mu_case {t : String} {body' : LocalTypeR}
    {role : String} {t' : String} {gbody' : GlobalType}
    (hcontr : LocalTypeR.lcontractive (LocalTypeR.mu t body') = true)
    (hinner' : CEmbedF CEmbed body' role gbody') :
    Choreography.Projection.Project.lcontractive (GlobalType.mu t' gbody') = true := by
  cases body' with
  | «end» =>
      cases gbody' with
      | «end» => simp [Choreography.Projection.Project.lcontractive]
      | var _ => simp [CEmbedF] at hinner'
      | mu _ _ => simp [CEmbedF] at hinner'
      | comm _ _ _ => simp [CEmbedF] at hinner'
  | var _ => simp [LocalTypeR.lcontractive] at hcontr
  | mu _ _ => simp [LocalTypeR.lcontractive] at hcontr
  | send _ _ =>
      cases gbody' with
      | «end» => simp [CEmbedF] at hinner'
      | var _ => simp [CEmbedF] at hinner'
      | mu _ _ => simp [CEmbedF] at hinner'
      | comm _ _ _ => simp [Choreography.Projection.Project.lcontractive]
  | recv _ _ =>
      cases gbody' with
      | «end» => simp [CEmbedF] at hinner'
      | var _ => simp [CEmbedF] at hinner'
      | mu _ _ => simp [CEmbedF] at hinner'
      | comm _ _ _ => simp [Choreography.Projection.Project.lcontractive]

/-- If a local type body is contractive, then embedding preserves the contractiveness
    property in the global type. This is used in the mu case of localType_has_embed. -/
/-! ## Embedding Existence Helpers: Contractiveness Lift -/
private lemma embed_lcontractive_of_local {body : LocalTypeR} {role : String} {gbody : GlobalType}
    (hcontr : LocalTypeR.lcontractive body = true) (hembed : CEmbed body role gbody) :
    Choreography.Projection.Project.lcontractive gbody = true := by
  -- Destructure the embedding by cases on body/gbody.
  have hF := CEmbed_destruct hembed
  cases body with
  | mu t body' =>
      cases gbody with
      | mu t' gbody' =>
          simp [CEmbedF] at hF
          rcases hF with ⟨_, _, hinner⟩
          have hinner' := CEmbed_destruct hinner
          exact embed_lcontractive_mu_case hcontr hinner'
      | «end» | var _ | comm _ _ _ =>
          simp [CEmbedF] at hF
  | «end» | var _ | send _ _ | recv _ _ =>
      cases gbody <;>
        simp [CEmbedF, LocalTypeR.lcontractive,
          Choreography.Projection.Project.lcontractive] at hF hcontr ⊢

/-- When lcontractive body = true in the context of a mu, body.isGuarded t = true.
    This follows from the structure of lcontractive which requires send/recv/end at the top,
    all of which are guarded for any variable. -/
/-! ## Embedding Existence Helpers: Guardedness from Contractiveness -/
private theorem lcontractive_implies_isGuarded (t : String) (body : LocalTypeR)
    (hcontr : LocalTypeR.lcontractive body = true) :
    body.isGuarded t = true := by
  cases body with
  | «end» =>
      simp [LocalTypeR.isGuarded]
  | var w =>
      simp [LocalTypeR.lcontractive] at hcontr
  | send p bs =>
      simp [LocalTypeR.isGuarded]
  | recv p bs =>
      simp [LocalTypeR.isGuarded]
  | mu s inner =>
      cases inner with
      | «end» =>
          simp [LocalTypeR.lcontractive, LocalTypeR.isGuarded] at hcontr ⊢
      | var w =>
          simp [LocalTypeR.lcontractive] at hcontr
      | send p bs =>
          simp [LocalTypeR.lcontractive, LocalTypeR.isGuarded] at hcontr ⊢
      | recv p bs =>
          simp [LocalTypeR.lcontractive, LocalTypeR.isGuarded] at hcontr ⊢
      | mu s' inner' =>
          simp [LocalTypeR.lcontractive] at hcontr

/-! ## Main Existence Theorems -/

/-- Helper: derive branch well-formedness for send from parent well-formedness. -/
private def derive_send_branch_wf (receiver : String) (lbs : List BranchR) (role : String)
    (hwf : ∀ partner, (LocalTypeR.send receiver lbs).hasSendTo partner → role ≠ partner)
    (hwf' : ∀ partner, (LocalTypeR.send receiver lbs).hasRecvFrom partner → role ≠ partner) :
    (∀ lb ∈ lbs, ∀ partner, lb.2.2.hasSendTo partner → role ≠ partner) ∧
    (∀ lb ∈ lbs, ∀ partner, lb.2.2.hasRecvFrom partner → role ≠ partner) :=
  ⟨fun _ hmem partner hsend => hwf partner (LocalTypeR.hasSendTo_send_branch hmem hsend),
   fun _ hmem partner hrecv => hwf' partner (LocalTypeR.hasRecvFrom_send_branch hmem hrecv)⟩

/-- Helper: derive branch well-formedness for recv from parent well-formedness. -/
private def derive_recv_branch_wf (sender : String) (lbs : List BranchR) (role : String)
    (hwf : ∀ partner, (LocalTypeR.recv sender lbs).hasSendTo partner → role ≠ partner)
    (hwf' : ∀ partner, (LocalTypeR.recv sender lbs).hasRecvFrom partner → role ≠ partner) :
    (∀ lb ∈ lbs, ∀ partner, lb.2.2.hasSendTo partner → role ≠ partner) ∧
    (∀ lb ∈ lbs, ∀ partner, lb.2.2.hasRecvFrom partner → role ≠ partner) :=
  ⟨fun _ hmem partner hsend => hwf partner (LocalTypeR.hasSendTo_recv_branch hmem hsend),
   fun _ hmem partner hrecv => hwf' partner (LocalTypeR.hasRecvFrom_recv_branch hmem hrecv)⟩

mutual
/-- Any well-formed local type can be embedded into some global type.

    The well-formedness conditions ensure that:
    - The role never sends to itself
    - The role never receives from itself

    This proof proceeds by structural recursion on the local type, with mutual
    induction handling branch lists. -/
theorem localType_has_embed (e : LocalTypeR) (role : String)
    (hwf : ∀ partner, e.hasSendTo partner → role ≠ partner)
    (hwf' : ∀ partner, e.hasRecvFrom partner → role ≠ partner) :
    ∃ g, CEmbed e role g := by
  -- Dispatch by constructor and recurse on substructures.
  cases e with
  | «end» =>
      refine ⟨.end, ?_⟩
      apply CEmbed_fold'
      simp [CEmbedF]
  | var t =>
      refine ⟨.var t, ?_⟩
      apply CEmbed_fold'
      simp [CEmbedF]
  | mu t body =>
      cases hcontr : LocalTypeR.lcontractive body with
      | true =>
          have hwf_body : ∀ partner, body.hasSendTo partner → role ≠ partner := by
            intro partner hsend
            exact hwf partner (LocalTypeR.hasSendTo_mu hsend)
          have hwf'_body : ∀ partner, body.hasRecvFrom partner → role ≠ partner := by
            intro partner hrecv
            exact hwf' partner (LocalTypeR.hasRecvFrom_mu hrecv)
          obtain ⟨gbody, hembed⟩ := localType_has_embed body role hwf_body hwf'_body
          have hguard : body.isGuarded t = true := lcontractive_implies_isGuarded t body hcontr
          refine ⟨.mu t gbody, ?_⟩
          apply CEmbed_fold'
          simp [CEmbedF]
          exact ⟨hguard, hembed⟩
      | false =>
          have hbad : (LocalTypeR.mu t body).hasSendTo role :=
            LocalTypeR.hasSendTo_noncontractive (t := t) (body := body) (partner := role) hcontr
          have : False := (hwf role hbad) rfl
          exact this.elim
  | send receiver lbs =>
      have hne : role ≠ receiver := hwf receiver LocalTypeR.hasSendTo_send
      have ⟨hwf_branches, hwf'_branches⟩ := derive_send_branch_wf receiver lbs role hwf hwf'
      obtain ⟨gbs, hembed⟩ := branches_have_embed lbs role hwf_branches hwf'_branches
      refine ⟨.comm role receiver gbs, ?_⟩
      apply CEmbed_fold'
      simp [CEmbedF]
      exact ⟨hne, hembed⟩
  | recv sender lbs =>
      have hne : sender ≠ role := by
        intro heq
        apply hwf' sender LocalTypeR.hasRecvFrom_recv
        exact heq.symm
      have ⟨hwf_branches, hwf'_branches⟩ := derive_recv_branch_wf sender lbs role hwf hwf'
      obtain ⟨gbs, hembed⟩ := branches_have_embed lbs role hwf_branches hwf'_branches
      refine ⟨.comm sender role gbs, ?_⟩
      apply CEmbed_fold'
      simp [CEmbedF]
      exact ⟨hne, hembed⟩
termination_by sizeOf e
decreasing_by
  all_goals
    subst_vars
    first
    | exact sizeOf_body_lt_sizeOf_mu _ _
    | exact sizeOf_branches_lt_sizeOf_send _ _

/-- Helper theorem for embedding branch lists. -/
theorem branches_have_embed (lbs : List BranchR) (role : String)
    (hwf : ∀ lb ∈ lbs, ∀ partner, lb.2.2.hasSendTo partner → role ≠ partner)
    (hwf' : ∀ lb ∈ lbs, ∀ partner, lb.2.2.hasRecvFrom partner → role ≠ partner) :
    ∃ gbs, BranchesEmbedRel CEmbed lbs role gbs := by
  -- Structural recursion on the branch list.
  cases lbs with
  | nil => exact ⟨[], List.Forall₂.nil⟩
  | cons hd tl =>
      have hwf_hd : ∀ partner, hd.2.2.hasSendTo partner → role ≠ partner :=
        fun p h => hwf hd (List.Mem.head tl) p h
      have hwf'_hd : ∀ partner, hd.2.2.hasRecvFrom partner → role ≠ partner :=
        fun p h => hwf' hd (List.Mem.head tl) p h
      have hwf_tl : ∀ lb ∈ tl, ∀ partner, lb.2.2.hasSendTo partner → role ≠ partner :=
        fun lb hmem p h => hwf lb (List.Mem.tail hd hmem) p h
      have hwf'_tl : ∀ lb ∈ tl, ∀ partner, lb.2.2.hasRecvFrom partner → role ≠ partner :=
        fun lb hmem p h => hwf' lb (List.Mem.tail hd hmem) p h
      obtain ⟨gcont, hcont⟩ := localType_has_embed hd.2.2 role hwf_hd hwf'_hd
      obtain ⟨gtl, htl⟩ := branches_have_embed tl role hwf_tl hwf'_tl
      refine ⟨(hd.1, gcont) :: gtl, ?_⟩
      exact List.Forall₂.cons ⟨rfl, hcont⟩ htl
termination_by sizeOf lbs
decreasing_by
  all_goals
    subst_vars
    first
    | exact sizeOf_cont_lt_sizeOf_branches _ _ _
    | exact sizeOf_tail_lt_sizeOf_branches _ _
end

/-! ## Participant Gating -/

/-- If a role participates in a global type and we can project, some embedding exists.
    This is the existential form used for participant gating.

    The proof proceeds by induction on participation:
    - Direct participation (role = sender/receiver): use localType_has_embed
    - Transitive participation (role in branch): use IH on participating branch
    - Mu: use IH on body -/
theorem CProject_has_CEmbed_participant {g : GlobalType} {role : String} {e : LocalTypeR}
    (_hproj : CProject g role e) (_hpart : part_of2 role g)
    (hwf : ∀ partner, e.hasSendTo partner → role ≠ partner)
    (hwf' : ∀ partner, e.hasRecvFrom partner → role ≠ partner) : ∃ g', CEmbed e role g' := by
  exact localType_has_embed e role hwf hwf'

end Choreography.Projection.Embed
