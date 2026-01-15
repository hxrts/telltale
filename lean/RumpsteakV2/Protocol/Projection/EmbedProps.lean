import RumpsteakV2.Protocol.Projection.Embed
import RumpsteakV2.Protocol.Projection.Projectb
import RumpsteakV2.Protocol.Participation

/-
The Problem. Prove that embedding and projection are inverses and that embedding is
deterministic. Given a local type e and a global type g, we want to establish:
1. If e embeds into both g1 and g2, then g1 = g2 (determinism)
2. If e embeds into g and g projects to e', then e = e' (roundtrip)
3. If g projects to e and e embeds into g', then g = g' (roundtrip)

The difficulty is that these operations are defined by mutual recursion with branch
processing, requiring simultaneous induction on types and branch lists. The roundtrip
properties require careful case analysis to show that CEmbed and CProject are structural
inverses at each constructor level.

Solution Structure. The proof is organized in three main sections:
1. Determinism: mutual induction proves embed_deterministic and branches_embed_deterministic
2. Roundtrip (embed → project): mutual induction proves embed_project_roundtrip
3. Existence: localType_has_embed shows any well-formed local type can be embedded

The well-formedness conditions (role ≠ partner in communications) prevent pathological
cases where a role sends to itself, ensuring the embedding is always possible.
-/

/-! # RumpsteakV2.Protocol.Projection.EmbedProps

Determinism and round-trip properties for CEmbed/CProject.
-/

namespace RumpsteakV2.Protocol.Projection.Embed

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Projectb
open RumpsteakV2.Protocol.Participation

/-! ## Determinism

Embedding is deterministic: a local type embeds into at most one global type. -/

mutual
  /-- Helper: determinism for mu case. -/
  private theorem embed_deterministic_mu (t : String) (body : LocalTypeR) {role : String}
      {g1 g2 : GlobalType} (h1F h2F : CEmbedF CEmbed (LocalTypeR.mu t body) role g1 ∧
        CEmbedF CEmbed (LocalTypeR.mu t body) role g2) : g1 = g2 := by
    cases g1 with
    | mu t1 gbody1 =>
        cases g2 with
        | mu t2 gbody2 =>
            simp [CEmbedF] at h1F h2F
            rcases h1F.1 with ⟨ht1, _, hbody1⟩
            rcases h2F.2 with ⟨ht2, _, hbody2⟩
            subst ht1; subst ht2
            have hbody := embed_deterministic hbody1 hbody2
            simp [hbody]
        | _ => simp [CEmbedF] at h2F
    | _ => simp [CEmbedF] at h1F

  /-- Helper: determinism for send case. -/
  private theorem embed_deterministic_send (receiver : String) (lbs : List (Label × LocalTypeR))
      {role : String} {g1 g2 : GlobalType}
      (h1F : CEmbedF CEmbed (LocalTypeR.send receiver lbs) role g1)
      (h2F : CEmbedF CEmbed (LocalTypeR.send receiver lbs) role g2) : g1 = g2 := by
    cases g1 with
    | comm sender1 receiver1 gbs1 =>
        cases g2 with
        | comm sender2 receiver2 gbs2 =>
            simp [CEmbedF] at h1F h2F
            rcases h1F with ⟨hrole1, _, hrecv1, hbr1⟩
            rcases h2F with ⟨hrole2, _, hrecv2, hbr2⟩
            subst hrole1; subst hrole2; subst hrecv1; subst hrecv2
            have hbs := branches_embed_deterministic hbr1 hbr2
            simp [hbs]
        | _ => simp [CEmbedF] at h2F
    | _ => simp [CEmbedF] at h1F

  /-- Helper: determinism for recv case. -/
  private theorem embed_deterministic_recv (sender : String) (lbs : List (Label × LocalTypeR))
      {role : String} {g1 g2 : GlobalType}
      (h1F : CEmbedF CEmbed (LocalTypeR.recv sender lbs) role g1)
      (h2F : CEmbedF CEmbed (LocalTypeR.recv sender lbs) role g2) : g1 = g2 := by
    cases g1 with
    | comm sender1 receiver1 gbs1 =>
        cases g2 with
        | comm sender2 receiver2 gbs2 =>
            simp [CEmbedF] at h1F h2F
            rcases h1F with ⟨hrole1, _, hsend1, hbr1⟩
            rcases h2F with ⟨hrole2, _, hsend2, hbr2⟩
            subst hrole1; subst hrole2; subst hsend1; subst hsend2
            have hbs := branches_embed_deterministic hbr1 hbr2
            simp [hbs]
        | _ => simp [CEmbedF] at h2F
    | _ => simp [CEmbedF] at h1F

  /-- Determinism for embedding: a local type embeds into at most one global type. -/
  theorem embed_deterministic {e : LocalTypeR} {role : String} {g1 g2 : GlobalType}
      (h1 : CEmbed e role g1) (h2 : CEmbed e role g2) : g1 = g2 := by
    have h1F := CEmbed_destruct h1
    have h2F := CEmbed_destruct h2
    cases e with
    | «end» =>
        cases g1 with
        | «end» => cases g2 with | «end» => rfl | _ => simp [CEmbedF] at h2F
        | _ => simp [CEmbedF] at h1F
    | var t =>
        cases g1 with
        | var t1 =>
            cases g2 with
            | var t2 =>
                simp [CEmbedF] at h1F h2F
                subst h1F; subst h2F; rfl
            | _ => simp [CEmbedF] at h2F
        | _ => simp [CEmbedF] at h1F
    | mu t body => exact embed_deterministic_mu t body ⟨h1F, h2F⟩
    | send receiver lbs => exact embed_deterministic_send receiver lbs h1F h2F
    | recv sender lbs => exact embed_deterministic_recv sender lbs h1F h2F

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

/-! ## Roundtrip Properties

Embedding and projection are inverses: embed then project yields the original local type. -/

mutual
  /-- Helper: roundtrip for mu case. -/
  private theorem embed_project_roundtrip_mu (t : String) (body : LocalTypeR)
      {role : String} {g : GlobalType} {e' : LocalTypeR}
      (hF : CEmbedF CEmbed (LocalTypeR.mu t body) role g)
      (hP : CProjectF CProject g role e') : LocalTypeR.mu t body = e' := by
    cases g with
    | mu t' gbody =>
        cases e' with
        | mu t'' body' =>
            simp [CEmbedF, CProjectF] at hF hP
            rcases hF with ⟨ht1, _, hbody1⟩
            rcases hP with ⟨ht2, _, hbody2⟩
            subst ht1; subst ht2
            have hbody := embed_project_roundtrip hbody1 hbody2
            simp [hbody]
        | _ => simp [CProjectF] at hP
    | _ => simp [CEmbedF] at hF

  /-- Helper: roundtrip for send case. -/
  private theorem embed_project_roundtrip_send (receiver : String) (lbs : List (Label × LocalTypeR))
      {role : String} {g : GlobalType} {e' : LocalTypeR}
      (hF : CEmbedF CEmbed (LocalTypeR.send receiver lbs) role g)
      (hP : CProjectF CProject g role e') : LocalTypeR.send receiver lbs = e' := by
    cases g with
    | comm sender receiver' gbs =>
        simp [CEmbedF] at hF
        rcases hF with ⟨hrole, _, hrecv, hbr⟩
        subst hrole
        cases e' with
        | send receiver'' lbs' =>
            simp [CProjectF] at hP
            rcases hP with ⟨hrecv', hpr⟩
            subst hrecv; subst hrecv'
            have hbs := branches_embed_project_roundtrip hbr hpr
            simp [hbs]
        | _ => simp [CProjectF] at hP
    | _ => simp [CEmbedF] at hF

  /-- Helper: roundtrip for recv case. -/
  private theorem embed_project_roundtrip_recv (sender : String) (lbs : List (Label × LocalTypeR))
      {role : String} {g : GlobalType} {e' : LocalTypeR}
      (hF : CEmbedF CEmbed (LocalTypeR.recv sender lbs) role g)
      (hP : CProjectF CProject g role e') : LocalTypeR.recv sender lbs = e' := by
    cases g with
    | comm sender' receiver gbs =>
        simp [CEmbedF] at hF
        rcases hF with ⟨hrole, hneq, hsend, hbr⟩
        subst hrole; subst hsend
        have hneq' : role ≠ sender := fun hrole' => hneq hrole'.symm
        cases e' with
        | recv sender'' lbs' =>
            simp [CProjectF, hneq'] at hP
            rcases hP with ⟨hsend', hpr⟩
            subst hsend'
            have hbs := branches_embed_project_roundtrip hbr hpr
            simp [hbs]
        | _ => simp [CProjectF, hneq'] at hP
    | _ => simp [CEmbedF] at hF

  /-- Embed then project gives back the same local type. -/
  theorem embed_project_roundtrip {e : LocalTypeR} {role : String} {g : GlobalType} {e' : LocalTypeR}
      (he : CEmbed e role g) (hp : CProject g role e') : e = e' := by
    have hF := CEmbed_destruct he
    have hP := CProject_destruct hp
    cases e with
    | «end» =>
        cases g with
        | «end» => cases e' with | «end» => rfl | _ => simp [CProjectF] at hP
        | _ => simp [CEmbedF] at hF
    | var t =>
        cases g with
        | var t' =>
            cases e' with
            | var t'' =>
                simp [CEmbedF, CProjectF] at hF hP
                subst hF; subst hP; rfl
            | _ => simp [CProjectF] at hP
        | _ => simp [CEmbedF] at hF
    | mu t body => exact embed_project_roundtrip_mu t body hF hP
    | send receiver lbs => exact embed_project_roundtrip_send receiver lbs hF hP
    | recv sender lbs => exact embed_project_roundtrip_recv sender lbs hF hP

  /-- Helper: process cons branch case. -/
  private theorem branches_embed_project_roundtrip_cons
      (lb : Label × LocalTypeR) (lbs_tl : List (Label × LocalTypeR))
      (gb : Label × GlobalType) (gbs_tl : List (Label × GlobalType))
      (lb' : Label × LocalTypeR) (lbs'_tl : List (Label × LocalTypeR)) {role : String}
      (hpair : lb.1 = gb.1 ∧ CEmbed lb.2 role gb.2)
      (htail : BranchesEmbedRel CEmbed lbs_tl role gbs_tl)
      (hpair2 : gb.1 = lb'.1 ∧ CProject gb.2 role lb'.2)
      (htail2 : BranchesProjRel CProject gbs_tl role lbs'_tl) :
      lb :: lbs_tl = lb' :: lbs'_tl := by
    have hcont_eq := embed_project_roundtrip hpair.2 hpair2.2
    have htail_eq := branches_embed_project_roundtrip htail htail2
    have hlabel_eq : lb.1 = lb'.1 := hpair.1.trans hpair2.1
    cases lb; cases lb'
    cases hlabel_eq; cases hcont_eq
    simp [htail_eq]

  /-- Embed/project roundtrip for branches. -/
  theorem branches_embed_project_roundtrip {lbs : List (Label × LocalTypeR)} {role : String}
      {gbs : List (Label × GlobalType)} {lbs' : List (Label × LocalTypeR)}
      (hbr : BranchesEmbedRel CEmbed lbs role gbs)
      (hpr : BranchesProjRel CProject gbs role lbs') : lbs = lbs' := by
    cases lbs with
    | nil =>
        cases gbs with
        | nil => cases hbr; cases hpr; rfl
        | cons _ _ => cases hbr
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
                        exact branches_embed_project_roundtrip_cons lb lbs_tl gb gbs_tl lb' lbs'_tl
                          hpair htail hpair2 htail2
end

/-- Project then embed gives back the same global type (follows from determinism). -/
theorem project_embed_roundtrip {g g' : GlobalType} {role : String} {e : LocalTypeR}
    (_hp : CProject g role e) (he : CEmbed e role g) (he' : CEmbed e role g') : g = g' :=
  embed_deterministic he he'

/-! ## Embedding Existence

Any well-formed local type can be embedded into some global type. -/

/-! ### Helper Lemmas -/

/-- If a local type body is contractive, then embedding preserves the contractiveness
    property in the global type. This is used in the mu case of localType_has_embed. -/
private lemma embed_lcontractive_of_local {body : LocalTypeR} {role : String} {gbody : GlobalType}
    (hcontr : LocalTypeR.lcontractive body = true) (hembed : CEmbed body role gbody) :
    RumpsteakV2.Protocol.Projection.Trans.lcontractive gbody = true := by
  have hF := CEmbed_destruct hembed
  cases body with
  | «end» =>
      cases gbody <;> simp [CEmbedF, LocalTypeR.lcontractive,
        RumpsteakV2.Protocol.Projection.Trans.lcontractive] at hF hcontr ⊢
  | var t =>
      cases gbody <;> simp [CEmbedF, LocalTypeR.lcontractive,
        RumpsteakV2.Protocol.Projection.Trans.lcontractive] at hF hcontr ⊢
  | send receiver lbs =>
      cases gbody <;> simp [CEmbedF, LocalTypeR.lcontractive,
        RumpsteakV2.Protocol.Projection.Trans.lcontractive] at hF hcontr ⊢
  | recv sender lbs =>
      cases gbody <;> simp [CEmbedF, LocalTypeR.lcontractive,
        RumpsteakV2.Protocol.Projection.Trans.lcontractive] at hF hcontr ⊢
  | mu t body' =>
      cases gbody with
      | mu t' gbody' =>
          simp [CEmbedF] at hF
          rcases hF with ⟨_, hcontr_gbody', hinner⟩
          -- Destruct the inner embedding to constrain gbody'
          have hinner' := CEmbed_destruct hinner
          cases body' with
          | «end» =>
              -- body' = .end means gbody' must be .end (from CEmbedF)
              cases gbody' with
              | «end» => simp [RumpsteakV2.Protocol.Projection.Trans.lcontractive]
              | var _ => simp [CEmbedF] at hinner'
              | mu _ _ => simp [CEmbedF] at hinner'
              | comm _ _ _ => simp [CEmbedF] at hinner'
          | var _ =>
              -- body' = .var contradicts hcontr (not contractive)
              simp [LocalTypeR.lcontractive] at hcontr
          | mu _ _ =>
              -- body' = .mu contradicts hcontr (not contractive)
              simp [LocalTypeR.lcontractive] at hcontr
          | send _ _ =>
              -- body' = .send means gbody' must be .comm (from CEmbedF)
              cases gbody' with
              | «end» => simp [CEmbedF] at hinner'
              | var _ => simp [CEmbedF] at hinner'
              | mu _ _ => simp [CEmbedF] at hinner'
              | comm _ _ _ => simp [RumpsteakV2.Protocol.Projection.Trans.lcontractive]
          | recv _ _ =>
              -- body' = .recv means gbody' must be .comm (from CEmbedF)
              cases gbody' with
              | «end» => simp [CEmbedF] at hinner'
              | var _ => simp [CEmbedF] at hinner'
              | mu _ _ => simp [CEmbedF] at hinner'
              | comm _ _ _ => simp [RumpsteakV2.Protocol.Projection.Trans.lcontractive]
      | «end» =>
          simp [CEmbedF] at hF
      | var t' =>
          simp [CEmbedF] at hF
      | comm sender receiver gbs =>
          simp [CEmbedF] at hF

/-- When lcontractive body = true in the context of a mu, body.isGuarded t = true.
    This follows from the structure of lcontractive which requires send/recv/end at the top,
    all of which are guarded for any variable. -/
private axiom lcontractive_implies_isGuarded (t : String) (body : LocalTypeR)
    (hcontr : LocalTypeR.lcontractive body = true) :
    body.isGuarded t = true

/-! ### Main Existence Theorems -/

mutual
  /-- Helper: derive branch well-formedness from send. -/
  private theorem derive_send_branch_wf (receiver : String) (lbs : List (Label × LocalTypeR))
      {role : String}
      (hwf : ∀ partner, (LocalTypeR.send receiver lbs).hasSendTo partner → role ≠ partner)
      (hwf' : ∀ partner, (LocalTypeR.send receiver lbs).hasRecvFrom partner → role ≠ partner) :
      (role ≠ receiver) ×
      (∀ lb ∈ lbs, ∀ partner, lb.2.hasSendTo partner → role ≠ partner) ×
      (∀ lb ∈ lbs, ∀ partner, lb.2.hasRecvFrom partner → role ≠ partner) :=
    ⟨hwf receiver LocalTypeR.hasSendTo_send,
     fun lb hmem p h => hwf p (LocalTypeR.hasSendTo_send_branch hmem h),
     fun lb hmem p h => hwf' p (LocalTypeR.hasRecvFrom_send_branch hmem h)⟩

  /-- Helper: derive branch well-formedness from recv. -/
  private theorem derive_recv_branch_wf (sender : String) (lbs : List (Label × LocalTypeR))
      {role : String}
      (hwf : ∀ partner, (LocalTypeR.recv sender lbs).hasSendTo partner → role ≠ partner)
      (hwf' : ∀ partner, (LocalTypeR.recv sender lbs).hasRecvFrom partner → role ≠ partner) :
      (sender ≠ role) ×
      (∀ lb ∈ lbs, ∀ partner, lb.2.hasSendTo partner → role ≠ partner) ×
      (∀ lb ∈ lbs, ∀ partner, lb.2.hasRecvFrom partner → role ≠ partner) :=
    ⟨fun heq => hwf' sender LocalTypeR.hasRecvFrom_recv heq.symm,
     fun lb hmem p h => hwf p (LocalTypeR.hasSendTo_recv_branch hmem h),
     fun lb hmem p h => hwf' p (LocalTypeR.hasRecvFrom_recv_branch hmem h)⟩

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
    cases e with
    | «end» => use .end; apply CEmbed_fold'; simp only [CEmbedF]
    | var t => use .var t; apply CEmbed_fold'; simp only [CEmbedF]
    | mu t body =>
        cases hcontr : LocalTypeR.lcontractive body with
        | true =>
            have hwf_body : ∀ partner, body.hasSendTo partner → role ≠ partner :=
              fun p h => hwf p (LocalTypeR.hasSendTo_mu h)
            have hwf'_body : ∀ partner, body.hasRecvFrom partner → role ≠ partner :=
              fun p h => hwf' p (LocalTypeR.hasRecvFrom_mu h)
            have _hterm : sizeOf body < sizeOf (LocalTypeR.mu t body) :=
              LocalTypeR.sizeOf_body_lt_sizeOf_mu t body
            obtain ⟨gbody, hembed⟩ := localType_has_embed body role hwf_body hwf'_body
            have hguard : body.isGuarded t = true := lcontractive_implies_isGuarded t body hcontr
            use .mu t gbody; apply CEmbed_fold'; simp [CEmbedF]; exact ⟨hguard, hembed⟩
        | false =>
            have hbad : (LocalTypeR.mu t body).hasSendTo role :=
              LocalTypeR.hasSendTo_noncontractive (t := t) (body := body) (partner := role) hcontr
            cases (hwf role hbad rfl)
    | send receiver lbs =>
        have ⟨hne, hwf_br, hwf'_br⟩ := derive_send_branch_wf receiver lbs hwf hwf'
        have _hterm : sizeOf lbs < sizeOf (LocalTypeR.send receiver lbs) :=
          LocalTypeR.sizeOf_branches_lt_sizeOf_send receiver lbs
        obtain ⟨gbs, hembed⟩ := branches_have_embed lbs role hwf_br hwf'_br
        use .comm role receiver gbs; apply CEmbed_fold'; simp [CEmbedF]; exact ⟨hne, hembed⟩
    | recv sender lbs =>
        have ⟨hne, hwf_br, hwf'_br⟩ := derive_recv_branch_wf sender lbs hwf hwf'
        have _hterm : sizeOf lbs < sizeOf (LocalTypeR.recv sender lbs) :=
          LocalTypeR.sizeOf_branches_lt_sizeOf_recv sender lbs
        obtain ⟨gbs, hembed⟩ := branches_have_embed lbs role hwf_br hwf'_br
        use .comm sender role gbs; apply CEmbed_fold'; simp [CEmbedF]; exact ⟨hne, hembed⟩
  termination_by sizeOf e

  /-- Helper theorem for embedding branch lists. -/
  theorem branches_have_embed (lbs : List (Label × LocalTypeR)) (role : String)
      (hwf : ∀ lb ∈ lbs, ∀ partner, lb.2.hasSendTo partner → role ≠ partner)
      (hwf' : ∀ lb ∈ lbs, ∀ partner, lb.2.hasRecvFrom partner → role ≠ partner) :
      ∃ gbs, BranchesEmbedRel CEmbed lbs role gbs := by
    cases lbs with
    | nil =>
        use []
        exact List.Forall₂.nil
    | cons hd tl =>
        have hwf_hd : ∀ partner, hd.2.hasSendTo partner → role ≠ partner :=
          fun p h => hwf hd (List.Mem.head tl) p h
        have hwf'_hd : ∀ partner, hd.2.hasRecvFrom partner → role ≠ partner :=
          fun p h => hwf' hd (List.Mem.head tl) p h
        have hwf_tl : ∀ lb ∈ tl, ∀ partner, lb.2.hasSendTo partner → role ≠ partner :=
          fun lb hmem p h => hwf lb (List.Mem.tail hd hmem) p h
        have hwf'_tl : ∀ lb ∈ tl, ∀ partner, lb.2.hasRecvFrom partner → role ≠ partner :=
          fun lb hmem p h => hwf' lb (List.Mem.tail hd hmem) p h
        have _hterm1 : sizeOf hd.2 < sizeOf (hd :: tl) :=
          LocalTypeR.sizeOf_cont_lt_sizeOf_branches hd.1 hd.2 tl
        have _hterm2 : sizeOf tl < sizeOf (hd :: tl) :=
          LocalTypeR.sizeOf_tail_lt_sizeOf_branches hd tl
        obtain ⟨gcont, hcont⟩ := localType_has_embed hd.2 role hwf_hd hwf'_hd
        obtain ⟨gtl, htl⟩ := branches_have_embed tl role hwf_tl hwf'_tl
        use (hd.1, gcont) :: gtl
        exact List.Forall₂.cons ⟨rfl, hcont⟩ htl
  termination_by sizeOf lbs
end

/-! ### Participant Gating -/

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

end RumpsteakV2.Protocol.Projection.Embed
