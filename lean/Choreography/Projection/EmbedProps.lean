import Choreography.Projection.Embed
import Choreography.Projection.DelegateFree
import Choreography.Projection.Projectb
import SessionTypes.Participation
import Choreography.Projection.EmbedPropsCore


namespace Choreography.Projection.Embed
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Projectb
open SessionTypes.Participation

/-! ## Embedding Existence

Any well-formed local type can be embedded into some global type. -/

-- Helper Lemmas

/-- Helper: contractiveness for mu case of embed_lcontractive_of_local. -/
private lemma embed_lcontractive_mu_case {t : String} {body' : LocalTypeR}
    {role : String} {t' : String} {gbody' : GlobalType}
    (hcontr : LocalTypeR.lcontractive (LocalTypeR.mu t body') = true)
    (hinner' : CEmbedF CEmbed body' role gbody') :
    Choreography.Projection.Trans.lcontractive (GlobalType.mu t' gbody') = true := by
  cases body' with
  | «end» =>
      cases gbody' with
      | «end» => simp [Choreography.Projection.Trans.lcontractive]
      | var _ => simp [CEmbedF] at hinner'
      | mu _ _ => simp [CEmbedF] at hinner'
      | comm _ _ _ => simp [CEmbedF] at hinner'
      | delegate _ _ _ _ _ => simp [CEmbedF] at hinner'
  | var _ => simp [LocalTypeR.lcontractive] at hcontr
  | mu _ _ => simp [LocalTypeR.lcontractive] at hcontr
  | send _ _ =>
      cases gbody' with
      | «end» => simp [CEmbedF] at hinner'
      | var _ => simp [CEmbedF] at hinner'
      | mu _ _ => simp [CEmbedF] at hinner'
      | comm _ _ _ => simp [Choreography.Projection.Trans.lcontractive]
      | delegate _ _ _ _ _ => simp [CEmbedF] at hinner'
  | recv _ _ =>
      cases gbody' with
      | «end» => simp [CEmbedF] at hinner'
      | var _ => simp [CEmbedF] at hinner'
      | mu _ _ => simp [CEmbedF] at hinner'
      | comm _ _ _ => simp [Choreography.Projection.Trans.lcontractive]
      | delegate _ _ _ _ _ => simp [CEmbedF] at hinner'

/-- If a local type body is contractive, then embedding preserves the contractiveness
    property in the global type. This is used in the mu case of local_type_has_embed. -/
-- Embedding Existence Helpers: Contractiveness Lift
private lemma embed_lcontractive_of_local {body : LocalTypeR} {role : String} {gbody : GlobalType}
    (hcontr : LocalTypeR.lcontractive body = true) (hembed : CEmbed body role gbody) :
    Choreography.Projection.Trans.lcontractive gbody = true := by
  -- Destructure the embedding by cases on body/gbody.
  have hF := c_embed_destruct hembed
  cases body with
  | mu t body' =>
      cases gbody with
      | mu t' gbody' =>
          simp [CEmbedF] at hF
          rcases hF with ⟨_, _, hinner⟩
          have hinner' := c_embed_destruct hinner
          exact embed_lcontractive_mu_case hcontr hinner'
      | «end» | var _ | comm _ _ _ | delegate _ _ _ _ _ =>
          simp [CEmbedF] at hF
  | «end» | var _ | send _ _ | recv _ _ =>
      cases gbody <;>
        simp [CEmbedF, LocalTypeR.lcontractive,
          Choreography.Projection.Trans.lcontractive] at hF hcontr ⊢

/-- When lcontractive body = true in the context of a mu, body.isGuarded t = true.
    This follows from the structure of lcontractive which requires send/recv/end at the top,
    all of which are guarded for any variable. -/
-- Embedding Existence Helpers: Guardedness from Contractiveness
private theorem lcontractive_implies_is_guarded (t : String) (body : LocalTypeR)
    (hcontr : LocalTypeR.lcontractive body = true) :
    body.isGuarded t = true := by
  cases body with
  | «end» =>
      simp [LocalTypeR.isGuarded]
/- ## Structured Block 4 -/
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

-- Main Existence Theorems

/-- Helper: derive branch well-formedness for send from parent well-formedness. -/
private def derive_send_branch_wf (receiver : String) (lbs : List BranchR) (role : String)
    (hwf : ∀ partner, (LocalTypeR.send receiver lbs).hasSendTo partner → role ≠ partner)
    (hwf' : ∀ partner, (LocalTypeR.send receiver lbs).hasRecvFrom partner → role ≠ partner) :
    (∀ lb ∈ lbs, ∀ partner, lb.2.2.hasSendTo partner → role ≠ partner) ∧
    (∀ lb ∈ lbs, ∀ partner, lb.2.2.hasRecvFrom partner → role ≠ partner) :=
  ⟨fun _ hmem partner hsend => hwf partner (LocalTypeR.has_send_to_send_branch hmem hsend),
   fun _ hmem partner hrecv => hwf' partner (LocalTypeR.has_recv_from_send_branch hmem hrecv)⟩

/-- Helper: derive branch well-formedness for recv from parent well-formedness. -/
private def derive_recv_branch_wf (sender : String) (lbs : List BranchR) (role : String)
    (hwf : ∀ partner, (LocalTypeR.recv sender lbs).hasSendTo partner → role ≠ partner)
    (hwf' : ∀ partner, (LocalTypeR.recv sender lbs).hasRecvFrom partner → role ≠ partner) :
    (∀ lb ∈ lbs, ∀ partner, lb.2.2.hasSendTo partner → role ≠ partner) ∧
    (∀ lb ∈ lbs, ∀ partner, lb.2.2.hasRecvFrom partner → role ≠ partner) :=
  ⟨fun _ hmem partner hsend => hwf partner (LocalTypeR.has_send_to_recv_branch hmem hsend),
   fun _ hmem partner hrecv => hwf' partner (LocalTypeR.has_recv_from_recv_branch hmem hrecv)⟩

mutual
-- local_type_has_embed Theorem

/-- Any well-formed local type can be embedded into some global type.

    The well-formedness conditions ensure that:
    - The role never sends to itself
    - The role never receives from itself

    This proof proceeds by structural recursion on the local type, with mutual
    induction handling branch lists. -/
theorem local_type_has_embed (e : LocalTypeR) (role : String)
    (hwf : ∀ partner, e.hasSendTo partner → role ≠ partner)
    (hwf' : ∀ partner, e.hasRecvFrom partner → role ≠ partner)
    (hpf : PayloadFree e) :
    ∃ g, CEmbed e role g := by
  -- Dispatch by constructor and recurse on substructures.
  cases e with
  | «end» =>
      refine ⟨.end, ?_⟩
      apply c_embed_fold'
      simp [CEmbedF]
  | var t =>
      refine ⟨.var t, ?_⟩
      apply c_embed_fold'
      simp [CEmbedF]

  -- local_type_has_embed Mu Case

  | mu t body =>
      cases hcontr : LocalTypeR.lcontractive body with
      | true =>
          have hwf_body : ∀ partner, body.hasSendTo partner → role ≠ partner := by
/- ## Structured Block 5 -/
            intro partner hsend
            exact hwf partner (LocalTypeR.has_send_to_mu hsend)
          have hwf'_body : ∀ partner, body.hasRecvFrom partner → role ≠ partner := by
            intro partner hrecv
            exact hwf' partner (LocalTypeR.has_recv_from_mu hrecv)
          obtain ⟨gbody, hembed⟩ := local_type_has_embed body role hwf_body hwf'_body (by simpa [PayloadFree] using hpf)
          have hguard : body.isGuarded t = true := lcontractive_implies_is_guarded t body hcontr
          refine ⟨.mu t gbody, ?_⟩
          apply c_embed_fold'
          simp [CEmbedF]
          exact ⟨hguard, hembed⟩
      | false =>
          have hbad : (LocalTypeR.mu t body).hasSendTo role :=
            LocalTypeR.has_send_to_noncontractive (t := t) (body := body) (partner := role) hcontr
          have : False := (hwf role hbad) rfl
          exact this.elim

  -- local_type_has_embed Send/Recv Cases

  | send receiver lbs =>
      have hne : role ≠ receiver := hwf receiver LocalTypeR.has_send_to_send
      have ⟨hwf_branches, hwf'_branches⟩ := derive_send_branch_wf receiver lbs role hwf hwf'
      obtain ⟨gbs, hembed⟩ := branches_have_embed lbs role hwf_branches hwf'_branches (by simpa [PayloadFree] using hpf)
      refine ⟨.comm role receiver gbs, ?_⟩
      apply c_embed_fold'
      simp [CEmbedF]
      exact ⟨hne, hembed⟩

  -- local_type_has_embed Recv Case

  | recv sender lbs =>
      have hne : sender ≠ role := by
        intro heq
        apply hwf' sender LocalTypeR.has_recv_from_recv
        exact heq.symm
      have ⟨hwf_branches, hwf'_branches⟩ := derive_recv_branch_wf sender lbs role hwf hwf'
      obtain ⟨gbs, hembed⟩ := branches_have_embed lbs role hwf_branches hwf'_branches (by simpa [PayloadFree] using hpf)
      refine ⟨.comm sender role gbs, ?_⟩
      apply c_embed_fold'
      simp [CEmbedF]
      exact ⟨hne, hembed⟩
termination_by sizeOf e
  decreasing_by
  all_goals
    subst_vars
    first
    | exact size_of_body_lt_size_of_mu _ _
    | exact size_of_branches_lt_size_of_send _ _

-- branches_have_embed Theorem

/-- Helper theorem for embedding branch lists. -/
theorem branches_have_embed (lbs : List BranchR) (role : String)
    (hwf : ∀ lb ∈ lbs, ∀ partner, lb.2.2.hasSendTo partner → role ≠ partner)
    (hwf' : ∀ lb ∈ lbs, ∀ partner, lb.2.2.hasRecvFrom partner → role ≠ partner)
    (hpf : BranchesPayloadFree lbs) :
    ∃ gbs, BranchesEmbedRel CEmbed lbs role gbs := by
  -- Structural recursion on the branch list.
  cases lbs with
  | nil => exact ⟨[], List.Forall₂.nil⟩
  | cons hd tl =>
      have hwf_hd : ∀ partner, hd.2.2.hasSendTo partner → role ≠ partner :=
/- ## Structured Block 6 -/
        fun p h => hwf hd (List.Mem.head tl) p h
      have hwf'_hd : ∀ partner, hd.2.2.hasRecvFrom partner → role ≠ partner :=
        fun p h => hwf' hd (List.Mem.head tl) p h
      have hwf_tl : ∀ lb ∈ tl, ∀ partner, lb.2.2.hasSendTo partner → role ≠ partner :=
        fun lb hmem p h => hwf lb (List.Mem.tail hd hmem) p h
      have hwf'_tl : ∀ lb ∈ tl, ∀ partner, lb.2.2.hasRecvFrom partner → role ≠ partner :=
        fun lb hmem p h => hwf' lb (List.Mem.tail hd hmem) p h
      have hpf' : hd.2.1 = none ∧ PayloadFree hd.2.2 ∧ BranchesPayloadFree tl := by
        obtain ⟨l, vt, c⟩ := hd
        simpa [BranchesPayloadFree] using hpf
      obtain ⟨gcont, hcont⟩ := local_type_has_embed hd.2.2 role hwf_hd hwf'_hd hpf'.2.1
      obtain ⟨gtl, htl⟩ := branches_have_embed tl role hwf_tl hwf'_tl hpf'.2.2
      refine ⟨(hd.1, gcont) :: gtl, ?_⟩
      exact List.Forall₂.cons ⟨rfl, hpf'.1, hcont⟩ htl
termination_by sizeOf lbs
decreasing_by
  all_goals
    subst_vars
    first
    | exact size_of_cont_lt_size_of_branches _ _ _ _
    | exact size_of_tail_lt_size_of_branches _ _
end

-- Participant Gating

/-- If a role participates in a global type and we can project, some embedding exists.
    This is the existential form used for participant gating.

    The proof proceeds by induction on participation:
    - Direct participation (role = sender/receiver): use local_type_has_embed
    - Transitive participation (role in branch): use IH on participating branch
    - Mu: use IH on body -/
theorem c_project_has_c_embed_participant {g : GlobalType} {role : String} {e : LocalTypeR}
    (_hproj : CProject g role e) (_hpart : part_of2 role g)
    (hwf : ∀ partner, e.hasSendTo partner → role ≠ partner)
    (hwf' : ∀ partner, e.hasRecvFrom partner → role ≠ partner)
    (hpf : PayloadFree e) : ∃ g', CEmbed e role g' := by
  exact local_type_has_embed e role hwf hwf' hpf

end Choreography.Projection.Embed
