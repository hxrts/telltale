import Choreography.Projection.Project.ImplCompPostfix.PrefixCases

/-! # Choreography.Projection.Project.ImplCompPostfix.SuffixCases

Suffix postfix cases and final CProjectTransRelComp_postfix theorem.
-/

set_option linter.unnecessarySimpa false

namespace Choreography.Projection.Project

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Trans
open Choreography.Projection.Projectb
open SessionCoTypes.EQ2
open SessionCoTypes.EQ2Props
open SessionCoTypes.EQ2Paco
open Paco
open SessionTypes.Participation
private theorem CProjectTransRelComp_postfix_suffix_mu_mu
    {v v' : String} {body_lt body_t b : LocalTypeR}
    (hrel_ab : CProjectTransRel (.mu v body_lt) b) (heq_bc : EQ2 b (.mu v' body_t))
    (hWFa : LocalTypeR.WellFormed (.mu v body_lt))
    (hWFc : LocalTypeR.WellFormed (.mu v' body_t)) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.mu v body_lt) (.mu v' body_t) := by
  -- Unfold both sides to build the EQ2F conjunction for mu/mu.
  simp only [EQ2F]
  have hWF_unfold_lt : LocalTypeR.WellFormed (body_lt.substitute v (.mu v body_lt)) :=
    LocalTypeR.WellFormed.unfold hWFa
  have hWF_unfold_t : LocalTypeR.WellFormed (body_t.substitute v' (.mu v' body_t)) :=
    LocalTypeR.WellFormed.unfold hWFc
  have hWFb : LocalTypeR.WellFormed b := CProjectTransRel_wf_right hrel_ab
  have hcomp_ab : CProjectTransRelCompWF (.mu v body_lt) b :=
    CProjectTransRelCompWF_of_CProjectTransRel hrel_ab
  have hcomp_lt_t : CProjectTransRelCompWF (.mu v body_lt) (.mu v' body_t) :=
    CProjectTransRelCompWF_extend_right hcomp_ab heq_bc hWFa hWFb hWFc
  constructor
  · have hcomp_left : CProjectTransRelCompWF
        (body_lt.substitute v (.mu v body_lt)) (.mu v' body_t) :=
      CProjectTransRelCompWF_extend_left
        (EQ2_unfold_left (EQ2_refl (.mu v body_lt))) hcomp_lt_t
        hWF_unfold_lt hWFa hWFc
    exact Or.inl hcomp_left
  · have hcomp_right : CProjectTransRelCompWF
        (.mu v body_lt) (body_t.substitute v' (.mu v' body_t)) :=
      CProjectTransRelCompWF_extend_right hcomp_lt_t
        (EQ2_unfold_right (EQ2_refl (.mu v' body_t))) hWFa hWFc hWF_unfold_t
    exact Or.inl hcomp_right

private theorem CProjectTransRelComp_postfix_suffix_mu_nonmu
    {v : String} {body_lt t b : LocalTypeR}
    (hrel_ab : CProjectTransRel (.mu v body_lt) b) (heq_bc : EQ2 b t)
    (hWFa : LocalTypeR.WellFormed (.mu v body_lt)) (hWFc : LocalTypeR.WellFormed t) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.mu v body_lt) t := by
  -- Build the left-unfolded composition and split on whether t is mu.
  have hWF_unfold_lt : LocalTypeR.WellFormed (body_lt.substitute v (.mu v body_lt)) :=
    LocalTypeR.WellFormed.unfold hWFa
  have hWFb : LocalTypeR.WellFormed b := CProjectTransRel_wf_right hrel_ab
  have hcomp_ab : CProjectTransRelCompWF (.mu v body_lt) b :=
    CProjectTransRelCompWF_of_CProjectTransRel hrel_ab
  have hcomp_lt_t : CProjectTransRelCompWF (.mu v body_lt) t :=
    CProjectTransRelCompWF_extend_right hcomp_ab heq_bc hWFa hWFb hWFc
  have hcomp_left : CProjectTransRelCompWF (body_lt.substitute v (.mu v body_lt)) t :=
    CProjectTransRelCompWF_extend_left
      (EQ2_unfold_left (EQ2_refl (.mu v body_lt))) hcomp_lt_t
      hWF_unfold_lt hWFa hWFc
  cases t with
  | mu v' body_t =>
      exact CProjectTransRelComp_postfix_suffix_mu_mu
        (v := v) (v' := v') (body_lt := body_lt) (body_t := body_t)
        hrel_ab heq_bc hWFa hWFc
  | _ =>
      simpa [EQ2F] using (Or.inl hcomp_left)

private theorem CProjectTransRelComp_postfix_suffix_nonmu_mu
    {lt b : LocalTypeR} {v' : String} {body_t : LocalTypeR}
    (hrel_ab : CProjectTransRel lt b) (heq_bc : EQ2 b (.mu v' body_t))
    (hWFa : LocalTypeR.WellFormed lt)
    (hWFc : LocalTypeR.WellFormed (.mu v' body_t)) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) lt (.mu v' body_t) := by
  -- Build the right-unfolded composition and split on whether lt is mu.
  have hWF_unfold_t : LocalTypeR.WellFormed (body_t.substitute v' (.mu v' body_t)) :=
    LocalTypeR.WellFormed.unfold hWFc
  have hWFb : LocalTypeR.WellFormed b := CProjectTransRel_wf_right hrel_ab
  have hcomp_ab : CProjectTransRelCompWF lt b :=
    CProjectTransRelCompWF_of_CProjectTransRel hrel_ab
  have hcomp_lt_t : CProjectTransRelCompWF lt (.mu v' body_t) :=
    CProjectTransRelCompWF_extend_right hcomp_ab heq_bc hWFa hWFb hWFc
  have hcomp_right : CProjectTransRelCompWF lt (body_t.substitute v' (.mu v' body_t)) :=
    CProjectTransRelCompWF_extend_right hcomp_lt_t
      (EQ2_unfold_right (EQ2_refl (.mu v' body_t))) hWFa hWFc hWF_unfold_t
  cases lt with
  | mu v body_lt =>
      exact CProjectTransRelComp_postfix_suffix_mu_mu
        (v := v) (v' := v') (body_lt := body_lt) (body_t := body_t)
        hrel_ab heq_bc hWFa hWFc
  | _ =>
      simpa [EQ2F] using (Or.inl hcomp_right)

private theorem CProjectTransRelComp_postfix_suffix_var_var
    {x y : String} {b : LocalTypeR}
    (hrel_ab : CProjectTransRel (.var x) b) (heq_bc : EQ2 b (.var y))
    (hWFa : LocalTypeR.WellFormed (.var x)) (hWFc : LocalTypeR.WellFormed (.var y)) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.var x) (.var y) := by
  -- Combine the base postfix relation with EQ2 on the right.
  simp only [EQ2F]
  have hbase_f := CProjectTransRel_postfix (.var x) b hrel_ab
  have heq_f := EQ2.destruct heq_bc
  cases b with
  | var _ =>
      simp only [EQ2F] at hbase_f heq_f
      exact hbase_f.trans heq_f
  | mu _ _ =>
      simpa only [EQ2F] using
        CProjectTransRel_EQ2_compose_through_mu_WF hrel_ab heq_bc hWFa hWFc
  | «end» => simp only [EQ2F] at hbase_f
  | send _ _ => simp only [EQ2F] at hbase_f
  | recv _ _ => simp only [EQ2F] at hbase_f

private theorem CProjectTransRelComp_postfix_suffix_send_send
    {p q : String} {bs cs : List (Label × LocalTypeR)} {b : LocalTypeR}
    (hrel_ab : CProjectTransRel (.send p bs) b) (heq_bc : EQ2 b (.send q cs))
    (hWFa : LocalTypeR.WellFormed (.send p bs)) (hWFc : LocalTypeR.WellFormed (.send q cs)) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.send p bs) (.send q cs) := by
  -- Transport branch relations across CProjectTransRel and EQ2.
  simp only [EQ2F]
  have hbase_f := CProjectTransRel_postfix (.send p bs) b hrel_ab
  have heq_f := EQ2.destruct heq_bc
  cases b with
  | send pb bbs =>
      simp only [EQ2F] at hbase_f heq_f
      have hWFb : LocalTypeR.WellFormed (.send pb bbs) := CProjectTransRel_wf_right hrel_ab
      have hWFbs : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2 :=
        LocalTypeR.WellFormed.branches_of_send (p := p) (bs := bs) hWFa
      have hWFbbs : ∀ lb ∈ bbs, LocalTypeR.WellFormed lb.2 :=
        LocalTypeR.WellFormed.branches_of_send (p := pb) (bs := bbs) hWFb
      have hWFcs : ∀ lb ∈ cs, LocalTypeR.WellFormed lb.2 :=
        LocalTypeR.WellFormed.branches_of_send (p := q) (bs := cs) hWFc
      have hbase_br := BranchesRel_lift_compWF hbase_f.2 hWFbs hWFbbs
      exact ⟨hbase_f.1.trans heq_f.1,
        BranchesRel_trans_chain
          (fun a b c => @CProjectTransRelCompWF_extend_right a b c)
          hbase_br heq_f.2 hWFbs hWFbbs hWFcs⟩
  | mu _ _ =>
      exact CProjectTransRel_EQ2_compose_through_mu_WF hrel_ab heq_bc hWFa hWFc
  | «end» => simp only [EQ2F] at hbase_f
  | var _ => simp only [EQ2F] at hbase_f
  | recv _ _ => simp only [EQ2F] at hbase_f

private theorem CProjectTransRelComp_postfix_suffix_recv_recv
    {p q : String} {bs cs : List (Label × LocalTypeR)} {b : LocalTypeR}
    (hrel_ab : CProjectTransRel (.recv p bs) b) (heq_bc : EQ2 b (.recv q cs))
    (hWFa : LocalTypeR.WellFormed (.recv p bs)) (hWFc : LocalTypeR.WellFormed (.recv q cs)) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.recv p bs) (.recv q cs) := by
  -- Transport branch relations across CProjectTransRel and EQ2.
  simp only [EQ2F]; have hbase_f := CProjectTransRel_postfix (.recv p bs) b hrel_ab
  have heq_f := EQ2.destruct heq_bc
  cases b with
  | recv pb bbs =>
      simp only [EQ2F] at hbase_f heq_f
      have hWFb : LocalTypeR.WellFormed (.recv pb bbs) := CProjectTransRel_wf_right hrel_ab
      have hWFbs : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2 :=
        LocalTypeR.WellFormed.branches_of_recv (p := p) (bs := bs) hWFa
      have hWFbbs : ∀ lb ∈ bbs, LocalTypeR.WellFormed lb.2 :=
        LocalTypeR.WellFormed.branches_of_recv (p := pb) (bs := bbs) hWFb
      have hWFcs : ∀ lb ∈ cs, LocalTypeR.WellFormed lb.2 :=
        LocalTypeR.WellFormed.branches_of_recv (p := q) (bs := cs) hWFc
      have hbase_br := BranchesRel_lift_compWF hbase_f.2 hWFbs hWFbbs
      exact ⟨hbase_f.1.trans heq_f.1,
        BranchesRel_trans_chain
          (fun a b c => @CProjectTransRelCompWF_extend_right a b c)
          hbase_br heq_f.2 hWFbs hWFbbs hWFcs⟩
  | mu _ _ =>
      exact CProjectTransRel_EQ2_compose_through_mu_WF hrel_ab heq_bc hWFa hWFc
  | «end» => simp only [EQ2F] at hbase_f
  | var _ => simp only [EQ2F] at hbase_f
  | send _ _ => simp only [EQ2F] at hbase_f

/- Helper: suffix case when lt is .end. -/
private theorem CProjectTransRelComp_postfix_suffix_end
    {t b : LocalTypeR}
    (hrel_ab : CProjectTransRel .end b) (heq_bc : EQ2 b t)
    (hWFc : LocalTypeR.WellFormed t) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) .end t := by
  -- Dispatch on t: mu uses the nonmu-mu helper, others are trivial/mismatch.
  cases t with
  | mu v' body_t =>
      exact CProjectTransRelComp_postfix_suffix_nonmu_mu hrel_ab heq_bc
        LocalTypeR.WellFormed_end hWFc
  | «end» =>
      simpa [EQ2F]
  | var v =>
      have hfalse : False := CProjectTransRelComp_end_not_var
        (Or.inr (Or.inr (Or.inl ⟨b, hrel_ab, heq_bc⟩))) LocalTypeR.WellFormed_end hWFc
      simpa [EQ2F] using hfalse
  | send p bs =>
      have hfalse : False := CProjectTransRelComp_end_not_send
        (Or.inr (Or.inr (Or.inl ⟨b, hrel_ab, heq_bc⟩))) LocalTypeR.WellFormed_end hWFc
      simpa [EQ2F] using hfalse
  | recv p bs =>
      have hfalse : False := CProjectTransRelComp_end_not_recv
        (Or.inr (Or.inr (Or.inl ⟨b, hrel_ab, heq_bc⟩))) LocalTypeR.WellFormed_end hWFc
      simpa [EQ2F] using hfalse

/- Helper: suffix case when lt is .var. -/
private theorem CProjectTransRelComp_postfix_suffix_var
    {x : String} {t b : LocalTypeR}
    (hrel_ab : CProjectTransRel (.var x) b) (heq_bc : EQ2 b t)
    (hWFa : LocalTypeR.WellFormed (.var x)) (hWFc : LocalTypeR.WellFormed t) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.var x) t := by
  -- Handle mu via nonmu-mu; var/var via the specialized lemma; mismatches by simp.
  cases t with
  | mu v' body_t =>
      exact CProjectTransRelComp_postfix_suffix_nonmu_mu hrel_ab heq_bc hWFa hWFc
  | var y =>
      exact CProjectTransRelComp_postfix_suffix_var_var hrel_ab heq_bc hWFa hWFc
  | «end» =>
      have hcomp : CProjectTransRelComp (.var x) .end :=
        Or.inr (Or.inr (Or.inl ⟨b, hrel_ab, heq_bc⟩))
      have hfalse : False := CProjectTransRelComp_var_not_end hcomp hWFa hWFc
      simpa [EQ2F] using hfalse
  | send p bs =>
      have hcomp : CProjectTransRelComp (.var x) (.send p bs) :=
        Or.inr (Or.inr (Or.inl ⟨b, hrel_ab, heq_bc⟩))
      have hfalse : False := CProjectTransRelComp_var_not_send hcomp hWFa hWFc
      simpa [EQ2F] using hfalse
  | recv p bs =>
      have hcomp : CProjectTransRelComp (.var x) (.recv p bs) :=
        Or.inr (Or.inr (Or.inl ⟨b, hrel_ab, heq_bc⟩))
      have hfalse : False := CProjectTransRelComp_var_not_recv hcomp hWFa hWFc
      simpa [EQ2F] using hfalse

/- Helper: suffix case when lt is .send. -/
private theorem CProjectTransRelComp_postfix_suffix_send
    {p : String} {bs : List (Label × LocalTypeR)} {t b : LocalTypeR}
    (hrel_ab : CProjectTransRel (.send p bs) b) (heq_bc : EQ2 b t)
    (hWFa : LocalTypeR.WellFormed (.send p bs)) (hWFc : LocalTypeR.WellFormed t) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.send p bs) t := by
  -- Handle mu via nonmu-mu; send/send via the specialized lemma; mismatches by simp.
  cases t with
  | mu v' body_t =>
      exact CProjectTransRelComp_postfix_suffix_nonmu_mu hrel_ab heq_bc hWFa hWFc
  | send q cs =>
      exact CProjectTransRelComp_postfix_suffix_send_send hrel_ab heq_bc hWFa hWFc
  | «end» =>
      have hcomp : CProjectTransRelComp (.send p bs) .end :=
        Or.inr (Or.inr (Or.inl ⟨b, hrel_ab, heq_bc⟩))
      have hfalse : False := CProjectTransRelComp_send_not_end hcomp hWFa hWFc
      simpa [EQ2F] using hfalse
  | var v =>
      have hcomp : CProjectTransRelComp (.send p bs) (.var v) :=
        Or.inr (Or.inr (Or.inl ⟨b, hrel_ab, heq_bc⟩))
      have hfalse : False := CProjectTransRelComp_send_not_var hcomp hWFa hWFc
      simpa [EQ2F] using hfalse
  | recv q cs =>
      have hcomp : CProjectTransRelComp (.send p bs) (.recv q cs) :=
        Or.inr (Or.inr (Or.inl ⟨b, hrel_ab, heq_bc⟩))
      have hfalse : False := CProjectTransRelComp_send_not_recv hcomp hWFa hWFc
      simpa [EQ2F] using hfalse

/- Helper: suffix case when lt is .recv. -/
private theorem CProjectTransRelComp_postfix_suffix_recv
    {p : String} {bs : List (Label × LocalTypeR)} {t b : LocalTypeR}
    (hrel_ab : CProjectTransRel (.recv p bs) b) (heq_bc : EQ2 b t)
    (hWFa : LocalTypeR.WellFormed (.recv p bs)) (hWFc : LocalTypeR.WellFormed t) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.recv p bs) t := by
  -- Handle mu via nonmu-mu; recv/recv via the specialized lemma; mismatches by simp.
  cases t with
  | mu v' body_t =>
      exact CProjectTransRelComp_postfix_suffix_nonmu_mu hrel_ab heq_bc hWFa hWFc
  | recv q cs =>
      exact CProjectTransRelComp_postfix_suffix_recv_recv hrel_ab heq_bc hWFa hWFc
  | «end» =>
      have hcomp : CProjectTransRelComp (.recv p bs) .end :=
        Or.inr (Or.inr (Or.inl ⟨b, hrel_ab, heq_bc⟩))
      have hfalse : False := CProjectTransRelComp_recv_not_end hcomp hWFa hWFc
      simpa [EQ2F] using hfalse
  | var v =>
      have hcomp : CProjectTransRelComp (.recv p bs) (.var v) :=
        Or.inr (Or.inr (Or.inl ⟨b, hrel_ab, heq_bc⟩))
      have hfalse : False := CProjectTransRelComp_recv_not_var hcomp hWFa hWFc
      simpa [EQ2F] using hfalse
  | send q cs =>
      have hcomp : CProjectTransRelComp (.recv p bs) (.send q cs) :=
        Or.inr (Or.inr (Or.inl ⟨b, hrel_ab, heq_bc⟩))
      have hfalse : False := CProjectTransRelComp_recv_not_send hcomp hWFa hWFc
      simpa [EQ2F] using hfalse

/- Helper: suffix case when lt is .mu. -/
private theorem CProjectTransRelComp_postfix_suffix_mu
    {v : String} {body_lt t b : LocalTypeR}
    (hrel_ab : CProjectTransRel (.mu v body_lt) b) (heq_bc : EQ2 b t)
    (hWFa : LocalTypeR.WellFormed (.mu v body_lt)) (hWFc : LocalTypeR.WellFormed t) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.mu v body_lt) t := by
  -- Mu/mu uses the dedicated lemma; mu/nonmu uses the left-unfold helper.
  cases t with
  | mu v' body_t =>
      exact CProjectTransRelComp_postfix_suffix_mu_mu hrel_ab heq_bc hWFa hWFc
  | _ =>
      exact CProjectTransRelComp_postfix_suffix_mu_nonmu hrel_ab heq_bc hWFa hWFc

private theorem CProjectTransRelComp_postfix_suffix
    {lt t b : LocalTypeR}
    (hrel_ab : CProjectTransRel lt b) (heq_bc : EQ2 b t)
    (hWFa : LocalTypeR.WellFormed lt) (hWFc : LocalTypeR.WellFormed t) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) lt t := by
  -- 2-hop suffix: CProjectTransRel lt b, then EQ2 b t.
  cases lt with
  | «end» => exact CProjectTransRelComp_postfix_suffix_end hrel_ab heq_bc hWFc
  | var x => exact CProjectTransRelComp_postfix_suffix_var (x := x) hrel_ab heq_bc hWFa hWFc
  | send p bs =>
      exact CProjectTransRelComp_postfix_suffix_send (p := p) (bs := bs) hrel_ab heq_bc hWFa hWFc
  | recv p bs =>
      exact CProjectTransRelComp_postfix_suffix_recv (p := p) (bs := bs) hrel_ab heq_bc hWFa hWFc
  | mu v body_lt =>
      exact CProjectTransRelComp_postfix_suffix_mu (v := v) (body_lt := body_lt) hrel_ab heq_bc hWFa hWFc

/-- Postfix property for the well-formed composite relation. -/
theorem CProjectTransRelComp_postfix :
    ∀ lt t, CProjectTransRelCompWF lt t → EQ2F (EQ2_closure CProjectTransRelCompWF) lt t := by
  intro lt t hcompWF
  -- Proof strategy: split on the four composition shapes (base/prefix/suffix/chain).
  rcases hcompWF with ⟨hcomp, hWFa, hWFc⟩
  rcases hcomp with hbase | ⟨b, heq_ab, hrel_bb'⟩ | ⟨b, hrel_ab, heq_bc⟩ | ⟨b, b', heq_ab, hrel_bb', heq_b'c⟩
  · -- Base case: CProjectTransRel lt t
    exact CProjectTransRelComp_postfix_base hbase hWFa hWFc
  · -- 2-hop prefix: ∃ b, EQ2 lt b ∧ CProjectTransRel b t
    exact CProjectTransRelComp_postfix_prefix heq_ab hrel_bb' hWFa hWFc
  · -- 2-hop suffix: ∃ b, CProjectTransRel lt b ∧ EQ2 b t
    exact CProjectTransRelComp_postfix_suffix hrel_ab heq_bc hWFa hWFc
  · -- 3-hop: ∃ b b', EQ2 lt b ∧ CProjectTransRel b b' ∧ EQ2 b' t
    exact CProjectTransRelComp_postfix_chain heq_ab hrel_bb' heq_b'c hWFa hWFc

/-- CProject implies EQ2 with trans.

Proven by coinduction using CProjectTransRelCompWF as witness relation.
Uses EQ2_coind_upto which handles the EQ2 closure automatically.

Requires `allCommsNonEmpty` assumption (matching Coq's `size_pred`) to handle
non-participant cases which recurse through branches. -/
theorem CProject_implies_EQ2_trans_thm (g : GlobalType) (role : String) (lt : LocalTypeR)
    (h : CProject g role lt) (hwf : g.wellFormed = true) : EQ2 lt (Trans.trans g role) := by
  -- Apply coinduction up-to with witness relation CProjectTransRelCompWF
  -- EQ2_coind_upto says: if ∀ a b, R a b → EQ2F (EQ2_closure R) a b, then R ⊆ EQ2
  -- EQ2_closure R = fun a b => R a b ∨ EQ2 a b, which matches CProjectTransRelComp_postfix
  apply EQ2_coind_upto (R := CProjectTransRelCompWF)
  · -- Post-fixpoint: CProjectTransRelComp closes under EQ2F with EQ2 closure.
    intro lt' t' hrel
    exact CProjectTransRelComp_postfix lt' t' hrel
  · -- Seed relation: CProjectTransRelCompWF holds by the base CProjectTransRel case.
    have hrel : CProjectTransRel lt (Trans.trans g role) := ⟨g, role, h, rfl, hwf⟩
    exact CProjectTransRelCompWF_of_CProjectTransRel hrel


end Choreography.Projection.Project
