import Choreography.Projection.Project.ImplCompPostfix.WellFormedClosure

/-! # Choreography.Projection.Project.ImplCompPostfix.PrefixCases

Prefix postfix cases dispatching on left constructor.
-/

set_option linter.unnecessarySimpa false

/-! ## Core Development -/

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
private theorem CProjectTransRelComp_postfix_prefix_send_send
    {p q : String} {bs cs : List BranchR} {b : LocalTypeR}
    (heq_ab : EQ2 (.send p bs) b) (hrel_bb' : CProjectTransRel b (.send q cs))
    (hWFa : LocalTypeR.WellFormed (.send p bs)) (hWFc : LocalTypeR.WellFormed (.send q cs)) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.send p bs) (.send q cs) := by
  -- Transport branch relations across EQ2 and CProjectTransRel.
  simp only [EQ2F]
  have heq_f := EQ2.destruct heq_ab
  have hbase_f := CProjectTransRel_postfix b (.send q cs) hrel_bb'
  cases b with
  | send pb bbs =>
      simp only [EQ2F] at heq_f hbase_f
      have hWFb : LocalTypeR.WellFormed (.send pb bbs) := CProjectTransRel_wf_left hrel_bb'
      have hWFbs : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2.2 :=
        LocalTypeR.WellFormed.branches_of_send (p := p) (bs := bs) hWFa
      have hWFbbs : ∀ lb ∈ bbs, LocalTypeR.WellFormed lb.2.2 :=
        LocalTypeR.WellFormed.branches_of_send (p := pb) (bs := bbs) hWFb
      have hWFcs : ∀ lb ∈ cs, LocalTypeR.WellFormed lb.2.2 :=
        LocalTypeR.WellFormed.branches_of_send (p := q) (bs := cs) hWFc
      have hbase_br := BranchesRel_lift_compWF hbase_f.2 hWFbbs hWFcs
      exact ⟨heq_f.1.trans hbase_f.1,
        BranchesRel_trans_chain_rev
          (fun a b c => @CProjectTransRelCompWF_extend_left a b c)
          heq_f.2 hbase_br hWFbs hWFbbs hWFcs⟩
  | mu _ _ =>
      exact EQ2_CProjectTransRel_compose_through_mu_WF heq_ab hrel_bb' hWFa hWFc
  | «end» => simp only [EQ2F] at heq_f
  | var _ => simp only [EQ2F] at heq_f
  | recv _ _ => simp only [EQ2F] at heq_f

private theorem CProjectTransRelComp_postfix_prefix_recv_recv
    {p q : String} {bs cs : List BranchR} {b : LocalTypeR}
    (heq_ab : EQ2 (.recv p bs) b) (hrel_bb' : CProjectTransRel b (.recv q cs))
    (hWFa : LocalTypeR.WellFormed (.recv p bs)) (hWFc : LocalTypeR.WellFormed (.recv q cs)) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.recv p bs) (.recv q cs) := by
  -- Transport branch relations across EQ2 and CProjectTransRel.
  simp only [EQ2F]; have heq_f := EQ2.destruct heq_ab
  have hbase_f := CProjectTransRel_postfix b (.recv q cs) hrel_bb'
  cases b with
  | recv pb bbs =>
      simp only [EQ2F] at heq_f hbase_f
      have hWFb : LocalTypeR.WellFormed (.recv pb bbs) := CProjectTransRel_wf_left hrel_bb'
      have hWFbs : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2.2 :=
        LocalTypeR.WellFormed.branches_of_recv (p := p) (bs := bs) hWFa
      have hWFbbs : ∀ lb ∈ bbs, LocalTypeR.WellFormed lb.2.2 :=
        LocalTypeR.WellFormed.branches_of_recv (p := pb) (bs := bbs) hWFb
      have hWFcs : ∀ lb ∈ cs, LocalTypeR.WellFormed lb.2.2 :=
        LocalTypeR.WellFormed.branches_of_recv (p := q) (bs := cs) hWFc
      have hbase_br := BranchesRel_lift_compWF hbase_f.2 hWFbbs hWFcs
      exact ⟨heq_f.1.trans hbase_f.1,
        BranchesRel_trans_chain_rev
          (fun a b c => @CProjectTransRelCompWF_extend_left a b c)
          heq_f.2 hbase_br hWFbs hWFbbs hWFcs⟩
  | mu _ _ =>
      exact EQ2_CProjectTransRel_compose_through_mu_WF heq_ab hrel_bb' hWFa hWFc
  | «end» => simp only [EQ2F] at heq_f
  | var _ => simp only [EQ2F] at heq_f
  | send _ _ => simp only [EQ2F] at heq_f

/- Helper: prefix case when lt is .end. -/
private theorem CProjectTransRelComp_postfix_prefix_end
    {t b : LocalTypeR}
    (heq_ab : EQ2 .end b) (hrel_bb' : CProjectTransRel b t)
    (hWFc : LocalTypeR.WellFormed t) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) .end t := by
  -- Dispatch on t: mu uses the nonmu-mu helper, others are trivial/mismatch.
  cases t with
  | mu v' body_t =>
      exact CProjectTransRelComp_postfix_prefix_nonmu_mu heq_ab hrel_bb'
        LocalTypeR.WellFormed_end hWFc
  | «end» =>
      simpa [EQ2F]
  | var v =>
      have hfalse : False := CProjectTransRelComp_end_not_var
        (Or.inr (Or.inl ⟨b, heq_ab, hrel_bb'⟩)) LocalTypeR.WellFormed_end hWFc
      simpa [EQ2F] using hfalse
  | send p bs =>
      have hfalse : False := CProjectTransRelComp_end_not_send
        (Or.inr (Or.inl ⟨b, heq_ab, hrel_bb'⟩)) LocalTypeR.WellFormed_end hWFc
      simpa [EQ2F] using hfalse
  | recv p bs =>
      have hfalse : False := CProjectTransRelComp_end_not_recv
        (Or.inr (Or.inl ⟨b, heq_ab, hrel_bb'⟩)) LocalTypeR.WellFormed_end hWFc
      simpa [EQ2F] using hfalse

/- Helper: prefix case when lt is .var. -/
private theorem CProjectTransRelComp_postfix_prefix_var
    {x : String} {t b : LocalTypeR}
    (heq_ab : EQ2 (.var x) b) (hrel_bb' : CProjectTransRel b t)
    (hWFa : LocalTypeR.WellFormed (.var x)) (hWFc : LocalTypeR.WellFormed t) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.var x) t := by
  -- Handle mu via nonmu-mu; var/var via the specialized lemma; mismatches by simp.
  cases t with
  | mu v' body_t =>
      exact CProjectTransRelComp_postfix_prefix_nonmu_mu heq_ab hrel_bb' hWFa hWFc
  | var y =>
      exact CProjectTransRelComp_postfix_prefix_var_var heq_ab hrel_bb' hWFa hWFc
  | «end» =>
      have hcomp : CProjectTransRelComp (.var x) .end :=
        Or.inr (Or.inl ⟨b, heq_ab, hrel_bb'⟩)
      have hfalse : False := CProjectTransRelComp_var_not_end hcomp hWFa hWFc
      simpa [EQ2F] using hfalse
  | send p bs =>
      have hcomp : CProjectTransRelComp (.var x) (.send p bs) :=
        Or.inr (Or.inl ⟨b, heq_ab, hrel_bb'⟩)
      have hfalse : False := CProjectTransRelComp_var_not_send hcomp hWFa hWFc
      simpa [EQ2F] using hfalse
  | recv p bs =>
      have hcomp : CProjectTransRelComp (.var x) (.recv p bs) :=
        Or.inr (Or.inl ⟨b, heq_ab, hrel_bb'⟩)
      have hfalse : False := CProjectTransRelComp_var_not_recv hcomp hWFa hWFc
      simpa [EQ2F] using hfalse

/- Helper: prefix case when lt is .send. -/
private theorem CProjectTransRelComp_postfix_prefix_send
    {p : String} {bs : List BranchR} {t b : LocalTypeR}
    (heq_ab : EQ2 (.send p bs) b) (hrel_bb' : CProjectTransRel b t)
    (hWFa : LocalTypeR.WellFormed (.send p bs)) (hWFc : LocalTypeR.WellFormed t) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.send p bs) t := by
  -- Handle mu via nonmu-mu; send/send via the specialized lemma; mismatches by simp.
  cases t with
  | mu v' body_t =>
      exact CProjectTransRelComp_postfix_prefix_nonmu_mu heq_ab hrel_bb' hWFa hWFc
  | send q cs =>
      exact CProjectTransRelComp_postfix_prefix_send_send heq_ab hrel_bb' hWFa hWFc
  | «end» =>
      have hcomp : CProjectTransRelComp (.send p bs) .end :=
        Or.inr (Or.inl ⟨b, heq_ab, hrel_bb'⟩)
      have hfalse : False := CProjectTransRelComp_send_not_end hcomp hWFa hWFc
      simpa [EQ2F] using hfalse
  | var v =>
      have hcomp : CProjectTransRelComp (.send p bs) (.var v) :=
        Or.inr (Or.inl ⟨b, heq_ab, hrel_bb'⟩)
      have hfalse : False := CProjectTransRelComp_send_not_var hcomp hWFa hWFc
      simpa [EQ2F] using hfalse
  | recv q cs =>
      have hcomp : CProjectTransRelComp (.send p bs) (.recv q cs) :=
        Or.inr (Or.inl ⟨b, heq_ab, hrel_bb'⟩)
      have hfalse : False := CProjectTransRelComp_send_not_recv hcomp hWFa hWFc
      simpa [EQ2F] using hfalse

/- Helper: prefix case when lt is .recv. -/
private theorem CProjectTransRelComp_postfix_prefix_recv
    {p : String} {bs : List BranchR} {t b : LocalTypeR}
    (heq_ab : EQ2 (.recv p bs) b) (hrel_bb' : CProjectTransRel b t)
    (hWFa : LocalTypeR.WellFormed (.recv p bs)) (hWFc : LocalTypeR.WellFormed t) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.recv p bs) t := by
  -- Handle mu via nonmu-mu; recv/recv via the specialized lemma; mismatches by simp.
  cases t with
  | mu v' body_t =>
      exact CProjectTransRelComp_postfix_prefix_nonmu_mu heq_ab hrel_bb' hWFa hWFc
  | recv q cs =>
      exact CProjectTransRelComp_postfix_prefix_recv_recv heq_ab hrel_bb' hWFa hWFc
  | «end» =>
      have hcomp : CProjectTransRelComp (.recv p bs) .end :=
        Or.inr (Or.inl ⟨b, heq_ab, hrel_bb'⟩)
      have hfalse : False := CProjectTransRelComp_recv_not_end hcomp hWFa hWFc
      simpa [EQ2F] using hfalse
  | var v =>
      have hcomp : CProjectTransRelComp (.recv p bs) (.var v) :=
        Or.inr (Or.inl ⟨b, heq_ab, hrel_bb'⟩)
      have hfalse : False := CProjectTransRelComp_recv_not_var hcomp hWFa hWFc
      simpa [EQ2F] using hfalse
  | send q cs =>
      have hcomp : CProjectTransRelComp (.recv p bs) (.send q cs) :=
        Or.inr (Or.inl ⟨b, heq_ab, hrel_bb'⟩)
      have hfalse : False := CProjectTransRelComp_recv_not_send hcomp hWFa hWFc
      simpa [EQ2F] using hfalse

/- Helper: prefix case when lt is .mu. -/
private theorem CProjectTransRelComp_postfix_prefix_mu
    {v : String} {body_lt t b : LocalTypeR}
    (heq_ab : EQ2 (.mu v body_lt) b) (hrel_bb' : CProjectTransRel b t)
    (hWFa : LocalTypeR.WellFormed (.mu v body_lt)) (hWFc : LocalTypeR.WellFormed t) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) (.mu v body_lt) t := by
  -- Mu/mu uses the dedicated lemma; mu/nonmu uses the left-unfold helper.
  cases t with
  | mu v' body_t =>
      exact CProjectTransRelComp_postfix_prefix_mu_mu heq_ab hrel_bb' hWFa hWFc
  | _ =>
      exact CProjectTransRelComp_postfix_prefix_mu_nonmu heq_ab hrel_bb' hWFa hWFc

theorem CProjectTransRelComp_postfix_prefix
    {lt t b : LocalTypeR}
    (heq_ab : EQ2 lt b) (hrel_bb' : CProjectTransRel b t)
    (hWFa : LocalTypeR.WellFormed lt) (hWFc : LocalTypeR.WellFormed t) :
    EQ2F (EQ2_closure CProjectTransRelCompWF) lt t := by
  -- 2-hop prefix: EQ2 lt b, then CProjectTransRel b t.
  cases lt with
  | «end» => exact CProjectTransRelComp_postfix_prefix_end heq_ab hrel_bb' hWFc
  | var x => exact CProjectTransRelComp_postfix_prefix_var (x := x) heq_ab hrel_bb' hWFa hWFc
  | send p bs =>
      exact CProjectTransRelComp_postfix_prefix_send (p := p) (bs := bs) heq_ab hrel_bb' hWFa hWFc
  | recv p bs =>
      exact CProjectTransRelComp_postfix_prefix_recv (p := p) (bs := bs) heq_ab hrel_bb' hWFa hWFc
  | mu v body_lt =>
      exact CProjectTransRelComp_postfix_prefix_mu (v := v) (body_lt := body_lt) heq_ab hrel_bb' hWFa hWFc

end Choreography.Projection.Project
