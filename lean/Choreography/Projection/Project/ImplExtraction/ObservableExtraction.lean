import Choreography.Projection.Project.ImplObservables

/-! # Choreography.Projection.Project.ImplExtraction.ObservableExtraction

Observable extraction: same-constructor CProjectTransRelComp structural equalities.
-/

/-
The Problem. State the projection/harmony lemma objective and the exact invariant boundary it preserves.
Solution Structure. Introduce local helper lemmas first, then discharge the main theorem by case analysis over the operational/projection relation.
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

/-! ## Observable Extraction Lemmas

These lemmas extract observable structure from CProjectTransRelComp when
both endpoints have the same head constructor. They capture that:
1. If var is related to var through the composition, they have the same name
2. If send is related to send, partners match and branches are pairwise related
3. If recv is related to recv, partners match and branches are pairwise related

These are sound because CProjectTransRelComp preserves observable behavior
(modulo equi-recursive equivalence).
-/

theorem CProjectTransRelComp_extend_right_noWF
    (h1 : CProjectTransRelComp a b) (h2 : EQ2 b c)
    (hWFa : LocalTypeR.WellFormed a) (hWFb : LocalTypeR.WellFormed b) (hWFc : LocalTypeR.WellFormed c) :
    CProjectTransRelComp a c := by
  exact CProjectTransRelComp_extend_right h1 h2 hWFa hWFb hWFc

theorem CProjectTransRelComp_extend_left_noWF
    (h1 : EQ2 a b) (h2 : CProjectTransRelComp b c)
    (hWFa : LocalTypeR.WellFormed a) (hWFb : LocalTypeR.WellFormed b) (hWFc : LocalTypeR.WellFormed c) :
    CProjectTransRelComp a c := by
  exact CProjectTransRelComp_extend_left h1 h2 hWFa hWFb hWFc

private theorem BranchesRel_trans_chain_head_noWF {R : Rel}
    (hextend : ∀ a b c, R a b → EQ2 b c →
      LocalTypeR.WellFormed a → LocalTypeR.WellFormed b → LocalTypeR.WellFormed c → R a c)
    {lb_bs lb_cs lb_ds : BranchR}
    (h1 : lb_bs.1 = lb_cs.1 ∧ (EQ2_closure R) lb_bs.2.2 lb_cs.2.2)
    (h2 : lb_cs.1 = lb_ds.1 ∧ EQ2 lb_cs.2.2 lb_ds.2.2)
    (hWFa : LocalTypeR.WellFormed lb_bs.2.2)
    (hWFb : LocalTypeR.WellFormed lb_cs.2.2)
    (hWFc : LocalTypeR.WellFormed lb_ds.2.2) :
    lb_bs.1 = lb_ds.1 ∧ (EQ2_closure R) lb_bs.2.2 lb_ds.2.2 := by
  constructor
  · exact h1.1.trans h2.1
  · cases h1.2 with
    | inl hr => exact Or.inl (hextend _ _ _ hr h2.2 hWFa hWFb hWFc)
    | inr heq => exact Or.inr (EQ2_trans_wf heq h2.2 hWFa hWFb hWFc)

private theorem BranchesRel_trans_chain_rev_head_noWF {R : Rel}
    (hextend : ∀ a b c, EQ2 a b → R b c →
      LocalTypeR.WellFormed a → LocalTypeR.WellFormed b → LocalTypeR.WellFormed c → R a c)
    {lb_bs lb_cs lb_ds : BranchR}
    (h1 : lb_bs.1 = lb_cs.1 ∧ EQ2 lb_bs.2.2 lb_cs.2.2)
    (h2 : lb_cs.1 = lb_ds.1 ∧ (EQ2_closure R) lb_cs.2.2 lb_ds.2.2)
    (hWFa : LocalTypeR.WellFormed lb_bs.2.2)
    (hWFb : LocalTypeR.WellFormed lb_cs.2.2)
    (hWFc : LocalTypeR.WellFormed lb_ds.2.2) :
    lb_bs.1 = lb_ds.1 ∧ (EQ2_closure R) lb_bs.2.2 lb_ds.2.2 := by
  constructor
  · exact h1.1.trans h2.1
  · cases h2.2 with
    | inl hr => exact Or.inl (hextend _ _ _ h1.2 hr hWFa hWFb hWFc)
    | inr heq => exact Or.inr (EQ2_trans_wf h1.2 heq hWFa hWFb hWFc)

theorem BranchesRel_trans_chain_noWF {R : Rel}
    (hextend : ∀ a b c, R a b → EQ2 b c →
      LocalTypeR.WellFormed a → LocalTypeR.WellFormed b → LocalTypeR.WellFormed c → R a c)
    {bs cs ds : List BranchR}
    (hbc : BranchesRel (EQ2_closure R) bs cs)
    (hcd : BranchesRel EQ2 cs ds)
    (hwf_bs : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2.2)
    (hwf_cs : ∀ lb ∈ cs, LocalTypeR.WellFormed lb.2.2)
    (hwf_ds : ∀ lb ∈ ds, LocalTypeR.WellFormed lb.2.2) :
    BranchesRel (EQ2_closure R) bs ds := by
  induction hbc generalizing ds with
  | nil => cases hcd; exact List.Forall₂.nil
  | cons h1 hbc_tail ih =>
      rename_i lb_bs lb_cs bs_tail cs_tail
      cases ds with
      | nil => cases hcd
      | cons lb_ds ds_tail =>
          cases hcd with
          | cons h2 hcd_tail =>
              constructor
              · exact BranchesRel_trans_chain_head_noWF hextend h1 h2
                  (hwf_bs lb_bs (by simp)) (hwf_cs lb_cs (by simp)) (hwf_ds lb_ds (by simp))
              · exact ih hcd_tail (wf_tail_of_cons hwf_bs)
                  (wf_tail_of_cons hwf_cs) (wf_tail_of_cons hwf_ds)

theorem BranchesRel_trans_chain_rev_noWF {R : Rel}
    (hextend : ∀ a b c, EQ2 a b → R b c →
      LocalTypeR.WellFormed a → LocalTypeR.WellFormed b → LocalTypeR.WellFormed c → R a c)
    {bs cs ds : List BranchR}
    (hbc : BranchesRel EQ2 bs cs)
    (hcd : BranchesRel (EQ2_closure R) cs ds)
    (hwf_bs : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2.2)
    (hwf_cs : ∀ lb ∈ cs, LocalTypeR.WellFormed lb.2.2)
    (hwf_ds : ∀ lb ∈ ds, LocalTypeR.WellFormed lb.2.2) :
    BranchesRel (EQ2_closure R) bs ds := by
  induction hbc generalizing ds with
  | nil => cases hcd; exact List.Forall₂.nil
  | cons h1 hbc_tail ih =>
      rename_i lb_bs lb_cs bs_tail cs_tail
      cases ds with
      | nil => cases hcd
      | cons lb_ds ds_tail =>
          cases hcd with
          | cons h2 hcd_tail =>
              constructor
              · exact BranchesRel_trans_chain_rev_head_noWF hextend h1 h2
                  (hwf_bs lb_bs (by simp)) (hwf_cs lb_cs (by simp)) (hwf_ds lb_ds (by simp))
              · exact ih hcd_tail (wf_tail_of_cons hwf_bs)
                  (wf_tail_of_cons hwf_cs) (wf_tail_of_cons hwf_ds)

/- Helper: left composition case for CProjectTransRelComp_var_extract. -/
private theorem CProjectTransRelComp_var_extract_left
    {v1 v2 : String} {b : LocalTypeR}
    (heq : EQ2 (.var v1) b) (hrel : CProjectTransRel b (.var v2)) : v1 = v2 := by
  -- Destructure the intermediate b and eliminate impossible cases.
  cases b with
  | var v =>
      have hv : v1 = v := by simpa [EQ2F] using (EQ2.destruct heq)
      have hb : LocalTypeR.var v2 = LocalTypeR.var v :=
        CProjectTransRel_source_var (v := v) (b := LocalTypeR.var v2) hrel
      cases hb
      simpa [hv]
  | «end» | send _ _ | recv _ _ =>
      simpa [EQ2F] using (EQ2.destruct heq)
  | mu t body =>
      rcases CProjectTransRel_source_mu (v := t) (body := body) (b := LocalTypeR.var v2) hrel
        with ⟨body', hEq⟩
      cases hEq

/- Helper: right composition case for CProjectTransRelComp_var_extract. -/
private theorem CProjectTransRelComp_var_extract_right
    {v1 v2 : String} {b : LocalTypeR}
    (hrel : CProjectTransRel (.var v1) b) (heq : EQ2 b (.var v2)) : v1 = v2 := by
  -- Right case reduces to EQ2 over vars.
  have hb : b = .var v1 := CProjectTransRel_source_var (v := v1) hrel
  subst hb
  simpa [EQ2F] using (EQ2.destruct heq)

/- Helper: base case for CProjectTransRelComp_var_extract. -/
private theorem CProjectTransRelComp_var_extract_base
    {v1 v2 : String} (hbase : CProjectTransRel (.var v1) (.var v2)) : v1 = v2 := by
  -- Direct CProjectTransRel on vars enforces equality.
  have hb : LocalTypeR.var v2 = LocalTypeR.var v1 :=
    CProjectTransRel_source_var (v := v1) (b := LocalTypeR.var v2) hbase
  cases hb
  rfl

/- Helper: both composition case for CProjectTransRelComp_var_extract. -/
private theorem CProjectTransRelComp_var_extract_both
    {v1 v2 : String} {b b' : LocalTypeR}
    (heq : EQ2 (.var v1) b) (hrel : CProjectTransRel b b') (heq' : EQ2 b' (.var v2))
    (hWFa : LocalTypeR.WellFormed (.var v1)) (hWFc : LocalTypeR.WellFormed (.var v2)) : v1 = v2 := by
  -- Compose EQ2 with CProjectTransRel and destruct.
  have hcomp :=
    EQ2_CProjectTransRel_EQ2_compose (a := .var v1) (c := .var v2) heq hrel heq' hWFa hWFc
  simpa [EQ2F] using hcomp

/-- When var is CProjectTransRelComp-related to var, the variable names match. -/
theorem CProjectTransRelComp_var_extract
    {v1 v2 : String} (h : CProjectTransRelComp (.var v1) (.var v2))
    (hWFa : LocalTypeR.WellFormed (.var v1)) (hWFc : LocalTypeR.WellFormed (.var v2)) : v1 = v2 := by
  -- Split the composed relation into base/left/right/both cases.
  rcases h with hbase | hleft | hright | hboth
  · exact CProjectTransRelComp_var_extract_base hbase
  · rcases hleft with ⟨b, heq, hrel⟩
    exact CProjectTransRelComp_var_extract_left heq hrel
  · rcases hright with ⟨b, hrel, heq⟩
    exact CProjectTransRelComp_var_extract_right hrel heq
  · rcases hboth with ⟨b, b', heq, hrel, heq'⟩
    exact CProjectTransRelComp_var_extract_both heq hrel heq' hWFa hWFc

/-- When send is CProjectTransRelComp-related to send, partners and branches match.
    Returns the partner equality and a BranchesRel for the continuation. -/
private theorem send_branches_wf (p : String) (bs : List BranchR)
    (hWF : LocalTypeR.WellFormed (.send p bs)) :
    ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2.2 := by
  -- Extract per-branch well-formedness from send well-formedness.
  exact LocalTypeR.WellFormed.branches_of_send (p := p) (bs := bs) hWF

/- Helper: base case for CProjectTransRelComp_send_extract. -/
private theorem CProjectTransRelComp_send_extract_base
    {p1 p2 : String} {bs1 bs2 : List BranchR}
    (hbase : CProjectTransRel (.send p1 bs1) (.send p2 bs2)) :
    p1 = p2 ∧ BranchesRel (EQ2_closure CProjectTransRelComp) bs1 bs2 := by
  -- Base CProjectTransRel implies postfix EQ2F on send.
  have hbase_f := CProjectTransRel_postfix (.send p1 bs1) (.send p2 bs2) hbase
  simpa [EQ2F] using hbase_f

/- Helper: left case for CProjectTransRelComp_send_extract. -/
private theorem CProjectTransRelComp_send_extract_left
    {p1 p2 : String} {bs1 bs2 : List BranchR} {b : LocalTypeR}
    (heq : EQ2 (.send p1 bs1) b) (hrel : CProjectTransRel b (.send p2 bs2))
    (hWFa : LocalTypeR.WellFormed (.send p1 bs1))
    (hWFc : LocalTypeR.WellFormed (.send p2 bs2)) :
    p1 = p2 ∧ BranchesRel (EQ2_closure CProjectTransRelComp) bs1 bs2 := by
  cases b with -- Split the intermediate b and lift branch relations when possible.
  | send pb bbs =>
      have hWFb : LocalTypeR.WellFormed (.send pb bbs) := CProjectTransRel_wf_left hrel
      have heq_f : EQ2F EQ2 (.send p1 bs1) (.send pb bbs) := EQ2.destruct heq
      have hrel_f := CProjectTransRel_postfix (.send pb bbs) (.send p2 bs2) hrel
      simp [EQ2F] at heq_f hrel_f
      obtain ⟨hp1, hbs1⟩ := heq_f
      obtain ⟨hp2, hbs2⟩ := hrel_f
      refine ⟨hp1.trans hp2, ?_⟩
      have hWFbs1 : ∀ lb ∈ bs1, LocalTypeR.WellFormed lb.2.2 := send_branches_wf p1 bs1 hWFa
      have hWFbbs : ∀ lb ∈ bbs, LocalTypeR.WellFormed lb.2.2 := send_branches_wf pb bbs hWFb
      have hWFbs2 : ∀ lb ∈ bs2, LocalTypeR.WellFormed lb.2.2 := send_branches_wf p2 bs2 hWFc
      exact BranchesRel_trans_chain_rev_noWF
        (fun a b c => CProjectTransRelComp_extend_left_noWF (a := a) (b := b) (c := c))
        hbs1 hbs2 hWFbs1 hWFbbs hWFbs2
  | mu t body =>
      rcases CProjectTransRel_source_mu (v := t) (body := body) (b := .send p2 bs2) hrel
        with ⟨body', hEq⟩
      cases hEq
  | «end» | var _ | recv _ _ =>
      simpa [EQ2F] using (EQ2.destruct heq)

/- Helper: right case for CProjectTransRelComp_send_extract. -/
private theorem CProjectTransRelComp_send_extract_right
    {p1 p2 : String} {bs1 bs2 : List BranchR} {b : LocalTypeR}
    (hrel : CProjectTransRel (.send p1 bs1) b) (heq : EQ2 b (.send p2 bs2))
    (hWFa : LocalTypeR.WellFormed (.send p1 bs1))
    (hWFc : LocalTypeR.WellFormed (.send p2 bs2)) :
    p1 = p2 ∧ BranchesRel (EQ2_closure CProjectTransRelComp) bs1 bs2 := by
  cases b with -- Split the intermediate b and lift branch relations when possible.
  | send pb bbs =>
      have hWFb : LocalTypeR.WellFormed (.send pb bbs) := CProjectTransRel_wf_right hrel
      have hrel_f := CProjectTransRel_postfix (.send p1 bs1) (.send pb bbs) hrel
      have heq_f : EQ2F EQ2 (.send pb bbs) (.send p2 bs2) := EQ2.destruct heq
      simp [EQ2F] at hrel_f heq_f; obtain ⟨hp1, hbs1⟩ := hrel_f; obtain ⟨hp2, hbs2⟩ := heq_f
      refine ⟨hp1.trans hp2, ?_⟩
      have hWFbs1 : ∀ lb ∈ bs1, LocalTypeR.WellFormed lb.2.2 := send_branches_wf p1 bs1 hWFa
      have hWFbbs : ∀ lb ∈ bbs, LocalTypeR.WellFormed lb.2.2 := send_branches_wf pb bbs hWFb
      have hWFbs2 : ∀ lb ∈ bs2, LocalTypeR.WellFormed lb.2.2 := send_branches_wf p2 bs2 hWFc
      exact BranchesRel_trans_chain_noWF
        (fun a b c => CProjectTransRelComp_extend_right_noWF (a := a) (b := b) (c := c))
        hbs1 hbs2 hWFbs1 hWFbbs hWFbs2
  | mu t body =>
      rcases CProjectTransRel_source_send (p := p1) (bs := bs1) (b := .mu t body) hrel with
        ⟨cs, hEq⟩
      cases hEq
  | «end» =>
      have hrel_f := CProjectTransRel_postfix (.send p1 bs1) .end (by simpa using hrel)
      simpa [EQ2F] using hrel_f
  | var v =>
      have hrel_f := CProjectTransRel_postfix (.send p1 bs1) (.var v) (by simpa using hrel)
      simpa [EQ2F] using hrel_f
  | recv q cs =>
      have hrel_f := CProjectTransRel_postfix (.send p1 bs1) (.recv q cs) (by simpa using hrel)
      simpa [EQ2F] using hrel_f

/- Helper: both case for CProjectTransRelComp_send_extract. -/
private theorem CProjectTransRelComp_send_extract_both
    {p1 p2 : String} {bs1 bs2 : List BranchR} {b b' : LocalTypeR}
    (heq : EQ2 (.send p1 bs1) b) (hrel : CProjectTransRel b b') (heq' : EQ2 b' (.send p2 bs2))
    (hWFa : LocalTypeR.WellFormed (.send p1 bs1))
    (hWFc : LocalTypeR.WellFormed (.send p2 bs2)) :
    p1 = p2 ∧ BranchesRel (EQ2_closure CProjectTransRelComp) bs1 bs2 := by
  -- Compose EQ2 ∘ CProjectTransRel ∘ EQ2, then destruct the send case.
  have hcomp :=
    EQ2_CProjectTransRel_EQ2_compose (a := .send p1 bs1) (c := .send p2 bs2) heq hrel heq'
      hWFa hWFc
  simpa [EQ2F] using hcomp

theorem CProjectTransRelComp_send_extract
    {p1 p2 : String} {bs1 bs2 : List BranchR}
    (h : CProjectTransRelComp (.send p1 bs1) (.send p2 bs2))
    (hWFa : LocalTypeR.WellFormed (.send p1 bs1))
    (hWFc : LocalTypeR.WellFormed (.send p2 bs2)) :
    p1 = p2 ∧ BranchesRel (EQ2_closure CProjectTransRelComp) bs1 bs2 := by
  rcases h with hbase | hleft | hright | hboth -- Split the composed relation into base/left/right/both cases.
  · exact CProjectTransRelComp_send_extract_base hbase
  · rcases hleft with ⟨b, heq, hrel⟩
    exact CProjectTransRelComp_send_extract_left heq hrel hWFa hWFc
  · rcases hright with ⟨b, hrel, heq⟩
    exact CProjectTransRelComp_send_extract_right hrel heq hWFa hWFc
  · rcases hboth with ⟨b, b', heq, hrel, heq'⟩
    exact CProjectTransRelComp_send_extract_both heq hrel heq' hWFa hWFc

/-- When recv is CProjectTransRelComp-related to recv, partners and branches match.
    Returns the partner equality and a BranchesRel for the continuation. -/
theorem recv_branches_wf (p : String) (bs : List BranchR)
    (hWF : LocalTypeR.WellFormed (.recv p bs)) :
    ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2.2 := by
  -- Extract per-branch well-formedness from recv well-formedness.
  exact LocalTypeR.WellFormed.branches_of_recv (p := p) (bs := bs) hWF

/- Helper: base case for CProjectTransRelComp_recv_extract. -/
end Choreography.Projection.Project
