import Choreography.Projection.Project.ImplTransRelComp.Core

/-! # Choreography.Projection.Project.ImplTransRelComp.CommCases

Comm-level postfix cases for CProjectTransRel.
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
private theorem CProjectTransRel_postfix_comm_send_sender
    {sender receiver role partner : String}
    {gbs : List (Label × GlobalType)} {lbs : List BranchR} {t : LocalTypeR}
    (hrs : role = sender)
    (hf : CProjectF CProject (GlobalType.comm sender receiver gbs) role (LocalTypeR.send partner lbs))
    (htrans : t = Trans.trans (GlobalType.comm sender receiver gbs) role)
    (hwf : (GlobalType.comm sender receiver gbs).wellFormed = true) :
    EQ2F (EQ2_closure CProjectTransRelComp) (LocalTypeR.send partner lbs) t := by
  -- Sender case: lift BranchesProjRel to BranchesRel and wrap into the closure.
  simp [CProjectF, hrs] at hf
  obtain ⟨hpartner, hbranches⟩ := hf
  have hwf_branches : ∀ gb, gb ∈ gbs → gb.2.wellFormed = true := by
    intro gb hmem
    exact GlobalType.wellFormed_comm_branches sender receiver gbs hwf gb hmem
  subst htrans
  rw [hrs, trans_comm_sender sender receiver sender gbs rfl, hpartner]
  exact ⟨rfl, BranchesRel_mono (fun _ _ hr => Or.inl (Or.inl hr))
    (branchesProjRel_to_branchesRel_CProjectTransRel gbs sender lbs hbranches hwf_branches)⟩

private theorem CProjectTransRel_postfix_comm_send_nonpart
    {sender receiver role partner : String}
    {gbs : List (Label × GlobalType)} {lbs : List BranchR} {t : LocalTypeR}
    (hproj : CProject (GlobalType.comm sender receiver gbs) role (LocalTypeR.send partner lbs))
    (htrans : t = Trans.trans (GlobalType.comm sender receiver gbs) role)
    (hwf : (GlobalType.comm sender receiver gbs).wellFormed = true) :
    EQ2F (EQ2_closure CProjectTransRelComp) (LocalTypeR.send partner lbs) t := by
  -- Non-participant send: use the extracted comm witness from CProject_send_implies_trans_send.
  have hexists := CProject_send_implies_trans_send
    (GlobalType.comm sender receiver gbs) role partner lbs hproj hwf
  obtain ⟨gbs', htrans_send, hbranches', hwf_gbs'⟩ := hexists
  subst htrans
  rw [htrans_send]
  exact ⟨rfl, BranchesRel_mono (fun _ _ hr => Or.inl (Or.inl hr))
    (branchesProjRel_to_branchesRel_CProjectTransRel gbs' role lbs hbranches' hwf_gbs')⟩

private theorem CProjectTransRel_postfix_comm_recv_receiver
    {sender receiver role partner : String}
    {gbs : List (Label × GlobalType)} {lbs : List BranchR} {t : LocalTypeR}
    (hrr : role = receiver) (hne : receiver ≠ sender)
    (hf : CProjectF CProject (GlobalType.comm sender receiver gbs) role (LocalTypeR.recv partner lbs))
    (htrans : t = Trans.trans (GlobalType.comm sender receiver gbs) role)
    (hwf : (GlobalType.comm sender receiver gbs).wellFormed = true) :
    EQ2F (EQ2_closure CProjectTransRelComp) (LocalTypeR.recv partner lbs) t := by
  -- Receiver case: lift BranchesProjRel to BranchesRel and wrap into the closure.
  simp [CProjectF, hrr, hne] at hf
  obtain ⟨hpartner, hbranches⟩ := hf
  have hwf_branches : ∀ gb, gb ∈ gbs → gb.2.wellFormed = true := by
    intro gb hmem
    exact GlobalType.wellFormed_comm_branches sender receiver gbs hwf gb hmem
  subst htrans
  rw [hrr, trans_comm_receiver sender receiver receiver gbs rfl hne, hpartner]
  exact ⟨rfl, BranchesRel_mono (fun _ _ hr => Or.inl (Or.inl hr))
    (branchesProjRel_to_branchesRel_CProjectTransRel gbs receiver lbs hbranches hwf_branches)⟩

private theorem CProjectTransRel_postfix_comm_recv_nonpart
    {sender receiver role partner : String}
    {gbs : List (Label × GlobalType)} {lbs : List BranchR} {t : LocalTypeR}
    (hproj : CProject (GlobalType.comm sender receiver gbs) role (LocalTypeR.recv partner lbs))
    (htrans : t = Trans.trans (GlobalType.comm sender receiver gbs) role)
    (hwf : (GlobalType.comm sender receiver gbs).wellFormed = true) :
    EQ2F (EQ2_closure CProjectTransRelComp) (LocalTypeR.recv partner lbs) t := by
  -- Non-participant recv: use the extracted comm witness from CProject_recv_implies_trans_recv.
  have hexists := CProject_recv_implies_trans_recv
    (GlobalType.comm sender receiver gbs) role partner lbs hproj hwf
  obtain ⟨gbs', htrans_recv, hbranches', hwf_gbs'⟩ := hexists
  subst htrans
  rw [htrans_recv]
  exact ⟨rfl, BranchesRel_mono (fun _ _ hr => Or.inl (Or.inl hr))
    (branchesProjRel_to_branchesRel_CProjectTransRel gbs' role lbs hbranches' hwf_gbs')⟩

private theorem CProjectTransRel_postfix_comm_send
    {sender receiver role partner : String}
    {gbs : List (Label × GlobalType)} {lbs : List BranchR} {t : LocalTypeR}
    (hproj : CProject (GlobalType.comm sender receiver gbs) role (LocalTypeR.send partner lbs))
    (htrans : t = Trans.trans (GlobalType.comm sender receiver gbs) role)
    (hwf : (GlobalType.comm sender receiver gbs).wellFormed = true)
    (hf : CProjectF CProject (GlobalType.comm sender receiver gbs) role (LocalTypeR.send partner lbs)) :
    EQ2F (EQ2_closure CProjectTransRelComp) (LocalTypeR.send partner lbs) t := by
  -- Split on the role to select sender/non-participant cases.
  by_cases hrs : role = sender
  · exact CProjectTransRel_postfix_comm_send_sender (t := t) hrs hf htrans hwf
  · by_cases hrr : role = receiver
    ·
      have hne' : receiver ≠ sender := fun heq => hrs (hrr ▸ heq)
      have : False := by simpa [CProjectF, hrr, hne'] using hf
      exact this.elim
    · exact CProjectTransRel_postfix_comm_send_nonpart (t := t) hproj htrans hwf

private theorem CProjectTransRel_postfix_comm_recv
    {sender receiver role partner : String}
    {gbs : List (Label × GlobalType)} {lbs : List BranchR} {t : LocalTypeR}
    (hproj : CProject (GlobalType.comm sender receiver gbs) role (LocalTypeR.recv partner lbs))
    (htrans : t = Trans.trans (GlobalType.comm sender receiver gbs) role)
    (hwf : (GlobalType.comm sender receiver gbs).wellFormed = true)
    (hf : CProjectF CProject (GlobalType.comm sender receiver gbs) role (LocalTypeR.recv partner lbs)) :
    EQ2F (EQ2_closure CProjectTransRelComp) (LocalTypeR.recv partner lbs) t := by
  -- Split on the role to select receiver/non-participant cases.
  by_cases hrs : role = sender
  ·
    have : False := by simpa [CProjectF, hrs] using hf
    exact this.elim
  · by_cases hrr : role = receiver
    · have hne' : receiver ≠ sender := fun heq => hrs (hrr ▸ heq)
      exact CProjectTransRel_postfix_comm_recv_receiver (t := t) hrr hne' hf htrans hwf
    · exact CProjectTransRel_postfix_comm_recv_nonpart (t := t) hproj htrans hwf

private theorem CProjectTransRel_postfix_comm_end
    {sender receiver role : String}
    {gbs : List (Label × GlobalType)} {t : LocalTypeR}
    (hproj : CProject (GlobalType.comm sender receiver gbs) role LocalTypeR.end)
    (hne : (GlobalType.comm sender receiver gbs).allCommsNonEmpty = true)
    (htrans : t = Trans.trans (GlobalType.comm sender receiver gbs) role) :
    EQ2F (EQ2_closure CProjectTransRelComp) LocalTypeR.end t := by
  -- Non-participant projecting to .end via CProject_end_trans_end.
  have htrans_end := CProject_end_trans_end (GlobalType.comm sender receiver gbs) role hproj hne
  subst htrans
  rw [htrans_end]
  simp [EQ2F]

private theorem CProjectTransRel_postfix_comm_var
    {sender receiver role v : String}
    {gbs : List (Label × GlobalType)} {t : LocalTypeR}
    (hproj : CProject (GlobalType.comm sender receiver gbs) role (LocalTypeR.var v))
    (hne : (GlobalType.comm sender receiver gbs).allCommsNonEmpty = true)
    (htrans : t = Trans.trans (GlobalType.comm sender receiver gbs) role) :
    EQ2F (EQ2_closure CProjectTransRelComp) (LocalTypeR.var v) t := by
  -- Non-participant projecting to .var via CProject_var_trans_var.
  have htrans_var := CProject_var_trans_var (GlobalType.comm sender receiver gbs) role v hproj hne
  subst htrans
  rw [htrans_var]
  simp [EQ2F]

private theorem CProjectTransRel_postfix_comm_mu
    {sender receiver role ltvar : String} {gbs : List (Label × GlobalType)}
    {lbody t : LocalTypeR}
    (hproj : CProject (GlobalType.comm sender receiver gbs) role (LocalTypeR.mu ltvar lbody))
    (htrans : t = Trans.trans (GlobalType.comm sender receiver gbs) role)
    (hne : (GlobalType.comm sender receiver gbs).allCommsNonEmpty = true)
    (hwf : (GlobalType.comm sender receiver gbs).wellFormed = true) :
    EQ2F (EQ2_closure CProjectTransRelComp) (LocalTypeR.mu ltvar lbody) t := by
  -- Non-participant mu: extract body and apply the mu closure helper.
  have hexists := CProject_mu_implies_trans_mu
    (GlobalType.comm sender receiver gbs) role ltvar lbody hproj hne
  obtain ⟨gbody, htrans_mu, hcontr, hbody_proj, _hwf_body⟩ := hexists
  subst htrans
  have hmu_rel :
      CProjectTransRel (LocalTypeR.mu ltvar lbody)
        (LocalTypeR.mu ltvar (Trans.trans gbody role)) := by
    -- Package CProject with the computed trans equality.
    have htrans_mu' :
        Trans.trans (GlobalType.comm sender receiver gbs) role =
          LocalTypeR.mu ltvar (Trans.trans gbody role) := by
      simpa using htrans_mu
    exact ⟨GlobalType.comm sender receiver gbs, role, hproj, htrans_mu'.symm, hwf⟩
  simpa [htrans_mu] using CProjectTransRel_postfix_mu_closure hmu_rel

/-- Helper: g = .end cases for CProjectTransRel_postfix. -/
private theorem CProjectTransRel_postfix_end_cases
    {role : String} {lt t : LocalTypeR}
    (hf : CProjectF CProject GlobalType.end role lt)
    (htrans : t = Trans.trans GlobalType.end role) :
    EQ2F (EQ2_closure CProjectTransRelComp) lt t := by
  -- Only the .end candidate is possible.
  cases lt with
  | «end» =>
      exact CProjectTransRel_postfix_end (role := role) (t := t) htrans
  | var _ | send _ _ | recv _ _ | mu _ _ =>
      -- Other constructors contradict CProjectF for .end.
      have : False := by simpa [CProjectF] using hf
      exact this.elim

/-- Helper: g = .var cases for CProjectTransRel_postfix. -/
private theorem CProjectTransRel_postfix_var_cases
    {vt : String} {role : String} {lt t : LocalTypeR}
    (hf : CProjectF CProject (GlobalType.var vt) role lt)
    (htrans : t = Trans.trans (GlobalType.var vt) role) :
    EQ2F (EQ2_closure CProjectTransRelComp) lt t := by
  -- Only the .var candidate is possible.
  cases lt with
  | var vlt =>
      exact CProjectTransRel_postfix_var (vt := vt) (vlt := vlt) hf htrans
  | «end» | send _ _ | recv _ _ | mu _ _ =>
      -- Other constructors contradict CProjectF for .var.
      have : False := by simpa [CProjectF] using hf
      exact this.elim

/-- Helper: g = .mu cases for CProjectTransRel_postfix. -/
private theorem CProjectTransRel_postfix_mu_cases
    {muvar : String} {gbody : GlobalType} {role : String} {lt t : LocalTypeR}
    (hproj : CProject (GlobalType.mu muvar gbody) role lt)
    (htrans : t = Trans.trans (GlobalType.mu muvar gbody) role)
    (hwf : (GlobalType.mu muvar gbody).wellFormed = true)
    (hne : (GlobalType.mu muvar gbody).allCommsNonEmpty = true)
    (hf : CProjectF CProject (GlobalType.mu muvar gbody) role lt) :
    EQ2F (EQ2_closure CProjectTransRelComp) lt t := by
  -- Split on the local candidate shape.
  cases lt with
  | «end» =>
      exact CProjectTransRel_postfix_mu_end (_hproj := hproj) (htrans := htrans) (hne := hne) hf
  | mu ltvar lbody =>
      exact CProjectTransRel_postfix_mu_mu (hproj := hproj) (htrans := htrans) (hwf := hwf)
        (hne := hne) hf
  | var _ | send _ _ | recv _ _ =>
      -- These constructors contradict CProjectF for .mu.
      have : False := by simpa [CProjectF] using hf
      exact this.elim

/-- Helper: g = .comm cases for CProjectTransRel_postfix. -/
private theorem CProjectTransRel_postfix_comm_cases
    {sender receiver role : String} {gbs : List (Label × GlobalType)} {lt t : LocalTypeR}
    (hproj : CProject (GlobalType.comm sender receiver gbs) role lt)
    (htrans : t = Trans.trans (GlobalType.comm sender receiver gbs) role)
    (hne : (GlobalType.comm sender receiver gbs).allCommsNonEmpty = true)
    (hwf : (GlobalType.comm sender receiver gbs).wellFormed = true)
    (hf : CProjectF CProject (GlobalType.comm sender receiver gbs) role lt) :
    EQ2F (EQ2_closure CProjectTransRelComp) lt t := by
  -- Dispatch by candidate constructor.
  cases lt with
  | «end» =>
      exact CProjectTransRel_postfix_comm_end (t := t) hproj hne htrans
  | send partner lbs =>
      exact CProjectTransRel_postfix_comm_send (t := t) hproj htrans hwf hf
  | recv partner lbs =>
      exact CProjectTransRel_postfix_comm_recv (t := t) hproj htrans hwf hf
  | mu ltvar lbody =>
      exact CProjectTransRel_postfix_comm_mu (t := t) hproj htrans hne hwf
  | var v =>
      exact CProjectTransRel_postfix_comm_var (t := t) hproj hne htrans

/-- Postfix property for CProjectTransRel with EQ2_closure of the composite relation. -/
theorem CProjectTransRel_postfix :
    ∀ lt t, CProjectTransRel lt t → EQ2F (EQ2_closure CProjectTransRelComp) lt t := by
  intro lt t ⟨g, role, hproj, htrans, hwf⟩
  -- Proof strategy: reduce to CProjectF cases and dispatch by global constructor.
  have hne : g.allCommsNonEmpty = true := by
    have hwf' := hwf
    simp [GlobalType.wellFormed, Bool.and_eq_true] at hwf'
    exact hwf'.1.1.2
  have hf := CProject_destruct hproj
  cases g with
  | «end» =>
      exact CProjectTransRel_postfix_end_cases (lt := lt) hf htrans
  | var vt =>
      exact CProjectTransRel_postfix_var_cases (lt := lt) (vt := vt) hf htrans
  | mu muvar gbody =>
      exact CProjectTransRel_postfix_mu_cases (lt := lt) (muvar := muvar) (gbody := gbody)
        hproj htrans hwf hne hf
  | comm sender receiver gbs =>
      exact CProjectTransRel_postfix_comm_cases (lt := lt) (sender := sender) (receiver := receiver)
        (gbs := gbs) hproj htrans hne hwf hf

/-- CProjectTransRelComp can be extended with EQ2 at the right to produce another CProjectTransRelComp.
    This is the key lemma that allows the BranchesRel_trans_chain helper to work. -/
theorem CProjectTransRelComp_extend_right
    (h1 : CProjectTransRelComp a b) (h2 : EQ2 b c)
    (_hWFa : LocalTypeR.WellFormed a)
    (hWFb : LocalTypeR.WellFormed b)
    (hWFc : LocalTypeR.WellFormed c) :
    CProjectTransRelComp a c := by
  -- Case split on which disjunct of CProjectTransRelComp a b holds
  rcases h1 with hbase | ⟨m, heq_am, hrel_mb⟩ | ⟨m, hrel_am, heq_mb⟩ | ⟨m, m', heq_am, hrel_mm', heq_m'b⟩
  · -- Base: CProjectTransRel a b ∧ EQ2 b c → 2-hop suffix (a, c)
    right; right; left
    exact ⟨b, hbase, h2⟩
  · -- 2-hop prefix: EQ2 a m ∧ CProjectTransRel m b ∧ EQ2 b c → 3-hop (a, c)
    right; right; right
    exact ⟨m, b, heq_am, hrel_mb, h2⟩
  · -- 2-hop suffix: CProjectTransRel a m ∧ EQ2 m b ∧ EQ2 b c → 2-hop suffix with combined EQ2
    right; right; left
    have hWFm : LocalTypeR.WellFormed m := CProjectTransRel_wf_right hrel_am
    exact ⟨m, hrel_am, EQ2_trans_wf heq_mb h2 hWFm hWFb hWFc⟩
  · -- 3-hop: EQ2 a m ∧ CProjectTransRel m m' ∧ EQ2 m' b ∧ EQ2 b c → 3-hop with combined EQ2
    right; right; right
    have hWFm' : LocalTypeR.WellFormed m' := CProjectTransRel_wf_right hrel_mm'
    exact ⟨m, m', heq_am, hrel_mm', EQ2_trans_wf heq_m'b h2 hWFm' hWFb hWFc⟩

/-- Composing CProjectTransRel and EQ2 through a mu intermediate (suffix case). -/
theorem CProjectTransRelComp_extend_left
    (h1 : EQ2 a b) (h2 : CProjectTransRelComp b c)
    (hWFa : LocalTypeR.WellFormed a)
    (hWFb : LocalTypeR.WellFormed b)
    (_hWFc : LocalTypeR.WellFormed c) :
    CProjectTransRelComp a c := by
  -- Case split on which disjunct of CProjectTransRelComp b c holds
  rcases h2 with hbase | ⟨m, heq_bm, hrel_mc⟩ | ⟨m, hrel_bm, heq_mc⟩ | ⟨m, m', heq_bm, hrel_mm', heq_m'c⟩
  · -- Base: EQ2 a b ∧ CProjectTransRel b c → 2-hop prefix (a, c)
    right; left
    exact ⟨b, h1, hbase⟩
  · -- 2-hop prefix: EQ2 a b ∧ EQ2 b m ∧ CProjectTransRel m c → 2-hop prefix with combined EQ2
    right; left
    have hWFm : LocalTypeR.WellFormed m := CProjectTransRel_wf_left hrel_mc
    exact ⟨m, EQ2_trans_wf h1 heq_bm hWFa hWFb hWFm, hrel_mc⟩
  · -- 2-hop suffix: EQ2 a b ∧ CProjectTransRel b m ∧ EQ2 m c → 3-hop (a, c)
    right; right; right
    exact ⟨b, m, h1, hrel_bm, heq_mc⟩
  · -- 3-hop: EQ2 a b ∧ EQ2 b m ∧ CProjectTransRel m m' ∧ EQ2 m' c → 3-hop with combined EQ2
    right; right; right
    have hWFm : LocalTypeR.WellFormed m := CProjectTransRel_wf_left hrel_mm'
    exact ⟨m, m', EQ2_trans_wf h1 heq_bm hWFa hWFb hWFm, hrel_mm', heq_m'c⟩

/-- Chain BranchesRel with EQ2 first, then EQ2_closure (reverse direction).
    Given BranchesRel EQ2 bs cs and BranchesRel (EQ2_closure R) cs ds,
    produce BranchesRel (EQ2_closure R) bs ds.

    Requires an extension hypothesis: R can be extended with EQ2 at the left
    to produce another R. This is satisfied by CProjectTransRelComp. -/
theorem BranchesRel_trans_chain_rev {R : Rel}
    (hextend : ∀ a b c, EQ2 a b → R b c →
      LocalTypeR.WellFormed a → LocalTypeR.WellFormed b → LocalTypeR.WellFormed c → R a c)
    {bs cs ds : List BranchR}
    (hbc : BranchesRel EQ2 bs cs)
    (hcd : BranchesRel (EQ2_closure R) cs ds)
    (hwf_bs : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2.2)
    (hwf_cs : ∀ lb ∈ cs, LocalTypeR.WellFormed lb.2.2)
    (hwf_ds : ∀ lb ∈ ds, LocalTypeR.WellFormed lb.2.2) :
    BranchesRel (EQ2_closure R) bs ds := by
  -- Use Forall₂ transitivity with a head/tail split.
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
              · exact BranchesRel_trans_chain_rev_head hextend h1 h2
                  (hwf_bs lb_bs (by simp)) (hwf_cs lb_cs (by simp)) (hwf_ds lb_ds (by simp))
              · exact ih hcd_tail (wf_tail_of_cons hwf_bs)
                  (wf_tail_of_cons hwf_cs) (wf_tail_of_cons hwf_ds)


end Choreography.Projection.Project
