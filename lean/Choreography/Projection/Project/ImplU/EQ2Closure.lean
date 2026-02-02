import Choreography.Projection.Project.ImplBase

/-! # Choreography.Projection.Project.ImplU.EQ2Closure

CProjectU EQ2 closure: CProjectUEQ2Rel and postfix cases for end, var, mu.
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

/-! ### CProjectU (unfolding-insensitive) EQ2 closure

This is the Coq-style path: project on fully-unfolded global/local types.
It avoids requiring exact constructor matching on the raw candidate. -/

def CProjectUEQ2Rel : ProjRel := fun g role cand =>
  ∃ e0, CProjectU g role e0 ∧ EQ2 e0 cand ∧ LocalTypeR.WellFormed e0 ∧ LocalTypeR.WellFormed cand

private theorem wf_tail_of_cons
    {lb : BranchR} {lbs : List BranchR}
    (hwf : ∀ lb' ∈ lb :: lbs, LocalTypeR.WellFormed lb'.2.2) :
    ∀ lb' ∈ lbs, LocalTypeR.WellFormed lb'.2.2 := by
  -- Derive tail well-formedness from a cons list witness.
  intro lb' hmem
  exact hwf lb' (by simp [hmem])

theorem BranchesProjRel_lift_EQ2_U
    {gbs : List (Label × GlobalType)} {role : String}
    {lbs0 lbs1 : List BranchR}
    (hproj : BranchesProjRel CProjectU gbs role lbs0)
    (heq : BranchesRel EQ2 lbs0 lbs1)
    (hwf0 : ∀ lb ∈ lbs0, LocalTypeR.WellFormed lb.2.2)
    (hwf1 : ∀ lb ∈ lbs1, LocalTypeR.WellFormed lb.2.2) :
    BranchesProjRel CProjectUEQ2Rel gbs role lbs1 := by
  -- Lift each branch pointwise through EQ2, preserving well-formedness.
  induction hproj generalizing lbs1 with
  | nil => cases heq; exact List.Forall₂.nil
  | cons hpair hrest ih =>
      rename_i gb lb0 gbs' lbs0'
      cases heq with
      | cons hpair' heq_rest =>
          rename_i lb1 lbs1'
          constructor
          · constructor
            · exact hpair.1.trans hpair'.1
            · exact ⟨lb0.2.2, hpair.2, hpair'.2, hwf0 lb0 (by simp), hwf1 lb1 (by simp)⟩
          · exact ih heq_rest (wf_tail_of_cons hwf0) (wf_tail_of_cons hwf1)

private theorem EQ2_fullUnfold_end {e : LocalTypeR} (hWF : LocalTypeR.WellFormed e) :
    EQ2 .end e → e.fullUnfold = .end := by
  intro heq
  have hobs := SessionCoTypes.Bisim.EQ2_transfer_observable heq
    (SessionCoTypes.Observable.Observable.is_end
      SessionCoTypes.Observable.UnfoldsToEnd.base) hWF
  rcases hobs with ⟨_, hrel⟩
  cases hrel with
  | is_end =>
      rename_i ha hb
      exact SessionCoTypes.Bisim.UnfoldsToEnd.fullUnfold_eq hb hWF
  | is_var =>
      rename_i v ha hb
      have hcontra : False :=
        (SessionCoTypes.Observable.UnfoldsToEnd.not_var_of_end
          (a := .end) (SessionCoTypes.Observable.UnfoldsToEnd.base)) v ha
      cases hcontra
  | is_send hbr =>
      rename_i p bs cs ha hb
      have hcontra : False :=
        (SessionCoTypes.Observable.CanSend.not_end (a := .end) (p := p) (bs := bs) ha)
          (SessionCoTypes.Observable.UnfoldsToEnd.base)
      cases hcontra
  | is_recv hbr =>
      rename_i p bs cs ha hb
      have hcontra : False :=
        (SessionCoTypes.Observable.CanRecv.not_end (a := .end) (p := p) (bs := bs) ha)
          (SessionCoTypes.Observable.UnfoldsToEnd.base)
      cases hcontra

private theorem EQ2_fullUnfold_end_wf {e : LocalTypeR} (hWF : LocalTypeR.WellFormed e) :
    EQ2 .end e → e.fullUnfold = .end := by
  exact EQ2_fullUnfold_end hWF


private theorem EQ2_fullUnfold_var {t : String} {e : LocalTypeR} (hWF : LocalTypeR.WellFormed e) :
    EQ2 (.var t) e → e.fullUnfold = .var t := by
  -- Transfer observables through EQ2 and eliminate impossible cases.
  intro heq
  have hobs := SessionCoTypes.Bisim.EQ2_transfer_observable heq
    (SessionCoTypes.Observable.Observable.is_var
      (SessionCoTypes.Observable.UnfoldsToVar.base (v := t))) hWF
  rcases hobs with ⟨_, hrel⟩
  cases hrel with
  | is_var =>
      rename_i v ha hb
      have hv := SessionCoTypes.Observable.UnfoldsToVar.deterministic ha
        (SessionCoTypes.Observable.UnfoldsToVar.base (v := t))
      subst hv
      exact SessionCoTypes.Bisim.UnfoldsToVar.fullUnfold_eq hb hWF
  | is_end =>
      rename_i ha hb
      cases (SessionCoTypes.Observable.UnfoldsToEnd.not_var (v := t)) ha
  | is_send hbr =>
      rename_i p bs cs ha hb
      cases
        (SessionCoTypes.Observable.CanSend.not_var
          (a := .var t) (p := p) (bs := bs) ha) t
          (SessionCoTypes.Observable.UnfoldsToVar.base (v := t))
  | is_recv hbr =>
      rename_i p bs cs ha hb
      cases
        (SessionCoTypes.Observable.CanRecv.not_var
          (a := .var t) (p := p) (bs := bs) ha) t
          (SessionCoTypes.Observable.UnfoldsToVar.base (v := t))
private theorem EQ2_fullUnfold_var_wf {t : String} {e : LocalTypeR} (hWF : LocalTypeR.WellFormed e) :
    EQ2 (.var t) e → e.fullUnfold = .var t := by
  exact EQ2_fullUnfold_var (t := t) hWF


theorem EQ2_fullUnfold_send {p : String} {bs : List BranchR}
    {e : LocalTypeR} (hWF : LocalTypeR.WellFormed e) :
    EQ2 (.send p bs) e → ∃ cs, e.fullUnfold = .send p cs ∧ BranchesRel EQ2 bs cs := by
  intro heq -- Transfer observables through EQ2 and eliminate impossible cases.
  have hobs := SessionCoTypes.Bisim.EQ2_transfer_observable heq
    (SessionCoTypes.Observable.Observable.is_send
      (SessionCoTypes.Observable.CanSend.base (partner := p) (branches := bs))) hWF
  rcases hobs with ⟨_, hrel⟩
  cases hrel with
  | is_send hbr =>
      rename_i p' bs' cs' ha hb
      have ⟨hp, hbs⟩ := SessionCoTypes.Observable.CanSend.deterministic ha
        (SessionCoTypes.Observable.CanSend.base (partner := p) (branches := bs))
      subst hp hbs
      exact ⟨_, SessionCoTypes.Bisim.CanSend.fullUnfold_eq hb hWF, hbr⟩
  | is_end =>
      rename_i ha hb
      cases (SessionCoTypes.Observable.UnfoldsToEnd.not_send (p := p) (bs := bs)) ha
  | is_var =>
      rename_i v ha hb
      cases
        (SessionCoTypes.Observable.CanSend.not_var
          (a := .send p bs) (p := p) (bs := bs)
          (SessionCoTypes.Observable.CanSend.base (partner := p) (branches := bs))) v ha
  | is_recv hbr =>
      rename_i p' bs' cs' ha hb
      cases
        (SessionCoTypes.Observable.CanSend.not_recv
          (a := .send p bs) (p := p) (q := p') (bs := bs) (cs := bs')
          (SessionCoTypes.Observable.CanSend.base (partner := p) (branches := bs))) ha
private theorem EQ2_fullUnfold_send_wf {p : String} {bs : List BranchR} {e : LocalTypeR}
    (hWF : LocalTypeR.WellFormed e) :
    EQ2 (.send p bs) e →
    ∃ cs, e.fullUnfold = .send p cs ∧ BranchesRel EQ2 bs cs := by
  exact EQ2_fullUnfold_send (p := p) (bs := bs) hWF


theorem EQ2_fullUnfold_recv {p : String} {bs : List BranchR}
    {e : LocalTypeR} (hWF : LocalTypeR.WellFormed e) :
    EQ2 (.recv p bs) e → ∃ cs, e.fullUnfold = .recv p cs ∧ BranchesRel EQ2 bs cs := by
  intro heq -- Transfer observables through EQ2 and eliminate impossible cases.
  have hobs := SessionCoTypes.Bisim.EQ2_transfer_observable heq
    (SessionCoTypes.Observable.Observable.is_recv
      (SessionCoTypes.Observable.CanRecv.base (partner := p) (branches := bs))) hWF
  rcases hobs with ⟨_, hrel⟩; cases hrel with
  | is_recv hbr =>
      rename_i p' bs' cs' ha hb
      have ⟨hp, hbs⟩ := SessionCoTypes.Observable.CanRecv.deterministic ha
        (SessionCoTypes.Observable.CanRecv.base (partner := p) (branches := bs))
      subst hp hbs
      exact ⟨_, SessionCoTypes.Bisim.CanRecv.fullUnfold_eq hb hWF, hbr⟩
  | is_end =>
      rename_i ha hb
      cases (SessionCoTypes.Observable.UnfoldsToEnd.not_recv (p := p) (bs := bs)) ha
  | is_var =>
      rename_i v ha hb
      cases
        (SessionCoTypes.Observable.CanRecv.not_var
          (a := .recv p bs) (p := p) (bs := bs)
          (SessionCoTypes.Observable.CanRecv.base (partner := p) (branches := bs))) v ha
  | is_send hbr =>
      rename_i p' bs' cs' ha hb
      cases
        (SessionCoTypes.Observable.CanSend.not_recv
          (a := .recv p bs) (p := p') (q := p) (bs := bs') (cs := bs) ha)
          (SessionCoTypes.Observable.CanRecv.base (partner := p) (branches := bs))

private theorem EQ2_fullUnfold_recv_wf {p : String} {bs : List BranchR} {e : LocalTypeR}
    (hWF : LocalTypeR.WellFormed e) :
    EQ2 (.recv p bs) e →
    ∃ cs, e.fullUnfold = .recv p cs ∧ BranchesRel EQ2 bs cs := by
  exact EQ2_fullUnfold_recv (p := p) (bs := bs) hWF

theorem EQ2_of_fullUnfold
    {e0 cand x : LocalTypeR}
    (heq_full : EQ2 e0 e0.fullUnfold) (heq : EQ2 e0 cand)
    (hWF_full : LocalTypeR.WellFormed e0.fullUnfold)
    (hWF : LocalTypeR.WellFormed e0) (hWFcand : LocalTypeR.WellFormed cand)
    (he0 : e0.fullUnfold = x) :
    EQ2 x cand := by
  -- Transfer EQ2 through a concrete fullUnfold equality.
  have heq_e0_x : EQ2 e0 x := by
    simpa [he0] using heq_full
  have hWF_x : LocalTypeR.WellFormed x := by
    simpa [he0] using hWF_full
  exact EQ2_trans_wf (EQ2_symm heq_e0_x) heq hWF_x hWF hWFcand

theorem cand_fullUnfold_eq_end
    {e0 cand : LocalTypeR}
    (heq_full : EQ2 e0 e0.fullUnfold) (heq : EQ2 e0 cand)
    (hWF_full : LocalTypeR.WellFormed e0.fullUnfold)
    (hWF : LocalTypeR.WellFormed e0) (hWFcand : LocalTypeR.WellFormed cand)
    (he0 : e0.fullUnfold = .end) :
    cand.fullUnfold = .end := by
  -- Derive EQ2 .end cand and apply the end fullUnfold lemma.
  have heq_end : EQ2 .end cand := EQ2_of_fullUnfold heq_full heq hWF_full hWF hWFcand he0
  exact EQ2_fullUnfold_end hWFcand heq_end

theorem EQ2_fullUnfold_to_fullUnfold
    {e0 cand : LocalTypeR}
    (heq_full : EQ2 e0 e0.fullUnfold) (heq : EQ2 e0 cand)
    (hWF_full : LocalTypeR.WellFormed e0.fullUnfold) (hWF : LocalTypeR.WellFormed e0)
    (hWFcand : LocalTypeR.WellFormed cand) (hWFcand_full : LocalTypeR.WellFormed cand.fullUnfold) :
    EQ2 e0.fullUnfold cand.fullUnfold := by
  -- Chain EQ2 through cand to reach cand.fullUnfold.
  have heq_full_cand : EQ2 e0.fullUnfold cand :=
    EQ2_trans_wf (EQ2_symm heq_full) heq hWF_full hWF hWFcand
  have heq_cand_full : EQ2 cand cand.fullUnfold := by
    have hiter := (EQ2_unfold_right_iter (a := cand) (b := cand) (EQ2_refl cand)) cand.muHeight
    simpa [LocalTypeR.fullUnfold] using hiter
  exact EQ2_trans_wf heq_full_cand heq_cand_full hWF_full hWFcand hWFcand_full

private theorem AllBranchesProj_lift_EQ2_U
    {gbs : List (Label × GlobalType)} {role : String}
    {e0_full cand_full : LocalTypeR}
    (heq_full_cand_full : EQ2 e0_full cand_full)
    (hWF_full : LocalTypeR.WellFormed e0_full)
    (hWFcand_full : LocalTypeR.WellFormed cand_full)
    (hall : AllBranchesProj CProjectU gbs role e0_full) :
    AllBranchesProj CProjectUEQ2Rel gbs role cand_full := by
  -- Lift each branch witness through EQ2 to CProjectUEQ2Rel.
  intro gb hgb
  have hproj' : CProjectU gb.2 role e0_full := hall gb hgb
  exact ⟨e0_full, hproj', heq_full_cand_full, hWF_full, hWFcand_full⟩

theorem CProjectUEQ2Rel_comm_nonpart
    {gbs : List (Label × GlobalType)} {role : String}
    {e0_full cand_full : LocalTypeR}
    (heq_full_cand_full : EQ2 e0_full cand_full)
    (hWF_full : LocalTypeR.WellFormed e0_full)
    (hWFcand_full : LocalTypeR.WellFormed cand_full)
    (hcore_nonpart :
      (∀ pair, pair ∈ gbs → part_of_all2 role pair.2) ∧ AllBranchesProj CProjectU gbs role e0_full) :
    (∀ pair, pair ∈ gbs → part_of_all2 role pair.2) ∧ AllBranchesProj CProjectUEQ2Rel gbs role cand_full := by
  -- Preserve the non-participant constraint and lift AllBranchesProj.
  rcases hcore_nonpart with ⟨hpart_all, hall⟩
  have hall' := AllBranchesProj_lift_EQ2_U heq_full_cand_full hWF_full hWFcand_full hall
  exact ⟨hpart_all, hall'⟩

theorem CProjectUEQ2Rel_postfix_end_case
    {g role cand e0 : _}
    (hg : GlobalType.fullUnfoldIter g = .end)
    (hcore : CProjectF_unfold_core CProjectU (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold e0))
    (heq_full : EQ2 e0 e0.fullUnfold) (heq : EQ2 e0 cand)
    (hWF_full : LocalTypeR.WellFormed e0.fullUnfold)
    (hWF : LocalTypeR.WellFormed e0) (hWFcand : LocalTypeR.WellFormed cand) :
    CProjectF_unfold_core CProjectUEQ2Rel (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold cand) := by
  -- Global end: only local end survives; all other cases contradict hcore.
  cases he0 : LocalTypeR.fullUnfold e0 with
  | «end» =>
      have hcand : cand.fullUnfold = .end :=
        cand_fullUnfold_eq_end heq_full heq hWF_full hWF hWFcand he0
      simpa [CProjectF_unfold_core, CProjectF, hg, hcand]
  | var _ =>
      have : False := by simpa [CProjectF_unfold_core, CProjectF, hg, he0] using hcore
      exact this.elim
  | send _ _ =>
      have : False := by simpa [CProjectF_unfold_core, CProjectF, hg, he0] using hcore
      exact this.elim
  | recv _ _ =>
      have : False := by simpa [CProjectF_unfold_core, CProjectF, hg, he0] using hcore
      exact this.elim
  | mu _ _ =>
      have : False := by simpa [CProjectF_unfold_core, CProjectF, hg, he0] using hcore
      exact this.elim

theorem CProjectUEQ2Rel_postfix_var_case
    {g role cand e0 : _} {v : String}
    (hg : GlobalType.fullUnfoldIter g = .var v)
    (hcore : CProjectF_unfold_core CProjectU (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold e0))
    (heq_full : EQ2 e0 e0.fullUnfold) (heq : EQ2 e0 cand)
    (hWF_full : LocalTypeR.WellFormed e0.fullUnfold)
    (hWF : LocalTypeR.WellFormed e0) (hWFcand : LocalTypeR.WellFormed cand) :
    CProjectF_unfold_core CProjectUEQ2Rel (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold cand) := by
  -- Global var: either non-participant end or contradiction by hcore.
  cases he0 : LocalTypeR.fullUnfold e0 with
  | var v' =>
      have hcontra := LocalTypeR.fullUnfold_not_var_of_closed (lt := e0) hWF.closed v'
      exact (False.elim (hcontra (by simpa [he0])))
  | «end» =>
      have hnonpart : ¬part_of2 role (GlobalType.fullUnfoldIter g) := by
        simpa [CProjectF_unfold_core, CProjectF, hg, he0] using hcore
      have hcand : cand.fullUnfold = .end :=
        cand_fullUnfold_eq_end heq_full heq hWF_full hWF hWFcand he0
      exact Or.inl ⟨hnonpart, hcand⟩
  | send _ _ =>
      have : False := by simpa [CProjectF_unfold_core, CProjectF, hg, he0] using hcore
      exact this.elim
  | recv _ _ =>
      have : False := by simpa [CProjectF_unfold_core, CProjectF, hg, he0] using hcore
      exact this.elim
  | mu _ _ =>
      have : False := by simpa [CProjectF_unfold_core, CProjectF, hg, he0] using hcore
      exact this.elim

theorem CProjectUEQ2Rel_postfix_mu_end_case
    {g role cand e0 : _} {t : String} {body : GlobalType}
    (hg : GlobalType.fullUnfoldIter g = .mu t body)
    (hcore : CProjectF_unfold_core CProjectU (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold e0))
    (heq_full : EQ2 e0 e0.fullUnfold) (heq : EQ2 e0 cand)
    (hWF_full : LocalTypeR.WellFormed e0.fullUnfold)
    (hWF : LocalTypeR.WellFormed e0) (hWFcand : LocalTypeR.WellFormed cand)
    (hWFproj : ∀ g role cand, CProjectU g role cand → LocalTypeR.WellFormed cand)
    (he0 : LocalTypeR.fullUnfold e0 = .end) :
    CProjectF_unfold_core CProjectUEQ2Rel (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold cand) := by
  -- Mu with end local: either non-participant end or unguarded mu case.
  have hcand : cand.fullUnfold = .end :=
    cand_fullUnfold_eq_end heq_full heq hWF_full hWF hWFcand he0
  have hcore' :
      ¬part_of2 role (GlobalType.mu t body) ∨
        ∃ candBody, CProjectU body role candBody ∧ candBody.isGuarded t = false :=
    by simpa [CProjectF_unfold_core, CProjectF, hg, he0] using hcore
  cases hcore' with
  | inl hnonpart =>
      have hnonpart' : ¬part_of2 role (GlobalType.fullUnfoldIter g) := by simpa [hg] using hnonpart
      exact Or.inl ⟨hnonpart', hcand⟩
  | inr hmu =>
      rcases hmu with ⟨candBody, hbody_proj, hguard⟩
      have hWFcandBody : LocalTypeR.WellFormed candBody := hWFproj _ _ _ hbody_proj
      have hrel : CProjectUEQ2Rel body role candBody :=
        ⟨candBody, hbody_proj, EQ2_refl candBody, hWFcandBody, hWFcandBody⟩
      exact Or.inr (by
        simpa [CProjectF_unfold_core, CProjectF, hg, he0] using
          ⟨candBody, hrel, Or.inr ⟨hguard, hcand⟩⟩)

end Choreography.Projection.Project
