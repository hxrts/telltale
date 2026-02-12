import Choreography.Projection.Project.ImplU.EQ2Closure

/-! # Choreography.Projection.Project.ImplU.CommCases

CProjectU EQ2 closure: comm case postfix and final CProjectU_EQ2 theorem.
-/

/-
The Problem. State the projection/harmony lemma objective and the exact invariant boundary it preserves.
Solution Structure. Introduce local helper lemmas first, then discharge the main theorem by case analysis over the operational/projection relation.
-/

set_option linter.unnecessarySimpa false

/-! ## Core Development -/

namespace Choreography.Projection.Project

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Project
open Choreography.Projection.Projectb
open SessionCoTypes.EQ2
open SessionCoTypes.EQ2Props
open SessionCoTypes.EQ2Paco
open Paco
open SessionTypes.Participation

/-! ## Mu Postfix Case -/

private theorem CProjectUEQ2Rel_postfix_mu_case
    {g role cand e0 : _} {t : String} {body : GlobalType}
    (hg : GlobalType.fullUnfoldIter g = .mu t body)
    (hcore : CProjectF_unfold_core CProjectU (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold e0))
    (heq_full : EQ2 e0 e0.fullUnfold) (heq : EQ2 e0 cand)
    (hWF_full : LocalTypeR.WellFormed e0.fullUnfold)
    (hWF : LocalTypeR.WellFormed e0) (hWFcand : LocalTypeR.WellFormed cand)
    (hWFproj : ∀ g role cand, CProjectU g role cand → LocalTypeR.WellFormed cand) :
    CProjectF_unfold_core CProjectUEQ2Rel (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold cand) := by
  -- Mu: only end case survives after fullUnfold, others contradict hcore.
  have hmu0 : e0.fullUnfold.muHeight = 0 :=
    LocalTypeR.fullUnfold_non_mu_of_contractive (lt := e0) hWF.contractive hWF.closed
  cases he0 : LocalTypeR.fullUnfold e0 with
  | mu _ _ =>
      have : False := by simpa [LocalTypeR.muHeight, he0] using hmu0
      exact this.elim
  | «end» =>
      exact CProjectUEQ2Rel_postfix_mu_end_case (g := g) (role := role) (cand := cand)
        (e0 := e0) (t := t) (body := body) hg hcore heq_full heq hWF_full hWF hWFcand hWFproj he0
  | var _ =>
      have : False := by simpa [CProjectF_unfold_core, CProjectF, hg, he0] using hcore
      exact this.elim
  | send _ _ =>
      have : False := by simpa [CProjectF_unfold_core, CProjectF, hg, he0] using hcore
      exact this.elim
  | recv _ _ =>
      have : False := by simpa [CProjectF_unfold_core, CProjectF, hg, he0] using hcore
      exact this.elim

/-! ## Comm Postfix End/Var/Mu Cases -/

/-! ### Comm End Case -/

private theorem CProjectUEQ2Rel_postfix_comm_end_case
    {g role cand e0 : _} {sender receiver : String} {gbs : List (Label × GlobalType)}
    (hg : GlobalType.fullUnfoldIter g = .comm sender receiver gbs)
    (he0 : LocalTypeR.fullUnfold e0 = .end)
    (hcore : CProjectF_unfold_core CProjectU (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold e0))
    (heq_full : EQ2 e0 e0.fullUnfold) (heq : EQ2 e0 cand)
    (hWF_full : LocalTypeR.WellFormed e0.fullUnfold)
    (hWF : LocalTypeR.WellFormed e0) (hWFcand : LocalTypeR.WellFormed cand)
    (hWFcand_full : LocalTypeR.WellFormed cand.fullUnfold)
    (heq_full_cand_full : EQ2 e0.fullUnfold cand.fullUnfold) :
    CProjectF_unfold_core CProjectUEQ2Rel (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold cand) := by
  -- comm/end: nonparticipant end or impossible participant branches.
  have hcore' := by simpa [CProjectF_unfold_core, CProjectF, hg, he0] using hcore
  cases hcore' with
  | inl hnonpart =>
      exact Or.inl ⟨by simpa [hg] using hnonpart,
        cand_fullUnfold_eq_end heq_full heq hWF_full hWF hWFcand he0⟩
  | inr hcore'' =>
      by_cases hrs : role = sender
      · exact False.elim (by simpa [hrs] using hcore'')
      · by_cases hrr : role = receiver
        · have hne : receiver ≠ sender := by
            intro h
            exact hrs (hrr.trans h)
          exact False.elim (by simpa [hrr, hne] using hcore'')
        · have hcore_nonpart : (∀ pair, pair ∈ gbs → part_of_all2 role pair.2) ∧
              AllBranchesProj CProjectU gbs role e0.fullUnfold := by
            simpa [hrs, hrr, he0] using hcore''
          exact Or.inr (by
	            simpa [CProjectF_unfold_core, CProjectF, hg, he0, hrs, hrr] using
	              (CProjectUEQ2Rel_comm_nonpart heq_full_cand_full hWF_full hWFcand_full hcore_nonpart))

/-! ### Comm Var Case -/

private theorem CProjectUEQ2Rel_postfix_comm_var_case
    {g role cand e0 : _} {sender receiver v : String} {gbs : List (Label × GlobalType)}
    (hg : GlobalType.fullUnfoldIter g = .comm sender receiver gbs)
    (he0 : LocalTypeR.fullUnfold e0 = .var v)
    (hcore : CProjectF_unfold_core CProjectU (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold e0))
    (hWF_full : LocalTypeR.WellFormed e0.fullUnfold)
    (hWFcand_full : LocalTypeR.WellFormed cand.fullUnfold)
    (heq_full_cand_full : EQ2 e0.fullUnfold cand.fullUnfold) :
    CProjectF_unfold_core CProjectUEQ2Rel (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold cand) := by
  -- comm/var: only nonparticipant branch is possible.
  by_cases hrs : role = sender
  · exact False.elim (by simpa [CProjectF_unfold_core, CProjectF, hg, he0, hrs] using hcore)
  · by_cases hrr : role = receiver
    · have hne : receiver ≠ sender := by intro h; exact hrs (hrr.trans h)
      exact False.elim (by simpa [CProjectF_unfold_core, CProjectF, hg, he0, hrr, hne] using hcore)
    · have hcore_nonpart :
          (∀ pair, pair ∈ gbs → part_of_all2 role pair.2) ∧
            AllBranchesProj CProjectU gbs role (LocalTypeR.var v) := by
        simpa [CProjectF_unfold_core, CProjectF, hg, he0, hrs, hrr] using hcore
      have hcore_nonpart' :
          (∀ pair, pair ∈ gbs → part_of_all2 role pair.2) ∧
            AllBranchesProj CProjectU gbs role e0.fullUnfold := by
        simpa [he0] using hcore_nonpart
      have hnonpart' := CProjectUEQ2Rel_comm_nonpart
        heq_full_cand_full hWF_full hWFcand_full hcore_nonpart'
	      exact Or.inr (by
	        simpa [CProjectF_unfold_core, CProjectF, hg, he0, hrs, hrr] using hnonpart')

/-! ### Comm Mu Case -/

private theorem CProjectUEQ2Rel_postfix_comm_mu_case
    {g role cand e0 : _} {sender receiver t : String} {gbs : List (Label × GlobalType)}
    {body0 : LocalTypeR}
    (hg : GlobalType.fullUnfoldIter g = .comm sender receiver gbs)
    (he0 : LocalTypeR.fullUnfold e0 = .mu t body0)
    (hcore : CProjectF_unfold_core CProjectU (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold e0))
    (hWF_full : LocalTypeR.WellFormed e0.fullUnfold)
    (hWFcand_full : LocalTypeR.WellFormed cand.fullUnfold)
    (heq_full_cand_full : EQ2 e0.fullUnfold cand.fullUnfold) :
    CProjectF_unfold_core CProjectUEQ2Rel (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold cand) := by
  -- comm/mu: only nonparticipant branch is possible.
  by_cases hrs : role = sender
  · exact False.elim (by simpa [CProjectF_unfold_core, CProjectF, hg, he0, hrs] using hcore)
  · by_cases hrr : role = receiver
    · have hne : receiver ≠ sender := by intro h; exact hrs (hrr.trans h)
      exact False.elim (by simpa [CProjectF_unfold_core, CProjectF, hg, he0, hrr, hne] using hcore)
    · have hcore_nonpart :
          (∀ pair, pair ∈ gbs → part_of_all2 role pair.2) ∧
            AllBranchesProj CProjectU gbs role e0.fullUnfold := by
        simpa [CProjectF_unfold_core, CProjectF, hg, he0, hrs, hrr] using hcore
      have hnonpart' := CProjectUEQ2Rel_comm_nonpart
        heq_full_cand_full hWF_full hWFcand_full hcore_nonpart
      exact Or.inr (by
        simpa [CProjectF_unfold_core, CProjectF, hg, he0, hrs, hrr] using hnonpart')

/-! ## Comm Send Cases -/

/-! ### Comm Send Sender Case -/

private theorem CProjectUEQ2Rel_postfix_comm_send_sender
    {g role cand e0 : _} {sender receiver p : String}
    {gbs : List (Label × GlobalType)} {bs : List BranchR}
    (hg : GlobalType.fullUnfoldIter g = .comm sender receiver gbs)
    (he0 : LocalTypeR.fullUnfold e0 = .send p bs)
    (hrs : role = sender)
    (hcore : CProjectF_unfold_core CProjectU (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold e0))
    (heq_full : EQ2 e0 e0.fullUnfold) (heq : EQ2 e0 cand)
    (hWF_full : LocalTypeR.WellFormed e0.fullUnfold)
    (hWF : LocalTypeR.WellFormed e0) (hWFcand : LocalTypeR.WellFormed cand)
    (hWFcand_full : LocalTypeR.WellFormed cand.fullUnfold) :
    CProjectF_unfold_core CProjectUEQ2Rel (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold cand) := by
  -- comm/send sender: lift branches through EQ2 and rebuild the send witness.
  have hfpair : p = receiver ∧ BranchesProjRel CProjectU gbs sender bs := by
    simpa [CProjectF_unfold_core, CProjectF, hg, he0, hrs] using hcore
  rcases hfpair with ⟨hpartner, hbranches⟩
  have heq_send : EQ2 (.send p bs) cand :=
    EQ2_of_fullUnfold heq_full heq hWF_full hWF hWFcand he0
  rcases EQ2_fullUnfold_send hWFcand heq_send with ⟨cs, hfull, hrel_br⟩
  have hWF_branches : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2.2 :=
    LocalTypeR.WellFormed.branches_of_send (p := p) (bs := bs) (by simpa [he0] using hWF_full)
  have hWF_branches_cand : ∀ lb ∈ cs, LocalTypeR.WellFormed lb.2.2 :=
    LocalTypeR.WellFormed.branches_of_send (p := p) (bs := cs) (by simpa [hfull] using hWFcand_full)
  have hbranches' : BranchesProjRel CProjectUEQ2Rel gbs sender cs :=
    BranchesProjRel_lift_EQ2_U hbranches hrel_br hWF_branches hWF_branches_cand
	  exact Or.inr (by
	    simpa [CProjectF_unfold_core, CProjectF, hg, hfull, hrs] using
	      ⟨(by simpa using hpartner), hbranches'⟩)

/-! ### Comm Send Nonparticipant Case -/

private theorem CProjectUEQ2Rel_postfix_comm_send_nonpart
    {g role cand e0 : _} {sender receiver p : String}
    {gbs : List (Label × GlobalType)} {bs : List BranchR}
    (hg : GlobalType.fullUnfoldIter g = .comm sender receiver gbs)
    (he0 : LocalTypeR.fullUnfold e0 = .send p bs)
    (hrs : role ≠ sender) (hrr : role ≠ receiver)
    (hcore : CProjectF_unfold_core CProjectU (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold e0))
    (hWF_full : LocalTypeR.WellFormed e0.fullUnfold)
    (hWFcand_full : LocalTypeR.WellFormed cand.fullUnfold)
    (heq_full_cand_full : EQ2 e0.fullUnfold cand.fullUnfold) :
    CProjectF_unfold_core CProjectUEQ2Rel (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold cand) := by
  -- comm/send nonparticipant: lift AllBranchesProj to cand.fullUnfold.
  have hcore_nonpart :
      (∀ pair, pair ∈ gbs → part_of_all2 role pair.2) ∧
        AllBranchesProj CProjectU gbs role (LocalTypeR.send p bs) := by
    simpa [CProjectF_unfold_core, CProjectF, hg, he0, hrs, hrr] using hcore
  have hcore_nonpart' :
      (∀ pair, pair ∈ gbs → part_of_all2 role pair.2) ∧
        AllBranchesProj CProjectU gbs role e0.fullUnfold := by
    simpa [he0] using hcore_nonpart
  have hnonpart' := CProjectUEQ2Rel_comm_nonpart
    heq_full_cand_full hWF_full hWFcand_full hcore_nonpart'
	  exact Or.inr (by
	    simpa [CProjectF_unfold_core, CProjectF, hg, he0, hrs, hrr] using hnonpart')

/-! ### Comm Send Dispatcher -/

private theorem CProjectUEQ2Rel_postfix_comm_send_case
    {g role cand e0 : _} {sender receiver p : String}
    {gbs : List (Label × GlobalType)} {bs : List BranchR}
    (hg : GlobalType.fullUnfoldIter g = .comm sender receiver gbs)
    (he0 : LocalTypeR.fullUnfold e0 = .send p bs)
    (hcore : CProjectF_unfold_core CProjectU (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold e0))
    (heq_full : EQ2 e0 e0.fullUnfold) (heq : EQ2 e0 cand)
    (hWF_full : LocalTypeR.WellFormed e0.fullUnfold)
    (hWF : LocalTypeR.WellFormed e0) (hWFcand : LocalTypeR.WellFormed cand)
    (hWFcand_full : LocalTypeR.WellFormed cand.fullUnfold)
    (heq_full_cand_full : EQ2 e0.fullUnfold cand.fullUnfold) :
    CProjectF_unfold_core CProjectUEQ2Rel (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold cand) := by
  -- comm/send: split into sender/receiver/nonparticipant cases.
  by_cases hrs : role = sender
  · exact CProjectUEQ2Rel_postfix_comm_send_sender (g := g) (role := role) (cand := cand) (e0 := e0)
      (sender := sender) (receiver := receiver) (p := p) (gbs := gbs) (bs := bs)
      hg he0 hrs hcore heq_full heq hWF_full hWF hWFcand hWFcand_full
  · by_cases hrr : role = receiver
    · have hne : receiver ≠ sender := by intro h; exact hrs (hrr.trans h)
      exact False.elim (by simpa [CProjectF_unfold_core, CProjectF, hg, he0, hrr, hne] using hcore)
    · exact CProjectUEQ2Rel_postfix_comm_send_nonpart (g := g) (role := role) (cand := cand) (e0 := e0)
        (sender := sender) (receiver := receiver) (p := p) (gbs := gbs) (bs := bs)
        hg he0 hrs hrr hcore hWF_full hWFcand_full heq_full_cand_full

/-! ## Comm Recv Cases -/

/-! ### Comm Recv Receiver Case -/

private theorem CProjectUEQ2Rel_postfix_comm_recv_receiver
    {g role cand e0 : _} {sender receiver p : String}
    {gbs : List (Label × GlobalType)} {bs : List BranchR}
    (hg : GlobalType.fullUnfoldIter g = .comm sender receiver gbs)
    (he0 : LocalTypeR.fullUnfold e0 = .recv p bs)
    (hrr : role = receiver) (hne : receiver ≠ sender)
    (hcore : CProjectF_unfold_core CProjectU (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold e0))
    (heq_full : EQ2 e0 e0.fullUnfold) (heq : EQ2 e0 cand)
    (hWF_full : LocalTypeR.WellFormed e0.fullUnfold)
    (hWF : LocalTypeR.WellFormed e0) (hWFcand : LocalTypeR.WellFormed cand)
    (hWFcand_full : LocalTypeR.WellFormed cand.fullUnfold) :
    CProjectF_unfold_core CProjectUEQ2Rel (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold cand) := by
  -- comm/recv receiver: lift branches through EQ2 and rebuild the recv witness.
  have hfpair : p = sender ∧ BranchesProjRel CProjectU gbs receiver bs := by
    simpa [CProjectF_unfold_core, CProjectF, hg, he0, hrr, hne] using hcore
  rcases hfpair with ⟨hpartner, hbranches⟩
  have heq_recv : EQ2 (.recv p bs) cand :=
    EQ2_of_fullUnfold heq_full heq hWF_full hWF hWFcand he0
  rcases EQ2_fullUnfold_recv hWFcand heq_recv with ⟨cs, hfull, hrel_br⟩
  have hWF_branches : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2.2 :=
    LocalTypeR.WellFormed.branches_of_recv (p := p) (bs := bs) (by simpa [he0] using hWF_full)
  have hWF_branches_cand : ∀ lb ∈ cs, LocalTypeR.WellFormed lb.2.2 :=
    LocalTypeR.WellFormed.branches_of_recv (p := p) (bs := cs) (by simpa [hfull] using hWFcand_full)
  have hbranches' : BranchesProjRel CProjectUEQ2Rel gbs receiver cs :=
    BranchesProjRel_lift_EQ2_U hbranches hrel_br hWF_branches hWF_branches_cand
	  exact Or.inr (by
	    simpa [CProjectF_unfold_core, CProjectF, hg, hfull, hrr, hne] using
	      ⟨(by simpa using hpartner), hbranches'⟩)

/-! ### Comm Recv Nonparticipant Case -/

private theorem CProjectUEQ2Rel_postfix_comm_recv_nonpart
    {g role cand e0 : _} {sender receiver p : String}
    {gbs : List (Label × GlobalType)} {bs : List BranchR}
    (hg : GlobalType.fullUnfoldIter g = .comm sender receiver gbs)
    (he0 : LocalTypeR.fullUnfold e0 = .recv p bs)
    (hrs : role ≠ sender) (hrr : role ≠ receiver)
    (hcore : CProjectF_unfold_core CProjectU (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold e0))
    (hWF_full : LocalTypeR.WellFormed e0.fullUnfold)
    (hWFcand_full : LocalTypeR.WellFormed cand.fullUnfold)
    (heq_full_cand_full : EQ2 e0.fullUnfold cand.fullUnfold) :
    CProjectF_unfold_core CProjectUEQ2Rel (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold cand) := by
  -- comm/recv nonparticipant: lift AllBranchesProj to cand.fullUnfold.
  have hcore_nonpart :
      (∀ pair, pair ∈ gbs → part_of_all2 role pair.2) ∧
        AllBranchesProj CProjectU gbs role (LocalTypeR.recv p bs) := by
    simpa [CProjectF_unfold_core, CProjectF, hg, he0, hrs, hrr] using hcore
  have hcore_nonpart' :
      (∀ pair, pair ∈ gbs → part_of_all2 role pair.2) ∧
        AllBranchesProj CProjectU gbs role e0.fullUnfold := by
    simpa [he0] using hcore_nonpart
  have hnonpart' := CProjectUEQ2Rel_comm_nonpart
    heq_full_cand_full hWF_full hWFcand_full hcore_nonpart'
	  exact Or.inr (by
	    simpa [CProjectF_unfold_core, CProjectF, hg, he0, hrs, hrr] using hnonpart')

/-! ### Comm Recv Dispatcher -/

private theorem CProjectUEQ2Rel_postfix_comm_recv_case
    {g role cand e0 : _} {sender receiver p : String}
    {gbs : List (Label × GlobalType)} {bs : List BranchR}
    (hg : GlobalType.fullUnfoldIter g = .comm sender receiver gbs)
    (he0 : LocalTypeR.fullUnfold e0 = .recv p bs)
    (hcore : CProjectF_unfold_core CProjectU (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold e0))
    (heq_full : EQ2 e0 e0.fullUnfold) (heq : EQ2 e0 cand)
    (hWF_full : LocalTypeR.WellFormed e0.fullUnfold)
    (hWF : LocalTypeR.WellFormed e0) (hWFcand : LocalTypeR.WellFormed cand)
    (hWFcand_full : LocalTypeR.WellFormed cand.fullUnfold)
    (heq_full_cand_full : EQ2 e0.fullUnfold cand.fullUnfold) :
    CProjectF_unfold_core CProjectUEQ2Rel (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold cand) := by
  -- comm/recv: split into receiver/ nonparticipant cases.
  by_cases hrs : role = sender
  · exact False.elim (by simpa [CProjectF_unfold_core, CProjectF, hg, he0, hrs] using hcore)
  · by_cases hrr : role = receiver
    · have hne : receiver ≠ sender := by intro h; exact hrs (hrr.trans h)
      exact CProjectUEQ2Rel_postfix_comm_recv_receiver (g := g) (role := role) (cand := cand) (e0 := e0)
        (sender := sender) (receiver := receiver) (p := p) (gbs := gbs) (bs := bs)
        hg he0 hrr hne hcore heq_full heq hWF_full hWF hWFcand hWFcand_full
    · exact CProjectUEQ2Rel_postfix_comm_recv_nonpart (g := g) (role := role) (cand := cand) (e0 := e0)
        (sender := sender) (receiver := receiver) (p := p) (gbs := gbs) (bs := bs)
        hg he0 hrs hrr hcore hWF_full hWFcand_full heq_full_cand_full

/-! ## Comm Case Dispatcher -/

private theorem CProjectUEQ2Rel_postfix_comm_case
    {g role cand e0 : _} {sender receiver : String} {gbs : List (Label × GlobalType)}
    (hg : GlobalType.fullUnfoldIter g = .comm sender receiver gbs)
    (hcore : CProjectF_unfold_core CProjectU (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold e0))
    (heq_full : EQ2 e0 e0.fullUnfold) (heq : EQ2 e0 cand)
    (hWF_full : LocalTypeR.WellFormed e0.fullUnfold)
    (hWF : LocalTypeR.WellFormed e0) (hWFcand : LocalTypeR.WellFormed cand)
    (hWFcand_full : LocalTypeR.WellFormed cand.fullUnfold) :
    CProjectF_unfold_core CProjectUEQ2Rel (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold cand) := by
  have heq_full_cand_full : EQ2 e0.fullUnfold cand.fullUnfold := -- relate fullUnfolds before splitting
    EQ2_fullUnfold_to_fullUnfold heq_full heq hWF_full hWF hWFcand hWFcand_full
  cases he0 : LocalTypeR.fullUnfold e0 with
  | «end» =>
      exact CProjectUEQ2Rel_postfix_comm_end_case
        hg he0 hcore heq_full heq hWF_full hWF hWFcand hWFcand_full heq_full_cand_full
  | var v =>
      exact CProjectUEQ2Rel_postfix_comm_var_case
        hg he0 hcore hWF_full hWFcand_full heq_full_cand_full
  | mu t body0 =>
      exact CProjectUEQ2Rel_postfix_comm_mu_case
        hg he0 hcore hWF_full hWFcand_full heq_full_cand_full
  | send p bs =>
      exact CProjectUEQ2Rel_postfix_comm_send_case
        hg he0 hcore heq_full heq hWF_full hWF hWFcand hWFcand_full heq_full_cand_full
  | recv p bs =>
      exact CProjectUEQ2Rel_postfix_comm_recv_case
        hg he0 hcore heq_full heq hWF_full hWF hWFcand hWFcand_full heq_full_cand_full

/-! ## Postfix Closure -/



private theorem CProjectUEQ2Rel_postfix
    (hWFproj : ∀ g role cand, CProjectU g role cand → LocalTypeR.WellFormed cand) :
    ∀ g role cand, CProjectUEQ2Rel g role cand →
      CProjectF_unfold CProjectUEQ2Rel g role cand := by
  intro g role cand hrel; rcases hrel with ⟨e0, hproj, heq, hWF, hWFcand⟩
  rcases (CProjectU_destruct hproj) with ⟨hwf_g, hWF0, hcore⟩; dsimp [CProjectF_unfold] at hcore ⊢
  refine ⟨hwf_g, hWFcand, ?_⟩
  have heq_full : EQ2 e0 e0.fullUnfold := by simpa [LocalTypeR.fullUnfold] using
    (EQ2_unfold_right_iter (a := e0) (b := e0) (EQ2_refl e0)) e0.muHeight
  have hWF_full : LocalTypeR.WellFormed e0.fullUnfold := LocalTypeR.WellFormed.fullUnfold hWF;
  have hWFcand_full : LocalTypeR.WellFormed cand.fullUnfold := LocalTypeR.WellFormed.fullUnfold hWFcand
  cases hg : GlobalType.fullUnfoldIter g with -- dispatch on the fully-unfolded global shape
  | «end» =>
      simpa [hg] using
        (CProjectUEQ2Rel_postfix_end_case (g := g) (role := role) (cand := cand) (e0 := e0)
          hg hcore heq_full heq hWF_full hWF hWFcand)
  | var v =>
      simpa [hg] using
        (CProjectUEQ2Rel_postfix_var_case (g := g) (role := role) (cand := cand) (e0 := e0) (v := v)
          hg hcore heq_full heq hWF_full hWF hWFcand)
  | mu t body =>
      simpa [hg] using
        (CProjectUEQ2Rel_postfix_mu_case (g := g) (role := role) (cand := cand) (e0 := e0) (t := t) (body := body)
          hg hcore heq_full heq hWF_full hWF hWFcand hWFproj)
  | comm sender receiver gbs =>
      simpa [hg] using
        (CProjectUEQ2Rel_postfix_comm_case (g := g) (role := role) (cand := cand) (e0 := e0)
          (sender := sender) (receiver := receiver) (gbs := gbs)
          hg hcore heq_full heq hWF_full hWF hWFcand hWFcand_full)

/-! ## Final EQ2 Stability Theorem -/

/-- CProjectU is stable under EQ2-equivalent candidates (with well-formedness). -/
theorem CProjectU_EQ2 (g : GlobalType) (role : String) (e0 e1 : LocalTypeR)
    (hproj : CProjectU g role e0) (heq : EQ2 e0 e1)
    (hWF : LocalTypeR.WellFormed e0) (hWF' : LocalTypeR.WellFormed e1)
    (hWFproj : ∀ g role cand, CProjectU g role cand → LocalTypeR.WellFormed cand) :
    CProjectU g role e1 := by
  apply CProjectU_coind
  · intro g' role' cand hrel
    exact CProjectUEQ2Rel_postfix hWFproj g' role' cand hrel
  · exact ⟨e0, hproj, heq, hWF, hWF'⟩


end Choreography.Projection.Project
