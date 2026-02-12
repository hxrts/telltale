import SessionCoTypes.Bisim.ObservableFromEQ2

/-! # SessionCoTypes.Bisim.EQ2Extraction

FullUnfold-based extraction lemmas and EQ2_transfer_observable theorem.
-/

/-
The Problem. When reasoning about EQ2, we often know that a type's fullUnfold
has no leading mu (from closed+contractive hypotheses). We need lemmas that
extract observable predicates (UnfoldsToEnd, etc.) from EQ2 under this condition.

Solution Structure. Proves extraction lemmas like `EQ2.end_right_implies_UnfoldsToEnd_of_fullUnfold_nonmu`:
when fullUnfold has muHeight=0 and EQ2 .end x holds, then UnfoldsToEnd x. Similar
lemmas for var, send, recv. The `EQ2_transfer_observable` theorem transfers
observable predicates between EQ2-related types.
-/

set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false

namespace SessionCoTypes.Bisim
open SessionTypes.LocalTypeR
open SessionTypes.GlobalType
open SessionCoTypes.Observable
open SessionCoTypes.EQ2
open SessionCoTypes.CoinductiveRel
/-! ## Extraction from EQ2 when fullUnfold is non-mu

These lemmas require only that the fully-unfolded form has no leading `mu`.
They are useful as a local, non-leaky swap point when such a fact is available
(e.g., from closed+contractive hypotheses). -/

/-! ## Non-μ Extraction: End/Var -/

theorem EQ2.end_right_implies_UnfoldsToEnd_of_fullUnfold_nonmu {x : LocalTypeR}
    (hmu : x.fullUnfold.muHeight = 0) (heq : EQ2 .end x) : UnfoldsToEnd x := by
  have hiter := (EQ2_unfold_right_iter (a := .end) (b := x) heq) x.muHeight
  have hfull : EQ2 .end x.fullUnfold := by
    simpa [LocalTypeR.fullUnfold] using hiter
  cases hx : x.fullUnfold with
  | «end» =>
      exact UnfoldsToEnd_of_fullUnfold_eq (by simpa [hx])
  | var v =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | send p bs =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | recv p bs =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | mu t body =>
      have hmu' : Nat.succ body.muHeight = 0 := by
        simpa [LocalTypeR.muHeight, hx] using hmu
      exact (False.elim (Nat.succ_ne_zero _ hmu'))

theorem EQ2.var_right_implies_UnfoldsToVar_of_fullUnfold_nonmu {x : LocalTypeR} {v : String}
    (hmu : x.fullUnfold.muHeight = 0) (heq : EQ2 (.var v) x) : UnfoldsToVar x v := by
  have hiter := (EQ2_unfold_right_iter (a := .var v) (b := x) heq) x.muHeight
  have hfull : EQ2 (.var v) x.fullUnfold := by
    simpa [LocalTypeR.fullUnfold] using hiter
  cases hx : x.fullUnfold with
  | var w =>
      have hf := EQ2.destruct hfull
      have hw : v = w := by
        simpa [EQ2F, hx] using hf
      subst hw
      exact UnfoldsToVar_of_fullUnfold_eq (by simpa [hx])
  | «end» =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | send p bs =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | recv p bs =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | mu t body =>
      have hmu' : Nat.succ body.muHeight = 0 := by
        simpa [LocalTypeR.muHeight, hx] using hmu
      exact (False.elim (Nat.succ_ne_zero _ hmu'))

/-! ## Non-μ Extraction: Send/Recv -/

theorem EQ2.send_right_implies_CanSend_of_fullUnfold_nonmu {x : LocalTypeR} {p : String}
    {bs : List BranchR} (hmu : x.fullUnfold.muHeight = 0)
    (heq : EQ2 (.send p bs) x) : ∃ cs, CanSend x p cs ∧ BranchesRel EQ2 bs cs := by
  have hiter := (EQ2_unfold_right_iter (a := .send p bs) (b := x) heq) x.muHeight
  have hfull : EQ2 (.send p bs) x.fullUnfold := by
    simpa [LocalTypeR.fullUnfold] using hiter
  cases hx : x.fullUnfold with
  | send q cs =>
      have hf := EQ2.destruct hfull
      have hpr : p = q ∧ BranchesRel EQ2 bs cs := by
        simpa [EQ2F, hx] using hf
      rcases hpr with ⟨hp, hbr⟩
      subst hp
      have hcan : CanSend x p cs := CanSend_of_fullUnfold_eq (by simpa [hx])
      exact ⟨cs, hcan, hbr⟩
  | «end» =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | var v =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | recv q cs =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | mu t body =>
      have hmu' : Nat.succ body.muHeight = 0 := by
        simpa [LocalTypeR.muHeight, hx] using hmu
      exact (False.elim (Nat.succ_ne_zero _ hmu'))

theorem EQ2.recv_right_implies_CanRecv_of_fullUnfold_nonmu {x : LocalTypeR} {p : String}
    {bs : List BranchR} (hmu : x.fullUnfold.muHeight = 0)
    (heq : EQ2 (.recv p bs) x) : ∃ cs, CanRecv x p cs ∧ BranchesRel EQ2 bs cs := by
  -- Reduce recv to send via duality.
  have hdual : EQ2 (.send p (dualBranches bs)) x.dual := by
    have h' := EQ2_dual_compat (a := .recv p bs) (b := x) heq
    simpa [LocalTypeR.dual] using h'
  have hmu' : x.dual.fullUnfold.muHeight = 0 := by
    simpa [fullUnfold_dual, muHeight_dual] using hmu
  obtain ⟨cs, hcan, hbr⟩ :=
    EQ2.send_right_implies_CanSend_of_fullUnfold_nonmu (x := x.dual) hmu' hdual
  exact CanSend_dual_to_CanRecv (x := x) (p := p) (bs := bs) (cs := cs) hcan hbr


/-! ## Observable Transfer via Unfold (no EQ2_trans) -/

/-! ## Observable Transfer Recursors -/

theorem UnfoldsToEnd_transfer {a b : LocalTypeR} (ha : UnfoldsToEnd a) (h : EQ2 a b)
    (hWFb : LocalTypeR.WellFormed b) : UnfoldsToEnd b := by
  revert h
  refine UnfoldsToEnd.rec (motive := fun a _ => EQ2 a b → UnfoldsToEnd b) ?base ?mu ha
  · intro h
    exact EQ2.end_right_implies_UnfoldsToEnd_of_contractive hWFb.closed hWFb.contractive h
  · intro t body _ ih h
    have h' : EQ2 (body.substitute t (.mu t body)) b := by
      simpa [LocalTypeR.unfold] using (EQ2_unfold_left (a := .mu t body) (b := b) h)
    exact ih h'

private theorem UnfoldsToVar_transfer {a b : LocalTypeR} {v : String} (ha : UnfoldsToVar a v)
    (h : EQ2 a b) (hWFb : LocalTypeR.WellFormed b) : UnfoldsToVar b v := by
  revert h
  refine UnfoldsToVar.rec (motive := fun a v _ => EQ2 a b → UnfoldsToVar b v) ?base ?mu ha
  · intro v h
    exact EQ2.var_right_implies_UnfoldsToVar_of_contractive hWFb.closed hWFb.contractive h
  · intro t body v _ ih h
    have h' : EQ2 (body.substitute t (.mu t body)) b := by
      simpa [LocalTypeR.unfold] using (EQ2_unfold_left (a := .mu t body) (b := b) h)
    exact ih h'

private theorem CanSend_transfer {a b : LocalTypeR} {p : String} {bs : List BranchR}
    (ha : CanSend a p bs) (h : EQ2 a b) (hWFb : LocalTypeR.WellFormed b) :
    ∃ cs, CanSend b p cs ∧ BranchesRel EQ2 bs cs := by
  revert h
  refine CanSend.rec
    (motive := fun a p bs _ => EQ2 a b → ∃ cs, CanSend b p cs ∧ BranchesRel EQ2 bs cs)
    ?base ?mu ha
  · intro partner branches h
    exact EQ2.send_right_implies_CanSend_of_contractive hWFb.closed hWFb.contractive h
  · intro t body p bs _ ih h
    have h' : EQ2 (body.substitute t (.mu t body)) b := by
      simpa [LocalTypeR.unfold] using (EQ2_unfold_left (a := .mu t body) (b := b) h)
    exact ih h'

private theorem CanRecv_transfer {a b : LocalTypeR} {p : String} {bs : List BranchR}
    (ha : CanRecv a p bs) (h : EQ2 a b) (hWFb : LocalTypeR.WellFormed b) :
    ∃ cs, CanRecv b p cs ∧ BranchesRel EQ2 bs cs := by
  -- Reduce recv to send on the dual type, then dualize the result back.
  have ha' : CanSend a.dual p (dualBranches bs) := CanRecv.dual ha
  have h' : EQ2 a.dual b.dual := EQ2_dual_compat h
  have hWFb' : LocalTypeR.WellFormed b.dual := SessionTypes.LocalTypeR.WellFormed.dual hWFb
  obtain ⟨cs, hsend, hbr⟩ :=
    CanSend_transfer (a := a.dual) (b := b.dual) (p := p)
      (bs := dualBranches bs) ha' h' hWFb'
  have hrecv : CanRecv b p (dualBranches cs) := by
    have hrecv' := CanSend.dual (t := b.dual) hsend
    simpa [LocalTypeR.dual_dual] using hrecv'
  have hbr' : BranchesRel EQ2 bs (dualBranches cs) := BranchesRel_dual_eq2 hbr
  exact ⟨dualBranches cs, hrecv, hbr'⟩

/-! ## Contractive μ/μ Observable Classification -/

theorem EQ2_mus_to_BisimF_of_contractive {t s : String} {body body' : LocalTypeR}
    (h : EQ2 (LocalTypeR.mu t body) (LocalTypeR.mu s body'))
    (hc1_closed : (LocalTypeR.mu t body).isClosed)
    (hc1 : (LocalTypeR.mu t body).isContractive = true)
    (hc2_closed : (LocalTypeR.mu s body').isClosed)
    (hc2 : (LocalTypeR.mu s body').isContractive = true) :
    BisimF EQ2 (LocalTypeR.mu t body) (LocalTypeR.mu s body') := by
  have hWFb : LocalTypeR.WellFormed (.mu s body') := ⟨hc2_closed, hc2⟩
  have hobs := observable_of_closed_contractive hc1_closed hc1
  cases hobs with
  | is_end hend =>
      have hEndB : UnfoldsToEnd (.mu s body') :=
        UnfoldsToEnd_transfer hend h hWFb
      exact BisimF.eq_end hend hEndB
  | is_var hvar =>
      rename_i v
      have hVarB : UnfoldsToVar (.mu s body') v :=
        UnfoldsToVar_transfer hvar h hWFb
      exact BisimF.eq_var hvar hVarB
  | is_send hsend =>
      rename_i p bs
      obtain ⟨bs', hCanSend, hbr⟩ := CanSend_transfer hsend h hWFb
      exact BisimF.eq_send hsend hCanSend (BranchesRel_to_BranchesRelBisim hbr)
  | is_recv hrecv =>
      rename_i p bs
      obtain ⟨bs', hCanRecv, hbr⟩ := CanRecv_transfer hrecv h hWFb
      exact BisimF.eq_recv hrecv hCanRecv (BranchesRel_to_BranchesRelBisim hbr)

/-! ## Extraction Bundles and Well-Formed Interface -/

/-- Closed + contractive extraction (fully proven). -/
def ContractiveExtraction : EQ2Extraction :=
  { Good := fun x => x.isClosed ∧ x.isContractive = true
    end_right := by
      intro x hgood h
      exact EQ2.end_right_implies_UnfoldsToEnd_of_contractive hgood.1 hgood.2 h
    var_right := by
      intro x v hgood h
      exact EQ2.var_right_implies_UnfoldsToVar_of_contractive hgood.1 hgood.2 h
    send_right := by
      intro x p bs hgood h
      exact EQ2.send_right_implies_CanSend_of_contractive (x := x) hgood.1 hgood.2 h
    recv_right := by
      intro x p bs hgood h
      exact EQ2.recv_right_implies_CanRecv_of_contractive (x := x) hgood.1 hgood.2 h
    mus_to_BisimF := by
      intro t s body body' hgood1 hgood2 h
      exact EQ2_mus_to_BisimF_of_contractive (t := t) (s := s) (body := body) (body' := body')
        h hgood1.1 hgood1.2 hgood2.1 hgood2.2 }

/-- Active extraction is gated on well-formedness (closed + contractive). -/
def ActiveExtraction : EQ2Extraction := ContractiveExtraction

/-! ## Well-Formed EQ2 Interface: End/Var -/

/-- If EQ2 .end x and x is well-formed, then x unfolds to end. -/
theorem EQ2.end_right_implies_UnfoldsToEnd {x : LocalTypeR} (hWF : LocalTypeR.WellFormed x)
    (h : EQ2 .end x) : UnfoldsToEnd x := by
  exact ActiveExtraction.end_right (x := x) ⟨hWF.closed, hWF.contractive⟩ h

/-- If EQ2 x .end, then x unfolds to end. -/
theorem EQ2.end_left_implies_UnfoldsToEnd {x : LocalTypeR} (hWF : LocalTypeR.WellFormed x)
    (h : EQ2 x .end) : UnfoldsToEnd x :=
  EQ2.end_right_implies_UnfoldsToEnd hWF (EQ2_symm h)

/-- If EQ2 (.var v) x, then x unfolds to var v. -/
theorem EQ2.var_right_implies_UnfoldsToVar {x : LocalTypeR} {v : String}
    (hWF : LocalTypeR.WellFormed x) (h : EQ2 (.var v) x) : UnfoldsToVar x v := by
  exact ActiveExtraction.var_right (x := x) (v := v) ⟨hWF.closed, hWF.contractive⟩ h

/-- If EQ2 x (.var v), then x unfolds to var v. -/
theorem EQ2.var_left_implies_UnfoldsToVar {x : LocalTypeR} {v : String}
    (hWF : LocalTypeR.WellFormed x) (h : EQ2 x (.var v)) : UnfoldsToVar x v :=
  EQ2.var_right_implies_UnfoldsToVar hWF (EQ2_symm h)

/-! ## Well-Formed EQ2 Interface: Send/Recv -/

/-- If EQ2 (.send p bs) x, then x can send to p with EQ2-related branches. -/
theorem EQ2.send_right_implies_CanSend {x : LocalTypeR} {p : String}
    {bs : List BranchR} (hWF : LocalTypeR.WellFormed x) (h : EQ2 (.send p bs) x) :
    ∃ cs, CanSend x p cs ∧ BranchesRel EQ2 bs cs := by
  exact ActiveExtraction.send_right (x := x) (p := p) (bs := bs) ⟨hWF.closed, hWF.contractive⟩ h

/-- If EQ2 x (.send p cs), then x can send to p with EQ2-related branches. -/
theorem EQ2.send_left_implies_CanSend {x : LocalTypeR} {p : String}
    {cs : List BranchR} (hWF : LocalTypeR.WellFormed x) (h : EQ2 x (.send p cs)) :
    ∃ bs, CanSend x p bs ∧ BranchesRel EQ2 bs cs := by
  have hsymm := EQ2_symm h
  obtain ⟨bs, hcan, hbr⟩ := EQ2.send_right_implies_CanSend hWF hsymm
  exact ⟨bs, hcan, BranchesRel_flip hbr⟩

/-- If EQ2 (.recv p bs) x, then x can recv from p with EQ2-related branches. -/
theorem EQ2.recv_right_implies_CanRecv {x : LocalTypeR} {p : String}
    {bs : List BranchR} (hWF : LocalTypeR.WellFormed x) (h : EQ2 (.recv p bs) x) :
    ∃ cs, CanRecv x p cs ∧ BranchesRel EQ2 bs cs := by
  exact ActiveExtraction.recv_right (x := x) (p := p) (bs := bs) ⟨hWF.closed, hWF.contractive⟩ h

/-- If EQ2 x (.recv p cs), then x can recv from p with EQ2-related branches. -/
theorem EQ2.recv_left_implies_CanRecv {x : LocalTypeR} {p : String}
    {cs : List BranchR} (hWF : LocalTypeR.WellFormed x) (h : EQ2 x (.recv p cs)) :
    ∃ bs, CanRecv x p bs ∧ BranchesRel EQ2 bs cs := by
  have hsymm := EQ2_symm h
  obtain ⟨bs, hcan, hbr⟩ := EQ2.recv_right_implies_CanRecv hWF hsymm
  exact ⟨bs, hcan, BranchesRel_flip hbr⟩

/-! ## Observable Transfer Relations -/

/-- Transfer observables across EQ2, gated on well-formedness of the target. -/
theorem EQ2_transfer_observable {a b : LocalTypeR} (h : EQ2 a b) (obs_a : Observable a)
    (hWF : LocalTypeR.WellFormed b) :
    ∃ obs_b : Observable b, ObservableRel EQ2 obs_a obs_b := by
  cases obs_a with
  | is_end h_end =>
      have hb : UnfoldsToEnd b := UnfoldsToEnd_transfer h_end h hWF
      exact ⟨Observable.is_end hb, ObservableRel.is_end (ha := h_end) (hb := hb)⟩
  | is_var h_var =>
      rename_i v
      have hb : UnfoldsToVar b v := UnfoldsToVar_transfer h_var h hWF
      exact ⟨Observable.is_var hb, ObservableRel.is_var (ha := h_var) (hb := hb)⟩
  | is_send h_send =>
      rename_i p bs
      obtain ⟨cs, hcan, hbr⟩ := CanSend_transfer h_send h hWF
      exact ⟨Observable.is_send hcan, ObservableRel.is_send (ha := h_send) (hb := hcan) hbr⟩
  | is_recv h_recv =>
      rename_i p bs
      obtain ⟨cs, hcan, hbr⟩ := CanRecv_transfer h_recv h hWF
      exact ⟨Observable.is_recv hcan, ObservableRel.is_recv (ha := h_recv) (hb := hcan) hbr⟩

/-- Transfer observables across EQ2 under well-formedness of the target. -/
theorem EQ2_transfer_observable_of_wellFormed {a b : LocalTypeR} (h : EQ2 a b)
    (obs_a : Observable a) (hWF : LocalTypeR.WellFormed b) :
    ∃ obs_b : Observable b, ObservableRel EQ2 obs_a obs_b :=
  EQ2_transfer_observable h obs_a hWF

/-! ## Observable Relation Utilities -/

/-- BranchesRel is reflexive for EQ2. -/
private theorem BranchesRel_refl : ∀ bs, BranchesRel EQ2 bs bs := by
  intro bs
  induction bs with
  | nil => exact List.Forall₂.nil
  | cons head tail ih =>
      exact List.Forall₂.cons ⟨rfl, EQ2_refl head.2.2⟩ ih

/-- Observable relation is reflexive. -/
theorem ObservableRel.refl {a : LocalTypeR} (obs : Observable a) :
    ObservableRel EQ2 obs obs := by
  cases obs with
  | is_end h =>
      exact ObservableRel.is_end (ha := h) (hb := h)
  | is_var h =>
      exact ObservableRel.is_var (ha := h) (hb := h)
  | is_send h =>
      exact ObservableRel.is_send (ha := h) (hb := h) (BranchesRel_refl _)
  | is_recv h =>
      exact ObservableRel.is_recv (ha := h) (hb := h) (BranchesRel_refl _)

/-- Observable relation is symmetric. -/
theorem ObservableRel.symm {a b : LocalTypeR} {obs_a : Observable a} {obs_b : Observable b}
    (h : ObservableRel EQ2 obs_a obs_b) : ObservableRel EQ2 obs_b obs_a := by
  cases h with
  | is_end =>
      rename_i ha hb
      exact ObservableRel.is_end (ha := hb) (hb := ha)
  | is_var =>
      rename_i v ha hb
      exact ObservableRel.is_var (ha := hb) (hb := ha)
  | is_send hbr =>
      rename_i p bs cs ha hb
      exact ObservableRel.is_send (ha := hb) (hb := ha) (BranchesRel_flip hbr)
  | is_recv hbr =>
      rename_i p bs cs ha hb
      exact ObservableRel.is_recv (ha := hb) (hb := ha) (BranchesRel_flip hbr)

/-! ## Observable Symmetry and μ/μ Bridge -/

/-- Observability is symmetric across EQ2. -/
theorem EQ2_observable_symmetric {a b : LocalTypeR} (h : EQ2 a b)
    (hWFa : LocalTypeR.WellFormed a) (hWFb : LocalTypeR.WellFormed b) :
    (∃ _ : Observable a, True) ↔ (∃ _ : Observable b, True) := by
  constructor
  · intro h_obs_a
    obtain ⟨obs_a, _⟩ := h_obs_a
    obtain ⟨obs_b, _⟩ := EQ2_transfer_observable h obs_a hWFb
    exact ⟨obs_b, True.intro⟩
  · intro h_obs_b
    obtain ⟨obs_b, _⟩ := h_obs_b
    have hsymm := EQ2_symm h
    obtain ⟨obs_a, _⟩ := EQ2_transfer_observable hsymm obs_b hWFa
    exact ⟨obs_a, True.intro⟩

theorem EQ2_mus_to_BisimF {t s : String} {body body' : LocalTypeR}
    (h : EQ2 (LocalTypeR.mu t body) (LocalTypeR.mu s body'))
    (hWF1 : LocalTypeR.WellFormed (LocalTypeR.mu t body))
    (hWF2 : LocalTypeR.WellFormed (LocalTypeR.mu s body')) :
    BisimF EQ2 (LocalTypeR.mu t body) (LocalTypeR.mu s body') := by
  exact ActiveExtraction.mus_to_BisimF
    (t := t) (s := s) (body := body) (body' := body')
    ⟨hWF1.closed, hWF1.contractive⟩ ⟨hWF2.closed, hWF2.contractive⟩ h

/-! ## Well-Formed Strengthening for Bisim Witnesses -/

private theorem BranchesRelBisim_strengthen {bs cs : List BranchR}
    (hbr : BranchesRelBisim EQ2 bs cs)
    (hWFbs : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2.2)
    (hWFcs : ∀ lc ∈ cs, LocalTypeR.WellFormed lc.2.2) :
    BranchesRelBisim (fun a b => EQ2 a b ∧ LocalTypeR.WellFormed a ∧ LocalTypeR.WellFormed b) bs cs := by
  induction hbr with
  | nil => exact List.Forall₂.nil
  | cons hhead htail ih =>
      rename_i b c bs' cs'
      constructor
      · exact ⟨hhead.1, hhead.2, hWFbs b (List.Mem.head _), hWFcs c (List.Mem.head _)⟩
      · exact ih (fun lb hm => hWFbs lb (List.Mem.tail _ hm))
                 (fun lc hm => hWFcs lc (List.Mem.tail _ hm))

private theorem BisimF_EQ2_to_EQ2WF {x y : LocalTypeR} (h : BisimF EQ2 x y)
    (hWFx : LocalTypeR.WellFormed x) (hWFy : LocalTypeR.WellFormed y) :
    BisimF (fun a b => EQ2 a b ∧ LocalTypeR.WellFormed a ∧ LocalTypeR.WellFormed b) x y := by
  cases h with
  | eq_end ha hb => exact BisimF.eq_end ha hb
  | eq_var ha hb => exact BisimF.eq_var ha hb
  | eq_send ha hb hbr =>
      apply BisimF.eq_send ha hb
      exact BranchesRelBisim_strengthen hbr
        (WellFormed_branches_of_CanSend ha hWFx)
        (WellFormed_branches_of_CanSend hb hWFy)
  | eq_recv ha hb hbr =>
      apply BisimF.eq_recv ha hb
      exact BranchesRelBisim_strengthen hbr
        (WellFormed_branches_of_CanRecv ha hWFx)
        (WellFormed_branches_of_CanRecv hb hWFy)

/-! ## Shared Observable Corollary for μ/μ -/

theorem mus_shared_observable_contractive {t s : String} {body body' : LocalTypeR}
    (h : EQ2 (LocalTypeR.mu t body) (LocalTypeR.mu s body'))
    (hcl1 : (LocalTypeR.mu t body).isClosed)
    (hc1 : (LocalTypeR.mu t body).isContractive = true)
    (hcl2 : (LocalTypeR.mu s body').isClosed)
    (hc2 : (LocalTypeR.mu s body').isContractive = true) :
    (UnfoldsToEnd (LocalTypeR.mu t body) ∧ UnfoldsToEnd (LocalTypeR.mu s body')) ∨
    (∃ v, UnfoldsToVar (LocalTypeR.mu t body) v ∧ UnfoldsToVar (LocalTypeR.mu s body') v) ∨
    (∃ p bs cs, CanSend (LocalTypeR.mu t body) p bs ∧ CanSend (LocalTypeR.mu s body') p cs ∧
       BranchesRel EQ2 bs cs) ∨
    (∃ p bs cs, CanRecv (LocalTypeR.mu t body) p bs ∧ CanRecv (LocalTypeR.mu s body') p cs ∧
       BranchesRel EQ2 bs cs) := by
  -- Use the contractive extraction to get BisimF
  have hbf := EQ2_mus_to_BisimF_of_contractive h hcl1 hc1 hcl2 hc2
  -- Case split on the BisimF result
  cases hbf with
  | eq_end ha hb =>
      exact Or.inl ⟨ha, hb⟩
  | eq_var ha hb =>
      rename_i v
      exact Or.inr (Or.inl ⟨v, ha, hb⟩)
  | eq_send ha hb hbr =>
      rename_i p bs cs
      exact Or.inr (Or.inr (Or.inl ⟨p, bs, cs, ha, hb, BranchesRelBisim_to_BranchesRel hbr⟩))
  | eq_recv ha hb hbr =>
      rename_i p bs cs
      exact Or.inr (Or.inr (Or.inr ⟨p, bs, cs, ha, hb, BranchesRelBisim_to_BranchesRel hbr⟩))

/-! ## EQ2 to Bisim Witness Construction -/
/-- EQ2 implies Bisim.

    This direction shows that coinductive equality implies membership-based bisimulation.
    The proof constructs the Bisim witness using EQ2 itself.

    **Semantic constraint**: This theorem relies on extraction lemmas that are valid for contractive
    types (where every mu-bound variable is guarded). All types from well-formed projections are
    contractive, so this theorem is sound in practice.

    Proof idea:
    - Use EQ2 as the witness relation for Bisim
    - Show EQ2 is a post-fixpoint of BisimF by destruct-ing EQ2 to EQ2F
    - Convert EQ2F structure to membership predicates using the extraction lemmas
    - For mu/mu case, use EQ2_mus_to_BisimF lemma -/
theorem EQ2.toBisim_raw {a b : LocalTypeR} (h : EQ2 a b)
    (hWFa : LocalTypeR.WellFormed a) (hWFb : LocalTypeR.WellFormed b) : Bisim a b := by
  -- Define the witness relation
  let R : Rel := fun x y => EQ2 x y ∧ LocalTypeR.WellFormed x ∧ LocalTypeR.WellFormed y
  -- Show R is a post-fixpoint of BisimF
  have hpostfix : ∀ x y, R x y → BisimF R x y := by
    intro x y ⟨hEQ2, hWFx, hWFy⟩
    -- Get observables for both types
    have obs_x := WellFormed.observable hWFx
    obtain ⟨obs_y, hrel⟩ := EQ2_transfer_observable hEQ2 obs_x hWFy
    -- Convert ObservableRel to BisimF
    cases hrel with
    | is_end =>
        rename_i ha hb
        exact BisimF.eq_end ha hb
    | is_var =>
        rename_i ha hb
        exact BisimF.eq_var ha hb
    | is_send hbr =>
        rename_i p bs cs ha hb
        apply BisimF.eq_send ha hb
        exact BranchesRelBisim_strengthen hbr
          (WellFormed_branches_of_CanSend ha hWFx)
          (WellFormed_branches_of_CanSend hb hWFy)
    | is_recv hbr =>
        rename_i p bs cs ha hb
        apply BisimF.eq_recv ha hb
        exact BranchesRelBisim_strengthen hbr
          (WellFormed_branches_of_CanRecv ha hWFx)
          (WellFormed_branches_of_CanRecv hb hWFy)
  -- Apply the coinduction principle
  exact ⟨R, hpostfix, h, hWFa, hWFb⟩

end SessionCoTypes.Bisim
