import SessionCoTypes.Bisim.Part1

/-! # Bisim Part 2: Unfolding Shape and Converse Lemmas

Connects membership predicates with fullUnfold and proves fullUnfold reflects
observable behavior for well-formed types.
-/

set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false

namespace SessionCoTypes.Bisim
open SessionTypes.LocalTypeR
open SessionTypes.GlobalType
open SessionCoTypes.Observable
/-! ## Unfolding Shape Lemmas

These lemmas connect the membership predicates with `fullUnfold`. They are used
to extract constructor shapes from EQ2 via the UnfoldsTo/CanSend/CanRecv lemmas. -/

private theorem UnfoldPathEndBounded.not_mu_var (t : String) :
    ∀ n, ¬ UnfoldPathEndBounded n (.mu t (.var t)) := by
  intro n h
  induction n with
  | zero =>
      cases h
  | succ n ih =>
      cases h with
      | step h' =>
      have h'' := by simpa [LocalTypeR.substitute] using h'
      exact ih h''

private theorem UnfoldPathVarBounded.not_mu_var (t : String) (v : String) :
    ∀ n, ¬ UnfoldPathVarBounded n v (.mu t (.var t)) := by
  intro n h
  induction n with
  | zero =>
      cases h
  | succ n ih =>
      cases h with
      | step h' =>
      have h'' := by simpa [LocalTypeR.substitute] using h'
      exact ih h''

private theorem CanSendPathBounded.not_mu_var (t : String) (p : String) (bs : List (Label × LocalTypeR)) :
    ∀ n, ¬ CanSendPathBounded n p bs (.mu t (.var t)) := by
  intro n h
  induction n with
  | zero =>
      cases h
  | succ n ih =>
      cases h with
      | step h' =>
      have h'' := by simpa [LocalTypeR.substitute] using h'
      exact ih h''

/-- Derived from `CanSendPathBounded.not_mu_var` via duality. -/
private theorem CanRecvPathBounded.not_mu_var (t : String) (p : String) (bs : List (Label × LocalTypeR)) :
    ∀ n, ¬ CanRecvPathBounded n p bs (.mu t (.var t)) := by
  intro n h
  have hsend := CanRecvPathBounded.to_CanSendPathBounded_dual h
  exact CanSendPathBounded.not_mu_var t p (dualBranches bs) n (by simpa [LocalTypeR.dual] using hsend)

theorem UnfoldsToEnd.not_mu_var {t : String} : ¬ UnfoldsToEnd (.mu t (.var t)) := by
  intro h
  obtain ⟨n, hn⟩ := UnfoldsToEnd.toBounded h
  exact UnfoldPathEndBounded.not_mu_var t n hn

theorem UnfoldsToVar.not_mu_var {t v : String} : ¬ UnfoldsToVar (.mu t (.var t)) v := by
  intro h
  obtain ⟨n, hn⟩ := UnfoldsToVar.toBounded h
  exact UnfoldPathVarBounded.not_mu_var t v n hn

theorem CanSend.not_mu_var {t p : String} {bs : List (Label × LocalTypeR)} :
    ¬ CanSend (.mu t (.var t)) p bs := by
  intro h
  obtain ⟨n, hn⟩ := CanSend.toBounded h
  exact CanSendPathBounded.not_mu_var t p bs n hn

/-- Derived from `CanSend.not_mu_var` via duality. -/
theorem CanRecv.not_mu_var {t p : String} {bs : List (Label × LocalTypeR)} :
    ¬ CanRecv (LocalTypeR.mu t (LocalTypeR.var t)) p bs := by
  intro h
  have hsend : CanSend (LocalTypeR.mu t (LocalTypeR.var t)).dual p (dualBranches bs) := CanRecv.dual h
  exact CanSend.not_mu_var (by simpa [LocalTypeR.dual] using hsend)

/-! ## Unfolding Converse Lemmas

These lemmas go in the opposite direction: if fullUnfold (or a finite unfold
iteration) yields a constructor, then the corresponding membership predicate holds,
i.e. bounded-path pattern. -/

private theorem unfold_iter_eq_end_to_UnfoldsToEnd (a : LocalTypeR) :
    ∀ n, (LocalTypeR.unfold^[n] a = .end) → UnfoldsToEnd a := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      have h' : a = .end := by
        simpa [Function.iterate_zero, id_eq] using h
      cases h'
      exact UnfoldsToEnd.base
  | succ n ih =>
      intro h
      cases a with
      | mu t body =>
          have h' : (LocalTypeR.unfold^[n] (body.substitute t (.mu t body))) = .end := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact UnfoldsToEnd.mu (ih (a := body.substitute t (.mu t body)) h')
      | «end» =>
          have h' : (LocalTypeR.unfold^[n] .end) = .end := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .end) h'
      | var v =>
          have h' : (LocalTypeR.unfold^[n] (.var v)) = .end := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .var v) h'
      | send p bs =>
          have h' : (LocalTypeR.unfold^[n] (.send p bs)) = .end := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .send p bs) h'
      | recv p bs =>
          have h' : (LocalTypeR.unfold^[n] (.recv p bs)) = .end := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .recv p bs) h'

private theorem unfold_iter_eq_var_to_UnfoldsToVar (a : LocalTypeR) (v : String) :
    ∀ n, (LocalTypeR.unfold^[n] a = .var v) → UnfoldsToVar a v := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      have h' : a = .var v := by
        simpa [Function.iterate_zero, id_eq] using h
      cases h'
      exact UnfoldsToVar.base
  | succ n ih =>
      intro h
      cases a with
      | mu t body =>
          have h' : (LocalTypeR.unfold^[n] (body.substitute t (.mu t body))) = .var v := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact UnfoldsToVar.mu (ih (a := body.substitute t (.mu t body)) h')
      | «end» =>
          have h' : (LocalTypeR.unfold^[n] .end) = .var v := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .end) h'
      | var w =>
          have h' : (LocalTypeR.unfold^[n] (.var w)) = .var v := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .var w) h'
      | send p bs =>
          have h' : (LocalTypeR.unfold^[n] (.send p bs)) = .var v := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .send p bs) h'
      | recv p bs =>
          have h' : (LocalTypeR.unfold^[n] (.recv p bs)) = .var v := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .recv p bs) h'

private theorem unfold_iter_eq_send_to_CanSend (a : LocalTypeR) (p : String)
    (bs : List (Label × LocalTypeR)) :
    ∀ n, (LocalTypeR.unfold^[n] a = .send p bs) → CanSend a p bs := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      have h' : a = .send p bs := by
        simpa [Function.iterate_zero, id_eq] using h
      cases h'
      exact CanSend.base
  | succ n ih =>
      intro h
      cases a with
      | mu t body =>
          have h' : (LocalTypeR.unfold^[n] (body.substitute t (.mu t body))) = .send p bs := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact CanSend.mu (ih (a := body.substitute t (.mu t body)) h')
      | «end» =>
          have h' : (LocalTypeR.unfold^[n] .end) = .send p bs := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .end) h'
      | var v =>
          have h' : (LocalTypeR.unfold^[n] (.var v)) = .send p bs := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .var v) h'
      | send q cs =>
          have h' : (LocalTypeR.unfold^[n] (.send q cs)) = .send p bs := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .send q cs) h'
      | recv q cs =>
          have h' : (LocalTypeR.unfold^[n] (.recv q cs)) = .send p bs := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .recv q cs) h'

/-- Derived from `unfold_iter_eq_send_to_CanSend` via duality. -/
private theorem unfold_iter_eq_recv_to_CanRecv (a : LocalTypeR) (p : String)
    (bs : List (Label × LocalTypeR)) :
    ∀ n, (LocalTypeR.unfold^[n] a = LocalTypeR.recv p bs) → CanRecv a p bs := by
  intro n h
  -- Dualize the unfold equality, then reduce to send.
  have hdual : (LocalTypeR.unfold^[n] a).dual = .send p (dualBranches bs) := by
    simpa [LocalTypeR.dual] using congrArg LocalTypeR.dual h
  have hsend : CanSend a.dual p (dualBranches bs) := by
    -- Commute dual with iterate.
    have h' : LocalTypeR.unfold^[n] a.dual = .send p (dualBranches bs) := by
      simpa [unfold_iter_dual n a] using hdual
    exact unfold_iter_eq_send_to_CanSend a.dual p (dualBranches bs) n h'
  have hrecv := CanSend.dual hsend
  simpa [dualBranches_dualBranches, LocalTypeR.dual_dual] using hrecv

theorem UnfoldsToEnd_of_fullUnfold_eq {a : LocalTypeR} (h : a.fullUnfold = .end) :
    UnfoldsToEnd a := by
  apply unfold_iter_eq_end_to_UnfoldsToEnd a a.muHeight
  simpa [LocalTypeR.fullUnfold] using h

theorem UnfoldsToVar_of_fullUnfold_eq {a : LocalTypeR} {v : String} (h : a.fullUnfold = .var v) :
    UnfoldsToVar a v := by
  apply unfold_iter_eq_var_to_UnfoldsToVar a v a.muHeight
  simpa [LocalTypeR.fullUnfold] using h

theorem CanSend_of_fullUnfold_eq {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : a.fullUnfold = .send p bs) : CanSend a p bs := by
  apply unfold_iter_eq_send_to_CanSend a p bs a.muHeight
  simpa [LocalTypeR.fullUnfold] using h

/-- Derived from `CanSend_of_fullUnfold_eq` via duality. -/
theorem CanRecv_of_fullUnfold_eq {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : a.fullUnfold = LocalTypeR.recv p bs) : CanRecv a p bs := by
  -- Reduce recv to send via duality on fullUnfold.
  have hdual : a.dual.fullUnfold = .send p (dualBranches bs) := by
    simpa [fullUnfold_dual, LocalTypeR.dual] using congrArg LocalTypeR.dual h
  have hsend := CanSend_of_fullUnfold_eq hdual
  have hrecv := CanSend.dual hsend
  simpa [dualBranches_dualBranches, LocalTypeR.dual_dual] using hrecv


/-- fullUnfold reflects observable predicates for well-formed types. -/
theorem UnfoldsToEnd.fullUnfold_eq {a : LocalTypeR} (h : UnfoldsToEnd a)
    (hWF : LocalTypeR.WellFormed a) : a.fullUnfold = .end := by
  have hmu : a.fullUnfold.muHeight = 0 :=
    LocalTypeR.fullUnfold_non_mu_of_contractive (lt := a) hWF.contractive hWF.closed
  cases hfull : a.fullUnfold with
  | «end» => rfl
  | var v =>
      have hcontra := (LocalTypeR.fullUnfold_not_var_of_closed (lt := a) hWF.closed v)
      exact (False.elim (hcontra (by simpa [hfull])))
  | send p bs =>
      have hcan : CanSend a p bs := CanSend_of_fullUnfold_eq (by simpa [hfull])
      have hcontra : False := (CanSend.not_end (a := a) (p := p) (bs := bs) hcan) h
      exact hcontra.elim
  | recv p bs =>
      have hcan : CanRecv a p bs := CanRecv_of_fullUnfold_eq (by simpa [hfull])
      have hcontra : False := (CanRecv.not_end (a := a) (p := p) (bs := bs) hcan) h
      exact hcontra.elim
  | mu t body =>
      have hcontra : Nat.succ body.muHeight = 0 := by
        simpa [LocalTypeR.muHeight, hfull] using hmu
      exact (False.elim (Nat.succ_ne_zero _ hcontra))

/-- fullUnfold reflects var unfolding for well-formed types. -/
theorem UnfoldsToVar.fullUnfold_eq {a : LocalTypeR} {v : String} (h : UnfoldsToVar a v)
    (hWF : LocalTypeR.WellFormed a) : a.fullUnfold = .var v := by
  have hmu : a.fullUnfold.muHeight = 0 :=
    LocalTypeR.fullUnfold_non_mu_of_contractive (lt := a) hWF.contractive hWF.closed
  cases hfull : a.fullUnfold with
  | var w =>
      have hvar : UnfoldsToVar a w := UnfoldsToVar_of_fullUnfold_eq (by simpa [hfull])
      have hw : w = v := UnfoldsToVar.deterministic hvar h
      simp only [hw]
  | «end» =>
      have hend : UnfoldsToEnd a := UnfoldsToEnd_of_fullUnfold_eq (by simpa [hfull])
      have hcontra : False := (UnfoldsToVar.not_end_of_var h) hend
      exact hcontra.elim
  | send p bs =>
      have hcan : CanSend a p bs := CanSend_of_fullUnfold_eq (by simpa [hfull])
      have hcontra : False := (CanSend.not_var (a := a) (p := p) (bs := bs) hcan) v h
      exact hcontra.elim
  | recv p bs =>
      have hcan : CanRecv a p bs := CanRecv_of_fullUnfold_eq (by simpa [hfull])
      have hcontra : False := (CanRecv.not_var (a := a) (p := p) (bs := bs) hcan) v h
      exact hcontra.elim
  | mu t body =>
      have hcontra : Nat.succ body.muHeight = 0 := by
        simpa [LocalTypeR.muHeight, hfull] using hmu
      exact (False.elim (Nat.succ_ne_zero _ hcontra))

/-- fullUnfold reflects send unfolding for well-formed types. -/
theorem CanSend.fullUnfold_eq {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanSend a p bs) (hWF : LocalTypeR.WellFormed a) : a.fullUnfold = .send p bs := by
  have hmu : a.fullUnfold.muHeight = 0 :=
    LocalTypeR.fullUnfold_non_mu_of_contractive (lt := a) hWF.contractive hWF.closed
  cases hfull : a.fullUnfold with
  | send q cs =>
      have hcan' : CanSend a q cs := CanSend_of_fullUnfold_eq (by simpa [hfull])
      obtain ⟨hp, hbs⟩ := CanSend.deterministic h hcan'
      simp only [hp, hbs]
  | «end» =>
      have hend : UnfoldsToEnd a := UnfoldsToEnd_of_fullUnfold_eq (by simpa [hfull])
      have hcontra : False := (CanSend.not_end (a := a) (p := p) (bs := bs) h) hend
      exact hcontra.elim
  | var v =>
      have hvar : UnfoldsToVar a v := UnfoldsToVar_of_fullUnfold_eq (by simpa [hfull])
      have hcontra : False := (CanSend.not_var (a := a) (p := p) (bs := bs) h) v hvar
      exact hcontra.elim
  | recv q cs =>
      have hcan : CanRecv a q cs := CanRecv_of_fullUnfold_eq (by simpa [hfull])
      have hcontra : False := (CanSend.not_recv (a := a) (p := p) (q := q) (bs := bs) (cs := cs) h) hcan
      exact hcontra.elim
  | mu t body =>
      have hcontra : Nat.succ body.muHeight = 0 := by
        simpa [LocalTypeR.muHeight, hfull] using hmu
      exact (False.elim (Nat.succ_ne_zero _ hcontra))

/-- fullUnfold reflects recv unfolding for well-formed types. -/
theorem CanRecv.fullUnfold_eq {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanRecv a p bs) (hWF : LocalTypeR.WellFormed a) : a.fullUnfold = .recv p bs := by
  -- Reduce recv to send via duality, then translate back across fullUnfold.
  have hsend : CanSend a.dual p (dualBranches bs) := CanRecv.dual h
  have hWFdual : LocalTypeR.WellFormed a.dual := SessionTypes.LocalTypeR.WellFormed.dual hWF
  have hfull_send : a.dual.fullUnfold = .send p (dualBranches bs) :=
    CanSend.fullUnfold_eq hsend hWFdual
  have hfull_dual : (a.fullUnfold).dual = .send p (dualBranches bs) := by
    simpa [fullUnfold_dual] using hfull_send
  have hfull := congrArg LocalTypeR.dual hfull_dual
  simpa [LocalTypeR.dual, dualBranches_involutive, LocalTypeR.dual_dual] using hfull

/-- CanSend implies all branches are well-formed under LocalTypeR.WellFormed a. -/
theorem WellFormed_branches_of_CanSend {a : LocalTypeR} {p : String}
    {bs : List (Label × LocalTypeR)} (h : CanSend a p bs) (hWF : LocalTypeR.WellFormed a) :
    ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2 := by
  have hfull : a.fullUnfold = .send p bs := CanSend.fullUnfold_eq h hWF
  have hWFfull : LocalTypeR.WellFormed a.fullUnfold := LocalTypeR.WellFormed.fullUnfold hWF
  have hWFsend : LocalTypeR.WellFormed (.send p bs) := by
    simpa [hfull] using hWFfull
  simpa using (LocalTypeR.WellFormed.branches_of_send (p := p) (bs := bs) hWFsend)

/-- CanRecv implies all branches are well-formed under LocalTypeR.WellFormed a. -/
theorem WellFormed_branches_of_CanRecv {a : LocalTypeR} {p : String}
    {bs : List (Label × LocalTypeR)} (h : CanRecv a p bs) (hWF : LocalTypeR.WellFormed a) :
    ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2 := by
  -- Use duality to lift branch well-formedness from the send case.
  have hsend : CanSend a.dual p (dualBranches bs) := CanRecv.dual h
  have hWFdual : LocalTypeR.WellFormed a.dual := SessionTypes.LocalTypeR.WellFormed.dual hWF
  have hWFbs := WellFormed_branches_of_CanSend hsend hWFdual
  intro lb hlb
  have hmem_dual : (lb.1, lb.2.dual) ∈ dualBranches bs := by
    -- Map membership across dualBranches.
    have hmem' : (lb.1, lb.2.dual) ∈ bs.map (fun b => (b.1, b.2.dual)) :=
      List.mem_map_of_mem (f := fun b => (b.1, b.2.dual)) hlb
    simpa [dualBranches_eq_map] using hmem'
  have hWFdual_branch : LocalTypeR.WellFormed lb.2.dual := hWFbs _ hmem_dual
  have hWF := SessionTypes.LocalTypeR.WellFormed.dual hWFdual_branch
  simpa [LocalTypeR.dual_dual] using hWF

end SessionCoTypes.Bisim
