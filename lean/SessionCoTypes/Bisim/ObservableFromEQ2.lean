import SessionCoTypes.Bisim.EQ2Equivalence

/-! # SessionCoTypes.Bisim.ObservableFromEQ2

Extracts observable behavior from EQ2 proofs under closedness/contractiveness.
-/

/-
The Problem. Converting EQ2 to Bisim requires extracting observable behavior
(UnfoldsToEnd, CanSend, etc.) from EQ2 proofs. This is only valid for contractive
types where mu-bound variables are guarded by communication.

Solution Structure. Defines `EQ2Extraction` interface for extracting observables.
Provides contractive-only extraction (fully proven), unconditional extraction
(for legacy compatibility), and hybrid default. The layered design isolates the
contractive requirement so it doesn't leak into downstream proofs.
-/

set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false

namespace SessionCoTypes.Bisim
open SessionTypes.LocalTypeR
open SessionTypes.GlobalType
open SessionCoTypes.Observable
open SessionCoTypes.EQ2
open SessionCoTypes.CoinductiveRel
/-! ## Observable Behavior Extraction from EQ2

These lemmas extract observable behavior from EQ2 proofs. They are needed for EQ2.to_bisim.

**IMPORTANT SEMANTIC CONSTRAINT**: These lemmas are only valid for *contractive* types,
where every mu-bound variable is guarded (appears only inside a communication before
any recursive reference). For non-contractive types like `.mu t (.var t)`, the EQ2
relation can hold for `EQ2 .end (.mu t (.var t))` (via the gfp semantics allowing
infinite chains), but `UnfoldsToEnd (.mu t (.var t))` is false (it cycles forever).

We expose a **layered extraction interface** so we can swap between:
- a contractive-only extraction (fully proven, requires proofs), and
- an unconditional extraction, with
- a hybrid default that prefers contractive proofs but falls back to the unconditional layer.

The global default matches the substitution environment default: **no extra obligations**
leak into downstream proofs, but we retain a single integration point for swapping. -/

/-! ## EQ2 Extraction Layer (Swap Point) -/

structure EQ2Extraction where
  Good : LocalTypeR → Prop
  end_right : ∀ {x}, Good x → EQ2 .end x → UnfoldsToEnd x
  var_right : ∀ {x v}, Good x → EQ2 (.var v) x → UnfoldsToVar x v
  send_right : ∀ {x p bs}, Good x → EQ2 (.send p bs) x →
    ∃ cs, CanSend x p cs ∧ BranchesRel EQ2 bs cs
  recv_right : ∀ {x p bs}, Good x → EQ2 (.recv p bs) x →
    ∃ cs, CanRecv x p cs ∧ BranchesRel EQ2 bs cs
  mus_to_BisimF :
    ∀ {t s body body'}, Good (.mu t body) → Good (.mu s body') →
      EQ2 (LocalTypeR.mu t body) (LocalTypeR.mu s body') → BisimF EQ2 (LocalTypeR.mu t body) (LocalTypeR.mu s body')

/-! ## Extraction: End Observables -/

/-- For closed, contractive types, `EQ2 .end x` implies `UnfoldsToEnd x`.

    Proof: By `observable_of_closed_contractive`, x has observable behavior. By the
    incompatibility lemmas above, the only possibility is `UnfoldsToEnd`. -/
theorem EQ2.end_right_implies_unfolds_to_end_of_closed {x : LocalTypeR}
    (hclosed : x.isClosed) (hcontr : x.isContractive = true) (heq : EQ2 .end x) : UnfoldsToEnd x := by
  have hobs := observable_of_closed_contractive hclosed hcontr
  cases hobs with
  | is_end h => exact h
  | is_var h => exact absurd heq (eq2_end_not_unfolds_to_var h)
  | is_send h => exact absurd heq (eq2_end_not_can_send h)
  | is_recv h => exact absurd heq (eq2_end_not_can_recv h)

/-- For contractive types, `EQ2 .end x` implies `UnfoldsToEnd x`. -/
theorem EQ2.end_right_implies_unfolds_to_end_of_contractive {x : LocalTypeR}
    (hclosed : x.isClosed) (hcontr : x.isContractive = true) (heq : EQ2 .end x) : UnfoldsToEnd x := by
  have hobs := observable_of_closed_contractive hclosed hcontr
  cases hobs with
  | is_end h => exact h
  | is_var h => exact absurd heq (eq2_end_not_unfolds_to_var h)
  | is_send h => exact absurd heq (eq2_end_not_can_send h)
  | is_recv h => exact absurd heq (eq2_end_not_can_recv h)

/-- For contractive types, `EQ2 x .end` implies `UnfoldsToEnd x`. -/
theorem EQ2.end_left_implies_unfolds_to_end_of_contractive {x : LocalTypeR}
    (hclosed : x.isClosed) (hcontr : x.isContractive = true) (heq : EQ2 x .end) : UnfoldsToEnd x :=
  EQ2.end_right_implies_unfolds_to_end_of_contractive hclosed hcontr (eq2_symm heq)

/-! ## Extraction: Variable Observables -/

/-- For contractive types, `EQ2 (.var v) x` implies `UnfoldsToVar x v`. -/
theorem EQ2.var_right_implies_unfolds_to_var_of_contractive {x : LocalTypeR} {v : String}
    (hclosed : x.isClosed) (hcontr : x.isContractive = true) (heq : EQ2 (.var v) x) : UnfoldsToVar x v := by
  have hobs := observable_of_closed_contractive hclosed hcontr
  cases hobs with
  | is_end h => exact absurd heq (eq2_var_not_unfolds_to_end h)
  | is_var h =>
      rename_i v'
      by_cases hne : v' = v
      · subst hne; exact h
      · exact (False.elim (eq2_var_not_unfolds_to_var_diff h heq hne))
  | is_send h => exact absurd heq (eq2_var_not_can_send h)
  | is_recv h => exact absurd heq (eq2_var_not_can_recv h)

/-- For contractive types, `EQ2 x (.var v)` implies `UnfoldsToVar x v`. -/
theorem EQ2.var_left_implies_unfolds_to_var_of_contractive {x : LocalTypeR} {v : String}
    (hclosed : x.isClosed) (hcontr : x.isContractive = true) (heq : EQ2 x (.var v)) : UnfoldsToVar x v :=
  EQ2.var_right_implies_unfolds_to_var_of_contractive hclosed hcontr (eq2_symm heq)

/-! ## Extraction: Send Observables -/

/-- For contractive types, `EQ2 (.send p bs) x` implies `CanSend x p cs` with matching branches. -/
theorem EQ2.send_right_implies_can_send_of_contractive {x : LocalTypeR} {p : String}
    {bs : List BranchR} (hclosed : x.isClosed) (hcontr : x.isContractive = true)
    (heq : EQ2 (.send p bs) x) : ∃ cs, CanSend x p cs ∧ BranchesRel EQ2 bs cs := by
  have hobs := observable_of_closed_contractive hclosed hcontr
  cases hobs with
  | is_end hend =>
      exact (False.elim (eq2_send_not_unfolds_to_end hend heq))
  | is_var hvar =>
      exact (False.elim (eq2_send_not_unfolds_to_var hvar heq))
  | is_recv hrecv =>
      exact (False.elim (eq2_send_not_can_recv hrecv heq))
  | is_send hsend =>
      rename_i p' cs
      obtain ⟨n, hn⟩ := CanSend.to_bounded hsend
      have hiter := (eq2_unfold_right_iter (a := .send p bs) (b := x) heq) n
      have hsend_unfold : EQ2 (.send p bs) ((LocalTypeR.unfold)^[n] x) := by
        simpa using hiter
      have hx : (LocalTypeR.unfold)^[n] x = .send p' cs :=
        CanSendPathBounded.unfold_iter_eq hn
      have hsend' : EQ2 (.send p bs) (.send p' cs) := by
        simpa [hx] using hsend_unfold
      have hf := EQ2.destruct hsend'
      have ⟨hp, hbr⟩ : p = p' ∧ BranchesRel EQ2 bs cs := by
        simpa [EQ2F] using hf
      subst hp
      exact ⟨cs, hsend, hbr⟩

/-! ## Branch Utilities for Extraction -/

/-- Flip the direction of a BranchesRel proof. -/
theorem branches_rel_flip {as bs : List BranchR}
    (h : BranchesRel EQ2 as bs) : BranchesRel EQ2 bs as := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hbc _ ih => exact List.Forall₂.cons ⟨hbc.1.symm, eq2_symm hbc.2⟩ ih

/-- Flip BranchesRel EQ2 across duality on both sides. -/
theorem branches_rel_dual_eq2 {bs cs : List BranchR}
    (h : BranchesRel EQ2 (dualBranches bs) cs) :
    BranchesRel EQ2 bs (dualBranches cs) := by
  induction bs generalizing cs with
  | nil =>
      cases h
      exact List.Forall₂.nil
  | cons head tail ih =>
      cases cs with
      | nil => cases h
      | cons head' tail' =>
          cases head with
          | mk l rest =>
              cases head' with
              | mk l' rest' =>
                  cases h with
                  | cons hbc htail =>
                      have hdu : EQ2 rest.2 rest'.2.dual := by
                        have h' := eq2_dual_compat hbc.2
                        simpa [dual_involutive] using h'
                      exact List.Forall₂.cons ⟨hbc.1, hdu⟩ (ih htail)

/-- Dualize CanSend into CanRecv along matching branches. -/
theorem can_send_dual_to_can_recv {x : LocalTypeR} {p : String}
    {bs cs : List BranchR}
    (hcan : CanSend x.dual p cs) (hbr : BranchesRel EQ2 (dualBranches bs) cs) :
    ∃ cs', CanRecv x p cs' ∧ BranchesRel EQ2 bs cs' := by
  have hcan' : CanRecv x p (dualBranches cs) := by
    have h' : CanRecv x.dual.dual p (dualBranches cs) :=
      CanSend.dual (t := x.dual) hcan
    simpa [dual_involutive] using h'
  have hbr' : BranchesRel EQ2 bs (dualBranches cs) :=
    branches_rel_dual_eq2 (bs := bs) (cs := cs) hbr
  exact ⟨dualBranches cs, hcan', hbr'⟩
/-! ## Extraction: Send/Receive Symmetry -/

/-- For contractive types, `EQ2 x (.send p cs)` implies `CanSend x p bs` with matching branches. -/
theorem EQ2.send_left_implies_can_send_of_contractive {x : LocalTypeR} {p : String}
    {cs : List BranchR} (hclosed : x.isClosed) (hcontr : x.isContractive = true)
    (heq : EQ2 x (.send p cs)) : ∃ bs, CanSend x p bs ∧ BranchesRel EQ2 bs cs := by
  have hsymm := eq2_symm heq
  obtain ⟨bs, hcan, hbr⟩ := EQ2.send_right_implies_can_send_of_contractive (x := x) hclosed hcontr hsymm
  exact ⟨bs, hcan, branches_rel_flip hbr⟩

/-- For contractive types, `EQ2 (.recv p bs) x` implies `CanRecv x p cs` with matching branches. -/
theorem EQ2.recv_right_implies_can_recv_of_contractive {x : LocalTypeR} {p : String}
    {bs : List BranchR} (hclosed : x.isClosed) (hcontr : x.isContractive = true)
    (heq : EQ2 (.recv p bs) x) : ∃ cs, CanRecv x p cs ∧ BranchesRel EQ2 bs cs := by
  have hobs := observable_of_closed_contractive hclosed hcontr
  cases hobs with
  | is_end hend =>
      exact (False.elim (eq2_recv_not_unfolds_to_end hend heq))
  | is_var hvar =>
      exact (False.elim (eq2_recv_not_unfolds_to_var hvar heq))
  | is_send hsend =>
      exact (False.elim (eq2_recv_not_can_send hsend heq))
  | is_recv hrecv =>
      rename_i p' cs
      obtain ⟨n, hn⟩ := CanRecv.to_bounded hrecv
      have hiter := (eq2_unfold_right_iter (a := .recv p bs) (b := x) heq) n
      have hrecv_unfold : EQ2 (.recv p bs) ((LocalTypeR.unfold)^[n] x) := by
        simpa using hiter
      have hx : (LocalTypeR.unfold)^[n] x = .recv p' cs :=
        CanRecvPathBounded.unfold_iter_eq hn
      have hf := EQ2.destruct hrecv_unfold
      have hpr : p = p' ∧ BranchesRel EQ2 bs cs := by
        simpa [EQ2F, hx] using hf
      rcases hpr with ⟨hp, hbr⟩
      subst hp
      have hcan : CanRecv x p cs := CanRecvPathBounded.to_can_recv hn
      exact ⟨cs, hcan, hbr⟩

/-- For contractive types, `EQ2 x (.recv p cs)` implies `CanRecv x p bs` with matching branches. -/
theorem EQ2.recv_left_implies_can_recv_of_contractive {x : LocalTypeR} {p : String}
    {cs : List BranchR} (hclosed : x.isClosed) (hcontr : x.isContractive = true)
    (heq : EQ2 x (.recv p cs)) : ∃ bs, CanRecv x p bs ∧ BranchesRel EQ2 bs cs := by
  have hsymm := eq2_symm heq
  obtain ⟨bs, hcan, hbr⟩ := EQ2.recv_right_implies_can_recv_of_contractive (x := x) hclosed hcontr hsymm
  exact ⟨bs, hcan, branches_rel_flip hbr⟩


end SessionCoTypes.Bisim
