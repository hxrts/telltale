import Telltale.Protocol.Projection.Projectb
import Telltale.Protocol.Projection.Project.Core
import Telltale.Protocol.Projection.Project.Muve
import Telltale.Protocol.Projection.Trans
import Telltale.Protocol.CoTypes.EQ2
import Telltale.Protocol.CoTypes.EQ2Props
import Telltale.Protocol.CoTypes.EQ2Paco
import Telltale.Protocol.CoTypes.Bisim
import Telltale.Protocol.Projection.ProjSubst
import Telltale.Proofs.Projection.SubstEndUnguarded
import Telltale.Protocol.Participation

/-! # Project ImplBase

EQ2-based congruence proofs and completeness results connecting CProject with trans.
-/

set_option linter.unnecessarySimpa false

/-
The Problem. Relate the coinductive projection relation `CProject` to the algorithmic
projection `trans`, and use that connection to justify the proof-carrying API
(`projectR?`) and its completeness.

Solution Structure. This file focuses on EQ2-based congruence proofs, the coinductive
witness relations that bridge `CProject` and `trans`, and the completeness theorems
for the projection API. The lightweight API and muve theory live in
`Project/Core.lean` and `Project/Muve.lean`.
-/

/-! # Telltale.Protocol.Projection.Project

Proof-carrying projection API for V2.

## Overview

This module collects the EQ2 congruence proofs and completeness results that
connect `CProject` with `trans`. Core API definitions are in `Project/Core.lean`,
and the muve theory is in `Project/Muve.lean`.

## Expose

The following definitions form the semantic interface for proofs:

- `projectR?`: proof-carrying projection (returns projection with CProject proof)
- `projectR?_some_iff_CProject`: specification lemma
- `projectR?_sound`: soundness (some implies CProject)
- `projectR?_complete`: completeness (CProject implies some)
- `EQ_end`: non-participants project to EEnd (EQ2-equivalent)
-/

namespace Telltale.Protocol.Projection.Project

open Telltale.Protocol.GlobalType
open Telltale.Protocol.LocalTypeR
open Telltale.Protocol.Projection.Trans
open Telltale.Protocol.Projection.Projectb
open Telltale.Protocol.CoTypes.EQ2
open Telltale.Protocol.CoTypes.EQ2Props
open Telltale.Protocol.CoTypes.EQ2Paco
open Paco
open Telltale.Protocol.Participation

/-! ## Projection-EQ2 Congruence Lemmas

The following lemmas establish that CProject and trans interact coherently with EQ2.
These correspond to key lemmas from the Coq development:
- `proj_proj`: if CProject g p e, then EQ2 e (trans g p)
- `Project_EQ2`: if CProject g p e0 and EQ2 e0 e1, then CProject g p e1

### CProject_implies_EQ2_trans Proof Strategy

The proof uses coinduction on EQ2 with the relation:
`CProjectTransRel lt cand := ∃ g role, CProject g role lt ∧ cand = trans g role`

For end, var, and participant comm cases, CProject and trans have matching structures.
For non-participants, we use `part_of2_or_end` + `EQ_end` to show EQ2 lt .end ∧ EQ2 .end (trans g role).
The mu case requires coinduction up-to with substitution lemmas.

See `subject_reduction/theories/Projection/indProj.v:221-260` for the Coq reference. -/

/-! ### Helper Lemmas for CProject_implies_EQ2_trans

The following helper lemmas support the proof of the main theorem. -/

/- Helper: part_of_all2 implies part_of2 (requires wellFormed for non-empty branches).

If a role participates on all branches, it certainly participates on some path.
The wellFormed hypothesis ensures branches are non-empty.

### Proof Strategy

Use well-founded induction on global type size:
- `comm_direct`: Trivially get `part_of2` via `part_of2.intro (.comm_direct ...)`
- `comm_all_branches`: wellFormed ensures branches ≠ [], so pick first branch.
  By IH on the continuation, get `part_of2 role cont`. Then construct
  `part_of2.intro (.comm_branch ...)` with the membership witness.
- `mu`: By IH on body, get `part_of2 role body`. Then construct
  `part_of2.intro (.mu ...)`.

### Coq Reference

See `subject_reduction/theories/Projection/indProj.v:180-192`.

We use an auxiliary version with weaker preconditions (just allCommsNonEmpty)
to avoid the semantic gap where body.allVarsBound [] cannot be proven from
(mu t body).wellFormed. -/
/-- Helper: sizeOf a member continuation is smaller than the comm node. -/
private theorem sizeOf_elem_snd_lt_comm (sender receiver : String)
    {branches : List (Label × GlobalType)} {gb : Label × GlobalType}
    (h : gb ∈ branches) :
    sizeOf gb.2 < sizeOf (GlobalType.comm sender receiver branches) := by
  -- Compare sizes: cont < pair < branches < comm.
  have h1 : sizeOf gb.2 < sizeOf gb := by
    cases gb with
    | mk l g => simp; omega
  have h2 : sizeOf gb < sizeOf branches := by
    have hlt := List.sizeOf_lt_of_mem h
    omega
  have h3 : sizeOf branches < sizeOf (GlobalType.comm sender receiver branches) := by
    simp [GlobalType.comm.sizeOf_spec]
    have hs : 0 < sizeOf sender := by
      have : sizeOf sender = 1 + sizeOf sender.bytes + sizeOf sender.isValidUTF8 := rfl
      omega
    have hr : 0 < sizeOf receiver := by
      have : sizeOf receiver = 1 + sizeOf receiver.bytes + sizeOf receiver.isValidUTF8 := rfl
      omega
    omega
  exact Nat.lt_trans h1 (Nat.lt_trans h2 h3)

/-- Helper: a branch membership inherits allCommsNonEmpty. -/
private theorem allCommsNonEmpty_of_mem {branches : List (Label × GlobalType)}
    {pair : Label × GlobalType} (hmem : pair ∈ branches)
    (hne : GlobalType.allCommsNonEmptyBranches branches = true) :
    pair.2.allCommsNonEmpty = true := by
  -- Peel the branch list until we find the member.
  induction branches with
  | nil => cases hmem
  | cons head tail ih =>
      simp only [GlobalType.allCommsNonEmptyBranches, Bool.and_eq_true] at hne
      cases hmem with
      | head => exact hne.1
      | tail _ hmem' => exact ih hmem' hne.2
/-- Helper: comm direct participant yields part_of2. -/
private theorem part_of_all2_implies_part_of2_aux_comm_direct (role : String)
    (sender receiver : String) (branches : List (Label × GlobalType))
    (hpart : is_participant role sender receiver = true) :
    part_of2 role (.comm sender receiver branches) := by
  -- Direct participation gives the comm constructor immediately.
  exact part_of2.intro _ (part_ofF.comm_direct sender receiver branches hpart)

/-- Helper: comm branch participation yields part_of2. -/
private theorem part_of_all2_implies_part_of2_aux_comm_branch (role : String)
    (sender receiver : String) (first : Label × GlobalType) (rest : List (Label × GlobalType))
    (hmem : first ∈ first :: rest) (ih : part_of2 role first.2) :
    part_of2 role (.comm sender receiver (first :: rest)) := by
  -- Use the comm-branch constructor with the head membership witness.
  exact part_of2.intro _ (part_ofF.comm_branch sender receiver first.1 first.2
    (first :: rest) hmem ih)

/-- part_of_all2 implies part_of2 under allCommsNonEmpty (auxiliary induction). -/
private theorem part_of_all2_implies_part_of2_aux_comm_cons (role : String)
    (sender receiver : String) (first : Label × GlobalType) (rest : List (Label × GlobalType))
    (hall : ∀ pair ∈ (first :: rest), part_of_all2 role pair.2)
    (ih : ∀ pair ∈ (first :: rest), part_of_all2 role pair.2 → part_of2 role pair.2) :
    part_of2 role (.comm sender receiver (first :: rest)) := by
  -- Recurse on the head branch and lift via the comm-branch constructor.
  have hmem : first ∈ first :: rest := by simp
  have hpair : part_of_all2 role first.2 := hall first hmem
  have ih_first := ih first hmem hpair
  exact part_of_all2_implies_part_of2_aux_comm_branch role sender receiver first rest hmem ih_first

/-- part_of_all2 implies part_of2 for mu nodes once the body case is known. -/
private theorem part_of_all2_implies_part_of2_aux_mu (role : String)
    (t : String) (body : GlobalType) (ih : part_of2 role body) :
    part_of2 role (.mu t body) := by
  -- Lift the body participation through the mu constructor.
  exact part_of2.intro _ (part_ofF.mu t body ih)

/-- part_of_all2 implies part_of2 for comm nodes once branch recursion is provided. -/
private theorem part_of_all2_implies_part_of2_aux_comm (role : String)
    (sender receiver : String) (branches : List (Label × GlobalType))
    (h : part_of_all2 role (.comm sender receiver branches))
    (hne : (GlobalType.comm sender receiver branches).allCommsNonEmpty = true)
    (ih : ∀ pair ∈ branches, part_of_all2 role pair.2 → part_of2 role pair.2) :
    part_of2 role (.comm sender receiver branches) := by
  -- Use the direct-participant or branch-participant case.
  have h_or := part_of_all2_comm_inv h
  cases h_or with
  | inl hpart =>
      exact part_of_all2_implies_part_of2_aux_comm_direct role sender receiver branches hpart
  | inr hall =>
      cases hbranches : branches with
      | nil =>
          -- Empty branches contradict allCommsNonEmpty for comm.
          have hne' : False := by
            simpa [GlobalType.allCommsNonEmpty, hbranches] using hne
          exact (False.elim hne')
      | cons first remaining =>
          have hall' : ∀ pair ∈ (first :: remaining), part_of_all2 role pair.2 := by
            simpa [hbranches] using hall
          exact part_of_all2_implies_part_of2_aux_comm_cons role sender receiver
            first remaining hall' (by simpa [hbranches] using ih)

/-- part_of_all2 implies part_of2 under allCommsNonEmpty (auxiliary induction). -/
private theorem part_of_all2_implies_part_of2_aux (role : String) (g : GlobalType)
    (h : part_of_all2 role g)
    (hne : g.allCommsNonEmpty = true) : part_of2 role g := by
  -- Structural recursion on g using allCommsNonEmpty for comm branches.
  match g with
  | .end => exact absurd h (not_part_of_all2_end role)
  | .var t => exact absurd h (not_part_of_all2_var role t)
  | .mu t body =>
      have hbody := part_of_all2_mu_inv h
      have hne_body : body.allCommsNonEmpty = true := by simpa [GlobalType.allCommsNonEmpty] using hne
      have ih := part_of_all2_implies_part_of2_aux role body hbody hne_body
      exact part_of_all2_implies_part_of2_aux_mu role t body ih
  | .comm sender receiver branches =>
      have hne_branches : GlobalType.allCommsNonEmptyBranches branches = true := by
        have hne' :
            (branches ≠ [] ∧ GlobalType.allCommsNonEmptyBranches branches = true) := by
          simpa [GlobalType.allCommsNonEmpty] using hne
        exact hne'.2
      have ih :
          ∀ pair ∈ branches, part_of_all2 role pair.2 → part_of2 role pair.2 := by
        intro pair hmem hpoa
        have hne_pair : pair.2.allCommsNonEmpty = true :=
          allCommsNonEmpty_of_mem hmem hne_branches
        exact part_of_all2_implies_part_of2_aux role pair.2 hpoa hne_pair
      exact part_of_all2_implies_part_of2_aux_comm role sender receiver branches h hne ih
termination_by sizeOf g
decreasing_by
  all_goals simp_wf
  · -- Mu case: sizeOf decreases to the body.
    simp only [sizeOf, GlobalType._sizeOf_1] at *; omega
  · simpa using (sizeOf_elem_snd_lt_comm (sender := sender) (receiver := receiver)
      (branches := branches) (gb := pair) hmem)

/-- Participation in all branches implies standard participation (under well-formedness). -/
theorem part_of_all2_implies_part_of2 (role : String) (g : GlobalType)
    (h : part_of_all2 role g)
    (hwf : g.wellFormed = true) : part_of2 role g := by
  -- wellFormed = (((allVarsBound ∧ allCommsNonEmpty) ∧ noSelfComm) ∧ isProductive)
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  exact part_of_all2_implies_part_of2_aux role g h hwf.1.1.2

/-- Helper: if CProject gives lt and role doesn't participate, then lt is EQ2 to trans.

This uses the muve/closed infrastructure from EQ_end and part_of2_or_end.

#### Proof Outline

1. By `part_of2_or_end`, we get `part_of_all2 role g ∨ EQ2 lt .end`
2. The Left case contradicts `hnotpart` via `part_of_all2_implies_part_of2`
3. The Right case: chain `EQ2 lt .end` with `EQ2 .end (trans g role)` from `EQ_end` -/
private theorem CProject_implies_EQ2_trans_nonpart_left (g : GlobalType) (role : String)
    (hnotpart : ¬part_of2 role g) (hwf : g.wellFormed = true)
    (hpart_all : part_of_all2 role g) : False := by
  -- part_of_all2 implies part_of2, contradicting the non-participant hypothesis.
  exact hnotpart (part_of_all2_implies_part_of2 role g hpart_all hwf)

private theorem CProject_implies_EQ2_trans_nonpart_right (g : GlobalType) (role : String)
    (lt : LocalTypeR) (hnotpart : ¬part_of2 role g) (hwf : g.wellFormed = true)
    (hlt_end : EQ2 lt .end) : EQ2 lt (trans g role) := by
  -- Chain EQ2 lt .end with EQ_end for trans.
  have hend_trans := EQ_end role g hnotpart hwf
  exact EQ2_trans_via_end hlt_end hend_trans

private theorem CProject_implies_EQ2_trans_nonpart (g : GlobalType) (role : String) (lt : LocalTypeR)
    (hproj : CProject g role lt)
    (hnotpart : ¬part_of2 role g)
    (hwf : g.wellFormed = true) :
    EQ2 lt (trans g role) := by
  -- By part_of2_or_end, we get EQ2 lt .end
  have h_or := part_of2_or_end role g lt hproj hwf
  cases h_or with
  | inl hpart_all =>
      -- Contradiction: part_of_all2 implies part_of2.
      exact (CProject_implies_EQ2_trans_nonpart_left g role hnotpart hwf hpart_all).elim
  | inr hlt_end =>
      -- Chain EQ2 lt .end with EQ_end.
      exact CProject_implies_EQ2_trans_nonpart_right g role lt hnotpart hwf hlt_end

/-! ### Main Theorem: CProject_implies_EQ2_trans

Proof sketch: define `CProjectTransRel a b := ∃ g role, CProject g role a ∧ b = trans g role`,
show it is a post-fixpoint of EQ2F by constructor cases (end/var/mu/comm participant/non-participant),
and use the non-participant lemma for the .end bridge. Coq ref: indProj.v:221-260. -/

/-! ### CProject Candidate-Shape Inversion Lemmas

These lemmas package common CProjectF destruct patterns for the Project_EQ2 port. -/

private theorem CProject_end_inv (role : String) (cand : LocalTypeR)
    (hproj : CProject .end role cand) : cand = .end := by
  cases cand with
  | «end» => rfl
  | var _ =>
      have hf := CProject_destruct hproj
      have : False := by
        simp [CProjectF] at hf
      exact this.elim
  | send _ _ =>
      have hf := CProject_destruct hproj
      have : False := by
        simp [CProjectF] at hf
      exact this.elim
  | recv _ _ =>
      have hf := CProject_destruct hproj
      have : False := by
        simp [CProjectF] at hf
      exact this.elim
  | mu _ _ =>
      have hf := CProject_destruct hproj
      have : False := by
        simp [CProjectF] at hf
      exact this.elim

private theorem CProject_var_inv (t role : String) (cand : LocalTypeR)
    (hproj : CProject (.var t) role cand) : cand = .var t := by
  cases cand with
  | var t' =>
      have hf := CProject_destruct hproj
      simp [CProjectF] at hf
      subst hf
      rfl
  | «end» =>
      have hf := CProject_destruct hproj
      have : False := by
        simp [CProjectF] at hf
      exact this.elim
  | send _ _ =>
      have hf := CProject_destruct hproj
      have : False := by
        simp [CProjectF] at hf
      exact this.elim
  | recv _ _ =>
      have hf := CProject_destruct hproj
      have : False := by
        simp [CProjectF] at hf
      exact this.elim
  | mu _ _ =>
      have hf := CProject_destruct hproj
      have : False := by
        simp [CProjectF] at hf
      exact this.elim

private theorem CProject_mu_inv (t : String) (gbody : GlobalType) (role : String) (cand : LocalTypeR)
    (hproj : CProject (.mu t gbody) role cand) :
    ∃ candBody, CProject gbody role candBody ∧
      ((candBody.isGuarded t = true ∧ cand = .mu t candBody) ∨
       (candBody.isGuarded t = false ∧ cand = .end)) := by
  simpa [CProjectF] using (CProject_destruct hproj)

private theorem CProject_comm_sender_inv (sender receiver : String)
    (gbs : List (Label × GlobalType)) (role : String) (cand : LocalTypeR)
    (hrole : role = sender)
    (hproj : CProject (.comm sender receiver gbs) role cand) :
    ∃ lbs, cand = .send receiver lbs ∧ BranchesProjRel CProject gbs sender lbs := by
  cases cand with
  | send partner lbs =>
      have hf := CProject_destruct hproj
      simp [CProjectF, hrole] at hf
      rcases hf with ⟨hpartner, hbranches⟩
      subst hpartner
      exact ⟨lbs, rfl, hbranches⟩
  | _ =>
      -- Non-send candidates contradict the comm sender clause.
      have hf := CProject_destruct hproj
      have : False := by simpa [CProjectF, hrole] using hf
      exact this.elim

private theorem CProject_comm_receiver_inv (sender receiver : String)
    (gbs : List (Label × GlobalType)) (role : String) (cand : LocalTypeR)
    (hrole : role = receiver) (hns : sender ≠ receiver)
    (hproj : CProject (.comm sender receiver gbs) role cand) :
    ∃ lbs, cand = .recv sender lbs ∧ BranchesProjRel CProject gbs receiver lbs := by
  have hsender : role ≠ sender := by
    intro h
    exact hns (h.symm.trans hrole)
  have hne : receiver ≠ sender := by
    intro h
    exact hns h.symm
  cases cand with
  | recv partner lbs =>
      have hf := CProject_destruct hproj
      simp [CProjectF, hrole, hne] at hf
      rcases hf with ⟨hpartner, hbranches⟩
      subst hpartner
      exact ⟨lbs, rfl, hbranches⟩
  | _ =>
      -- Non-recv candidates contradict the comm receiver clause.
      have hf := CProject_destruct hproj
      have : False := by simpa [CProjectF, hrole, hne] using hf
      exact this.elim

private theorem CProject_comm_other_inv (sender receiver : String)
    (gbs : List (Label × GlobalType)) (role : String) (cand : LocalTypeR)
    (hs : role ≠ sender) (hr : role ≠ receiver)
    (hproj : CProject (.comm sender receiver gbs) role cand) :
    AllBranchesProj CProject gbs role cand := by
  have hf := CProject_destruct hproj
  simp [CProjectF, hs, hr] at hf
  exact hf

private theorem CProject_fullUnfold_right_of_muHeight_zero
    {g : GlobalType} {role : String} {cand : LocalTypeR}
    (hproj : CProject g role cand) (hmu : cand.muHeight = 0) :
    CProject g role cand.fullUnfold := by
  simpa [LocalTypeR.fullUnfold_muHeight_zero hmu] using hproj

private theorem CProject_fullUnfold_left_of_muHeight_zero
    {g : GlobalType} {role : String} {cand : LocalTypeR}
    (hproj : CProject g role cand.fullUnfold) (hmu : cand.muHeight = 0) :
    CProject g role cand := by
  simpa [LocalTypeR.fullUnfold_muHeight_zero hmu] using hproj

private theorem CProjectU_fullUnfold_right_of_muHeight_zero
    {g : GlobalType} {role : String} {cand : LocalTypeR}
    (hproj : CProjectU g role cand) (hmu : cand.muHeight = 0) :
    CProjectU g role cand.fullUnfold := by
  simpa [LocalTypeR.fullUnfold_muHeight_zero hmu] using hproj

private theorem CProjectU_fullUnfold_left_of_muHeight_zero
    {g : GlobalType} {role : String} {cand : LocalTypeR}
    (hproj : CProjectU g role cand.fullUnfold) (hmu : cand.muHeight = 0) :
    CProjectU g role cand := by
  simpa [LocalTypeR.fullUnfold_muHeight_zero hmu] using hproj


end Telltale.Protocol.Projection.Project
