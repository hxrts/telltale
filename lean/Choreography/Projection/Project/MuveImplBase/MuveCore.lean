import Choreography.Projection.Project.Core
import Choreography.Projection.Projectb
import SessionTypes.Participation
import SessionCoTypes.EQ2
import SessionCoTypes.EQ2Props
import Choreography.Projection.Project.MuveImplBase.MuveCoreFreeVars

/-! # Choreography.Projection.Project.Muve

Muve (mu-var-end) infrastructure and non-participant projection results.

## Expose

The following definitions form the semantic interface for proofs:

- `isMuve`: mu-var-end predicate on local types
- `eq_end`: non-participants project to EEnd (EQ2)
- `c_project_muve_of_not_part_of2`: non-participant projections are muve
- `part_of2_or_end`: participant-or-end classification
-/

namespace Choreography.Projection.Project
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Project
open Choreography.Projection.Projectb
open SessionTypes.Participation
open SessionCoTypes.EQ2
open SessionCoTypes.EQ2Props

/-! ## Structural Well-Formedness

Following the Coq development, we separate structural properties (allCommsNonEmpty, noSelfComm)
from variable binding (allVarsBound). The structural properties compose well with mu bodies,
while allVarsBound does not (body.allVarsBound [t] doesn't imply body.allVarsBound []).

This avoids the semantic gap that arises from using full wellFormed. -/

-- Mu Structural Well-Formedness Helper
private theorem well_formed_mu_body (t : String) (body : GlobalType)
    (hwf : (GlobalType.mu t body).wellFormed = true) :
    body.allCommsNonEmpty = true ∧ body.noSelfComm = true := by
  unfold GlobalType.wellFormed at hwf
  simp only [GlobalType.allCommsNonEmpty, GlobalType.noSelfComm, Bool.and_eq_true] at hwf
  simp_all only [and_self]

-- Size Decrease Helper for Comm Branches
private theorem size_of_pair_snd_lt_comm (sender receiver : String) (pair : Label × GlobalType)
    (rest : List (Label × GlobalType)) :
    sizeOf pair.2 < sizeOf (GlobalType.comm sender receiver (pair :: rest)) := by
  -- sizeOf (comm s r bs) = 1 + sizeOf s + sizeOf r + sizeOf bs
  -- sizeOf (pair :: rest) = 1 + sizeOf pair + sizeOf rest
  -- sizeOf pair = 1 + sizeOf pair.1 + sizeOf pair.2
  -- So sizeOf pair.2 < 1 + sizeOf s + sizeOf r + (1 + (1 + sizeOf pair.1 + sizeOf pair.2) + sizeOf rest)
  --               = 3 + sizeOf s + sizeOf r + sizeOf pair.1 + sizeOf pair.2 + sizeOf rest
  -- Which is: sizeOf pair.2 < sizeOf pair.2 + (3 + sizeOf s + sizeOf r + sizeOf pair.1 + sizeOf rest)
  -- Since 3 + ... > 0, this is true
  simp only [GlobalType.comm.sizeOf_spec]
  have hp : sizeOf pair = 1 + sizeOf pair.1 + sizeOf pair.2 := by rfl
  simp only [List.cons.sizeOf_spec, hp]
  omega

-- Comm Branch Well-Formedness Helper
private theorem well_formed_comm_cont (sender receiver : String) (pair : Label × GlobalType)
    (rest : List (Label × GlobalType))
    (hwf : (GlobalType.comm sender receiver (pair :: rest)).wellFormed = true) :
    pair.2.wellFormed = true := by
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf ⊢
  simp only [GlobalType.allVarsBound, allVarsBoundBranches,
             GlobalType.allCommsNonEmpty, allCommsNonEmptyBranches,
             GlobalType.noSelfComm, noSelfCommBranches,
             GlobalType.isProductive, isProductiveBranches,
             Bool.and_eq_true] at hwf ⊢
  tauto

-- Auxiliary Muve Projection Theorems
private theorem trans_muve_of_not_part_of2_aux_base (g : GlobalType) (role : String) :
    g = .end ∨ (∃ t, g = .var t) → isMuve (trans g role) = true := by
  -- Base cases follow directly from trans and isMuve definitions.
  intro h
  cases h with
  | inl hEnd => cases hEnd; simp [Choreography.Projection.Trans.trans, isMuve]
  | inr hVar => rcases hVar with ⟨t, rfl⟩; simp [Choreography.Projection.Trans.trans, isMuve]

-- Auxiliary Mu Case
private theorem trans_muve_of_not_part_of2_aux_mu (t : String) (body : GlobalType) (role : String)
    (_hnotpart : ¬ part_of2 role (.mu t body))
    (_hne : (GlobalType.mu t body).allCommsNonEmpty = true)
    (_hnsc : (GlobalType.mu t body).noSelfComm = true)
    (hbody : isMuve (trans body role) = true) :
    isMuve (trans (.mu t body) role) = true := by
  -- The mu case reduces to the body when the projection is guarded.
  unfold trans
  rw [Choreography.Projection.Trans.trans.eq_3]
  by_cases hguard : (trans body role).isGuarded t
  · simp only [hguard, ↓reduceIte, isMuve]
    exact hbody
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte, isMuve]

-- Main Auxiliary Recursor
private theorem trans_muve_of_not_part_of2_aux (g : GlobalType) (role : String)
    (hnotpart : ¬ part_of2 role g)
    (hne : g.allCommsNonEmpty = true) (hnsc : g.noSelfComm = true) :
    isMuve (trans g role) = true := by
  -- Dispatch on g and delegate to the focused helpers.
  match g with
  | .end => exact trans_muve_of_not_part_of2_aux_base .end role (Or.inl rfl)
  | .var t => exact trans_muve_of_not_part_of2_aux_base (.var t) role (Or.inr ⟨t, rfl⟩)
  | .mu t body =>
      have hnotpart_body : ¬ part_of2 role body := by
/- ## Structured Block 6 -/
        intro hbody
        exact hnotpart (part_of2.intro _ (part_ofF.mu t body hbody))
      have hne_body : body.allCommsNonEmpty = true := by
        simpa [GlobalType.allCommsNonEmpty] using hne
      have hnsc_body : body.noSelfComm = true := by
        simpa [GlobalType.noSelfComm] using hnsc
      have hbody : isMuve (trans body role) = true :=
        trans_muve_of_not_part_of2_aux body role hnotpart_body hne_body hnsc_body
      exact trans_muve_of_not_part_of2_aux_mu t body role hnotpart hne hnsc hbody
  -- Auxiliary Recursor: Comm Case
  | .comm sender receiver branches =>
      -- Participants contradict the non-participation hypothesis; non-participants recurse.
      cases hrole_sender : role == sender with
      | true =>
          have hpart : part_of2 role (GlobalType.comm sender receiver branches) := by
            apply part_of2.intro; apply part_ofF.comm_direct
            simp [is_participant, hrole_sender]
          exact (hnotpart hpart).elim
      | false =>
          cases hrole_receiver : role == receiver with
          | true =>
              have hpart : part_of2 role (GlobalType.comm sender receiver branches) := by
                apply part_of2.intro; apply part_ofF.comm_direct
                simp [is_participant, hrole_sender, hrole_receiver]
              exact (hnotpart hpart).elim
          | false =>
              cases branches with
              | nil =>
                  simp [Choreography.Projection.Trans.trans, hrole_sender, hrole_receiver, isMuve]
              | cons first rest =>
                  unfold trans
                  rw [Choreography.Projection.Trans.trans.eq_5]
                  simp only [hrole_sender, Bool.false_eq_true, ↓reduceIte, hrole_receiver]
                  have hnotpart_cont : ¬ part_of2 role first.2 := by
                    intro hcont
                    have hmem : (first.1, first.2) ∈ first :: rest := by simp
                    exact hnotpart (part_of2.intro _ (part_ofF.comm_branch sender receiver
                      first.1 first.2 (first :: rest) hmem hcont))
                  have hne_cont : first.2.allCommsNonEmpty = true := by
                    simp only [GlobalType.allCommsNonEmpty, allCommsNonEmptyBranches,
                      Bool.and_eq_true] at hne
                    exact hne.2.1
                  have hnsc_cont : first.2.noSelfComm = true := by
                    simp only [GlobalType.noSelfComm, noSelfCommBranches,
                      Bool.and_eq_true] at hnsc
                    exact hnsc.2.1
                  exact trans_muve_of_not_part_of2_aux first.2 role hnotpart_cont hne_cont hnsc_cont
  | .delegate p q sid r cont =>
      have hrp : (role == p) = false := by
        cases h : role == p
        · rfl
        · exact (hnotpart (part_of2.intro _ (part_ofF.delegate_direct p q sid r cont
            (by simp [is_participant, h])))).elim
      have hrq : (role == q) = false := by
        cases h : role == q
        · rfl
        · exact (hnotpart (part_of2.intro _ (part_ofF.delegate_direct p q sid r cont
            (by simp [is_participant, h])))).elim
      have hnotpart_cont : ¬ part_of2 role cont := fun hc =>
        hnotpart (part_of2.intro _ (part_ofF.delegate_cont p q sid r cont hc))
      have hne_cont : cont.allCommsNonEmpty = true := by
        simpa [GlobalType.allCommsNonEmpty] using hne
      have hnsc_cont : cont.noSelfComm = true := by
        simp only [GlobalType.noSelfComm, Bool.and_eq_true] at hnsc
        exact hnsc.2
      have hcont := trans_muve_of_not_part_of2_aux cont role hnotpart_cont hne_cont hnsc_cont
      unfold trans
      rw [Choreography.Projection.Trans.trans.eq_def]
      simpa [hrp, hrq] using hcont
termination_by sizeOf g
decreasing_by
  all_goals
    simp_wf
    subst_vars
    first
/- ## Structured Block 7 -/
    | omega
    | exact size_of_body_lt_mu _ _
    | simpa [GlobalType.comm.sizeOf_spec] using size_of_pair_snd_lt_comm _ _ _ _

-- Non-Participant Muve Projection Theorem
theorem trans_muve_of_not_part_of2 (g : GlobalType) (role : String)
    (hnotpart : ¬ part_of2 role g) (hwf : g.wellFormed = true) :
    isMuve (trans g role) = true := by
  -- Extract structural properties from wellFormed
  -- wellFormed = (((allVarsBound ∧ allCommsNonEmpty) ∧ noSelfComm) ∧ isProductive)
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  exact trans_muve_of_not_part_of2_aux g role hnotpart hwf.1.1.2 hwf.1.2

end Choreography.Projection.Project
