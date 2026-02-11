import Choreography.Projection.Blind.Core.Lemmas

/-! # Choreography.Projection.Blind.Core.Theorems

Main projectability and final blindness theorems.
-/

/-
The Problem. We need the final theorem connecting well-formed blind global
types to projectability.

Solution Structure. Proves the key theorem and wraps supporting final lemmas.
-/

namespace Choreography.Projection.Blind

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Trans
open Choreography.Projection.Projectb

section
open Classical

/-! ## Main Theorem -/

/-- Core lemma: projectb succeeds on trans output when noSelfComm and isBlind hold.

    This is the heart of the proof - we only need noSelfComm (for comm cases)
    and isBlind (for non-participant uniformity). We don't need isClosed or
    the full wellFormed predicate. -/
theorem projectb_trans_of_noSelfComm_blind (g : GlobalType) (role : String)
    (hnoself : g.noSelfComm = true)
    (hblind : isBlind g = true) :
    projectb g role (Trans.trans g role) = true := by
  match g with
  | .end =>
      -- end case: trivial
      simp only [Trans.trans, projectb]
  | .var t =>
      -- var case: projectb matches var with var (always true)
      simp only [Trans.trans, projectb, beq_self_eq_true]
  | .mu t body =>
      -- mu case: recurse on body
      unfold Trans.trans
      have hnoself' := noSelfComm_mu_body hnoself
      have hblind' := isBlind_mu_body hblind
      by_cases hguard : (Trans.trans body role).isGuarded t
      · -- Guarded: mu preserved
        simp only [hguard, ↓reduceIte, projectb, beq_self_eq_true]
        exact projectb_trans_of_noSelfComm_blind body role hnoself' hblind'
      · -- Unguarded: collapses to end
        simp only [hguard, Bool.false_eq_true, ↓reduceIte, projectb]
        exact projectb_trans_of_noSelfComm_blind body role hnoself' hblind'
  | .comm sender receiver branches =>
      -- comm case: split on role participation
      -- Extract sender ≠ receiver from noSelfComm
      have hne_sr : sender ≠ receiver := by
        -- noSelfComm for comm = (sender != receiver) && noSelfCommBranches
        have hnoself' := hnoself
        simp only [GlobalType.noSelfComm, Bool.and_eq_true, bne_iff_ne, ne_eq] at hnoself'
        exact hnoself'.1
      -- Note: We have noSelfComm and isBlind for branches, which would allow
      -- recursive calls via hnoself_branches := noSelfComm_comm_branches hnoself
      -- and hblind_branches := isBlind_comm_branches hblind
      have hnoself_branches : ∀ p ∈ branches, p.2.noSelfComm = true :=
        noSelfComm_comm_branches (s := sender) (r := receiver) (bs := branches) hnoself
      have hblind_branches : ∀ p ∈ branches, isBlind p.2 = true :=
        isBlind_comm_branches (s := sender) (r := receiver) (bs := branches) hblind
      have hblind_comm : commBlindFor sender receiver branches = true := by
        have hblind' := hblind
        simp [isBlind, Bool.and_eq_true] at hblind'
        exact hblind'.1
      have hbranches_proj :
          ∀ p ∈ branches, projectb p.2 role (Trans.trans p.2 role) = true := by
        intro p hp
        exact projectb_trans_of_noSelfComm_blind p.2 role (hnoself_branches p hp) (hblind_branches p hp)
      by_cases hs : role = sender
      · -- Sender case: role = sender
        -- The result is .send receiver (transBranches branches role)
        -- projectb checks that projectbBranches matches
        have hproj_branches :=
          projectbBranches_trans_of_all branches role hbranches_proj
        have hproj_branches' :
            projectbBranches branches sender (transBranches branches sender) = true := by
          simpa [hs] using hproj_branches
        have htrans' :
            Trans.trans (GlobalType.comm sender receiver branches) sender =
              .send receiver (transBranches branches sender) := by
          simpa using trans_comm_sender sender receiver sender branches rfl
        simp [hs, htrans', projectb, hproj_branches']
      · by_cases hr : role = receiver
        · -- Receiver case: role = receiver
          -- The result is .recv sender (transBranches branches role)
          -- projectb checks that projectbBranches matches
          have hproj_branches :=
            projectbBranches_trans_of_all branches role hbranches_proj
          have hproj_branches' :
              projectbBranches branches receiver (transBranches branches receiver) = true := by
            simpa [hr] using hproj_branches
          have hns : receiver ≠ sender := Ne.symm hne_sr
          have htrans' :
              Trans.trans (GlobalType.comm sender receiver branches) receiver =
                .recv sender (transBranches branches receiver) := by
            simpa using trans_comm_receiver sender receiver receiver branches rfl hns
          simp [hr, hns, htrans', projectb, hproj_branches']
        · -- Non-participant case: role ≠ sender, role ≠ receiver
          -- The result is trans of the first branch continuation
          -- All branches must project uniformly (from blindness)
          cases hbranches : branches with
          | nil =>
              simp [projectbAllBranches, projectb, Trans.trans, hs, hr]
          | cons head rest =>
              cases head with
              | mk label cont =>
                  have hne : (label, cont) :: rest ≠ [] := by simp
                  have hblind_comm' :
                      commBlindFor sender receiver ((label, cont) :: rest) = true := by
                    simpa [hbranches] using hblind_comm
                  have huniform :
                      ∀ p ∈ ((label, cont) :: rest),
                        Trans.trans p.2 role = Trans.trans cont role := by
                    have huniform' :=
                      trans_uniform_for_nonparticipant (sender := sender) (receiver := receiver)
                        (role := role) (branches := (label, cont) :: rest) hblind_comm' hs hr hne
                    intro p hp
                    have h := huniform' p hp
                    simpa using h
                  have hproj_all :=
                    projectbAllBranches_trans_of_all_uniform ((label, cont) :: rest) role
                      (Trans.trans cont role) huniform (by
                        intro p hp
                        exact hbranches_proj p (by simpa [hbranches] using hp))
                  have hbs : (role == sender) = false := by
                    simpa using (beq_false_of_ne hs)
                  have hbr : (role == receiver) = false := by
                    simpa using (beq_false_of_ne hr)
                  have htrans_comm :
                      Trans.trans (GlobalType.comm sender receiver ((label, cont) :: rest)) role =
                        Trans.trans cont role := by
                    simp [Trans.trans, hbs, hbr]
                  have hproj_all' :
                      projectbAllBranches ((label, cont) :: rest) role
                        (Trans.trans (GlobalType.comm sender receiver ((label, cont) :: rest)) role) = true := by
                    simpa [htrans_comm] using hproj_all
                  unfold projectb
                  simp [hbs, hbr]
                  exact hproj_all'
  | .delegate p q sid r cont =>
      -- Delegate case: split on role participation
      -- Extract noSelfComm and isBlind for continuation
      have hnoself_cont : cont.noSelfComm = true := noSelfComm_delegate_cont hnoself
      have hblind_cont : isBlind cont = true := hblind  -- isBlind delegates to continuation
      have hcont_proj := projectb_trans_of_noSelfComm_blind cont role hnoself_cont hblind_cont
      by_cases hp : role = p
      · -- Delegator case: role = p
        -- trans gives .send q [(_delegate, some (.chan sid r), trans cont role)]
        -- projectb matches this exact shape
        have htrans : Trans.trans (GlobalType.delegate p q sid r cont) p =
            .send q [(⟨"_delegate", .unit⟩, some (.chan sid r), Trans.trans cont p)] := by
          -- Compute the candidate projection for the delegator.
          simp [Trans.trans]
        have hcont_proj' : projectb cont p (Trans.trans cont p) = true := by
          -- Specialize the IH to the delegator role.
          simpa [hp] using hcont_proj
        -- Reduce projectb to the continuation goal.
        calc
          projectb (GlobalType.delegate p q sid r cont) role
              (Trans.trans (GlobalType.delegate p q sid r cont) role)
              = projectb (GlobalType.delegate p q sid r cont) p
                  (Trans.trans (GlobalType.delegate p q sid r cont) p) := by
                    simp [hp]
          _ = projectb cont p (Trans.trans cont p) := by
                simp [projectb, htrans, reduceBEq]
          _ = true := hcont_proj'
      · by_cases hq : role = q
        · -- Delegatee case: role = q
          -- trans gives .recv p [(_delegate, some (.chan sid r), trans cont role)]
          -- projectb matches this exact shape
          have hqp : q ≠ p := by
            -- Non-participation on p follows from the outer case split.
            intro hqp
            apply hp
            simp [hq, hqp]
          have hpne : (q == p) = false := by
            simpa [beq_eq_false_iff_ne, ne_eq] using hqp
          have htrans : Trans.trans (GlobalType.delegate p q sid r cont) q =
              .recv p [(⟨"_delegate", .unit⟩, some (.chan sid r), Trans.trans cont q)] := by
            -- Compute the candidate projection for the delegatee.
            simp [Trans.trans, hpne]
          have hcont_proj' : projectb cont q (Trans.trans cont q) = true := by
            -- Specialize the IH to the delegatee role.
            simpa [hq] using hcont_proj
          have hrole_p' : (q == p) = false := by
            -- Convert role inequality into BEq for the delegatee.
            simpa [beq_eq_false_iff_ne, ne_eq] using hqp
          -- Reduce projectb to the continuation goal.
          calc
          projectb (GlobalType.delegate p q sid r cont) role
              (Trans.trans (GlobalType.delegate p q sid r cont) role)
              = projectb (GlobalType.delegate p q sid r cont) q
                  (Trans.trans (GlobalType.delegate p q sid r cont) q) := by
                      simp [hq]
          _ = projectb cont q (Trans.trans cont q) := by
                  simp [projectb, htrans, hrole_p', reduceBEq]
          _ = true := hcont_proj'
        · -- Non-participant case: role ≠ p, role ≠ q
          -- trans gives trans cont role, projectb does projectb cont role cand
          have hpne : (role == p) = false := by
            simpa [beq_eq_false_iff_ne, ne_eq] using hp
          have hqne : (role == q) = false := by
            simpa [beq_eq_false_iff_ne, ne_eq] using hq
          have htrans : Trans.trans (GlobalType.delegate p q sid r cont) role =
              Trans.trans cont role := by
            -- Compute the candidate projection for a non-participant.
            simp [Trans.trans, hpne, hqne]
          -- Reduce projectb to the continuation goal.
          calc
            projectb (GlobalType.delegate p q sid r cont) role
                (Trans.trans (GlobalType.delegate p q sid r cont) role)
                = projectb cont role (Trans.trans cont role) := by
                    -- Unfold only the LHS and pick the non-participant branch.
                    conv_lhs => unfold Choreography.Projection.Projectb.projectb
                    simp [hpne, hqne, htrans]
            _ = true := hcont_proj
termination_by g
decreasing_by
  all_goals
    first
    | exact sizeOf_body_lt_mu _ _
    | apply sizeOf_elem_snd_lt_comm; assumption
    | simp only [sizeOf, GlobalType._sizeOf_1]; omega

end

/-! ## wellFormed implies noSelfComm -/

/-- wellFormed implies noSelfComm. -/
theorem noSelfComm_of_wellFormed (g : GlobalType)
    (hwf : g.wellFormed = true) : g.noSelfComm = true := by
  -- wellFormed = allVarsBound && allCommsNonEmpty && noSelfComm && isProductive
  -- This is left-associative: ((allVarsBound && allCommsNonEmpty) && noSelfComm) && isProductive
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  exact hwf.1.2

/-! ## Final Theorems -/

/-- Wrapper: projectb succeeds on trans output for WellFormedBlind types. -/
theorem projectb_trans_of_wellFormedBlind (g : GlobalType) (role : String)
    (_hclosed : g.isClosed = true)
    (hwf : g.wellFormed = true)
    (hblind : isBlind g = true) :
    projectb g role (Trans.trans g role) = true :=
  projectb_trans_of_noSelfComm_blind g role (noSelfComm_of_wellFormed g hwf) hblind

/-- Projectable from WellFormedBlind: removes the extra postulate.

    If a global type is closed, well-formed, and blind, then it is projectable. -/
theorem projectable_of_wellFormedBlind (g : GlobalType)
    (h : WellFormedBlind g = true) :
    ∀ role, ∃ lt, CProject g role lt := by
  intro role
  -- WellFormedBlind g = g.isClosed && g.wellFormed && isBlind g
  simp only [WellFormedBlind, Bool.and_eq_true] at h
  -- h : (g.isClosed = true ∧ g.wellFormed = true) ∧ isBlind g = true
  have hclosed : g.isClosed = true := h.1.1
  have hwf : g.wellFormed = true := h.1.2
  have hblind : isBlind g = true := h.2
  use Trans.trans g role
  have hproj := projectb_trans_of_wellFormedBlind g role hclosed hwf hblind
  exact projectb_sound g role (Trans.trans g role) hproj


end Choreography.Projection.Blind
