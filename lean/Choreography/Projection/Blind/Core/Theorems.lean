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

/-! ## Communication Helpers: Sender -/

/-- Sender branch of the communication case. -/
private theorem projectb_trans_comm_sender_case
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (hs : role = sender)
    (hbranches_proj : ∀ p ∈ branches, projectb p.2 role (Trans.trans p.2 role) = true) :
    projectb (.comm sender receiver branches) role
      (Trans.trans (.comm sender receiver branches) role) = true := by
  have hproj_branches := projectbBranches_trans_of_all branches role hbranches_proj
  have hproj_branches' :
      projectbBranches branches sender (transBranches branches sender) = true := by
    simpa [hs] using hproj_branches
  have htrans' :
      Trans.trans (.comm sender receiver branches) sender =
        .send receiver (transBranches branches sender) := by
    simpa using trans_comm_sender sender receiver sender branches rfl
  simp [hs, htrans', projectb, hproj_branches']

/-! ## Communication Helpers: Receiver -/

/-- Receiver branch of the communication case. -/
private theorem projectb_trans_comm_receiver_case
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (hr : role = receiver) (hne_sr : sender ≠ receiver)
    (hbranches_proj : ∀ p ∈ branches, projectb p.2 role (Trans.trans p.2 role) = true) :
    projectb (.comm sender receiver branches) role
      (Trans.trans (.comm sender receiver branches) role) = true := by
  have hproj_branches := projectbBranches_trans_of_all branches role hbranches_proj
  have hproj_branches' :
      projectbBranches branches receiver (transBranches branches receiver) = true := by
    simpa [hr] using hproj_branches
  have hns : receiver ≠ sender := Ne.symm hne_sr
  have htrans' :
      Trans.trans (.comm sender receiver branches) receiver =
        .recv sender (transBranches branches receiver) := by
    simpa using trans_comm_receiver sender receiver receiver branches rfl hns
  simp [hr, hns, htrans', projectb, hproj_branches']

/-! ## Communication Helpers: Nonparticipant Cons -/

/-- Non-participant `cons` branch helper for communication case. -/
private theorem projectb_trans_comm_nonparticipant_cons
    (sender receiver role : String) (label : Label) (cont : GlobalType)
    (rest : List (Label × GlobalType))
    (hs : role ≠ sender) (hr : role ≠ receiver)
    (hblind_comm : commBlindFor sender receiver ((label, cont) :: rest) = true)
    (hbranches_proj : ∀ p ∈ ((label, cont) :: rest),
      projectb p.2 role (Trans.trans p.2 role) = true) :
    projectb (.comm sender receiver ((label, cont) :: rest)) role
      (Trans.trans (.comm sender receiver ((label, cont) :: rest)) role) = true := by
  have hne : (label, cont) :: rest ≠ [] := by simp
  have huniform :
      ∀ p ∈ ((label, cont) :: rest), Trans.trans p.2 role = Trans.trans cont role := by
    have huniform' := trans_uniform_for_nonparticipant (sender := sender) (receiver := receiver)
      (role := role) (branches := (label, cont) :: rest) hblind_comm hs hr hne
    intro p hp
    simpa using huniform' p hp
  have hproj_all := projectbAllBranches_trans_of_all_uniform ((label, cont) :: rest) role
    (Trans.trans cont role) huniform hbranches_proj
  have hbs : (role == sender) = false := by simpa using (beq_false_of_ne hs)
  have hbr : (role == receiver) = false := by simpa using (beq_false_of_ne hr)
  have htrans_comm :
      Trans.trans (.comm sender receiver ((label, cont) :: rest)) role =
        Trans.trans cont role := by
    simp [Trans.trans, hbs, hbr]
  have hproj_all' :
      projectbAllBranches ((label, cont) :: rest) role
        (Trans.trans (.comm sender receiver ((label, cont) :: rest)) role) = true := by
    simpa [htrans_comm] using hproj_all
  unfold projectb
  simp [hbs, hbr]
  exact hproj_all'

/-! ## Communication Helpers: Nonparticipant -/

/-- Non-participant branch of the communication case. -/
private theorem projectb_trans_comm_nonparticipant_case
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (hs : role ≠ sender) (hr : role ≠ receiver)
    (hblind_comm : commBlindFor sender receiver branches = true)
    (hbranches_proj : ∀ p ∈ branches, projectb p.2 role (Trans.trans p.2 role) = true) :
    projectb (.comm sender receiver branches) role
      (Trans.trans (.comm sender receiver branches) role) = true := by
  cases hbranches : branches with
  | nil =>
      simp [projectbAllBranches, projectb, Trans.trans, hs, hr]
  | cons head rest =>
      cases head with
      | mk label cont =>
          have hblind_comm' :
              commBlindFor sender receiver ((label, cont) :: rest) = true := by
            simpa [hbranches] using hblind_comm
          have hbranches_proj' : ∀ p ∈ ((label, cont) :: rest),
              projectb p.2 role (Trans.trans p.2 role) = true := by
            intro p hp
            exact hbranches_proj p (by simpa [hbranches] using hp)
          exact projectb_trans_comm_nonparticipant_cons sender receiver role label cont rest
            hs hr hblind_comm' hbranches_proj'

/-! ## Communication Helpers: Dispatcher -/

/-- Communication-case dispatcher. -/
private theorem projectb_trans_comm_case
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (hne_sr : sender ≠ receiver)
    (hblind_comm : commBlindFor sender receiver branches = true)
    (hbranches_proj : ∀ p ∈ branches, projectb p.2 role (Trans.trans p.2 role) = true) :
    projectb (.comm sender receiver branches) role
      (Trans.trans (.comm sender receiver branches) role) = true := by
  by_cases hs : role = sender
  · exact projectb_trans_comm_sender_case sender receiver role branches hs hbranches_proj
  · by_cases hr : role = receiver
    · exact projectb_trans_comm_receiver_case sender receiver role branches hr hne_sr hbranches_proj
    · exact projectb_trans_comm_nonparticipant_case sender receiver role branches hs hr hblind_comm hbranches_proj

/-! ## Delegate Helpers: Sender -/

/-- Delegator branch of the delegate case. -/
private theorem projectb_trans_delegate_sender_case
    (p q role r : String) (sid : Nat) (cont : GlobalType)
    (hp : role = p)
    (hcont_proj : projectb cont role (Trans.trans cont role) = true) :
    projectb (.delegate p q sid r cont) role
      (Trans.trans (.delegate p q sid r cont) role) = true := by
  have htrans : Trans.trans (.delegate p q sid r cont) p =
      .send q [(⟨"_delegate", .unit⟩, some (.chan sid r), Trans.trans cont p)] := by
    simp [Trans.trans]
  have hcont_proj' : projectb cont p (Trans.trans cont p) = true := by
    simpa [hp] using hcont_proj
  calc
    projectb (.delegate p q sid r cont) role (Trans.trans (.delegate p q sid r cont) role)
        = projectb (.delegate p q sid r cont) p (Trans.trans (.delegate p q sid r cont) p) := by
            simp [hp]
    _ = projectb cont p (Trans.trans cont p) := by
          simp [projectb, htrans, reduceBEq]
    _ = true := hcont_proj'

/-! ## Delegate Helpers: Receiver -/

/-- Delegatee branch of the delegate case. -/
private theorem projectb_trans_delegate_receiver_case
    (p q role r : String) (sid : Nat) (cont : GlobalType)
    (hp : role ≠ p) (hq : role = q)
    (hcont_proj : projectb cont role (Trans.trans cont role) = true) :
    projectb (.delegate p q sid r cont) role
      (Trans.trans (.delegate p q sid r cont) role) = true := by
  have hqp : q ≠ p := by
    intro hqp
    have hrole : role = p := by
      simp [hq, hqp]
    exact hp hrole
  have hqnep : (q == p) = false := by
    simpa [beq_eq_false_iff_ne, ne_eq] using hqp
  have htrans : Trans.trans (.delegate p q sid r cont) q =
      .recv p [(⟨"_delegate", .unit⟩, some (.chan sid r), Trans.trans cont q)] := by
    simp [Trans.trans, hqnep]
  have hcont_proj' : projectb cont q (Trans.trans cont q) = true := by
    simpa [hq] using hcont_proj
  calc
    projectb (.delegate p q sid r cont) role (Trans.trans (.delegate p q sid r cont) role)
        = projectb (.delegate p q sid r cont) q (Trans.trans (.delegate p q sid r cont) q) := by
            simp [hq]
    _ = projectb cont q (Trans.trans cont q) := by
          simp [projectb, htrans, hqnep, reduceBEq]
    _ = true := hcont_proj'

/-! ## Delegate Helpers: Nonparticipant -/

/-- Non-participant branch of the delegate case. -/
private theorem projectb_trans_delegate_nonparticipant_case
    (p q role r : String) (sid : Nat) (cont : GlobalType)
    (hp : role ≠ p) (hq : role ≠ q)
    (hcont_proj : projectb cont role (Trans.trans cont role) = true) :
    projectb (.delegate p q sid r cont) role
      (Trans.trans (.delegate p q sid r cont) role) = true := by
  have hpne : (role == p) = false := by
    simpa [beq_eq_false_iff_ne, ne_eq] using hp
  have hqne : (role == q) = false := by
    simpa [beq_eq_false_iff_ne, ne_eq] using hq
  have htrans : Trans.trans (.delegate p q sid r cont) role = Trans.trans cont role := by
    simp [Trans.trans, hpne, hqne]
  calc
    projectb (.delegate p q sid r cont) role (Trans.trans (.delegate p q sid r cont) role)
        = projectb cont role (Trans.trans cont role) := by
            conv_lhs => unfold Choreography.Projection.Projectb.projectb
            simp [hpne, hqne, htrans]
    _ = true := hcont_proj

/-! ## Delegate Helpers: Dispatcher -/

/-- Delegate-case dispatcher. -/
private theorem projectb_trans_delegate_case
    (p q role r : String) (sid : Nat) (cont : GlobalType)
    (hcont_proj : projectb cont role (Trans.trans cont role) = true) :
    projectb (.delegate p q sid r cont) role
      (Trans.trans (.delegate p q sid r cont) role) = true := by
  by_cases hp : role = p
  · exact projectb_trans_delegate_sender_case p q role r sid cont hp hcont_proj
  · by_cases hq : role = q
    · exact projectb_trans_delegate_receiver_case p q role r sid cont hp hq hcont_proj
    · exact projectb_trans_delegate_nonparticipant_case p q role r sid cont hp hq hcont_proj

/-! ## Main Theorem (Recursive Core) -/

/-- Core lemma: projectb succeeds on trans output when noSelfComm and isBlind hold.

    This is the heart of the proof - we only need noSelfComm (for comm cases)
    and isBlind (for non-participant uniformity). We don't need isClosed or
    the full wellFormed predicate. -/
theorem projectb_trans_of_noSelfComm_blind (g : GlobalType) (role : String)
    (hnoself : g.noSelfComm = true)
    (hblind : isBlind g = true) :
    projectb g role (Trans.trans g role) = true := by
  match g with
  -- Main theorem: end/var/mu cases.
  | .end =>
      -- end case: trivial
      simp only [Trans.trans, projectb]
  | .var t =>
      -- var case: projectb matches var with var (always true)
      simp only [Trans.trans, projectb, beq_self_eq_true]
  | .mu t body =>
      unfold Trans.trans
      have hnoself' := noSelfComm_mu_body hnoself
      have hblind' := isBlind_mu_body hblind
      by_cases hguard : (Trans.trans body role).isGuarded t
      · simpa [hguard, projectb, beq_self_eq_true] using
          projectb_trans_of_noSelfComm_blind body role hnoself' hblind'
      · simpa [hguard, projectb] using
          projectb_trans_of_noSelfComm_blind body role hnoself' hblind'
  | .comm sender receiver branches =>
      have hne_sr : sender ≠ receiver := by
        have hnoself' := hnoself
        simp only [GlobalType.noSelfComm, Bool.and_eq_true, bne_iff_ne, ne_eq] at hnoself'
        exact hnoself'.1
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
        exact projectb_trans_of_noSelfComm_blind p.2 role
          (hnoself_branches p hp) (hblind_branches p hp)
      exact projectb_trans_comm_case sender receiver role branches hne_sr hblind_comm hbranches_proj
  | .delegate p q sid r cont =>
      have hnoself_cont : cont.noSelfComm = true := noSelfComm_delegate_cont hnoself
      have hblind_cont : isBlind cont = true := by simpa [isBlind] using hblind
      have hcont_proj := projectb_trans_of_noSelfComm_blind cont role hnoself_cont hblind_cont
      exact projectb_trans_delegate_case p q role r sid cont hcont_proj
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
