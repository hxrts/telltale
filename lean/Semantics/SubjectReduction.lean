import Mathlib.Data.List.Basic
import Mathlib.Data.List.Forall2
import Semantics.Typing
import Semantics.EnvStep
import Choreography.Harmony
import SessionCoTypes.EQ2
import SessionCoTypes.EQ2Props
import SessionCoTypes.EQ2.HeadInversion


/-
The Problem. Show that typing is preserved by operational steps: when a
well-typed configuration steps, its resulting configuration remains well-typed.

Solution Structure. Define configurations and typing judgments, state the
subject-reduction claims as a bundle, then prove preservation of typing and
well-formedness, plus auxiliary EQ2 preservation facts for projections.
-/

/-! # Semantics.SubjectReduction

Subject reduction for V2.

## Overview

Subject reduction states that if a configuration is well-typed under a global type
and the configuration takes a step, then the resulting configuration is well-typed
under the stepped global type.

## Expose

The following definitions form the semantic interface for proofs:

- `Configuration`: a process configuration (global type + role processes)
- `WellTypedConfig`: typing judgment for configurations
- `ConfigStep`: global step plus per-process local advancement (`ProcessAdvance`)
- `step_preserves_typing`: subject reduction for head communication steps
- `Claims` (in `Semantics.SubjectReductionGeneral`): bundle of safety properties
-/

namespace Semantics.SubjectReduction

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Project
open Choreography.Projection.Project
open SessionCoTypes.EQ2
open Semantics.EnvStep
open Semantics.Typing
open Choreography.Harmony
open SessionCoTypes.EQ2.HeadInversion

/-! ## Configuration -/

/-- A process is abstracted as having a (representative) local type. -/
structure Process where
  -- Each process is identified by a role and its local type.
  role : String
  localType : LocalTypeR
  deriving Inhabited

/-- A configuration consists of a global type and a list of processes. -/
structure Configuration where
  -- A configuration records the global type and its processes.
  globalType : GlobalType
  processes : List Process
  deriving Inhabited

/-! ## Typing Judgment

Following the ECOOP 2025 Coq mechanization, we use a fixed role set S that contains
all roles of the global type. This handles the case where roles can shrink during
stepping (Remark 10 in the paper). -/

/-- A process is well-typed if its local type is well-formed and `EQ2`-equivalent
to the projection of the global type. Comparison is on representatives, restricted
to well-formed types where `EQ2` is an equivalence. -/
def Process.wellTyped (p : Process) (g : GlobalType) : Prop :=
  p.localType.WellFormed ∧ EQ2 p.localType (trans g p.role)

/-- A configuration is well-typed relative to a fixed role set S if:
    1. All processes are well-typed under the global type
    2. The roles of the global type are contained in the process roles (S)
    3. The processes form a well-formed environment with unique roles

This follows the Coq definition of coherent:
  coherent l := ∃ g S, coherentG g ∧ l = map (proj g) S ∧ uniq S ∧ subset (roles g) S -/
structure WellTypedConfig (c : Configuration) : Prop where
  -- Bundle the typing and role-side invariants.
  /-- Each process is typed by the projection of the global type. -/
  processes_typed : ∀ p ∈ c.processes, p.wellTyped c.globalType
  /-- Global type roles are contained in process roles. -/
  roles_contained : ∀ r ∈ c.globalType.roles, r ∈ c.processes.map Process.role
  /-- No duplicate roles in processes. -/
  roles_unique : (c.processes.map Process.role).Nodup

/-! ## Local Advancement

A participant's *own* local type advances: it is fully unfolded to its head
normal form, and the branch selected by the global action's label is taken
from that form. A non-participant's local type is left untouched. The
projection of the global type plays no role in the step. -/

/-- A role participates in `act` when it is the sender or the receiver. -/
def Participant (act : GlobalActionR) (role : String) : Prop :=
  role = act.sender ∨ role = act.receiver

instance (act : GlobalActionR) (role : String) : Decidable (Participant act role) := by
  unfold Participant; infer_instance

/-- Local advancement of `role` by the global action `act`, on the role's own
local type `lt`: the sender takes the `act.label` branch of the `send` that
`lt.fullUnfold` exposes, the receiver that of the exposed `recv`. -/
inductive LocalAdvance (act : GlobalActionR) (role : String) :
    LocalTypeR → LocalTypeR → Prop where
  | send {lt : LocalTypeR} {bs : List BranchR} {cont : LocalTypeR} :
      role = act.sender → lt.fullUnfold = .send act.receiver bs →
      (∃ vt, (act.label, vt, cont) ∈ bs) → LocalAdvance act role lt cont
  | recv {lt : LocalTypeR} {bs : List BranchR} {cont : LocalTypeR} :
      role = act.receiver → role ≠ act.sender → lt.fullUnfold = .recv act.sender bs →
      (∃ vt, (act.label, vt, cont) ∈ bs) → LocalAdvance act role lt cont

/-- How one process evolves across a configuration step. Participants advance
their own local type by the action (`LocalAdvance` on `p.localType`);
non-participants keep their local type verbatim. No projection is mentioned. -/
structure ProcessAdvance (act : GlobalActionR) (p p' : Process) : Prop where
  /-- The process keeps its role. -/
  role_eq : p'.role = p.role
  /-- Participants advance their own local type by the action. -/
  advance : Participant act p.role →
    ∃ lt, LocalAdvance act p.role p.localType lt ∧ p'.localType = lt
  /-- Non-participants are unchanged. -/
  frame : ¬ Participant act p.role → p'.localType = p.localType

/-! ## Configuration Stepping -/

/-- A configuration can step when the global type can step. -/
def Configuration.canStep (c : Configuration) (act : GlobalActionR) : Prop :=
  -- A configuration steps when its global type can step.
  SessionTypes.GlobalType.canStep c.globalType act

/-- Configuration stepping: the global type steps and each process evolves
locally (pointwise, in order) according to `ProcessAdvance`. -/
structure ConfigStep (c c' : Configuration) (act : GlobalActionR) : Prop where
  /-- The global type steps. -/
  global_step : step c.globalType act c'.globalType
  /-- Each process advances locally by the action. -/
  processes_advance :
    List.Forall₂ (ProcessAdvance act) c.processes c'.processes

/-! ## List Helpers -/

/-- Pointwise process advancement preserves the role list. -/
theorem forall2_roles {act : GlobalActionR} :
    ∀ {ps ps' : List Process}, List.Forall₂ (ProcessAdvance act) ps ps' →
      ps.map Process.role = ps'.map Process.role
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
      simp [h.role_eq, forall2_roles hs]

/-- Every target process has a source process related by advancement. -/
theorem forall2_exists_left {act : GlobalActionR} :
    ∀ {ps ps' : List Process}, List.Forall₂ (ProcessAdvance act) ps ps' →
      ∀ p' ∈ ps', ∃ p ∈ ps, ProcessAdvance act p p'
  | [], [], .nil => by simp
  | p :: _, _ :: _, .cons h hs => by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨p, List.mem_cons_self, h⟩
      · obtain ⟨r, hr, hr'⟩ := forall2_exists_left hs q hq
        exact ⟨r, List.mem_cons_of_mem _ hr, hr'⟩

/-! ## Head-Step Inversion -/

/-- A step of a communication whose head matches the action takes a branch. -/
theorem head_step_mem {s r : String} {bs : List (Label × GlobalType)}
    {act : GlobalActionR} {g' : GlobalType}
    (h : step (.comm s r bs) act g') (hs : act.sender = s) (hr : act.receiver = r) :
    (act.label, g') ∈ bs := by
  cases h with
  | comm_head _ _ _ _ _ hmem => exact hmem
  | comm_async _ _ _ _ _ _ _ _ hcond _ _ _ => exact absurd hr (hcond hs)

/-- Membership in projected branches comes from a global branch. -/
theorem mem_transBranches_inv {role : String} {label : Label}
    {vt : Option SessionTypes.ValType} {cont : LocalTypeR} :
    ∀ {bs : List (Label × GlobalType)}, (label, vt, cont) ∈ transBranches bs role →
      ∃ g0, (label, g0) ∈ bs ∧ cont = trans g0 role
  | [], h => by simp [transBranches, Choreography.Projection.Trans.transBranches] at h
  | (l, g0) :: rest, h => by
      have h' : (label, vt, cont) = (l, none, trans g0 role) ∨
          (label, vt, cont) ∈ transBranches rest role := by
        simpa [transBranches, Choreography.Projection.Trans.transBranches] using h
      rcases h' with h' | h'
      · simp only [Prod.mk.injEq] at h'
        exact ⟨g0, by simp [h'.1], h'.2.2⟩
      · obtain ⟨g1, hm, he⟩ := mem_transBranches_inv h'
        exact ⟨g1, List.mem_cons_of_mem _ hm, he⟩

/-! ## Head-Step Hypotheses -/

/-- Hypotheses under which the head-step subject reduction theorem is proved. -/
structure HeadStepHyps (c : Configuration) (act : GlobalActionR) : Prop where
  /-- The global type is a communication whose head is `act`. -/
  head : ∃ bs, c.globalType = .comm act.sender act.receiver bs
  /-- Branch labels are unique (so the label picks one continuation). -/
  unique : c.globalType.uniqueBranchLabels = true
  /-- The global type is closed. -/
  closed : c.globalType.isClosed = true
  /-- The global type is well-formed. -/
  wf : c.globalType.wellFormed = true
  /-- The global type is blind (needed for non-participant coherence). -/
  blind : Choreography.Projection.Blind.isBlind c.globalType = true

/-! ## Type Preservation Lemmas -/

/-- Non-participants have unchanged types (up to EQ2) after a step.

**Note:** Requires g to be closed/wellFormed and blind. -/
theorem other_type_preserved (g g' : GlobalType) (act : GlobalActionR) (role : String)
    (hstep : step g act g')
    (hclosed : g.isClosed = true)
    (hwf : g.wellFormed = true)
    (hns : role ≠ act.sender) (hnr : role ≠ act.receiver)
    (hblind : Choreography.Projection.Blind.isBlind g = true)
    : EQ2 (trans g' role) (trans g role) := by
  -- Delegate to the projection harmony lemma for non-participants.
  exact proj_trans_other_step g g' act role hstep hclosed hwf hns hnr hblind

/-- Sender harmony for head steps: the sender's projection of `g` advances by
the send action to (exactly) its projection of `g'`. -/
theorem sender_type_after_step {bs : List (Label × GlobalType)} {g' : GlobalType}
    {act : GlobalActionR} (hstep : step (.comm act.sender act.receiver bs) act g') :
    LocalAdvance act act.sender (trans (.comm act.sender act.receiver bs) act.sender)
      (trans g' act.sender) := by
  rw [trans_comm_sender _ _ _ bs rfl]
  exact .send rfl rfl ⟨none, mem_trans_branches_of_mem bs _ g' _ (head_step_mem hstep rfl rfl)⟩

/-- Receiver harmony for head steps (no self-communication): the receiver's
projection of `g` advances by the receive action to its projection of `g'`. -/
theorem receiver_type_after_step {bs : List (Label × GlobalType)} {g' : GlobalType}
    {act : GlobalActionR} (hne : act.receiver ≠ act.sender)
    (hstep : step (.comm act.sender act.receiver bs) act g') :
    LocalAdvance act act.receiver (trans (.comm act.sender act.receiver bs) act.receiver)
      (trans g' act.receiver) := by
  rw [trans_comm_receiver _ _ _ bs rfl hne]
  exact .recv rfl hne rfl
    ⟨none, mem_trans_branches_of_mem bs _ g' _ (head_step_mem hstep rfl rfl)⟩

/-! ## Subject Reduction -/

/-- The stepped global type of a configuration step is well-formed. -/
theorem stepped_trans_wf {c c' : Configuration} {act : GlobalActionR}
    (hh : HeadStepHyps c act) (hstep : ConfigStep c c' act) (role : String) :
    (trans c'.globalType role).WellFormed :=
  trans_well_formed_of_well_formed _ role
    (step_preserves_well_formed _ _ act hstep.global_step hh.wf)

/-- Branch labels of a head communication satisfying `HeadStepHyps` are unique. -/
theorem head_labels_nodup {c : Configuration} {act : GlobalActionR}
    {bs : List (Label × GlobalType)} (hh : HeadStepHyps c act)
    (hg : c.globalType = .comm act.sender act.receiver bs) : (branchLabels bs).Nodup := by
  have hu := hh.unique
  rw [hg] at hu
  simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true, decide_eq_true_eq] at hu
  exact hu.1

/-- A typed sender's own type exposes, after full unfolding, a `send` to the
receiver whose branches are pairwise `EQ2` to the projected branches. -/
theorem own_head_send {p : Process} {act : GlobalActionR} {bs : List (Label × GlobalType)}
    (ht : p.wellTyped (.comm act.sender act.receiver bs))
    (hwf : (trans (.comm act.sender act.receiver bs) p.role).WellFormed)
    (hs : p.role = act.sender) :
    ∃ as, p.localType.fullUnfold = .send act.receiver as ∧
      BranchesRel EQ2 as (transBranches bs p.role) := by
  have he := trans_comm_sender _ act.receiver _ bs hs
  exact eq2_full_unfold_send_inv ht.1 hwf ht.2 (by rw [he]; rfl)

/-- A typed receiver's own type exposes, after full unfolding, a `recv` from the
sender whose branches are pairwise `EQ2` to the projected branches. -/
theorem own_head_recv {p : Process} {act : GlobalActionR} {bs : List (Label × GlobalType)}
    (ht : p.wellTyped (.comm act.sender act.receiver bs))
    (hwf : (trans (.comm act.sender act.receiver bs) p.role).WellFormed)
    (hr : p.role = act.receiver) (hs : p.role ≠ act.sender) :
    ∃ as, p.localType.fullUnfold = .recv act.sender as ∧
      BranchesRel EQ2 as (transBranches bs p.role) := by
  have he := trans_comm_receiver act.sender _ _ bs hr hs
  exact eq2_full_unfold_recv_inv ht.1 hwf ht.2 (by rw [he]; rfl)

/-- A branch of the process's own type carrying the stepped label is
well-formed and `EQ2` to the projection of the stepped global continuation. -/
theorem own_cont_typed {role : String} {as : List BranchR} {bs : List (Label × GlobalType)}
    {label : Label} {vt : Option SessionTypes.ValType} {cont : LocalTypeR} {g' : GlobalType}
    (hWFas : ∀ lb ∈ as, lb.2.2.WellFormed) (hrel : BranchesRel EQ2 as (transBranches bs role))
    (hm : (label, vt, cont) ∈ as) (huniq : (branchLabels bs).Nodup)
    (hg' : (label, g') ∈ bs) : cont.WellFormed ∧ EQ2 cont (trans g' role) := by
  obtain ⟨y, hy, hl, -, hE⟩ := branches_rel_mem_left hrel hm
  obtain ⟨g0, hg0, hy2⟩ := mem_transBranches_inv (label := y.1) (vt := y.2.1) hy
  rw [← hl] at hg0
  rw [mem_branch_unique_label huniq hg0 hg'] at hy2
  exact ⟨hWFas _ hm, hy2 ▸ hE⟩

/-- Core of participant preservation: the own-type continuation chosen by
`LocalAdvance` is well-formed and `EQ2` to the projection of `g'`. -/
theorem local_advance_typed {p : Process} {act : GlobalActionR}
    {bs : List (Label × GlobalType)} {lt : LocalTypeR} {gc : GlobalType}
    (ht : p.wellTyped (.comm act.sender act.receiver bs))
    (hwf : (trans (.comm act.sender act.receiver bs) p.role).WellFormed)
    (huniq : (branchLabels bs).Nodup) (hg' : (act.label, gc) ∈ bs)
    (hadv : LocalAdvance act p.role p.localType lt) :
    lt.WellFormed ∧ EQ2 lt (trans gc p.role) := by
  cases hadv with
  | send hs hfu hm =>
      obtain ⟨vt, hm⟩ := hm
      obtain ⟨as, has, hrel⟩ := own_head_send ht hwf hs
      rw [hfu] at has; cases has
      exact own_cont_typed (wf_cont_of_full_unfold_send ht.1 hfu) hrel hm huniq hg'
  | recv hr hs hfu hm =>
      obtain ⟨vt, hm⟩ := hm
      obtain ⟨as, has, hrel⟩ := own_head_recv ht hwf hr hs
      rw [hfu] at has; cases has
      exact own_cont_typed (wf_cont_of_full_unfold_recv ht.1 hfu) hrel hm huniq hg'

/-- A participant's advanced own type is well-typed under the stepped global
type: it is `EQ2` to the projection of the stepped global type. -/
theorem participant_typed {c c' : Configuration} {act : GlobalActionR}
    (htyped : WellTypedConfig c) (hh : HeadStepHyps c act) (hstep : ConfigStep c c' act)
    {p p' : Process} (hpm : p ∈ c.processes)
    (hadv : ProcessAdvance act p p') (hp : Participant act p.role) :
    p'.wellTyped c'.globalType := by
  obtain ⟨bs, hg⟩ := hh.head
  obtain ⟨lt, hlt, hpl⟩ := hadv.advance hp
  have ht := htyped.processes_typed p hpm
  have hwf := trans_well_formed_of_well_formed _ p.role hh.wf
  have hstep' := hstep.global_step
  rw [hg] at ht hwf hstep'
  have h := local_advance_typed ht hwf (head_labels_nodup hh hg)
    (head_step_mem hstep' rfl rfl) hlt
  rw [Process.wellTyped, hpl, hadv.role_eq]
  exact h

/-- A non-participant's unchanged type is still `EQ2` to the projection of the
stepped global type (via `other_type_preserved` and `eq2_trans_wf`). -/
theorem nonparticipant_typed {c c' : Configuration} {act : GlobalActionR}
    (htyped : WellTypedConfig c) (hh : HeadStepHyps c act) (hstep : ConfigStep c c' act)
    {p p' : Process} (hpm : p ∈ c.processes)
    (hadv : ProcessAdvance act p p') (hp : ¬ Participant act p.role) :
    p'.wellTyped c'.globalType := by
  have hns : p.role ≠ act.sender := fun h => hp (Or.inl h)
  have hnr : p.role ≠ act.receiver := fun h => hp (Or.inr h)
  have hE := other_type_preserved _ _ act p.role hstep.global_step hh.closed hh.wf hns hnr
    hh.blind
  obtain ⟨hwfp, hEp⟩ := htyped.processes_typed p hpm
  rw [Process.wellTyped, hadv.frame hp, hadv.role_eq]
  exact ⟨hwfp, SessionCoTypes.EQ2Props.eq2_trans_wf hEp (eq2_symm hE) hwfp
    (trans_well_formed_of_well_formed _ _ hh.wf) (stepped_trans_wf hh hstep _)⟩

/-- Subject reduction for head communication steps: a well-typed configuration
whose global type is a communication headed by `act` steps (with each process
advancing locally per `ProcessAdvance`) to a well-typed configuration.

This is the head-step corollary; `step_preserves_typing_general`
(`Semantics.SubjectReductionGeneral`) covers every `step` (including `mu` and
`comm_async`) without the head-shape premise. -/
theorem step_preserves_typing {c c' : Configuration} {act : GlobalActionR}
    (htyped : WellTypedConfig c) (hh : HeadStepHyps c act)
    (hstep : ConfigStep c c' act) :
    WellTypedConfig c' where
  processes_typed := by
    intro p' hp'
    obtain ⟨p, hpm, hadv⟩ := forall2_exists_left hstep.processes_advance p' hp'
    by_cases hp : Participant act p.role
    · exact participant_typed htyped hh hstep hpm hadv hp
    · exact nonparticipant_typed htyped hh hstep hpm hadv hp
  roles_contained := by
    intro r hr
    have hroles := step_roles_subset c.globalType c'.globalType act hstep.global_step r hr
    rw [← forall2_roles hstep.processes_advance]
    exact htyped.roles_contained r hroles
  roles_unique := by
    rw [← forall2_roles hstep.processes_advance]
    exact htyped.roles_unique

/-- The projected environment of any global type is well-formed (its domain is
`g.roles`, which is duplicate-free). This holds unconditionally. -/
theorem projEnv_wellformed (g : GlobalType) : WellFormedEnv (projEnv g) := by
  constructor
  rw [proj_env_dom]
  exact GlobalType.roles_nodup _

/-! ## Payload matching

`BranchesRel` compares the `Option ValType` delegation payload of each branch,
so `Process.wellTyped` forces the process's own branches to carry exactly the
payloads of the projection (`none` for plain communications, `some (.chan ..)`
for delegation). -/

/-- Label/payload agreement between a well-typed process's `send` head and the
projection's `send` head (the projection is well-formed, e.g. by
`trans_well_formed_of_well_formed`). -/
theorem wellTyped_payload_agree_send {p : Process} {g : GlobalType} {q : String}
    {bs cs : List BranchR} (ht : p.wellTyped g) (hwf : (trans g p.role).WellFormed)
    (hp : p.localType.fullUnfold = .send q bs) (hg : (trans g p.role).fullUnfold = .send q cs) :
    List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2.1 = b.2.1) bs cs := by
  obtain ⟨as, has, hrel⟩ := eq2_full_unfold_send_inv ht.1 hwf ht.2 hg
  rw [hp] at has
  cases has
  exact hrel.payload_eq

/-- Label/payload agreement between a well-typed process's `recv` head and the
projection's `recv` head. -/
theorem wellTyped_payload_agree_recv {p : Process} {g : GlobalType} {q : String}
    {bs cs : List BranchR} (ht : p.wellTyped g) (hwf : (trans g p.role).WellFormed)
    (hp : p.localType.fullUnfold = .recv q bs) (hg : (trans g p.role).fullUnfold = .recv q cs) :
    List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2.1 = b.2.1) bs cs := by
  obtain ⟨as, has, hrel⟩ := eq2_full_unfold_recv_inv ht.1 hwf ht.2 hg
  rw [hp] at has
  cases has
  exact hrel.payload_eq

/-- Negative example: a process whose single `send` branch carries a spurious
`some ValType.nat` payload is not well-typed against the plain communication
`a → b : m`, whose projection carries payload `none`. -/
theorem payload_mismatch_not_wellTyped :
    ¬ Process.wellTyped
      ⟨"a", .send "b" [(⟨"m", .unit⟩, some SessionTypes.ValType.nat, .end)]⟩
      (.comm "a" "b" [(⟨"m", .unit⟩, .end)]) := by
  intro ht
  have h := ht.2
  simp only [trans_comm_sender "a" "b" "a" _ rfl, transBranches,
    Choreography.Projection.Trans.transBranches] at h
  have hf := EQ2.destruct h
  simp [EQ2F, BranchesRel] at hf

/-- Hence no configuration whose process list contains the mismatched process
is well-typed. -/
theorem payload_mismatch_not_wellTypedConfig (ps : List Process)
    (hmem : (⟨"a", .send "b" [(⟨"m", .unit⟩, some SessionTypes.ValType.nat, .end)]⟩ : Process)
      ∈ ps) :
    ¬ WellTypedConfig ⟨.comm "a" "b" [(⟨"m", .unit⟩, .end)], ps⟩ :=
  fun hc => payload_mismatch_not_wellTyped (hc.processes_typed _ hmem)

end Semantics.SubjectReduction
