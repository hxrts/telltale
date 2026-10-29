import Mathlib.Data.List.Basic
import Mathlib.Data.List.Forall2
import Semantics.Typing
import Semantics.EnvStep
import Choreography.Harmony
import SessionCoTypes.EQ2


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
- `Claims`: bundle of safety properties
-/

namespace Semantics.SubjectReduction

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Project
open Choreography.Projection.Project
open SessionCoTypes.EQ2
open SessionCoTypes.Quotient
open Semantics.EnvStep
open Semantics.Typing
open Choreography.Harmony

/-! ## Configuration -/

/-- A process is abstracted as having a local type. -/
structure Process where
  -- Each process is identified by a role and its local type.
  role : String
  localType : QLocalTypeR
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

/-- A process is well-typed if its local type matches the projection of the global type. -/
def Process.wellTyped (p : Process) (g : GlobalType) : Prop :=
  -- Typing means the local type matches the projection of the global type.
  p.localType = QLocalTypeR.ofLocal (trans g p.role)

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

A participant's local type advances by consuming the branch selected by the
global action; a non-participant's local type is left untouched. -/

/-- A role participates in `act` when it is the sender or the receiver. -/
def Participant (act : GlobalActionR) (role : String) : Prop :=
  role = act.sender ∨ role = act.receiver

instance (act : GlobalActionR) (role : String) : Decidable (Participant act role) := by
  unfold Participant; infer_instance

/-- Local advancement of `role` by the global action `act`: the sender consumes
the `act.label` branch of its `send`, the receiver that of its `recv`. -/
inductive LocalAdvance (act : GlobalActionR) (role : String) :
    LocalTypeR → LocalTypeR → Prop where
  | send {bs : List BranchR} {cont : LocalTypeR} :
      role = act.sender → (∃ vt, (act.label, vt, cont) ∈ bs) →
      LocalAdvance act role (.send act.receiver bs) cont
  | recv {bs : List BranchR} {cont : LocalTypeR} :
      role = act.receiver → role ≠ act.sender → (∃ vt, (act.label, vt, cont) ∈ bs) →
      LocalAdvance act role (.recv act.sender bs) cont

/-- How one process evolves across a configuration step. Participants advance
their (old) projected local type by the action; non-participants keep their
local type verbatim. Nothing here mentions the projection of the new global type. -/
structure ProcessAdvance (g : GlobalType) (act : GlobalActionR) (p p' : Process) : Prop where
  /-- The process keeps its role. -/
  role_eq : p'.role = p.role
  /-- Participants advance their old local type by the action. -/
  advance : Participant act p.role →
    ∃ lt, LocalAdvance act p.role (trans g p.role) lt ∧ p'.localType = QLocalTypeR.ofLocal lt
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
    List.Forall₂ (ProcessAdvance c.globalType act) c.processes c'.processes

/-! ## List Helpers -/

/-- Pointwise process advancement preserves the role list. -/
theorem forall2_roles {g : GlobalType} {act : GlobalActionR} :
    ∀ {ps ps' : List Process}, List.Forall₂ (ProcessAdvance g act) ps ps' →
      ps.map Process.role = ps'.map Process.role
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
      simp [h.role_eq, forall2_roles hs]

/-- Every target process has a source process related by advancement. -/
theorem forall2_exists_left {g : GlobalType} {act : GlobalActionR} :
    ∀ {ps ps' : List Process}, List.Forall₂ (ProcessAdvance g act) ps ps' →
      ∀ p' ∈ ps', ∃ p ∈ ps, ProcessAdvance g act p p'
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

/-- A participant of a head communication projects to a send/recv over the
projected branches. -/
theorem trans_head_participant (s r role : String) (bs : List (Label × GlobalType))
    (hp : role = s ∨ role = r) :
    trans (.comm s r bs) role = .send r (transBranches bs role) ∨
      trans (.comm s r bs) role = .recv s (transBranches bs role) := by
  by_cases hs : role = s
  · exact Or.inl (trans_comm_sender s r role bs hs)
  · exact Or.inr (trans_comm_receiver s r role bs (hp.resolve_left hs) hs)

/-- The advanced type of a head participant is the projection of a branch
carrying the action label. -/
theorem local_advance_head_inv {s r role : String} {bs : List (Label × GlobalType)}
    {act : GlobalActionR} {lt : LocalTypeR} (hp : role = s ∨ role = r)
    (h : LocalAdvance act role (trans (.comm s r bs) role) lt) :
    ∃ g0, (act.label, g0) ∈ bs ∧ lt = trans g0 role := by
  rcases trans_head_participant s r role bs hp with he | he <;> rw [he] at h <;>
    cases h <;> rename_i hm <;> obtain ⟨vt, hm⟩ := hm <;> exact mem_transBranches_inv hm

/-! ## Claims -/

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

/-- Claims bundle for subject reduction. -/
structure Claims where
  /-- Subject reduction for head communication steps. -/
  subject_reduction : ∀ c c' act, WellTypedConfig c → HeadStepHyps c act →
      ConfigStep c c' act → WellTypedConfig c'
  /-- Projected environments are always well-formed. -/
  projEnv_wellformed : ∀ g, WellFormedEnv (projEnv g)

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
  exact .send rfl ⟨none, mem_trans_branches_of_mem bs _ g' _ (head_step_mem hstep rfl rfl)⟩

/-- Receiver harmony for head steps (no self-communication): the receiver's
projection of `g` advances by the receive action to its projection of `g'`. -/
theorem receiver_type_after_step {bs : List (Label × GlobalType)} {g' : GlobalType}
    {act : GlobalActionR} (hne : act.receiver ≠ act.sender)
    (hstep : step (.comm act.sender act.receiver bs) act g') :
    LocalAdvance act act.receiver (trans (.comm act.sender act.receiver bs) act.receiver)
      (trans g' act.receiver) := by
  rw [trans_comm_receiver _ _ _ bs rfl hne]
  exact .recv rfl hne
    ⟨none, mem_trans_branches_of_mem bs _ g' _ (head_step_mem hstep rfl rfl)⟩

/-! ## Subject Reduction -/

/-- A participant's advanced type is the projection of the stepped global type. -/
theorem participant_typed {c c' : Configuration} {act : GlobalActionR}
    (hh : HeadStepHyps c act) (hstep : ConfigStep c c' act) {p p' : Process}
    (hadv : ProcessAdvance c.globalType act p p') (hp : Participant act p.role) :
    p'.wellTyped c'.globalType := by
  obtain ⟨bs, hg⟩ := hh.head
  obtain ⟨lt, hlt, hpl⟩ := hadv.advance hp
  rw [hg] at hlt
  obtain ⟨g0, hm, rfl⟩ := local_advance_head_inv hp hlt
  have hstep' := hstep.global_step
  rw [hg] at hstep'
  have huniq : (branchLabels bs).Nodup := by
    have hu := hh.unique
    rw [hg] at hu
    simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true, decide_eq_true_eq] at hu
    exact hu.1
  have heq := mem_branch_unique_label huniq hm (head_step_mem hstep' rfl rfl)
  simp [Process.wellTyped, hpl, hadv.role_eq, heq]

/-- A non-participant's unchanged type is still the projection of the stepped
global type (via `other_type_preserved`). -/
theorem nonparticipant_typed {c c' : Configuration} {act : GlobalActionR}
    (htyped : WellTypedConfig c) (hh : HeadStepHyps c act) (hstep : ConfigStep c c' act)
    {p p' : Process} (hpm : p ∈ c.processes)
    (hadv : ProcessAdvance c.globalType act p p') (hp : ¬ Participant act p.role) :
    p'.wellTyped c'.globalType := by
  have hns : p.role ≠ act.sender := fun h => hp (Or.inl h)
  have hnr : p.role ≠ act.receiver := fun h => hp (Or.inr h)
  have hE := other_type_preserved _ _ act p.role hstep.global_step hh.closed hh.wf hns hnr
    hh.blind
  have hq : QLocalTypeR.ofLocal (trans c.globalType p.role) =
      QLocalTypeR.ofLocal (trans c'.globalType p.role) := Quot.sound (eq2_symm hE)
  simp only [Process.wellTyped, hadv.frame hp, hadv.role_eq]
  exact (htyped.processes_typed p hpm).trans hq

/-- Subject reduction for head communication steps: a well-typed configuration
whose global type is a communication headed by `act` steps (with each process
advancing locally per `ProcessAdvance`) to a well-typed configuration.

Async (`comm_async`) and `mu`-headed steps are not covered: there the local
types are related to the stepped projection only up to EQ2 through unfolding. -/
theorem step_preserves_typing {c c' : Configuration} {act : GlobalActionR}
    (htyped : WellTypedConfig c) (hh : HeadStepHyps c act)
    (hstep : ConfigStep c c' act) :
    WellTypedConfig c' where
  processes_typed := by
    intro p' hp'
    obtain ⟨p, hpm, hadv⟩ := forall2_exists_left hstep.processes_advance p' hp'
    by_cases hp : Participant act p.role
    · exact participant_typed hh hstep hadv hp
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

/-- Build the claims bundle from proven theorems. -/
def claims : Claims where
  subject_reduction := fun _ _ _ h1 h2 h3 => step_preserves_typing h1 h2 h3
  projEnv_wellformed := projEnv_wellformed

end Semantics.SubjectReduction
