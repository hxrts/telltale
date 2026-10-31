import Semantics.SubjectReduction

/-
The Problem. `step_preserves_typing` needs the global type to be literally a
communication headed by the stepped action. Global `step` also unfolds `mu`
binders and performs asynchronous (`comm_async`) steps under unrelated prefixes.

Solution Structure.
1. `trans_mu_unfold_eq2`: projection of a `mu`-unfolding is `EQ2` to the
   projection of the `mu` (reusing `trans_substitute_unfold`).
2. `participant_step_typed`: by the `step` recursor, a typed participant's own
   advance is typed by the projection of the stepped type. The `mu` case
   transports typing through (1); the `comm_async` case either recurses into the
   first branch (participant outside the prefix) or is contradictory.
3. `step_preserves_typing_general`: subject reduction for every `ConfigStep`.
-/

/-! # Semantics.SubjectReductionGeneral

Subject reduction for arbitrary global steps (`comm_head`, `comm_async`, `mu`).

## Asynchronous steps

`ConfigStep` asks every participant to advance by `LocalAdvance`, i.e. by the
head of its own fully unfolded type. For an async step of `comm s r bs` whose
action shares a role with `{s, r}`, that role's head is the prefix action, not
the stepped one, so no `ConfigStep` exists (`async_overlap_not_participant`).
Preservation therefore holds for *all* configuration steps with no fragment
side condition; the overlapping async global steps are simply not realizable
at the configuration level. Concretely, for
`g = comm a b [(l, comm a c [(m, end)])]` (`c ≠ b`),
`step g (a → c : m) (comm a b [(l, end)])` holds, but `a`'s type unfolds to
`send b …`, so `a` cannot advance (`async_counterexample_no_advance`). Async
steps whose action avoids the prefix roles (e.g. `c → d` under `a → b`) are
realized and preserved.

## Main Results

- `trans_mu_unfold_eq2`, `wellTyped_mu_unfold`
- `participant_step_typed`
- `StepHyps`, `step_preserves_typing_general`
- `Claims`, `claims`
-/

namespace Semantics.SubjectReduction

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Project
open SessionCoTypes.EQ2
open SessionCoTypes.EQ2.HeadInversion
open Choreography.Harmony
open Semantics.EnvStep
open Semantics.Typing

/-! ## Projection of a `mu`-Unfolding -/

/-- Projection of the one-step unfolding of a well-formed `mu t body` is `EQ2`
to the projection of `mu t body` itself. -/
theorem trans_mu_unfold_eq2 (t : String) (body : GlobalType) (role : String)
    (hwf : (GlobalType.mu t body).wellFormed = true) :
    EQ2 (trans (body.substitute t (.mu t body)) role) (trans (.mu t body) role) := by
  have hclosed := GlobalType.is_closed_of_well_formed _ hwf
  have h1 := trans_substitute_unfold t body role hclosed
  have hwfm := trans_well_formed_of_well_formed _ role hwf
  have h2 : EQ2 (trans (.mu t body) role).unfold (trans (.mu t body) role) :=
    eq2_unfold_left (eq2_refl _)
  exact SessionCoTypes.EQ2Props.eq2_trans_wf h1 h2
    (trans_well_formed_of_well_formed _ role (well_formed_mu_unfold t body hwf))
    hwfm.unfold hwfm

/-- Typing against a well-formed `mu` transfers to its unfolding. -/
theorem wellTyped_mu_unfold {lt : LocalTypeR} {t : String} {body : GlobalType}
    {role : String} (hwf : (GlobalType.mu t body).wellFormed = true)
    (hlwf : lt.WellFormed) (hE : EQ2 lt (trans (.mu t body) role)) :
    EQ2 lt (trans (body.substitute t (.mu t body)) role) :=
  SessionCoTypes.EQ2Props.eq2_trans_wf hE (eq2_symm (trans_mu_unfold_eq2 t body role hwf))
    hlwf (trans_well_formed_of_well_formed _ role hwf)
    (trans_well_formed_of_well_formed _ role (well_formed_mu_unfold t body hwf))

/-! ## Async Participants -/

/-- Well-formed communications have distinct endpoints. -/
theorem comm_receiver_ne_sender {s r : String} {bs : List (Label × GlobalType)}
    (hwf : (GlobalType.comm s r bs).wellFormed = true) : r ≠ s := by
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  have hno := hwf.1.2
  simp [GlobalType.noSelfComm] at hno
  intro h; exact hno.1 h.symm

/-- A role that can advance by an async action of `comm s r bs` (one that is not
the head action) is neither `s` nor `r`: their heads expose the prefix. -/
theorem async_overlap_not_participant {s r role : String} {bs : List (Label × GlobalType)}
    {act : GlobalActionR} {lt lt' : LocalTypeR}
    (hns : act.sender ≠ r) (hcond : act.sender = s → act.receiver ≠ r)
    (hwf : (GlobalType.comm s r bs).wellFormed = true) (hlwf : lt.WellFormed)
    (hE : EQ2 lt (trans (.comm s r bs) role)) (hadv : LocalAdvance act role lt lt') :
    role ≠ s ∧ role ≠ r := by
  have hwfT := trans_well_formed_of_well_formed _ role hwf
  have hrs := comm_receiver_ne_sender hwf
  refine ⟨fun hs => ?_, fun hr => ?_⟩
  · obtain ⟨as, has, -⟩ := eq2_full_unfold_send_inv hlwf hwfT hE
      (by rw [trans_comm_sender s r role bs hs]; rfl)
    cases hadv with
    | send hrole hfu _ =>
        rw [hfu] at has; cases has
        exact hcond (hrole ▸ hs) rfl
    | recv _ _ hfu _ => rw [hfu] at has; cases has
  · obtain ⟨as, has, -⟩ := eq2_full_unfold_recv_inv hlwf hwfT hE
      (by rw [trans_comm_receiver s r role bs hr (hr ▸ hrs)]; rfl)
    cases hadv with
    | send hrole _ _ => exact hns (hrole ▸ hr)
    | recv hrole _ hfu _ =>
        rw [hfu] at has; cases has
        exact hcond rfl (hrole ▸ hr)

/-! ## Participant Preservation -/

/-- Motive: a typed participant's own advance is typed by the stepped type. -/
def PartMotive (g : GlobalType) (act : GlobalActionR) (g' : GlobalType) : Prop :=
  g.wellFormed = true → g.uniqueBranchLabels = true →
  ∀ role lt lt', lt.WellFormed → EQ2 lt (trans g role) →
    LocalAdvance act role lt lt' → lt'.WellFormed ∧ EQ2 lt' (trans g' role)

/-- Branch motive: the head branch's step satisfies `PartMotive`. -/
def PartBranchMotive (bs : List (Label × GlobalType)) (act : GlobalActionR)
    (bs' : List (Label × GlobalType)) : Prop :=
  ∀ l g, bs.head? = some (l, g) → ∃ g', bs'.head? = some (l, g') ∧ PartMotive g act g'

/-- Head case of the participant motive. -/
theorem part_motive_head (s r : String) (bs : List (Label × GlobalType)) (label : Label)
    (cont : GlobalType) (hmem : (label, cont) ∈ bs) :
    PartMotive (.comm s r bs) ⟨s, r, label⟩ cont := by
  intro hwf huniq role lt lt' hlwf hE hadv
  have hnd : (branchLabels bs).Nodup := by
    simp only [GlobalType.uniqueBranchLabels, Bool.and_eq_true, decide_eq_true_eq] at huniq
    exact huniq.1
  exact local_advance_typed (act := ⟨s, r, label⟩) (p := ⟨role, lt⟩) ⟨hlwf, hE⟩
    (trans_well_formed_of_well_formed _ role hwf) hnd hmem hadv

/-- Async case of the participant motive: recurse into the first branch. -/
theorem part_motive_async (s r : String) (bs bs' : List (Label × GlobalType))
    (act : GlobalActionR) (hns : act.sender ≠ r) (hcond : act.sender = s → act.receiver ≠ r)
    (hne : bs ≠ []) (ih : PartBranchMotive bs act bs') :
    PartMotive (.comm s r bs) act (.comm s r bs') := by
  intro hwf huniq role lt lt' hlwf hE hadv
  obtain ⟨hrs, hrr⟩ := async_overlap_not_participant hns hcond hwf hlwf hE hadv
  obtain ⟨⟨l, g0⟩, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨g0', hhd, ih0⟩ := ih l g0 rfl
  obtain ⟨⟨l', g1⟩, rest', rfl⟩ : ∃ x rest', bs' = x :: rest' := by
    cases bs' with
    | nil => simp at hhd
    | cons x xs => exact ⟨x, xs, rfl⟩
  simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hhd
  obtain ⟨-, rfl⟩ := hhd
  rw [trans_comm_other s r role _ hrs hrr] at hE ⊢
  have hwf0 := well_formed_first_of_comm s r (l, g0) rest hwf
  have hu0 : g0.uniqueBranchLabels = true := by
    simp only [GlobalType.uniqueBranchLabels, uniqueBranchLabelsBranches,
      Bool.and_eq_true] at huniq
    exact huniq.2.1
  exact ih0 hwf0 hu0 role lt lt' hlwf hE hadv

/-- `mu` case of the participant motive: transport typing to the unfolding. -/
theorem part_motive_mu (t : String) (body : GlobalType) (act : GlobalActionR)
    (g' : GlobalType) (ih : PartMotive (body.substitute t (.mu t body)) act g') :
    PartMotive (.mu t body) act g' := by
  intro hwf huniq role lt lt' hlwf hE hadv
  have hu : (body.substitute t (.mu t body)).uniqueBranchLabels = true :=
    GlobalType.unique_branch_labels_substitute body t _ huniq huniq
  exact ih (well_formed_mu_unfold t body hwf) hu role lt lt' hlwf
    (wellTyped_mu_unfold hwf hlwf hE) hadv

/-- Participant preservation for every global step: if a well-formed local type
`EQ2` to the projection of `g` advances by `act`, the result is well-formed and
`EQ2` to the projection of the stepped type `g'`. Requires `g` well-formed with
unique branch labels. -/
theorem participant_step_typed {g g' : GlobalType} {act : GlobalActionR}
    (hstep : step g act g') : PartMotive g act g' :=
  @step.rec (motive_1 := fun g act g' _ => PartMotive g act g')
    (motive_2 := fun bs act bs' _ => PartBranchMotive bs act bs')
    (fun s r bs label cont hmem => part_motive_head s r bs label cont hmem)
    (fun s r bs bs' act _ _ hns hcond hmem _ _ ih =>
      part_motive_async s r bs bs' act hns hcond (List.ne_nil_of_mem hmem) ih)
    (fun t body act g' _ ih => part_motive_mu t body act g' ih)
    (fun _ _ _ h => by simp at h)
    (fun label g g' _ _ _ _ _ ih _ => fun l g0 h => by
      simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨g', rfl, ih⟩)
    g act g' hstep

/-! ## General Subject Reduction -/

/-- Side conditions of the general subject reduction theorem (no head shape). -/
structure StepHyps (c : Configuration) : Prop where
  /-- Branch labels are unique. -/
  unique : c.globalType.uniqueBranchLabels = true
  /-- The global type is closed. -/
  closed : c.globalType.isClosed = true
  /-- The global type is well-formed. -/
  wf : c.globalType.wellFormed = true
  /-- The global type is blind (needed for non-participant coherence). -/
  blind : Choreography.Projection.Blind.isBlind c.globalType = true

/-- Head-step hypotheses imply the general step hypotheses. -/
theorem HeadStepHyps.toStepHyps {c : Configuration} {act : GlobalActionR}
    (hh : HeadStepHyps c act) : StepHyps c :=
  ⟨hh.unique, hh.closed, hh.wf, hh.blind⟩

/-- Participant case of general subject reduction. -/
theorem participant_typed_general {c c' : Configuration} {act : GlobalActionR}
    (htyped : WellTypedConfig c) (hh : StepHyps c) (hstep : ConfigStep c c' act)
    {p p' : Process} (hpm : p ∈ c.processes)
    (hadv : ProcessAdvance act p p') (hp : Participant act p.role) :
    p'.wellTyped c'.globalType := by
  obtain ⟨lt, hlt, hpl⟩ := hadv.advance hp
  have ht := htyped.processes_typed p hpm
  rw [Process.wellTyped, hpl, hadv.role_eq]
  exact participant_step_typed hstep.global_step hh.wf hh.unique p.role _ lt ht.1 ht.2 hlt

/-- Non-participant case of general subject reduction. -/
theorem nonparticipant_typed_general {c c' : Configuration} {act : GlobalActionR}
    (htyped : WellTypedConfig c) (hh : StepHyps c) (hstep : ConfigStep c c' act)
    {p p' : Process} (hpm : p ∈ c.processes)
    (hadv : ProcessAdvance act p p') (hp : ¬ Participant act p.role) :
    p'.wellTyped c'.globalType := by
  have hE := other_type_preserved _ _ act p.role hstep.global_step hh.closed hh.wf
    (fun h => hp (Or.inl h)) (fun h => hp (Or.inr h)) hh.blind
  obtain ⟨hwfp, hEp⟩ := htyped.processes_typed p hpm
  rw [Process.wellTyped, hadv.frame hp, hadv.role_eq]
  exact ⟨hwfp, SessionCoTypes.EQ2Props.eq2_trans_wf hEp (eq2_symm hE) hwfp
    (trans_well_formed_of_well_formed _ _ hh.wf)
    (trans_well_formed_of_well_formed _ _
      (step_preserves_well_formed _ _ act hstep.global_step hh.wf))⟩

/-- Subject reduction for every configuration step: a well-typed configuration
whose global type is closed, well-formed, blind and has unique branch labels
steps (by any `step` derivation: `comm_head`, `comm_async` or `mu`, with each
process advancing per `ProcessAdvance`) to a well-typed configuration. -/
theorem step_preserves_typing_general {c c' : Configuration} {act : GlobalActionR}
    (htyped : WellTypedConfig c) (hh : StepHyps c) (hstep : ConfigStep c c' act) :
    WellTypedConfig c' where
  processes_typed := by
    intro p' hp'
    obtain ⟨p, hpm, hadv⟩ := forall2_exists_left hstep.processes_advance p' hp'
    by_cases hp : Participant act p.role
    · exact participant_typed_general htyped hh hstep hpm hadv hp
    · exact nonparticipant_typed_general htyped hh hstep hpm hadv hp
  roles_contained := by
    intro r hr
    have hroles := step_roles_subset c.globalType c'.globalType act hstep.global_step r hr
    rw [← forall2_roles hstep.processes_advance]
    exact htyped.roles_contained r hroles
  roles_unique := by
    rw [← forall2_roles hstep.processes_advance]
    exact htyped.roles_unique

/-! ## Async Counterexample -/

/-- The async example of the module doc: `a`'s own type `send b [(l, send c …)]`
cannot advance by `a → c : m`, although the global type steps by that action. -/
theorem async_counterexample_no_advance (l m : Label) (lt' : LocalTypeR) :
    ¬ LocalAdvance ⟨"a", "c", m⟩ "a"
      (.send "b" [(l, none, .send "c" [(m, none, .end)])]) lt' := by
  intro h
  cases h with
  | send _ hfu _ => simp [LocalTypeR.fullUnfold, LocalTypeR.muHeight] at hfu
  | recv _ hne _ _ => exact hne rfl

/-! ## Claims -/

/-- Claims bundle for subject reduction. -/
structure Claims where
  /-- Subject reduction for head communication steps. -/
  subject_reduction : ∀ c c' act, WellTypedConfig c → HeadStepHyps c act →
      ConfigStep c c' act → WellTypedConfig c'
  /-- Subject reduction for all steps (`comm_head`, `comm_async`, `mu`). -/
  subject_reduction_general : ∀ c c' act, WellTypedConfig c → StepHyps c →
      ConfigStep c c' act → WellTypedConfig c'
  /-- Projected environments are always well-formed. -/
  projEnv_wellformed : ∀ g, WellFormedEnv (projEnv g)

/-- Build the claims bundle from proven theorems. -/
def claims : Semantics.SubjectReduction.Claims where
  subject_reduction := fun _ _ _ h1 h2 h3 => step_preserves_typing h1 h2 h3
  subject_reduction_general := fun _ _ _ h1 h2 h3 => step_preserves_typing_general h1 h2 h3
  projEnv_wellformed := projEnv_wellformed

end Semantics.SubjectReduction
