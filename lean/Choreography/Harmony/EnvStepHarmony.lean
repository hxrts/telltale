import Choreography.Harmony.NonParticipantSteps
import Choreography.Harmony.ParticipantStepProjection

/-
The Problem. `Semantics.EnvStep.EnvStep` is an environment-level step defined
independently of global steps. We must show that a global step is reflected by
an environment step on the projections (harmony), and conversely that an
environment step of a projected environment is realized by a global step.

Solution Structure. For a head communication `p → q : ℓ` of
`g = comm p q bs`, the sender/receiver projections are computed by
`trans_comm_sender`/`trans_comm_receiver` and `mem_trans_branches_of_mem`;
non-participants are handled by `proj_trans_other_step`. The converse inverts
the sender's projected `send` to recover a branch of `bs`.
-/

/-! # Choreography.Harmony.EnvStepHarmony

Harmony between global steps and the independent environment step `EnvStep`.

## Main Results

- `step_harmony`: a head-communication global step of a closed, well-formed,
  blind global type induces an `EnvStep` on the projections onto any role set
  containing the two participants.
- `envstep_realizable`: an `EnvStep` of the projection of `comm p q bs` whose
  action is a `p → q` communication is realized by a global step.
- `Claims` / `claims`: bundle of both directions.

## Scope

Only head communications are covered. Asynchronous (`comm_async`) global steps
are not reflected by `EnvStep`: for `g = comm a b [(l, comm a c [(m, end)])]`
with `c ≠ b`, `step g (a → c : m) (comm a b [(l, end)])` holds, yet `a`'s
projection is `send b …`, not a send to `c`. Reflecting such steps needs a local
asynchronous-permutation step relation, which this development does not have.
Steps through `mu` require relating `trans (mu t body)` to the projection of
the unfolding; that is also not covered here.
-/

namespace Choreography.Harmony

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionCoTypes.EQ2
open Choreography.Projection.Project (trans_comm_sender trans_comm_receiver transBranches)
open Choreography.Projection.Blind (isBlind)
open Semantics.EnvStep

/-! ## Helpers -/

/-- A step from `comm p q bs` labelled with the head action picks a branch. -/
private theorem head_step_mem {p q : String} {l : Label} {bs : List (Label × GlobalType)}
    {g' : GlobalType} (h : step (.comm p q bs) ⟨p, q, l⟩ g') : (l, g') ∈ bs := by
  cases h with
  | comm_head _ _ _ _ _ hmem => exact hmem
  | comm_async _ _ _ _ _ _ _ _ hcond _ _ _ => exact absurd rfl (hcond rfl)

/-- A projected branch `(l, none, c)` comes from some global branch `(l, cont)`. -/
private theorem mem_of_mem_trans_branches {bs : List (Label × GlobalType)} {role : String}
    {l : Label} {c : LocalTypeR} (h : (l, none, c) ∈ transBranches bs role) :
    ∃ cont, (l, cont) ∈ bs := by
  induction bs with
  | nil => simp [transBranches, Choreography.Projection.Trans.transBranches] at h
  | cons hd tl ih =>
      obtain ⟨l', g⟩ := hd
      simp only [transBranches, Choreography.Projection.Trans.transBranches,
        List.mem_cons] at h
      rcases h with h | h
      · obtain ⟨rfl, -⟩ := Prod.mk.inj h
        exact ⟨g, List.mem_cons_self⟩
      · obtain ⟨cont, hc⟩ := ih h
        exact ⟨cont, List.mem_cons_of_mem _ hc⟩

/-- Well-formed head communications have distinct endpoints. -/
private theorem receiver_ne_sender_of_wf {p q : String} {bs : List (Label × GlobalType)}
    (hwf : (GlobalType.comm p q bs).wellFormed = true) : q ≠ p := by
  simp only [GlobalType.wellFormed, Bool.and_eq_true] at hwf
  have hno := hwf.1.2
  simp [GlobalType.noSelfComm] at hno
  intro hEq; exact hno.1 hEq.symm

/-! ## Per-Role Components -/

/-- Sender component of harmony for a head step. -/
private theorem harmony_sender {p q : String} {l : Label} {bs : List (Label × GlobalType)}
    {g' : GlobalType} {S : List String} (hmem : (l, g') ∈ bs) (hp : p ∈ S) :
    ∃ bs' cont, (projLocalEnvOnto (.comm p q bs) S).lookup p = some (.send q bs') ∧
      (l, none, cont) ∈ bs' ∧
      ∃ t', (projLocalEnvOnto g' S).lookup p = some t' ∧ EQ2 t' cont := by
  refine ⟨transBranches bs p, Choreography.Projection.Project.trans g' p, ?_, mem_trans_branches_of_mem bs l g' p hmem,
    Choreography.Projection.Project.trans g' p, by simp [lookup_proj_local_env_onto, hp], eq2_refl _⟩
  simp [lookup_proj_local_env_onto, hp, trans_comm_sender p q p bs rfl]

/-- Receiver component of harmony for a head step. -/
private theorem harmony_receiver {p q : String} {l : Label} {bs : List (Label × GlobalType)}
    {g' : GlobalType} {S : List String} (hmem : (l, g') ∈ bs) (hq : q ∈ S) (hne : q ≠ p) :
    ∃ bs' cont, (projLocalEnvOnto (.comm p q bs) S).lookup q = some (.recv p bs') ∧
      (l, none, cont) ∈ bs' ∧
      ∃ t', (projLocalEnvOnto g' S).lookup q = some t' ∧ EQ2 t' cont := by
  refine ⟨transBranches bs q, Choreography.Projection.Project.trans g' q, ?_, mem_trans_branches_of_mem bs l g' q hmem,
    Choreography.Projection.Project.trans g' q, by simp [lookup_proj_local_env_onto, hq], eq2_refl _⟩
  simp [lookup_proj_local_env_onto, hq, trans_comm_receiver p q q bs rfl hne]

/-- Frame component: non-participants keep their projection up to `EQ2`. -/
private theorem harmony_frame {g g' : GlobalType} {act : GlobalActionR} {S : List String}
    (hstep : step g act g') (hclosed : g.isClosed = true) (hwf : g.wellFormed = true)
    (hblind : isBlind g = true) (r : String) (hns : r ≠ act.sender)
    (hnr : r ≠ act.receiver) (t : LocalTypeR)
    (ht : (projLocalEnvOnto g S).lookup r = some t) :
    ∃ t', (projLocalEnvOnto g' S).lookup r = some t' ∧ EQ2 t' t := by
  rw [lookup_proj_local_env_onto] at ht
  split at ht
  · cases ht
    exact ⟨Choreography.Projection.Project.trans g' r, by simp [lookup_proj_local_env_onto, *],
      proj_trans_other_step g g' act r hstep hclosed hwf hns hnr hblind⟩
  · cases ht

/-! ## Step Harmony -/

/-- Step harmony: a head-communication global step of a closed, well-formed,
blind global type induces an `EnvStep` between the projections onto `S`. -/
theorem step_harmony (g g' : GlobalType) (act : GlobalActionR)
    (bs : List (Label × GlobalType)) (S : List String) (hstep : step g act g')
    (hhead : g = .comm act.sender act.receiver bs) (hclosed : g.isClosed = true)
    (hwf : g.wellFormed = true) (hblind : isBlind g = true)
    (hs : act.sender ∈ S) (hr : act.receiver ∈ S) :
    EnvStep (projLocalEnvOnto g S) act (projLocalEnvOnto g' S) := by
  obtain ⟨p, q, l⟩ := act
  subst hhead
  have hmem := head_step_mem hstep
  refine ⟨by simp [proj_local_env_onto_dom], harmony_sender hmem hs,
    harmony_receiver hmem hr (receiver_ne_sender_of_wf hwf), ?_⟩
  exact harmony_frame hstep hclosed hwf hblind

/-! ## Converse -/

/-- Converse harmony: an `EnvStep` of the projection of `comm p q bs` whose
action is a `p → q` communication is realized by a global step. -/
theorem envstep_realizable {p q : String} {bs : List (Label × GlobalType)}
    {S : List String} {act : GlobalActionR} {env' : LocalEnv}
    (hp : act.sender = p) (hq : act.receiver = q)
    (h : EnvStep (projLocalEnvOnto (.comm p q bs) S) act env') :
    ∃ g', step (.comm p q bs) act g' := by
  obtain ⟨bs', c, hlk, hmem, _⟩ := h.sender
  obtain ⟨p', q', l⟩ := act
  simp only at hp hq; subst hp hq
  rw [lookup_proj_local_env_onto, trans_comm_sender p' q' p' bs rfl] at hlk
  split at hlk
  · cases hlk
    obtain ⟨cont, hc⟩ := mem_of_mem_trans_branches hmem
    exact ⟨cont, step.comm_head p' q' bs l cont hc⟩
  · cases hlk

/-! ## Claims Bundle -/

/-- Claims bundle for harmony between global steps and `EnvStep`. -/
structure Claims where
  /-- Head-communication global steps induce environment steps. -/
  harmony : ∀ g g' act bs S, step g act g' → g = .comm act.sender act.receiver bs →
    g.isClosed = true → g.wellFormed = true → isBlind g = true →
    act.sender ∈ S → act.receiver ∈ S →
    EnvStep (projLocalEnvOnto g S) act (projLocalEnvOnto g' S)
  /-- Environment steps of a projected head communication are realizable. -/
  realizable : ∀ p q bs S act env', act.sender = p → act.receiver = q →
    EnvStep (projLocalEnvOnto (.comm p q bs) S) act env' →
    ∃ g', step (.comm p q bs) act g'

/-- Build the claims bundle from the proven theorems. -/
theorem claims : Claims where
  harmony := step_harmony
  realizable := fun _ _ _ _ _ _ hp hq h => envstep_realizable hp hq h

end Choreography.Harmony
