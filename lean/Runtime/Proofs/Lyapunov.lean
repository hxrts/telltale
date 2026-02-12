import Runtime.VM.Runtime.Scheduler
import Runtime.Proofs.VM.Scheduler
import Protocol.DeadlockFreedom

/-! # Progress Measure for Session Type Liveness

Adapts the Lyapunov stability technique from Gibbs (Hamiltonian/Stability.lean,
MeanField/Stability.lean) to prove liveness properties for session-typed systems.

In the physics setting, a Lyapunov function maps phase-space points to ℝ≥0,
equals zero at equilibrium, and decreases along trajectories. The discrete
analogue is a **progress measure**: a function from configurations to ℕ that
equals zero when the protocol is done and decreases under communication steps.

The well-foundedness of ℕ gives termination for finite protocols. For recursive
protocols, the measure bounds the number of remaining actions in a single
unfolding.

## Relationship to Gibbs

| Gibbs (continuous)   | Telltale (discrete)            |
|----------------------|--------------------------------|
| `LyapunovData`       | `ProgressMeasureData`          |
| `StrictLyapunovData` | `StrictProgressMeasureData`    |
| `PhasePoint n → ℝ`   | `State → ℕ`                    |
| `V_decreasing`       | `step_nonincreasing`           |
| `V_to_zero`          | `productive_step_decreasing`   |
| `HasDerivAt`         | `step s = some s'`             |
| `energy_dissipation` | communication consumes measure | -/

/-! ## Key Results

- `progressMeasure_nonincreasing_wt`: well-typed instruction steps do not
  increase the progress measure on local types.
- `progressMeasure_decrease_send/recv/offer`: communication steps strictly
  decrease the measure.
- `progressMeasure_pos_of_decide`: types that reach communication have
  positive measure.
- `ProgressMeasureData`: abstract framework for discrete Lyapunov arguments,
  giving deadlock freedom and bounded termination from a single measure.
-/

/-
The Problem. Proving liveness (deadlock freedom, eventual termination) for
session-typed systems requires showing that progress is always possible. This
is analogous to stability arguments in dynamical systems but in a discrete setting.

Solution Structure. Adapts Lyapunov stability theory to session types: defines
a progress measure (ℕ-valued function on configurations) that equals zero at
protocol completion and strictly decreases on communication steps. The well-
foundedness of ℕ yields termination. Key lemmas connect instruction execution
to measure decrease/non-increase.
-/

set_option autoImplicit false

section

/-! ## LocalType Progress Measure -/

/-- Progress measure on local types: counts remaining communication actions
    to reach `end_`. For guarded types, positive measure is equivalent to
    the type having pending communication.

    Recursive types contribute the body's measure. Since guarded types have
    at least one communication prefix before any variable reference, the
    body's measure is positive whenever the type can communicate.

    Branch types use the sum of branch measures to ensure any selected
    continuation has measure strictly less than the parent. -/
def LocalType.progressMeasure : LocalType → Nat
  | .send _ _ L => 1 + progressMeasure L
  | .recv _ _ L => 1 + progressMeasure L
  | .select _ bs => 1 + sumBranches bs
  | .branch _ bs => 1 + sumBranches bs
  | .end_ => 0
  | .var _ => 0
  | .mu L => progressMeasure L
where
  /-- Sum of progress measures across branch continuations. -/
  sumBranches : List (Label × LocalType) → Nat
    | [] => 0
    | (_, L) :: rest => progressMeasure L + sumBranches rest

/-! ## Zero and positivity -/

@[simp] theorem progressMeasure_end : LocalType.progressMeasure .end_ = 0 := rfl
@[simp] theorem progressMeasure_var (n : Nat) : (LocalType.var n).progressMeasure = 0 := rfl

theorem progressMeasure_send_pos (r : Role) (T : ValType) (L : LocalType) :
    0 < (LocalType.send r T L).progressMeasure := by
  simp [LocalType.progressMeasure]

theorem progressMeasure_recv_pos (r : Role) (T : ValType) (L : LocalType) :
    0 < (LocalType.recv r T L).progressMeasure := by
  simp [LocalType.progressMeasure]

theorem progressMeasure_select_pos (r : Role) (bs : List (Label × LocalType)) :
    0 < (LocalType.select r bs).progressMeasure := by
  simp [LocalType.progressMeasure]

theorem progressMeasure_branch_pos (r : Role) (bs : List (Label × LocalType)) :
    0 < (LocalType.branch r bs).progressMeasure := by
  simp [LocalType.progressMeasure]

/-- Positive progress measure from the decidable reachability checker.
    Types that can reach communication have positive measure. -/
theorem progressMeasure_pos_of_decide :
    ∀ (L : LocalType), reachesCommDecide L = true → 0 < L.progressMeasure
  | .send r T L', _ => progressMeasure_send_pos r T L'
  | .recv r T L', _ => progressMeasure_recv_pos r T L'
  | .select r bs, _ => progressMeasure_select_pos r bs
  | .branch r bs, _ => progressMeasure_branch_pos r bs
  | .end_, h => by simp [reachesCommDecide] at h
  | .var _, h => by simp [reachesCommDecide] at h
  | .mu L', h => by
      simp only [LocalType.progressMeasure]
      exact progressMeasure_pos_of_decide L' (by simp [reachesCommDecide] at h; exact h)

/-! ## Decrease under communication -/

/-- Sending strictly decreases the progress measure. -/
theorem progressMeasure_advance_send (r : Role) (T : ValType) (L : LocalType) :
    L.progressMeasure < (LocalType.send r T L).progressMeasure := by
  show L.progressMeasure < 1 + L.progressMeasure
  omega

/-- Receiving strictly decreases the progress measure. -/
theorem progressMeasure_advance_recv (r : Role) (T : ValType) (L : LocalType) :
    L.progressMeasure < (LocalType.recv r T L).progressMeasure := by
  show L.progressMeasure < 1 + L.progressMeasure
  omega

/-- The sum of branch measures is an upper bound on each individual branch.
    This is the key lemma connecting branch selection to measure decrease. -/
theorem sumBranches_mem_le (l : Label) (L : LocalType) (bs : List (Label × LocalType))
    (h : (l, L) ∈ bs) :
    L.progressMeasure ≤ LocalType.progressMeasure.sumBranches bs := by
  induction bs with
  | nil => cases h
  | cons hd tl ih =>
    obtain ⟨l', L'⟩ := hd
    show L.progressMeasure ≤ L'.progressMeasure + LocalType.progressMeasure.sumBranches tl
    rcases List.mem_cons.mp h with heq | hmem
    · have hL : L = L' := congrArg Prod.snd heq
      rw [hL]; omega
    · have := ih hmem; omega

/-- Selecting a branch strictly decreases the progress measure. -/
theorem progressMeasure_advance_select (r : Role) (bs : List (Label × LocalType))
    (l : Label) (L : LocalType) (h : (l, L) ∈ bs) :
    L.progressMeasure < (LocalType.select r bs).progressMeasure := by
  show L.progressMeasure < 1 + LocalType.progressMeasure.sumBranches bs
  have := sumBranches_mem_le l L bs h
  omega

/-! ## Nonincreasing under well-typed steps -/

/-- Well-typed instruction steps do not increase the progress measure.
    This is the discrete analogue of Gibbs's `V_decreasing` property:
    the Lyapunov function is non-increasing along system trajectories. -/
theorem progressMeasure_nonincreasing_wt {γ ε : Type}
    [GuardLayer γ] [EffectRuntime ε] [EffectSpec ε]
    (i : Instr γ ε) (sk : SessionKind γ) (L L' : LocalType)
    (h : WellTypedInstr i sk L L') :
    L'.progressMeasure ≤ L.progressMeasure := by
  cases h with
  | wt_send _ _ _ r T L' =>
    exact Nat.le_of_lt (progressMeasure_advance_send r T L')
  | wt_receive _ _ _ r T L' =>
    exact Nat.le_of_lt (progressMeasure_advance_recv r T L')
  | wt_offer _ _ r choices lbl L' hmem =>
    exact Nat.le_of_lt (progressMeasure_advance_select r choices lbl L' hmem)
  | wt_choose => exact le_refl _
  | wt_acquire => exact le_refl _
  | wt_release => exact le_refl _
  | wt_invoke =>
    show (LocalType.end_).progressMeasure ≤ (EffectSpec.handlerType _).progressMeasure
    simp [progressMeasure_end]
  | wt_open => exact le_refl _
  | wt_close => exact le_refl _
  | wt_fork => exact le_refl _
  | wt_join => exact le_refl _
  | wt_abort => exact le_refl _
  | wt_noop => exact le_refl _

/-- Communication steps strictly decrease the progress measure. -/
theorem progressMeasure_decrease_of_wt_send {γ ε : Type} [GuardLayer γ] [EffectRuntime ε]
    (_sid : SessionId) (_chan _val : Reg) (r : Role) (T : ValType) (L' : LocalType) :
    L'.progressMeasure < (LocalType.send r T L').progressMeasure :=
  progressMeasure_advance_send r T L'

theorem progressMeasure_decrease_of_wt_recv {γ ε : Type} [GuardLayer γ] [EffectRuntime ε]
    (_sid : SessionId) (_chan _dst : Reg) (r : Role) (T : ValType) (L' : LocalType) :
    L'.progressMeasure < (LocalType.recv r T L').progressMeasure :=
  progressMeasure_advance_recv r T L'

theorem progressMeasure_decrease_of_wt_offer {γ ε : Type} [GuardLayer γ] [EffectRuntime ε]
    (_sid : SessionId) (_chan : Reg) (r : Role) (choices : List (Label × LocalType))
    (lbl : Label) (L' : LocalType) (hmem : (lbl, L') ∈ choices) :
    L'.progressMeasure < (LocalType.select r choices).progressMeasure :=
  progressMeasure_advance_select r choices lbl L' hmem

/-! ## Abstract Progress Measure Framework -/

/-- Progress measure data for a discrete transition system.

    The discrete analogue of Gibbs's `LyapunovData`. A progress measure
    maps states to ℕ, equals zero at terminal states, and does not
    increase under transitions. -/
structure ProgressMeasureData (State : Type) where
  /-- The progress measure. -/
  measure : State → Nat
  /-- One-step transition. -/
  step : State → Option State
  /-- Termination predicate. -/
  done : State → Prop
  /-- Zero measure characterizes terminal states. -/
  measure_zero_iff_done : ∀ s, measure s = 0 ↔ done s
  /-- Steps do not increase the measure. -/
  step_nonincreasing : ∀ s s', step s = some s' → measure s' ≤ measure s
  /-- Non-terminal states can step (progress / deadlock freedom). -/
  progress : ∀ s, ¬done s → ∃ s', step s = some s'

/-- Strict progress measure: productive steps strictly decrease the measure.

    The discrete analogue of Gibbs's `StrictLyapunovData`. Adds a
    predicate identifying productive steps and requires the measure
    to strictly decrease on those steps. Under a fairness assumption
    that productive steps occur infinitely often, this gives termination. -/
structure StrictProgressMeasureData (State : Type)
    extends ProgressMeasureData State where
  /-- Predicate identifying productive (communication) steps. -/
  is_productive : State → State → Prop
  /-- Productive steps strictly decrease the measure. -/
  productive_step_decreasing : ∀ s s',
    step s = some s' → is_productive s s' → measure s' < measure s

/-! ## Consequences of the framework -/

/-- Deadlock freedom from the progress measure: non-terminal states can step. -/
theorem ProgressMeasureData.deadlock_free {State : Type}
    (D : ProgressMeasureData State) (s : State) (h : ¬D.done s) :
    ∃ s', D.step s = some s' :=
  D.progress s h

/-- Positive measure implies non-terminal. -/
theorem ProgressMeasureData.not_done_of_pos {State : Type}
    (D : ProgressMeasureData State) (s : State) (h : 0 < D.measure s) :
    ¬D.done s := by
  intro hdone
  have := (D.measure_zero_iff_done s).mpr hdone
  omega

/-- A trace forms a chain starting from state `s`: each pair's first element
    matches the current state and the next pair continues from the second. -/
def IsChainFrom {State : Type} : State → List (State × State) → Prop
  | _, [] => True
  | s, (a, b) :: tl => a = s ∧ IsChainFrom b tl

/-- Productive step chains have length bounded by the initial measure.
    Requires the trace to form a chain from `s` so the measure decrease
    propagates through the entire trace. -/
theorem StrictProgressMeasureData.productive_steps_bounded {State : Type}
    (D : StrictProgressMeasureData State) (s : State) :
    ∀ (trace : List (State × State)),
      IsChainFrom s trace →
      (∀ p ∈ trace, D.step p.1 = some p.2 ∧ D.is_productive p.1 p.2) →
      trace.length ≤ D.measure s := by
  intro trace hchain hall
  induction trace generalizing s with
  | nil => exact Nat.zero_le _
  | cons hd tl ih =>
    obtain ⟨heq, hchain_tl⟩ := hchain
    subst heq
    have ⟨hstep, hprod⟩ := hall hd (List.mem_cons_self ..)
    have hdec := D.productive_step_decreasing hd.1 hd.2 hstep hprod
    have htl := ih hd.2 hchain_tl (fun p hp => hall p (List.mem_cons_of_mem _ hp))
    simp [List.length_cons]
    omega

/-- Witness object certifying productive-step bound tightness at initial state `s`:
    the provided productive chain has length exactly the Lyapunov bound. -/
structure ProductiveStepBoundTightnessWitness {State : Type}
    (D : StrictProgressMeasureData State) (s : State) where
  trace : List (State × State)
  chainFrom : IsChainFrom s trace
  productiveTrace : ∀ p ∈ trace, D.step p.1 = some p.2 ∧ D.is_productive p.1 p.2
  saturatesBound : trace.length = D.measure s

/-- Witness-based tightness proposition for the productive-step bound. -/
def productiveStepBoundTight {State : Type}
    (D : StrictProgressMeasureData State) (s : State) : Prop :=
  Nonempty (ProductiveStepBoundTightnessWitness D s)

/-- Tightness closure: a saturating witness upgrades the productive-step bound
    from an upper bound to an exact bound at `s`. -/
theorem StrictProgressMeasureData.productive_steps_bound_exact_of_tightWitness
    {State : Type}
    (D : StrictProgressMeasureData State) (s : State)
    (hTight : productiveStepBoundTight D s) :
    ∃ trace,
      IsChainFrom s trace ∧
      (∀ p ∈ trace, D.step p.1 = some p.2 ∧ D.is_productive p.1 p.2) ∧
      trace.length ≤ D.measure s ∧
      trace.length = D.measure s := by
  rcases hTight with ⟨w⟩
  refine ⟨w.trace, w.chainFrom, w.productiveTrace, ?_, w.saturatesBound⟩
  exact D.productive_steps_bounded s w.trace w.chainFrom w.productiveTrace

/-! ## Buffer Progress Measure -/

/-- Buffer contribution to the progress measure: number of pending messages. -/
def bufferProgressMeasure {α : Type} (buf : List α) : Nat := buf.length

/-- Dequeuing strictly decreases the buffer measure. -/
theorem bufferProgressMeasure_dequeue {α : Type} (v : α) (rest : List α) :
    bufferProgressMeasure rest < bufferProgressMeasure (v :: rest) := by
  simp [bufferProgressMeasure]

@[simp] theorem bufferProgressMeasure_nil {α : Type} :
    bufferProgressMeasure ([] : List α) = 0 := rfl

/-- Enqueuing increases the buffer measure by one. -/
theorem bufferProgressMeasure_enqueue {α : Type} (buf : List α) (v : α) :
    bufferProgressMeasure (buf ++ [v]) = bufferProgressMeasure buf + 1 := by
  simp [bufferProgressMeasure]

/-! ## VM Progress Measure -/

/-- Per-session progress measure: combines endpoint type measures with
    pending buffer sizes. This is the concrete Lyapunov function for
    a single session. -/
structure SessionProgressMeasure where
  /-- Sum of `progressMeasure` over all endpoint local types in the session. -/
  typeMeasure : Nat
  /-- Total number of pending messages across all buffers in the session. -/
  bufferMeasure : Nat
  /-- Combined measure. -/
  total : Nat := typeMeasure + bufferMeasure

namespace SessionProgressMeasure

/-- Canonical Lyapunov value extracted from structural components. -/
def lyapunov (m : SessionProgressMeasure) : Nat :=
  m.typeMeasure + m.bufferMeasure

/-- Composition of per-session measures is additive on each component. -/
def compose (m₁ m₂ : SessionProgressMeasure) : SessionProgressMeasure where
  typeMeasure := m₁.typeMeasure + m₂.typeMeasure
  bufferMeasure := m₁.bufferMeasure + m₂.bufferMeasure

@[simp] theorem lyapunov_compose (m₁ m₂ : SessionProgressMeasure) :
    lyapunov (compose m₁ m₂) = lyapunov m₁ + lyapunov m₂ := by
  simp [lyapunov, compose, Nat.add_left_comm, Nat.add_comm]

end SessionProgressMeasure

/-- System-level Lyapunov value: additive over composed session lists. -/
def systemLyapunov (ms : List SessionProgressMeasure) : Nat :=
  (ms.map SessionProgressMeasure.lyapunov).foldl (· + ·) 0

private theorem foldl_add_shift (l : List Nat) (n : Nat) :
    l.foldl (· + ·) n = n + l.foldl (· + ·) 0 := by
  induction l generalizing n with
  | nil =>
    simp
  | cons h t ih =>
      simp only [List.foldl, Nat.zero_add]
      have ih1 := ih (n + h)
      have ih2 := ih h
      calc
        t.foldl (· + ·) (n + h) = (n + h) + t.foldl (· + ·) 0 := ih1
        _ = n + (h + t.foldl (· + ·) 0) := by ring
        _ = n + t.foldl (· + ·) h := by rw [← ih2]

theorem systemLyapunov_append (ms₁ ms₂ : List SessionProgressMeasure) :
    systemLyapunov (ms₁ ++ ms₂) = systemLyapunov ms₁ + systemLyapunov ms₂ := by
  unfold systemLyapunov
  rw [List.map_append, List.foldl_append]
  simpa using foldl_add_shift (l := List.map SessionProgressMeasure.lyapunov ms₂)
    (n := List.foldl (· + ·) 0 (List.map SessionProgressMeasure.lyapunov ms₁))

/-- Delegation conservation principle (balanced transfer):
    if type and buffer mass are redistributed but totals are preserved,
    the combined Lyapunov value is preserved. -/
theorem lyapunov_conserved_under_balanced_delegation
    (mSender mRecv mSender' mRecv' : SessionProgressMeasure)
    (hType :
      mSender'.typeMeasure + mRecv'.typeMeasure =
        mSender.typeMeasure + mRecv.typeMeasure)
    (hBuf :
      mSender'.bufferMeasure + mRecv'.bufferMeasure =
        mSender.bufferMeasure + mRecv.bufferMeasure) :
    SessionProgressMeasure.lyapunov mSender' + SessionProgressMeasure.lyapunov mRecv' =
      SessionProgressMeasure.lyapunov mSender + SessionProgressMeasure.lyapunov mRecv := by
  simp [SessionProgressMeasure.lyapunov] at hType hBuf ⊢
  omega

/-- A VM configuration admits a progress measure when each session's
    monitored types satisfy the nonincreasing property under well-typed steps.

    The measure function is parameterized externally to avoid self-referential
    structure fields (which would create invalid nested inductives in Lean 4). -/
def VMAdmitsProgressMeasure {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (measure : VMState ι γ π ε ν → Nat) (st : VMState ι γ π ε ν) : Prop :=
  ∀ st' : VMState ι γ π ε ν,
    schedStep st = some st' → measure st' ≤ measure st

/-! ## VM Deadlock Freedom via Progress Measure -/

/-- Helper: if the scheduler selects a coroutine, schedStep produces a result. -/
theorem schedStep_some_of_schedule {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (cid : CoroutineId) (st' : VMState ι γ π ε ν)
    (h : schedule st = some (cid, st')) :
    ∃ st'', schedStep st = some st'' := by
  simp only [schedStep, h]
  exact ⟨_, rfl⟩

/-- VM deadlock freedom: a well-formed VM with a runnable coroutine can step.

    This combines the progress measure framework with scheduler liveness.
    The progress measure ensures types can advance (nonincreasing on steps,
    strictly decreasing on communication). Scheduler liveness ensures
    runnable coroutines get scheduled. Together they give: if some coroutine
    is ready and in the queue, the VM can take a step. -/
def vm_deadlock_free_via_progress : Prop :=
  ∀ {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν),
    WFVMState st →
    (∃ cid, cid ∈ st.sched.readyQueue ∧
      match st.coroutines[cid]? with
      | some c => c.status = .ready ∨ c.status = .speculating
      | none => False) →
    ∃ st', schedStep st = some st'

/-- VM deadlock freedom holds: follows from scheduler liveness. -/
theorem vm_deadlock_free_via_progress_holds : vm_deadlock_free_via_progress := by
  intro ι γ π ε ν _ _ _ _ _ _ _ _ _ _ _ _ st _hwf ⟨cid, hmem, hstatus⟩
  have hsf := starvation_free_holds st
  have hcid := hsf cid hmem
  match hcoro : st.coroutines[cid]? with
  | none =>
    simp only [hcoro] at hstatus
  | some c =>
    simp only [hcoro] at hstatus hcid
    obtain ⟨cid', st', hsched⟩ := hcid hstatus
    exact schedStep_some_of_schedule st cid' st' hsched

end
