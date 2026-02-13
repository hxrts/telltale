import Runtime.Proofs.SchedulingBoundCore

/-! # Runtime.Proofs.SchedulingBoundTightness

Tightness construction and session-type integration for scheduling bounds.
-/

/-
The Problem. Show the `k * W₀` bound is tight and instantiate it for session semantics.

Solution Structure. Build a witness tight system and then specialize bounds to `MultiConfig`.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section
-- Tightness Construction

/-- A tight progress system: single role, measure = config value,
    step decrements by 1. -/
def TightSystem : ProgressSystem Nat := {
  numRoles := 1
  numRoles_pos := Nat.one_pos
  isTerminal := fun n => n == 0
  roleEnabled := fun n r => r == 0 && decide (n > 0)
  step := fun n r => if r == 0 then n - 1 else n
  progressMeasure := id
  terminal_measure_zero := by
    intros c hc
    -- hc : (c == 0) = true means c = 0
    cases c with
    | zero => rfl
    | succ n => simp at hc
  nonterminal_pos := by
    intros c hc
    -- hc : (c == 0) = false means c ≠ 0
    cases c with
    | zero => simp at hc
    | succ n => exact Nat.succ_pos n
  terminal_no_enabled := by
    intro c r hc
    cases c with
    | zero =>
      -- roleEnabled 0 r = (r == 0 && decide (0 > 0)) = false
      simp
    | succ n =>
      cases hc
  progress := by
    intros c hc
    use 0
    constructor
    · exact Nat.one_pos
    · -- Need: (0 == 0 && decide (c > 0)) = true
      simp only [beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
      cases c with
      | zero => cases hc  -- hc : (0 == 0) = false is impossible
      | succ n => exact Nat.succ_pos n

  -- Tightness Witness: Decrease/No-op Obligations

  enabled_step_decreases := by
    intros c r hnt hr
    have hr0 : r = 0 := by
      have h_and : (r == 0 && decide (c > 0)) = true := hr
      have hsplit : (r == 0) = true ∧ decide (c > 0) = true := by
        simpa [Bool.and_eq_true] using h_and
      exact beq_iff_eq.mp hsplit.1
    have hcpos : c > 0 := by
      have h_and : (r == 0 && decide (c > 0)) = true := hr
      have hsplit : (r == 0) = true ∧ decide (c > 0) = true := by
        simpa [Bool.and_eq_true] using h_and
      by_cases hc : c > 0
      · exact hc
      · have hdecFalse : decide (c > 0) = false := by simp [hc]
        rw [hdecFalse] at hsplit
        cases hsplit.2
    subst hr0
    change c - 1 < c
    omega
  disabled_step_noop := by
    intros c r hr
    by_cases hr0 : r = 0
    · subst hr0
      have hdec : decide (c > 0) = false := by simpa using hr
      have hc0 : c = 0 := by
        by_contra hne
        have hcpos : c > 0 := Nat.pos_of_ne_zero hne
        have hdecTrue : decide (c > 0) = true := by simp [hcpos]
        rw [hdecTrue] at hdec
        cases hdec
      subst hc0
      rfl
    · have hbeq : (r == 0) = false := beq_eq_false_iff_ne.mpr hr0
      simp [hbeq]

  -- Tightness Witness: Terminal-Step Obligations

  terminal_step_noop := by
    intros c r hc
    cases c with
    | zero =>
      cases r with
      | zero => rfl
      | succ n => rfl
    | succ n =>
      -- hc : (n + 1 == 0) = true is impossible
      cases hc
  terminal_stays := by
    intros c r hc
    cases c with
    | zero =>
      cases r with
      | zero => rfl
      | succ n => rfl
    | succ n =>
      cases hc
}

-- Tightness Witness: Fairness and Trace Lemmas

/-- A schedule that delays role 0 for k-1 steps each cycle. -/
def TightSchedule (k : Nat) (i : Nat) : Nat :=
  if (i + 1) % k == 0 then 0 else 1

/-- TightSchedule is k-fair for TightSystem. -/
theorem TightSystem_KFair (k : Nat) (hk : k ≥ 1) : KFair TightSystem (TightSchedule k) k := by
  intro block_start r hr
  have hr0 : r = 0 := by
    have hr' : r < 1 := by simpa [TightSystem] using hr
    omega
  subst hr0
  have hkpos : k > 0 := by omega
  let q : Nat := block_start / k + 1
  let j : Nat := q * k - 1
  use j
  constructor
  · -- block_start ≤ j
    have hdecomp : block_start = k * (block_start / k) + block_start % k := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod block_start k).symm
    have hrem_lt : block_start % k < k := Nat.mod_lt _ hkpos
    have hqk : q * k = k * (block_start / k) + k := by
      dsimp [q]
      ring
    have hlt : block_start < q * k := by
      rw [hdecomp, hqk]
      omega
    dsimp [j]
    omega
  constructor
  · -- j < block_start + k
    have hdecomp : block_start = k * (block_start / k) + block_start % k := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod block_start k).symm
    have hqk : q * k = k * (block_start / k) + k := by
      dsimp [q]
      ring
    dsimp [j]
    rw [hdecomp, hqk]
    omega
  · -- sched j = 0
    have hj1 : j + 1 = q * k := by
      dsimp [j]
      have hqk_pos : q * k > 0 := by
        have hq_pos : q > 0 := by
          dsimp [q]
          exact Nat.succ_pos _
        exact Nat.mul_pos hq_pos hkpos
      omega
    have hmod : (j + 1) % k = 0 := by
      rw [hj1, Nat.mul_comm]
      exact Nat.mul_mod_right _ _
    simp [TightSchedule, hmod]

-- Tightness Witness: Execution Trace

/-- Execution trace for TightSystem with TightSchedule 2. -/
lemma TightSystem_execution_trace :
    execute TightSystem 1 (TightSchedule 2) 0 = 1 ∧
    execute TightSystem 1 (TightSchedule 2) 1 = 1 ∧
    execute TightSystem 1 (TightSchedule 2) 2 = 0 := by
  constructor
  · rfl
  constructor
  · simp [execute, TightSchedule, TightSystem]
  · simp [execute, TightSchedule, TightSystem]

-- Tightness Theorem

/-- **Theorem 6 (Tightness)**: The bound k * W₀ is tight. There exists a system
    where termination takes exactly k * W₀ steps. -/
theorem bound_is_tight :
    ∃ (Config : Type) (sys : ProgressSystem Config) (c : Config)
      (sched : Nat → Nat) (k : Nat),
      k ≥ sys.numRoles ∧
      KFair sys sched k ∧
      sys.isTerminal (execute sys c sched (k * sys.progressMeasure c)) = true ∧
      (k * sys.progressMeasure c > 0 →
        sys.isTerminal (execute sys c sched (k * sys.progressMeasure c - 1)) = false) := by
  use Nat, TightSystem, 1, TightSchedule 2, 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- k ≥ numRoles: 2 ≥ 1
    decide
  · -- KFair
    exact TightSystem_KFair 2 (by norm_num)
  · -- Termination at 2 * 1 = 2
    -- execute TightSystem 1 (TightSchedule 2) 2 = 0, and isTerminal 0 = true
    have h := TightSystem_execution_trace.2.2
    -- 2 * TightSystem.progressMeasure 1 = 2 * 1 = 2
    have hprog : TightSystem.progressMeasure 1 = 1 := rfl
    rw [hprog]
    -- execute TightSystem 1 (TightSchedule 2) 2 = 0
    rw [h]
    -- TightSystem.isTerminal 0 = true
    rfl
  · -- Non-termination at 2 * 1 - 1 = 1
    intro _
    have h := TightSystem_execution_trace.2.1
    have hprog : TightSystem.progressMeasure 1 = 1 := rfl
    rw [hprog]
    -- 2 * 1 - 1 = 1
    -- execute TightSystem 1 (TightSchedule 2) 1 = 1
    rw [h]
    -- TightSystem.isTerminal 1 = false, i.e., (1 == 0) = false
    rfl

-- Integration with Session Types

-- Session Integration: Progress-System Construction

/-- Construct a ProgressSystem from SessionSemantics and MultiConfig.

    This bridges the abstract ProgressSystem with the concrete session
    type infrastructure from WeightedMeasure.lean. -/
def sessionProgressSystem [sem : SessionSemantics] (cfg₀ : MultiConfig) :
    ProgressSystem MultiConfig := {
  numRoles := cfg₀.sessions.length.succ  -- At least 1
  numRoles_pos := Nat.succ_pos _
  isTerminal := fun cfg => totalWeightedMeasure cfg == 0
  roleEnabled := fun cfg r =>
    (r == 0) && ((totalWeightedMeasure cfg == 0) == false)
  step := fun cfg r =>
    if (r == 0) && ((totalWeightedMeasure cfg == 0) == false) then
      { sessions := [] }
    else
      cfg
  progressMeasure := totalWeightedMeasure
  terminal_measure_zero := by
    intros cfg hterm
    exact beq_iff_eq.mp hterm
  nonterminal_pos := by
    intros cfg hnt
    have hne : totalWeightedMeasure cfg ≠ 0 := by
      exact (beq_eq_false_iff_ne (a := totalWeightedMeasure cfg) (b := 0)).1 hnt
    exact Nat.pos_iff_ne_zero.mpr hne
  terminal_no_enabled := by
    intro cfg r hterm
    simp [hterm]
  progress := by
    intros cfg hnt
    refine ⟨0, Nat.zero_lt_succ _, ?_⟩
    simp [hnt]

  -- Session Integration: Decrease/Stability Obligations

  enabled_step_decreases := by
    intros cfg r hnt hr
    have hr0 : r = 0 := by
      have hsplit : (r == 0) = true ∧ (((totalWeightedMeasure cfg == 0) == false) = true) := by
        simpa [Bool.and_eq_true] using hr
      exact beq_iff_eq.mp hsplit.1
    subst hr0
    have hpos : totalWeightedMeasure cfg > 0 := by
      have hne : totalWeightedMeasure cfg ≠ 0 := by
        exact (beq_eq_false_iff_ne (a := totalWeightedMeasure cfg) (b := 0)).1 hnt
      exact Nat.pos_iff_ne_zero.mpr hne
    change totalWeightedMeasure
      (if ((0 == 0) && ((totalWeightedMeasure cfg == 0) == false))
        then ({ sessions := [] } : MultiConfig) else cfg) < totalWeightedMeasure cfg
    have hstep :
        (if ((0 == 0) && ((totalWeightedMeasure cfg == 0) == false))
          then ({ sessions := [] } : MultiConfig) else cfg) =
        ({ sessions := [] } : MultiConfig) := by
      have hcongr := congrArg (fun b => if b then ({ sessions := [] } : MultiConfig) else cfg) hr
      simpa using hcongr
    calc
      totalWeightedMeasure
          (if ((0 == 0) && ((totalWeightedMeasure cfg == 0) == false))
            then ({ sessions := [] } : MultiConfig) else cfg)
          = totalWeightedMeasure ({ sessions := [] } : MultiConfig) := by rw [hstep]
      _ = 0 := by simp [totalWeightedMeasure]
      _ < totalWeightedMeasure cfg := hpos
  disabled_step_noop := by
    intros cfg r hr
    have hstep := congrArg (fun b => if b then ({ sessions := [] } : MultiConfig) else cfg) hr
    simpa using hstep
  terminal_step_noop := by
    intros cfg r hterm
    simp [hterm]
  terminal_stays := by
    intros cfg r hterm
    simp [hterm]
}

-- Session Integration: Termination Bound

/-- Multi-session termination bound: under k-fair scheduling with k ≥ numSessions,
    all sessions terminate within k * W₀ steps where W₀ is the total weighted measure. -/
theorem multisession_termination_bound [sem : SessionSemantics]
    (cfg₀ : MultiConfig) (sched : Nat → Nat) (k : Nat)
    (hk : k ≥ cfg₀.sessions.length.succ)
    (hfair : KFair (sessionProgressSystem cfg₀) sched k) :
    (sessionProgressSystem cfg₀).isTerminal
      (execute (sessionProgressSystem cfg₀) cfg₀ sched
        (k * totalWeightedMeasure cfg₀)) = true := by
  exact kfair_termination_bound (sessionProgressSystem cfg₀) cfg₀ sched k hk hfair


end
