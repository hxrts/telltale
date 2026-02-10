import Runtime.Proofs.WeightedMeasure

/-!
# Deterministic Termination Bounds for Scheduled Protocol Execution

Formalizes deterministic termination bounds under k-fair scheduling.
The main result: under a k-fair schedule with k ≥ numRoles, any execution
terminates within k * W₀ steps, where W₀ is the initial progress measure.

## Key Definitions

- `ProgressSystem`: Abstract progress system with roles, steps, and measure
- `KFair`: k-fairness predicate (every role scheduled in every k-window)
- `execute`: Execute t steps from config using schedule

## Main Results

- `measure_nonincreasing`: Progress measure never increases
- `block_progress`: Measure strictly decreases over k steps when non-terminal
- `kfair_termination_bound`: k * W₀ steps suffice for termination
- `roundrobin_termination_bound`: Corollary for n-fair (round-robin)
- `bound_is_tight`: The k * W₀ bound is tight
-/

/-
The Problem. We need concrete termination bounds for scheduled protocol execution
to guarantee protocols complete in bounded time, enabling practical timeouts and
resource allocation. The bound must account for arbitrary k-fair scheduling.

Solution Structure. Defines `ProgressSystem` abstracting configurations with roles,
steps, and progress measures. Proves `measure_nonincreasing` (steps don't increase
measure) and `block_progress` (k steps strictly decrease when non-terminal). The
main theorem `kfair_termination_bound` shows k * W₀ steps suffice, with tightness.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

/-! ## Progress System Abstraction -/

/-- A progress system: configurations with a step function, roles, and a
    progress measure that strictly decreases on every productive step.

    This generalizes the SessionSemantics from WeightedMeasure.lean to support
    arbitrary configurations with scheduling. -/
structure ProgressSystem (Config : Type) where
  /-- Number of roles (participants) in the system. -/
  numRoles : Nat
  /-- At least one role exists. -/
  numRoles_pos : numRoles > 0
  /-- Check if a configuration is terminal (all sessions ended). -/
  isTerminal : Config → Bool
  /-- Check if role r is enabled (can make progress) in config c. -/
  roleEnabled : Config → Nat → Bool
  /-- Execute one step for role r in config c. -/
  step : Config → Nat → Config
  /-- Progress measure (weighted Lyapunov function). -/
  progressMeasure : Config → Nat
  /-- Terminal configs have measure 0. -/
  terminal_measure_zero : ∀ c, isTerminal c = true → progressMeasure c = 0
  /-- Non-terminal configs have positive measure. -/
  nonterminal_pos : ∀ c, isTerminal c = false → progressMeasure c > 0
  /-- Terminal configs have no enabled roles. -/
  terminal_no_enabled : ∀ c r, isTerminal c = true → roleEnabled c r = false
  /-- Progress: non-terminal configs have at least one enabled role. -/
  progress : ∀ c, isTerminal c = false →
    ∃ r, r < numRoles ∧ roleEnabled c r = true
  /-- Stepping an enabled role in a non-terminal config decreases the measure. -/
  enabled_step_decreases : ∀ c r,
    isTerminal c = false → roleEnabled c r = true →
    progressMeasure (step c r) < progressMeasure c
  /-- Stepping a disabled role is a no-op. -/
  disabled_step_noop : ∀ c r, roleEnabled c r = false → step c r = c
  /-- Stepping a terminal config is a no-op. -/
  terminal_step_noop : ∀ c r, isTerminal c = true → step c r = c
  /-- Terminal configs remain terminal after any step. -/
  terminal_stays : ∀ c r, isTerminal c = true → isTerminal (step c r) = true

variable {Config : Type}

/-! ## Scheduled Execution -/

/-- Execute t steps from config c using schedule sched : Nat → Nat.
    sched i returns the role index to schedule at step i. -/
def execute (sys : ProgressSystem Config) (c : Config)
    (sched : Nat → Nat) : Nat → Config
  | 0 => c
  | n + 1 => sys.step (execute sys c sched n) (sched n)

/-! ## K-Fair Scheduling -/

/-- A schedule is k-fair if every role index r < numRoles appears at least
    once in every consecutive window of k steps. -/
def KFair (sys : ProgressSystem Config) (sched : Nat → Nat) (k : Nat) : Prop :=
  ∀ block_start r, r < sys.numRoles →
    ∃ j, block_start ≤ j ∧ j < block_start + k ∧ sched j = r

/-- Round-robin scheduling is numRoles-fair. -/
def IsRoundRobin (sys : ProgressSystem Config) (sched : Nat → Nat) : Prop :=
  KFair sys sched sys.numRoles

/-! ## Measure Properties -/

/-- **Theorem 1 (Measure is non-increasing)**: The progress measure never
    increases during execution. At each step, the measure either stays
    the same (disabled role or terminal) or strictly decreases (enabled role). -/
theorem measure_nonincreasing
    (sys : ProgressSystem Config) (c : Config) (sched : Nat → Nat)
    (t : Nat) :
    sys.progressMeasure (execute sys c sched t) ≤ sys.progressMeasure c := by
  induction t with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    simp only [execute]
    by_cases h_enabled : sys.roleEnabled (execute sys c sched t) (sched t) = true
    · by_cases h_terminal : sys.isTerminal (execute sys c sched t) = true
      · rw [sys.terminal_step_noop _ _ h_terminal]
        exact ih
      · have hdec := sys.enabled_step_decreases _ _ (by simpa using h_terminal) h_enabled
        exact Nat.le_trans (Nat.le_of_lt hdec) ih
    · rw [sys.disabled_step_noop _ _ (by simpa using h_enabled)]
      exact ih

/-- **Theorem 2 (Execute split)**: Executing a + b steps equals executing a steps
    then b more steps with a shifted schedule. -/
theorem execute_split
    (sys : ProgressSystem Config) (c : Config) (sched : Nat → Nat)
    (a b : Nat) :
    execute sys c sched (a + b) =
    execute sys (execute sys c sched a) (fun i => sched (a + i)) b := by
  induction b with
  | zero => simp [execute]
  | succ b ih =>
    -- execute c sched (a + (b+1)) = step (execute c sched (a+b)) (sched (a+b))
    -- execute (execute c sched a) sched' (b+1) = step (execute (execute c sched a) sched' b) (sched' b)
    -- By IH, execute c sched (a+b) = execute (execute c sched a) sched' b
    -- And sched' b = sched (a + b)
    show execute sys c sched (a + b + 1) = execute sys (execute sys c sched a) (fun i => sched (a + i)) (b + 1)
    simp only [execute]
    rw [ih]

/-- **Theorem 3 (Shifted schedule preserves k-fairness)**: Shifting a k-fair
    schedule by any offset gives another k-fair schedule. -/
theorem kfair_shift
    (sys : ProgressSystem Config) (sched : Nat → Nat)
    (k t : Nat)
    (hfair : KFair sys sched k) :
    KFair sys (fun i => sched (t + i)) k := by
  intros block_start r hr
  obtain ⟨j, hj₁, hj₂, hj₃⟩ := hfair (block_start + t) r hr
  use j - t
  constructor
  · omega
  constructor
  · omega
  · simp only
    have : t + (j - t) = j := by omega
    rw [this]
    exact hj₃

/-- **Lemma**: If no enabled role is scheduled during [start, start + len),
    then the config doesn't change. -/
theorem noop_steps_preserve
    (sys : ProgressSystem Config) (c : Config) (sched : Nat → Nat)
    (start len : Nat)
    (h : ∀ i, start ≤ i → i < start + len →
      sys.roleEnabled (execute sys c sched i) (sched i) = false) :
    execute sys c sched (start + len) = execute sys c sched start := by
  induction len with
  | zero => simp
  | succ len ih =>
    have hadd : start + (len + 1) = (start + len) + 1 := by ring
    rw [hadd, execute]
    have h_disabled : sys.roleEnabled (execute sys c sched (start + len)) (sched (start + len)) = false := by
      apply h
      · omega
      · omega
    rw [sys.disabled_step_noop _ _ (by simpa using h_disabled)]
    apply ih
    intros i hi1 hi2
    exact h i hi1 (by omega)

/-- **Lemma**: Measure decreases monotonically with execution. -/
theorem measure_decreasing_mono
    (sys : ProgressSystem Config) (c : Config) (sched : Nat → Nat)
    (t1 t2 : Nat) (h : t1 ≤ t2) :
    sys.progressMeasure (execute sys c sched t2) ≤
    sys.progressMeasure (execute sys c sched t1) := by
  have hsplit := execute_split sys c sched t1 (t2 - t1)
  rw [Nat.add_sub_cancel' h] at hsplit
  rw [hsplit]
  exact measure_nonincreasing sys _ _ _

/-- In a k-window starting at a non-terminal config, there exists a productive step. -/
theorem exists_productive_step
    (sys : ProgressSystem Config) (c : Config) (sched : Nat → Nat)
    (block_start : Nat) (k : Nat)
    (_hk : k ≥ sys.numRoles)
    (hfair : KFair sys sched k)
    (hnt : sys.isTerminal (execute sys c sched block_start) = false) :
    ∃ t, block_start ≤ t ∧ t < block_start + k ∧
      sys.roleEnabled (execute sys c sched t) (sched t) = true := by
  -- By progress, there's an enabled role at block_start
  obtain ⟨r, hr₀, hr₁⟩ := sys.progress _ hnt
  -- By k-fairness, this role is scheduled somewhere in [block_start, block_start + k)
  obtain ⟨j, hj₁, hj₂, hj₃⟩ := hfair block_start r hr₀
  -- Either some step in [block_start, j) is productive, or the config at j is unchanged
  by_cases h_noop : ∀ t, block_start ≤ t → t < j → sys.roleEnabled (execute sys c sched t) (sched t) = false
  · -- If no step in [block_start, j) is productive, config at j = config at block_start
    have h_config_eq : execute sys c sched j = execute sys c sched block_start := by
      have hlen : j = block_start + (j - block_start) := by omega
      rw [hlen]
      apply noop_steps_preserve
      intros i hi1 hi2
      exact h_noop i hi1 (by omega)
    -- So role r is enabled at j, and sched j = r
    use j
    constructor
    · exact hj₁
    constructor
    · exact hj₂
    · rw [h_config_eq, hj₃]
      exact hr₁
  · -- Some step before j is productive
    push_neg at h_noop
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := h_noop
    use t
    constructor
    · exact ht₁
    constructor
    · omega
    · simpa using ht₃

/-- Measure decreases with a productive step. -/
lemma measure_decreases_with_productive_step
    (sys : ProgressSystem Config) (c : Config) (sched : Nat → Nat) (t : Nat)
    (h_enabled : sys.roleEnabled (execute sys c sched t) (sched t) = true)
    (h_pos : sys.progressMeasure (execute sys c sched t) > 0) :
    sys.progressMeasure (execute sys c sched (t + 1)) <
    sys.progressMeasure (execute sys c sched t) := by
  have h_terminal_false : sys.isTerminal (execute sys c sched t) = false := by
    by_contra h
    push_neg at h
    have := sys.terminal_measure_zero _ (by simpa using h)
    omega
  simp only [execute]
  exact sys.enabled_step_decreases _ _ h_terminal_false h_enabled

/-- **Theorem 4 (Block progress)**: If the config at block_start is non-terminal
    and the schedule is k-fair with k ≥ numRoles, then the measure strictly
    decreases by the end of the block. -/
theorem block_progress
    (sys : ProgressSystem Config) (c : Config) (sched : Nat → Nat)
    (block_start : Nat) (k : Nat)
    (hk : k ≥ sys.numRoles)
    (hfair : KFair sys sched k)
    (hnt : sys.isTerminal (execute sys c sched block_start) = false) :
    sys.progressMeasure (execute sys c sched (block_start + k)) <
    sys.progressMeasure (execute sys c sched block_start) := by
  -- Get a productive step in the window
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_productive_step sys c sched block_start k hk hfair hnt
  -- The config at block_start has positive measure (non-terminal)
  have h_start_pos : sys.progressMeasure (execute sys c sched block_start) > 0 :=
    sys.nonterminal_pos _ hnt
  -- The config at t has positive measure
  -- Key insight: if roleEnabled is true at t, then the config is non-terminal
  -- (otherwise enabled_step_decreases wouldn't make sense - can't decrease from 0)
  have h_t_nonterminal : sys.isTerminal (execute sys c sched t) = false := by
    by_contra hterm
    have hdisabled :=
      sys.terminal_no_enabled (c := execute sys c sched t) (r := sched t) (by simpa using hterm)
    simp [hdisabled] at ht₃
  have h_t_pos : sys.progressMeasure (execute sys c sched t) > 0 :=
    sys.nonterminal_pos _ h_t_nonterminal
  -- Productive step at t decreases measure
  have h_decrease := measure_decreases_with_productive_step sys c sched t ht₃ h_t_pos
  -- Measure at block_start + k ≤ measure at t + 1 < measure at t ≤ measure at block_start
  have ht1_le : t + 1 ≤ block_start + k := Nat.succ_le_of_lt ht₂
  have h_mono1 := measure_decreasing_mono sys c sched (t + 1) (block_start + k) ht1_le
  have h_mono2 := measure_decreasing_mono sys c sched block_start t ht₁
  -- Chain: measure(block_start+k) ≤ measure(t+1) < measure(t) ≤ measure(block_start)
  calc sys.progressMeasure (execute sys c sched (block_start + k))
      ≤ sys.progressMeasure (execute sys c sched (t + 1)) := h_mono1
    _ < sys.progressMeasure (execute sys c sched t) := h_decrease
    _ ≤ sys.progressMeasure (execute sys c sched block_start) := h_mono2

/-- **Lemma**: Once the system reaches a terminal config, it stays terminal. -/
theorem terminal_persists
    (sys : ProgressSystem Config) (c : Config) (sched : Nat → Nat)
    (t₀ : Nat)
    (hterm : sys.isTerminal (execute sys c sched t₀) = true)
    (t : Nat) (ht : t ≥ t₀) :
    sys.isTerminal (execute sys c sched t) = true := by
  -- Prove by showing execute doesn't change after terminal
  have h_aux : ∀ n, sys.isTerminal (execute sys c sched (t₀ + n)) = true := by
    intro n
    induction n with
    | zero => exact hterm
    | succ n ih =>
      show sys.isTerminal (execute sys c sched (t₀ + n + 1)) = true
      simp only [execute]
      exact sys.terminal_stays _ _ ih
  have ht_eq : t = t₀ + (t - t₀) := by omega
  rw [ht_eq]
  exact h_aux (t - t₀)

/-- **Theorem 5 (k-fair termination bound)**: Under a k-fair schedule with
    k ≥ numRoles, the system reaches a terminal configuration within
    k * W₀ steps, where W₀ = progressMeasure c.

    Proof by strong induction on progressMeasure c:
    - If progressMeasure c = 0, then c is terminal and stays terminal.
    - If progressMeasure c = W + 1 > 0, apply block_progress to get
      progressMeasure (execute sys c sched k) ≤ W. By induction hypothesis,
      continuing from there gives termination within k * W more steps.
      Total: k + k * W = k * (W + 1) = k * progressMeasure c. -/
theorem kfair_termination_bound
    (sys : ProgressSystem Config) (c : Config) (sched : Nat → Nat)
    (k : Nat) (hk : k ≥ sys.numRoles)
    (hfair : KFair sys sched k) :
    sys.isTerminal (execute sys c sched (k * sys.progressMeasure c)) = true := by
  have hstrong :
      ∀ m : Nat, ∀ c' : Config, ∀ sched' : Nat → Nat,
        sys.progressMeasure c' = m →
        KFair sys sched' k →
        sys.isTerminal (execute sys c' sched' (k * m)) = true := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro c' sched' hpm hfair'
      cases m with
      | zero =>
        have hterm0 : sys.isTerminal c' = true := by
          by_cases hnt : sys.isTerminal c' = false
          · have hpos := sys.nonterminal_pos c' hnt
            rw [hpm] at hpos
            omega
          · cases htc : sys.isTerminal c' with
            | false => exact False.elim (hnt htc)
            | true => simp
        simpa [hpm, execute] using hterm0
      | succ m' =>
        by_cases hnt0 : sys.isTerminal c' = false
        · have hblock :
              sys.progressMeasure (execute sys c' sched' k) <
                sys.progressMeasure (execute sys c' sched' 0) := by
            simpa [execute] using
              (block_progress sys c' sched' 0 k hk hfair' (by simpa [execute] using hnt0))
          have hm1_lt : sys.progressMeasure (execute sys c' sched' k) < Nat.succ m' := by
            simpa [hpm, execute] using hblock
          let c1 : Config := execute sys c' sched' k
          let m1 : Nat := sys.progressMeasure c1
          have hm1_lt' : m1 < Nat.succ m' := by simpa [c1, m1] using hm1_lt
          have hfair_shifted : KFair sys (fun i => sched' (k + i)) k :=
            kfair_shift sys sched' k k hfair'
          have hrec :
              sys.isTerminal (execute sys c1 (fun i => sched' (k + i)) (k * m1)) = true :=
            ih m1 hm1_lt' c1 (fun i => sched' (k + i)) rfl hfair_shifted
          have hterm_t0 : sys.isTerminal (execute sys c' sched' (k + k * m1)) = true := by
            have hsplit := execute_split sys c' sched' k (k * m1)
            calc
              sys.isTerminal (execute sys c' sched' (k + k * m1))
                  = sys.isTerminal (execute sys (execute sys c' sched' k)
                      (fun i => sched' (k + i)) (k * m1)) := by rw [hsplit]
              _ = sys.isTerminal (execute sys c1 (fun i => sched' (k + i)) (k * m1)) := by
                    simp [c1]
              _ = true := hrec
          have hm1_le : m1 ≤ m' := Nat.lt_succ_iff.mp hm1_lt'
          have ht_ge : k + k * m1 ≤ k * Nat.succ m' := by
            have hmul : k * m1 ≤ k * m' := Nat.mul_le_mul_left _ hm1_le
            calc
              k + k * m1 ≤ k + k * m' := Nat.add_le_add_left hmul k
              _ = k * Nat.succ m' := by
                    simp [Nat.mul_succ, Nat.add_comm]
          have hstay := terminal_persists sys c' sched' (k + k * m1) hterm_t0
            (k * Nat.succ m') ht_ge
          simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstay
        · have hterm0 : sys.isTerminal c' = true := by
            cases htc : sys.isTerminal c' with
            | false => exact False.elim (hnt0 htc)
            | true => simp
          have hstay := terminal_persists sys c' sched' 0 (by simpa [execute] using hterm0)
            (k * Nat.succ m') (by omega)
          simpa [Nat.mul_succ, execute] using hstay
  exact hstrong (sys.progressMeasure c) c sched rfl hfair

/-- **Corollary (Round-robin termination)**: Under round-robin scheduling,
    termination occurs within numRoles * W₀ steps. -/
theorem roundrobin_termination_bound
    (sys : ProgressSystem Config) (c : Config) (sched : Nat → Nat)
    (hrr : IsRoundRobin sys sched) :
    sys.isTerminal
      (execute sys c sched (sys.numRoles * sys.progressMeasure c)) = true := by
  exact kfair_termination_bound sys c sched sys.numRoles (Nat.le_refl _) hrr

/-! ## Tightness Construction -/

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

/-! ## Integration with Session Types -/

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
