import Runtime.Proofs.WeightedMeasure

/-! # Runtime.Proofs.SchedulingBoundCore

Generic k-fair scheduling bounds for abstract progress systems.
-/

/-
The Problem. Derive deterministic k-fair termination bounds from abstract measure/step axioms.

Solution Structure. Define progress systems and fair execution; prove nonincreasing and block-decrease lemmas,
then the `k * W₀` termination theorem.
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

/-! ## Execution Window and Monotonicity Lemmas -/

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

/-! ## Productive-Step Existence -/

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

/-! ## Block Progress -/

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

/-! ## Terminal Persistence -/

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

/-! ## K-Fair Termination Bounds -/

/-! ### Base Case Helper -/

/-- Base case helper: measure `0` implies terminality. -/
private lemma kfair_measure_zero_terminal
    (sys : ProgressSystem Config) (c : Config)
    (hpm : sys.progressMeasure c = 0) :
    sys.isTerminal c = true := by
  by_cases hnt : sys.isTerminal c = false
  · have hpos := sys.nonterminal_pos c hnt
    rw [hpm] at hpos
    omega
  · cases htc : sys.isTerminal c with
    | false => exact False.elim (hnt htc)
    | true => simpa using htc

/-! ### Successor Case Helper -/

/-- Successor case helper for k-fair termination strong induction. -/
private lemma kfair_termination_succ_step
    (sys : ProgressSystem Config) (k : Nat) (hk : k ≥ sys.numRoles)
    (m : Nat) (c' : Config) (sched' : Nat → Nat)
    (hpm : sys.progressMeasure c' = Nat.succ m)
    (hfair' : KFair sys sched' k)
    (hnt0 : sys.isTerminal c' = false)
    (ih :
      ∀ m1, m1 < Nat.succ m → ∀ c1 : Config, ∀ sched1 : Nat → Nat,
        sys.progressMeasure c1 = m1 →
        KFair sys sched1 k →
        sys.isTerminal (execute sys c1 sched1 (k * m1)) = true) :
    sys.isTerminal (execute sys c' sched' (k * Nat.succ m)) = true := by
  have hblock :
      sys.progressMeasure (execute sys c' sched' k) <
        sys.progressMeasure (execute sys c' sched' 0) := by
    simpa [execute] using
      (block_progress sys c' sched' 0 k hk hfair' (by simpa [execute] using hnt0))
  have hm1_lt : sys.progressMeasure (execute sys c' sched' k) < Nat.succ m := by
    simpa [hpm, execute] using hblock
  let c1 : Config := execute sys c' sched' k
  let m1 : Nat := sys.progressMeasure c1
  have hm1_lt' : m1 < Nat.succ m := by simpa [c1, m1] using hm1_lt
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
  have hm1_le : m1 ≤ m := Nat.lt_succ_iff.mp hm1_lt'
  have ht_ge : k + k * m1 ≤ k * Nat.succ m := by
    have hmul : k * m1 ≤ k * m := Nat.mul_le_mul_left _ hm1_le
    calc
      k + k * m1 ≤ k + k * m := Nat.add_le_add_left hmul k
      _ = k * Nat.succ m := by simp [Nat.mul_succ, Nat.add_comm]
  have hstay := terminal_persists sys c' sched' (k + k * m1) hterm_t0
    (k * Nat.succ m) ht_ge
  simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstay

/-! ### Main Bound Theorem -/

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
        have hterm0 : sys.isTerminal c' = true :=
          kfair_measure_zero_terminal sys c' hpm
        simpa [hpm, execute] using hterm0
      | succ m' =>
        by_cases hnt0 : sys.isTerminal c' = false
        · exact
            kfair_termination_succ_step
              sys k hk m' c' sched' hpm hfair' hnt0
              (fun m1 hm1 c1 sched1 hpm1 hfair1 =>
                ih m1 hm1 c1 sched1 hpm1 hfair1)
        · have hterm0 : sys.isTerminal c' = true := by
            cases htc : sys.isTerminal c' with
            | false => exact False.elim (hnt0 htc)
            | true => simpa using htc
          have hstay := terminal_persists sys c' sched' 0
            (by simpa [execute] using hterm0)
            (k * Nat.succ m') (by omega)
          simpa [Nat.mul_succ, execute] using hstay
  exact hstrong (sys.progressMeasure c) c sched rfl hfair

/-! ## Round-Robin Corollary -/

/-- **Corollary (Round-robin termination)**: Under round-robin scheduling,
    termination occurs within numRoles * W₀ steps. -/
theorem roundrobin_termination_bound
    (sys : ProgressSystem Config) (c : Config) (sched : Nat → Nat)
    (hrr : IsRoundRobin sys sched) :
    sys.isTerminal
      (execute sys c sched (sys.numRoles * sys.progressMeasure c)) = true := by
  exact kfair_termination_bound sys c sched sys.numRoles (Nat.le_refl _) hrr


end
