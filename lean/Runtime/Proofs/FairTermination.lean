/-! # Runtime.Proofs.FairTermination

Generic fair-scheduling termination: a ranking measure that never increases,
strictly decreases on every enabled (productive) step, and whose enabledness
survives unproductive steps of other roles, bounds the number of k-fair
scheduler steps before completion by `k * measure`.
-/

/-
The Problem. Termination under fairness must be derived from per-step facts
about the step relation, not assumed as a field of a model.

Solution Structure. `FairRanking` collects only one-step obligations
(monotonicity, strict decrease when enabled, stability of enabledness, and
"not done ⇒ some role enabled"). `fair_window_decrease` shows each k-window
from a non-done state strictly decreases the measure; `fair_termination`
iterates this to the `k * measure` bound.
-/

set_option autoImplicit false

namespace Runtime.Proofs.FairTermination

universe u

variable {State : Type u}

/-- Execute `n` scheduler-indexed steps. -/
def run (step : State → Nat → State) (s₀ : State) (sched : Nat → Nat) : Nat → State
  | 0 => s₀
  | n + 1 => step (run step s₀ sched n) (sched n)

/-- k-fairness over role indices: every role is scheduled in every k-window. -/
def KFair (numRoles k : Nat) (sched : Nat → Nat) : Prop :=
  ∀ blockStart r, r < numRoles → ∃ j, blockStart ≤ j ∧ j < blockStart + k ∧ sched j = r

/-- One-step ranking obligations for a scheduler-indexed step function. -/
structure FairRanking (State : Type u) where
  /-- Number of schedulable roles. -/
  numRoles : Nat
  /-- One step of the scheduled role. -/
  step : State → Nat → State
  /-- Ranking measure. -/
  measure : State → Nat
  /-- Completion predicate. -/
  Done : State → Prop
  /-- Role `r` has an enabled (productive) instruction. -/
  Enabled : State → Nat → Prop
  /-- No step increases the measure. -/
  nonincreasing : ∀ s r, measure (step s r) ≤ measure s
  /-- Running an enabled role strictly decreases the measure. -/
  enabled_decreases : ∀ s r, Enabled s r → measure (step s r) < measure s
  /-- An unproductive step (measure unchanged) does not disable another role. -/
  enabled_stable : ∀ s r r', Enabled s r → measure (step s r') = measure s →
    Enabled (step s r') r
  /-- Progress: a state that is not done has an enabled role. -/
  progress : ∀ s, ¬ Done s → ∃ r, r < numRoles ∧ Enabled s r

namespace FairRanking

variable (R : FairRanking State) (s₀ : State) (sched : Nat → Nat)

/-- The measure is non-increasing along any run. -/
theorem run_mono (a d : Nat) :
    R.measure (run R.step s₀ sched (a + d)) ≤ R.measure (run R.step s₀ sched a) := by
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.le_trans (R.nonincreasing _ _) ih

/-- Helper: from `b`, either the measure already dropped, or it is unchanged
and role `r` is still enabled after `d` steps. -/
theorem drop_or_enabled {b r : Nat} (hEn : R.Enabled (run R.step s₀ sched b) r) (d : Nat) :
    (∃ i, b ≤ i ∧ i < b + d ∧
        R.measure (run R.step s₀ sched (i + 1)) < R.measure (run R.step s₀ sched b)) ∨
      (R.measure (run R.step s₀ sched (b + d)) = R.measure (run R.step s₀ sched b) ∧
        R.Enabled (run R.step s₀ sched (b + d)) r) := by
  induction d with
  | zero => exact Or.inr ⟨rfl, hEn⟩
  | succ d ih =>
    rcases ih with ⟨i, h1, h2, h3⟩ | ⟨hEq, hEnd⟩
    · exact Or.inl ⟨i, h1, by omega, h3⟩
    · have hStep : run R.step s₀ sched (b + (d + 1)) =
          R.step (run R.step s₀ sched (b + d)) (sched (b + d)) := rfl
      by_cases hM : R.measure (run R.step s₀ sched (b + (d + 1))) =
          R.measure (run R.step s₀ sched (b + d))
      · refine Or.inr ⟨hM.trans hEq, ?_⟩
        rw [hStep] at hM ⊢
        exact R.enabled_stable _ _ _ hEnd hM
      · have hLe := R.nonincreasing (run R.step s₀ sched (b + d)) (sched (b + d))
        have hC : R.measure (run R.step s₀ sched (b + (d + 1))) =
            R.measure (R.step (run R.step s₀ sched (b + d)) (sched (b + d))) := by rw [hStep]
        have hlt : R.measure (run R.step s₀ sched (b + d + 1)) <
            R.measure (run R.step s₀ sched b) := by
          show R.measure (R.step (run R.step s₀ sched (b + d)) (sched (b + d))) < _
          omega
        exact Or.inl ⟨b + d, by omega, by omega, hlt⟩

/-- Every k-window starting at a non-done state strictly decreases the measure. -/
theorem fair_window_decrease {k : Nat} (hFair : KFair R.numRoles k sched) (b : Nat)
    (hND : ¬ R.Done (run R.step s₀ sched b)) :
    R.measure (run R.step s₀ sched (b + k)) < R.measure (run R.step s₀ sched b) := by
  obtain ⟨r, hr, hEn⟩ := R.progress _ hND
  obtain ⟨j, hbj, hjk, hsj⟩ := hFair b r hr
  have hDrop : ∃ i, b ≤ i ∧ i < b + k ∧
      R.measure (run R.step s₀ sched (i + 1)) < R.measure (run R.step s₀ sched b) := by
    rcases R.drop_or_enabled s₀ sched hEn (j - b) with ⟨i, h1, h2, h3⟩ | ⟨hEq, hEnj⟩
    · exact ⟨i, h1, by omega, h3⟩
    · have hj : b + (j - b) = j := by omega
      rw [hj] at hEq hEnj
      have hDec := R.enabled_decreases _ _ hEnj
      rw [← hsj] at hDec
      exact ⟨j, hbj, hjk, by
        show R.measure (R.step (run R.step s₀ sched j) (sched j)) < _
        omega⟩
  obtain ⟨i, _, hik, hlt⟩ := hDrop
  have hMono := R.run_mono s₀ sched (i + 1) (b + k - (i + 1))
  rw [show i + 1 + (b + k - (i + 1)) = b + k by omega] at hMono
  omega

/-- Iterated window bound: from step `b` with measure at most `m`, completion
is reached within `k * m` further steps. -/
theorem done_within {k : Nat} (hFair : KFair R.numRoles k sched) (m : Nat) :
    ∀ b, R.measure (run R.step s₀ sched b) ≤ m →
      ∃ n, b ≤ n ∧ n ≤ b + k * m ∧ R.Done (run R.step s₀ sched n) := by
  induction m with
  | zero =>
    intro b hm
    by_cases hD : R.Done (run R.step s₀ sched b)
    · exact ⟨b, Nat.le_refl _, Nat.le_add_right _ _, hD⟩
    · have := R.fair_window_decrease s₀ sched hFair b hD
      omega
  | succ m ih =>
    intro b hm
    by_cases hD : R.Done (run R.step s₀ sched b)
    · exact ⟨b, Nat.le_refl _, Nat.le_add_right _ _, hD⟩
    · have hW := R.fair_window_decrease s₀ sched hFair b hD
      obtain ⟨n, h1, h2, h3⟩ := ih (b + k) (by omega)
      exact ⟨n, by omega, by rw [Nat.mul_succ]; omega, h3⟩

/-- Fair termination: under a k-fair schedule, completion is reached within
`k * measure s₀` steps. -/
theorem fair_termination {k : Nat} (hFair : KFair R.numRoles k sched) :
    ∃ n, n ≤ k * R.measure s₀ ∧ R.Done (run R.step s₀ sched n) := by
  obtain ⟨n, _, h2, h3⟩ := R.done_within s₀ sched hFair (R.measure s₀) 0 (Nat.le_refl _)
  exact ⟨n, by omega, h3⟩

end FairRanking

end Runtime.Proofs.FairTermination
