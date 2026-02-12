import Mathlib
import ClassicalAnalysisAPI

/-! # Classical.Families.SpectralGapTermination

Spectral-gap assumptions and reusable termination-rate lemmas for finite-state
Markov chains.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped BigOperators

section

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Classical
namespace SpectralGapTermination

/-- Finite-state Markov chain as a stochastic kernel. -/
structure MarkovChain (State : Type*) [Fintype State] where
  transition : State → State → ℝ
  nonneg : ∀ s s', 0 ≤ transition s s'
  stochastic : ∀ s, ∑ s', transition s s' = 1

variable {State : Type*} [Fintype State] [DecidableEq State]
variable [EntropyAPI.AnalysisModel]

/-! ## Markov Chain and Spectral Quantities -/

/-- Transition matrix over `ℝ`. -/
def transitionMatrix (mc : MarkovChain State) : Matrix State State ℝ :=
  Matrix.of mc.transition

/-- Transition matrix cast to `ℂ` for spectral analysis. -/
def transitionMatrixC (mc : MarkovChain State) : Matrix State State ℂ :=
  EntropyAPI.transitionMatrixComplex mc.transition

/-- Absolute values of nontrivial eigenvalues (`λ ≠ 1`). -/
def nontrivialEigenvalueModuli (mc : MarkovChain State) : Set ℝ :=
  EntropyAPI.nontrivialSpectrumModuli mc.transition

/-- Second-largest eigenvalue in absolute value (real-valued by construction). -/
def secondLargestEigenvalue (mc : MarkovChain State) : ℝ :=
  EntropyAPI.secondSpectrumValue mc.transition

/-- Spectral gap `γ = 1 - |λ₂|`. -/
def spectralGap (mc : MarkovChain State) : ℝ :=
  1 - secondLargestEigenvalue mc

/-- Side condition certifying the spectral gap is nonnegative. -/
def SpectralGapNonneg (mc : MarkovChain State) : Prop :=
  secondLargestEigenvalue mc ≤ 1

theorem spectralGap_nonneg (mc : MarkovChain State) (h : SpectralGapNonneg mc) :
    0 ≤ spectralGap mc := by
  unfold spectralGap SpectralGapNonneg at *
  linarith

/-! ## Conductance and Cheeger Bound -/

/-- Conductance witness used by the Cheeger inequality interface. -/
structure ConductanceWitness (mc : MarkovChain State) where
  Φ : ℝ
  nonneg : 0 ≤ Φ
  upper : Φ ≤ Real.sqrt (2 * spectralGap mc)

/-- Conductance constant extracted from the witness. -/
def conductance (mc : MarkovChain State) (w : ConductanceWitness mc) : ℝ :=
  w.Φ

/-- Cheeger-style lower bound `γ ≥ Φ² / 2` from the witness inequality. -/
theorem cheeger_inequality (mc : MarkovChain State)
    (hGap : 0 ≤ spectralGap mc)
    (w : ConductanceWitness mc) :
    (conductance mc w) ^ 2 / 2 ≤ spectralGap mc := by
  unfold conductance
  have hsqrtNonneg : 0 ≤ Real.sqrt (2 * spectralGap mc) := Real.sqrt_nonneg _
  have hsq : w.Φ ^ 2 ≤ (Real.sqrt (2 * spectralGap mc)) ^ 2 := by
    have hmul :
        w.Φ * w.Φ ≤ (Real.sqrt (2 * spectralGap mc)) * (Real.sqrt (2 * spectralGap mc)) := by
      exact mul_le_mul w.upper w.upper w.nonneg (le_trans w.nonneg w.upper)
    simpa only [pow_two] using hmul
  have hsqrtSplit : (Real.sqrt (2 * spectralGap mc)) ^ 2 =
      (Real.sqrt 2 * Real.sqrt (spectralGap mc)) ^ 2 := by
    have h2 : 0 ≤ (2 : ℝ) := by norm_num
    rw [Real.sqrt_mul h2 (spectralGap mc)]
  have hsqrtSq : (Real.sqrt 2 * Real.sqrt (spectralGap mc)) ^ 2 = 2 * spectralGap mc := by
    calc
      (Real.sqrt 2 * Real.sqrt (spectralGap mc)) ^ 2 =
          (Real.sqrt 2) ^ 2 * (Real.sqrt (spectralGap mc)) ^ 2 := by ring
      _ = (2 : ℝ) * spectralGap mc := by
          rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hGap]
  have hmain : w.Φ ^ 2 ≤ 2 * spectralGap mc := by
    calc
      w.Φ ^ 2 ≤ (Real.sqrt (2 * spectralGap mc)) ^ 2 := hsq
      _ = (Real.sqrt 2 * Real.sqrt (spectralGap mc)) ^ 2 := hsqrtSplit
      _ = 2 * spectralGap mc := hsqrtSq
  nlinarith [hmain]

/-- Side condition certifying strict positivity of the spectral gap. -/
def SpectralGapPos (mc : MarkovChain State) : Prop :=
  secondLargestEigenvalue mc < 1

theorem spectralGap_pos (mc : MarkovChain State) (h : SpectralGapPos mc) :
    0 < spectralGap mc := by
  unfold spectralGap SpectralGapPos at *
  linarith

/-! ## Stationary Distribution Witnesses -/

/-- Probability-distribution predicate on finite states. -/
def IsProbabilityDist (π : State → ℝ) : Prop :=
  (∀ s, 0 ≤ π s) ∧ (∑ s, π s = 1)

/-- Stationarity equation `π P = π`. -/
def IsStationary (mc : MarkovChain State) (π : State → ℝ) : Prop :=
  ∀ s', (∑ s, π s * mc.transition s s') = π s'

/-- Witness packaging an explicit stationary distribution. -/
structure StationaryWitness (mc : MarkovChain State) where
  π : State → ℝ
  prob : IsProbabilityDist π
  stationary : IsStationary mc π

omit [DecidableEq State] in
theorem exists_stationary_dist (mc : MarkovChain State)
    (w : StationaryWitness mc) :
    ∃ π : State → ℝ, IsProbabilityDist π ∧ IsStationary mc π := by
  exact ⟨w.π, w.prob, w.stationary⟩

/-! ## Hitting and Termination Bounds -/

/-- Witness for expected hitting-time bounds from spectral data. -/
structure HittingTimeWitness (mc : MarkovChain State) where
  τ : State → ℝ
  nonneg : ∀ s, 0 ≤ τ s
  bounded_by_gap : ∀ s, τ s ≤ 1 / spectralGap mc

/-- Expected hitting-time function extracted from the witness. -/
def expectedHittingTime {mc : MarkovChain State} (w : HittingTimeWitness mc) : State → ℝ :=
  w.τ

theorem hitting_time_spectral_bound (mc : MarkovChain State)
    (_hGap : 0 < spectralGap mc)
    (w : HittingTimeWitness mc) :
    ∀ s, expectedHittingTime w s ≤ 1 / spectralGap mc := by
  intro s
  exact w.bounded_by_gap s

/-- Witness for expected termination-time bounds. -/
structure TerminationWitness (mc : MarkovChain State)
    extends HittingTimeWitness mc where
  terminal : State → Prop
  zero_on_terminal : ∀ s, terminal s → τ s = 0

/-- Expected termination-time function extracted from the witness. -/
def expectedTerminationTime {mc : MarkovChain State}
    (w : TerminationWitness mc) : State → ℝ :=
  w.τ

theorem expected_termination_bound (mc : MarkovChain State)
    (_hGap : 0 < spectralGap mc)
    (w : TerminationWitness mc) :
    ∀ s, expectedTerminationTime w s ≤ 1 / spectralGap mc := by
  intro s
  exact w.toHittingTimeWitness.bounded_by_gap s

/-! ## Independent Session Composition -/

section IndependentSessions

variable {State₁ : Type*}
variable [Fintype State₁] [DecidableEq State₁]
variable [EntropyAPI.AnalysisModel]

/-- Witness for spectral-gap behavior under independent session composition. -/
structure IndependentSessionsWitness
    [EntropyAPI.AnalysisModel]
    (mc₁ : MarkovChain State₁) (mc₂ : MarkovChain State₁) where
  productChain : MarkovChain (State₁ × State₁)
  gap_lower_bound :
    min (spectralGap (State := State₁) mc₁) (spectralGap (State := State₁) mc₂) ≤
      spectralGap (State := State₁ × State₁) productChain

theorem independent_sessions_spectral_gap
    [EntropyAPI.AnalysisModel]
    (mc₁ : MarkovChain State₁) (mc₂ : MarkovChain State₁)
    (w : IndependentSessionsWitness mc₁ mc₂) :
    min (spectralGap (State := State₁) mc₁) (spectralGap (State := State₁) mc₂) ≤
      spectralGap (State := State₁ × State₁) w.productChain := by
  exact w.gap_lower_bound

end IndependentSessions

end SpectralGapTermination
end Classical
