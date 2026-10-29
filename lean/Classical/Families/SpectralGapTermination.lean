import Mathlib
import ClassicalAnalysisAPI

/-! # Classical.Families.SpectralGapTermination

Spectral-gap vocabulary for finite-state Markov chains, packaged as an honest
conditional interface (Option B).

**What is proved here.** Only elementary algebra: nonnegativity/positivity of
`spectralGap` from the stated side conditions, and the squaring step that turns
an assumed bound `Φ ≤ √(2γ)` into `Φ² / 2 ≤ γ`.

**What is assumed, not proved.** Every classical spectral result (Cheeger's
inequality, existence of a stationary distribution, hitting/termination times
bounded by `1 / γ`, product-chain gap bounds) enters only as a field of a
`*Witness` structure supplied by the caller. Nothing in this module relates the
witness quantities to the transition kernel; in particular `ConductanceWitness.Φ`
is *not* defined as the conductance (bottleneck ratio) of the chain. A genuine
proof would need: the variational (Dirichlet-form) characterisation of the gap
of a reversible chain, the definition of conductance as a minimum over cuts,
and the Cheeger/Jerrum-Sinclair argument; Perron-Frobenius for stationarity;
and a spectral-decomposition bound on expected hitting times.
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

/-- `γ ≥ 0` from the side condition `|λ₂| ≤ 1` (definitional unfolding). -/
theorem spectral_gap_nonneg (mc : MarkovChain State) (h : SpectralGapNonneg mc) :
    0 ≤ spectralGap mc := by
  unfold spectralGap SpectralGapNonneg at *
  linarith

/-! ## Conductance and Cheeger Bound -/

/-- Assumed Cheeger-type input. `Φ` is an arbitrary real number; the field
`upper : Φ ≤ √(2γ)` *is* the (assumed) Cheeger upper bound. `Φ` is never tied
to the cut-based conductance of `mc`; a real Cheeger inequality would define
`Φ` from the kernel and prove `upper`. -/
structure ConductanceWitness (mc : MarkovChain State) where
  Φ : ℝ
  nonneg : 0 ≤ Φ
  upper : Φ ≤ Real.sqrt (2 * spectralGap mc)

/-- The `Φ` value carried by an assumed `ConductanceWitness` (not computed from `mc`). -/
def conductance (mc : MarkovChain State) (w : ConductanceWitness mc) : ℝ :=
  w.Φ

/-- Conditional Cheeger-style lower bound: *assuming* `0 ≤ Φ ≤ √(2γ)` (the
witness fields), squaring yields `Φ² / 2 ≤ γ`. This is only the algebraic
squaring step; the analytic content of Cheeger's inequality is the assumption. -/
theorem cheeger_bound_of_conductance_witness (mc : MarkovChain State)
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

/-- `γ > 0` from the side condition `|λ₂| < 1` (definitional unfolding). -/
theorem spectral_gap_pos (mc : MarkovChain State) (h : SpectralGapPos mc) :
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

/-- Assumed input: an explicit stationary distribution supplied by the caller.
Use the fields directly; existence is not derived from the kernel here (that
would require Perron-Frobenius / a compactness argument). -/
structure StationaryWitness (mc : MarkovChain State) where
  π : State → ℝ
  prob : IsProbabilityDist π
  stationary : IsStationary mc π

/-! ## Hitting and Termination Bounds -/

/-- Assumed input: a nonnegative function `τ` with `τ s ≤ 1 / γ`. The bound
`bounded_by_gap` is the assumed classical result; `τ` is not defined as an
expected hitting time of `mc`. A real proof would define `τ` as the expectation
of the hitting time and bound it through the spectral decomposition of `P`. -/
structure HittingTimeWitness (mc : MarkovChain State) where
  τ : State → ℝ
  nonneg : ∀ s, 0 ≤ τ s
  bounded_by_gap : ∀ s, τ s ≤ 1 / spectralGap mc

/-- The `τ` function carried by an assumed `HittingTimeWitness`. -/
def expectedHittingTime {mc : MarkovChain State} (w : HittingTimeWitness mc) : State → ℝ :=
  w.τ

/-- Assumed input: a `HittingTimeWitness` (so `τ ≤ 1 / γ` is assumed) that
also vanishes on a caller-chosen terminal predicate. -/
structure TerminationWitness (mc : MarkovChain State)
    extends HittingTimeWitness mc where
  terminal : State → Prop
  zero_on_terminal : ∀ s, terminal s → τ s = 0

/-- The `τ` function carried by an assumed `TerminationWitness`. -/
def expectedTerminationTime {mc : MarkovChain State}
    (w : TerminationWitness mc) : State → ℝ :=
  w.τ

/-! ## Independent Session Composition -/

section IndependentSessions

variable {State₁ : Type*}
variable [Fintype State₁] [DecidableEq State₁]
variable [EntropyAPI.AnalysisModel]

/-- Assumed input: some chain on the product space whose gap is at least the
minimum of the two factor gaps. `productChain` is not required to be the
tensor product of `mc₁` and `mc₂`; a real result would construct the product
kernel and compute its spectrum. -/
structure IndependentSessionsWitness
    [EntropyAPI.AnalysisModel]
    (mc₁ : MarkovChain State₁) (mc₂ : MarkovChain State₁) where
  productChain : MarkovChain (State₁ × State₁)
  gap_lower_bound :
    min (spectralGap (State := State₁) mc₁) (spectralGap (State := State₁) mc₂) ≤
      spectralGap (State := State₁ × State₁) productChain

end IndependentSessions

end SpectralGapTermination
end Classical
