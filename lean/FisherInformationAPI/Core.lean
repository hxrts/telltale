import Mathlib
import ClassicalAnalysisAPI

/-! # FisherInformationAPI.Core

Finite exponential families, parameter coordinates, density, score, Fisher
information, log-partition Hessian, and score mean identities.

Part of the `FisherInformationAPI` boundary (finite-discrete Fisher
information geometry); re-exported by the `FisherInformationAPI` module.
-/

set_option autoImplicit false

namespace FisherInformationAPI

open scoped BigOperators Matrix MatrixOrder
open Asymptotics

noncomputable section

/-! ## Finite Families -/

/-- A finite-discrete exponential-family presentation.

The two base-measure side conditions are structural, not laws: they are exactly
what makes the normalized density nonnegative and total to one. -/
structure Family where
  Ω : Type*
  omegaFinite : Fintype Ω
  omegaDecEq : DecidableEq Ω
  d : ℕ
  sufficientStatistic : Ω → Fin d → ℝ
  baseMeasureWeight : Ω → ℝ
  baseMeasureWeight_nonneg : ∀ ω, 0 ≤ baseMeasureWeight ω
  baseMeasureWeight_exists_pos : ∃ ω, 0 < baseMeasureWeight ω

attribute [instance] Family.omegaFinite Family.omegaDecEq

/-! ## Parameter Coordinates -/

/-- Natural coordinates `θ`; wrapped to keep the semantic role visible. -/
structure naturalParameter (d : ℕ) where
  coord : Fin d → ℝ

/-- Expectation coordinates `μ`; same shape as natural coordinates but distinct. -/
structure expectationParameter (d : ℕ) where
  coord : Fin d → ℝ

instance {d : ℕ} : CoeFun (naturalParameter d) (fun _ => Fin d → ℝ) where
  coe θ := θ.coord

instance {d : ℕ} : CoeFun (expectationParameter d) (fun _ => Fin d → ℝ) where
  coe μ := μ.coord

@[ext]
theorem naturalParameter_ext {d : ℕ} {θ η : naturalParameter d}
    (h : ∀ i, θ i = η i) : θ = η := by
  -- Extensionality reduces equality of wrapped coordinates to pointwise equality.
  cases θ
  cases η
  congr
  exact funext h

@[ext]
theorem expectationParameter_ext {d : ℕ} {μ ν : expectationParameter d}
    (h : ∀ i, μ i = ν i) : μ = ν := by
  -- The expectation-coordinate wrapper has the same extensionality principle.
  cases μ
  cases ν
  congr
  exact funext h

/-! ## Exponential Family Density -/

/-- Finite-dimensional dot product. -/
def dot {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  ∑ i, x i * y i

/-- Unnormalized partition summand for one outcome. -/
def partitionTerm (F : Family) (θ : naturalParameter F.d) (ω : F.Ω) : ℝ :=
  F.baseMeasureWeight ω * Real.exp (dot θ (F.sufficientStatistic ω))

/-- The positive finite partition sum before applying logarithm. -/
def partitionSum (F : Family) (θ : naturalParameter F.d) : ℝ :=
  ∑ ω, partitionTerm F θ ω

/-- The log-partition function `A(θ) = log ∑ω ν(ω) exp(⟨θ,Tω⟩)`. -/
def logPartition (F : Family) (θ : naturalParameter F.d) : ℝ :=
  Real.log (partitionSum F θ)

/-- Exponential-family density normalized by `exp (logPartition F θ)`. -/
def density (F : Family) (θ : naturalParameter F.d) (ω : F.Ω) : ℝ :=
  partitionTerm F θ ω / Real.exp (logPartition F θ)

/-- Expectations under the finite density at `θ`. -/
def expectationOf (F : Family) (θ : naturalParameter F.d) (f : F.Ω → ℝ) : ℝ :=
  ∑ ω, density F θ ω * f ω

/-! ## Score And Fisher Information -/

/-- Expected sufficient statistic, the finite-family gradient target. -/
def expectedStatistic (F : Family) (θ : naturalParameter F.d) (i : Fin F.d) : ℝ :=
  expectationOf F θ (fun ω => F.sufficientStatistic ω i)

/-- Formal log-partition gradient used by the finite exponential-family API. -/
def gradientLogPartition (F : Family) (θ : naturalParameter F.d) : Fin F.d → ℝ :=
  expectedStatistic F θ

/-- Score vector `T(ω) - ∇A(θ)` for a finite exponential family. -/
def score (F : Family) (θ : naturalParameter F.d) (ω : F.Ω) : Fin F.d → ℝ :=
  fun i => F.sufficientStatistic ω i - gradientLogPartition F θ i

/-- The score definition is the statistic-minus-gradient formula. -/
theorem score_eq_statistic_sub_gradient
    (F : Family) (θ : naturalParameter F.d) (ω : F.Ω) :
    score F θ ω =
      fun i => F.sufficientStatistic ω i - gradientLogPartition F θ i := by
  -- The theorem pins the public formula to the implementation definition.
  rfl

/-- Fisher information as the covariance matrix of the score. -/
def fisherInformation (F : Family) (θ : naturalParameter F.d) :
    Matrix (Fin F.d) (Fin F.d) ℝ :=
  fun i j => expectationOf F θ (fun ω => score F θ ω i * score F θ ω j)

/-- The natural parameter `θ + t • δ` along a direction `δ`. -/
def perturbParameter {d : ℕ} (θ : naturalParameter d) (t : ℝ)
    (δ : Fin d → ℝ) : naturalParameter d :=
  ⟨fun i => θ i + t * δ i⟩

/-- Coordinate basis vector `e_i` in natural coordinates. -/
def basisVector {d : ℕ} (i : Fin d) : Fin d → ℝ :=
  Pi.single i 1

/-- Second partial derivative `∂²A / ∂θ_i ∂θ_j` of the log-partition at `θ`,
computed with real one-variable derivatives along coordinate directions. -/
def hessianLogPartition (F : Family) (θ : naturalParameter F.d) :
    Matrix (Fin F.d) (Fin F.d) ℝ :=
  fun i j => deriv (fun s => deriv (fun t => logPartition F
    (perturbParameter (perturbParameter θ s (basisVector j)) t (basisVector i))) 0) 0

/-! ## Density Normalization -/

/-- Every partition summand is nonnegative. -/
theorem partitionTerm_nonneg (F : Family) (θ : naturalParameter F.d) (ω : F.Ω) :
    0 ≤ partitionTerm F θ ω := by
  -- Nonnegative base mass times a positive exponential is nonnegative.
  exact mul_nonneg (F.baseMeasureWeight_nonneg ω) (le_of_lt (Real.exp_pos _))

/-- The finite partition sum is strictly positive. -/
theorem partitionSum_pos (F : Family) (θ : naturalParameter F.d) :
    0 < partitionSum F θ := by
  -- One positive base weight contributes a strictly positive summand.
  rcases F.baseMeasureWeight_exists_pos with ⟨ω0, hω0⟩
  rw [partitionSum]
  exact Finset.sum_pos'
    (fun ω _ => partitionTerm_nonneg F θ ω)
    ⟨ω0, Finset.mem_univ ω0, mul_pos hω0 (Real.exp_pos _)⟩

/-- Densities are nonnegative pointwise. -/
theorem density_nonneg (F : Family) (θ : naturalParameter F.d) (ω : F.Ω) :
    0 ≤ density F θ ω := by
  -- Normalization divides a nonnegative numerator by a positive denominator.
  exact div_nonneg
    (partitionTerm_nonneg F θ ω)
    (le_of_lt (Real.exp_pos _))

/-- The density over a finite family sums to one. -/
theorem density_sum_one (F : Family) (θ : naturalParameter F.d) :
    ∑ ω, density F θ ω = 1 := by
  -- Pull out the constant normalizer and cancel it with the partition sum.
  have hZ : 0 < partitionSum F θ := partitionSum_pos F θ
  calc
    ∑ ω, density F θ ω
        = (∑ ω, partitionTerm F θ ω) / Real.exp (logPartition F θ) := by
          simp [density, div_eq_mul_inv, Finset.sum_mul]
    _ = partitionSum F θ / Real.exp (logPartition F θ) := by
          rfl
    _ = partitionSum F θ / partitionSum F θ := by
          rw [logPartition, Real.exp_log hZ]
    _ = 1 := by
          exact div_self (ne_of_gt hZ)

/-! ## Score Mean Identities -/

/-- Each coordinate of the score has expectation zero. -/
theorem expectedScoreCoordZero
    (F : Family) (θ : naturalParameter F.d) (i : Fin F.d) :
    expectationOf F θ (fun ω => score F θ ω i) = 0 := by
  -- Expand the centered statistic and cancel its mean using density normalization.
  let μ : ℝ := expectedStatistic F θ i
  have hμ : μ = expectationOf F θ (fun ω => F.sufficientStatistic ω i) := rfl
  have hconst :
      (∑ ω, density F θ ω * μ) = μ * (∑ ω, density F θ ω) := by
    -- Pull the constant mean out of the finite sum.
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _hω
    ring
  calc
    expectationOf F θ (fun ω => score F θ ω i)
        = ∑ ω, density F θ ω *
            (F.sufficientStatistic ω i - μ) := by
          simp [expectationOf, score, gradientLogPartition, expectedStatistic, hμ]
    _ = (∑ ω, density F θ ω * F.sufficientStatistic ω i) -
          (∑ ω, density F θ ω * μ) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro ω _hω
          ring
    _ = expectationOf F θ (fun ω => F.sufficientStatistic ω i) -
          μ * (∑ ω, density F θ ω) := by
          rw [hconst]
          rfl
    _ = μ - μ * (∑ ω, density F θ ω) := by
          rw [← hμ]
    _ = 0 := by
          rw [density_sum_one]
          ring

/-- The score has zero expectation in every finite direction. -/
theorem expectedScoreZero
    (F : Family) (θ : naturalParameter F.d) (v : Fin F.d → ℝ) :
    expectationOf F θ (fun ω => dot v (score F θ ω)) = 0 := by
  -- Exchange finite sums explicitly, then use coordinate score zero-mean.
  calc
    expectationOf F θ (fun ω => dot v (score F θ ω))
        = ∑ i, v i * expectationOf F θ (fun ω => score F θ ω i) := by
          simp only [expectationOf, dot]
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _hi
          apply Finset.sum_congr rfl
          intro ω _hω
          ring
    _ = 0 := by
          simp [expectedScoreCoordZero]

end

end FisherInformationAPI
