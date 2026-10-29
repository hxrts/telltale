import FisherInformationAPI.Core

/-! # FisherInformationAPI.Geometry

Model interface, minimality, Legendre duality, KL bridge, and Fisher metric.

Part of the `FisherInformationAPI` boundary (finite-discrete Fisher
information geometry); re-exported by the `FisherInformationAPI` module.
-/

set_option autoImplicit false

namespace FisherInformationAPI

open scoped BigOperators Matrix MatrixOrder
open Asymptotics

noncomputable section

/-! ## Model And Law Predicates -/

/-- Matrix positive semidefiniteness through quadratic forms. -/
def MatrixPSD {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ v : Fin d → ℝ, 0 ≤ ∑ i, ∑ j, v i * A i j * v j

/-- Information-geometric operations selected by a concrete backend. -/
class Model where
  family : Family
  fisherAt : naturalParameter family.d → Matrix (Fin family.d) (Fin family.d) ℝ
  expectationParam : naturalParameter family.d → expectationParameter family.d
  naturalParam : expectationParameter family.d → naturalParameter family.d

/-- Law: Fisher matrices are positive semidefinite. -/
abbrev FisherPSD (M : Model) : Prop :=
  ∀ θ, MatrixPSD (M.fisherAt θ)

/-- Law: selected Fisher implementation agrees with the log-partition Hessian target. -/
abbrev FisherEqHessian (M : Model) : Prop :=
  ∀ θ, M.fisherAt θ = hessianLogPartition M.family θ

/-! ## Minimality And Legendre Duality -/

/-- Natural-to-expectation map given by the log-partition gradient `∇A`. -/
def mappingNaturalToExpectation (F : Family)
    (θ : naturalParameter F.d) : expectationParameter F.d :=
  ⟨gradientLogPartition F θ⟩

/-- Minimal representation: the sufficient statistics are affinely independent
on the support of the base measure. No nonzero direction `v` makes `⟨v, T ω⟩`
constant on the support. Equivalently the Fisher matrix is positive definite,
so `∇A` is injective onto the mean-parameter space. -/
def isMinimal (F : Family) : Prop :=
  ∀ v : Fin F.d → ℝ,
    (∃ c : ℝ, ∀ ω, F.baseMeasureWeight ω ≠ 0 → dot v (F.sufficientStatistic ω) = c) →
      v = 0

/-- Mean-parameter space realized by the model: the image of `expectationParam`. -/
def meanParameterSpace (M : Model) : Set (expectationParameter M.family.d) :=
  Set.range M.expectationParam

/-- Legendre dual potential `A*(μ) = ⟨θ(μ), μ⟩ - A(θ(μ))` at the model inverse. -/
def dualPotential (M : Model) (μ : expectationParameter M.family.d) : ℝ :=
  dot (M.naturalParam μ) μ - logPartition M.family (M.naturalParam μ)

/-- Negative entropy of `p_θ` relative to the base measure, `∑ p log (p / ν)`. -/
def negEntropy (F : Family) (θ : naturalParameter F.d) : ℝ :=
  ∑ ω, density F θ ω * Real.log (density F θ ω / F.baseMeasureWeight ω)

/-- Natural parameters map to expectation parameters through the gradient map. -/
theorem mappingNaturalToExpectation_eq_gradient
    (F : Family) (θ : naturalParameter F.d) :
    mappingNaturalToExpectation F θ = ⟨gradientLogPartition F θ⟩ := by
  -- This pins the public map to the finite-family gradient definition.
  rfl

/-- Law: for minimal families, the model expectation map is `∇A`, and the
model natural map inverts it on the mean-parameter space. -/
abbrev LegendreDuality (M : Model) : Prop :=
  isMinimal M.family →
    (∀ θ, M.expectationParam θ = mappingNaturalToExpectation M.family θ) ∧
      (∀ θ, M.naturalParam (M.expectationParam θ) = θ) ∧
      (∀ μ ∈ meanParameterSpace M, M.expectationParam (M.naturalParam μ) = μ)

/-- Law: for minimal families, the dual potential at `μ = ∇A(θ)` is the
negative entropy of `p_θ`, and it dominates `⟨θ', μ⟩ - A(θ')` for every `θ'`
(so `A*` is the Legendre-Fenchel conjugate of `A`). -/
abbrev DualPotentialEqLegendre (M : Model) : Prop :=
  isMinimal M.family → ∀ θ,
    dualPotential M (M.expectationParam θ) = negEntropy M.family θ ∧
      ∀ θ' : naturalParameter M.family.d, dot θ' (M.expectationParam θ) - logPartition M.family θ' ≤
        dualPotential M (M.expectationParam θ)

/-! ## KL Bridge And Fisher Metric -/

/-- Difference of two natural parameters. -/
def naturalParameterSub {d : ℕ}
    (θ₂ θ₁ : naturalParameter d) : Fin d → ℝ :=
  fun i => θ₂ i - θ₁ i

/-- KL divergence `∑ p₁ log (p₁ / p₂)` between two finite densities. -/
def klDensity (F : Family) (θ₁ θ₂ : naturalParameter F.d) : ℝ :=
  ∑ ω, density F θ₁ ω * Real.log (density F θ₁ ω / density F θ₂ ω)

/-- Closed-form exponential-family KL: the Bregman divergence of `A`,
`A(θ₂) - A(θ₁) - ⟨θ₂ - θ₁, ∇A(θ₁)⟩`. -/
def klClosedForm (M : Model)
    (θ₁ θ₂ : naturalParameter M.family.d) : ℝ :=
  logPartition M.family θ₂ - logPartition M.family θ₁ -
    dot (naturalParameterSub θ₂ θ₁) (gradientLogPartition M.family θ₁)

/-- KL divergence between two parameters through the existing entropy API. -/
def klBetweenParameters [EntropyAPI.Model]
    (M : Model)
    (θ₁ θ₂ : naturalParameter M.family.d) : ℝ :=
  EntropyAPI.klDivergence
    (density M.family θ₁)
    (density M.family θ₂)

/-- The KL bridge is definitionally the entropy API KL on the two densities. -/
theorem klBetweenParameters_agrees_entropy [EntropyAPI.Model]
    (M : Model)
    (θ₁ θ₂ : naturalParameter M.family.d) :
    klBetweenParameters M θ₁ θ₂ =
      EntropyAPI.klDivergence
        (density M.family θ₁)
        (density M.family θ₂) := by
  -- This theorem makes the trust-boundary reuse explicit for downstream users.
  rfl

/-- Law-backed closed form for KL between two natural parameters. -/
theorem klBetweenParameters_closed_form
    [EntropyAPI.Model]
    (M : Model)
    (hKL : ∀ θ₁ θ₂, klBetweenParameters M θ₁ θ₂ = klClosedForm M θ₁ θ₂)
    (θ₁ θ₂ : naturalParameter M.family.d) :
    klBetweenParameters M θ₁ θ₂ = klClosedForm M θ₁ θ₂ := by
  -- The concrete entropy backend supplies `hKL`; the API theorem just exposes it.
  exact hKL θ₁ θ₂

/-- Fisher metric induced by the model-selected Fisher matrix. -/
def fisherMetric (M : Model) (θ : naturalParameter M.family.d)
    (v w : Fin M.family.d → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * M.fisherAt θ i j * w j

/-- Fisher PSD immediately gives nonnegative squared Fisher length. -/
theorem fisherMetric_psd_of_fisherPSD
    (M : Model) (hPSD : FisherPSD M)
    (θ : naturalParameter M.family.d) (v : Fin M.family.d → ℝ) :
    0 ≤ fisherMetric M θ v v := by
  -- The metric was chosen to share the same quadratic-form shape as `MatrixPSD`.
  exact hPSD θ v

/-- Law: KL between the parameter densities equals the Bregman closed form. -/
abbrev KLClosedForm (M : Model) : Prop :=
  ∀ θ₁ θ₂, klDensity M.family θ₁ θ₂ = klClosedForm M θ₁ θ₂

/-- Law: KL between parameters is nonnegative. -/
abbrev KLNonneg (M : Model) : Prop :=
  ∀ θ₁ θ₂, 0 ≤ klClosedForm M θ₁ θ₂

/-- Law: zero KL characterizes equal parameters under minimality. -/
abbrev KLZeroIffEqualParameters (M : Model) : Prop :=
  isMinimal M.family →
    ∀ θ₁ θ₂, klClosedForm M θ₁ θ₂ = 0 ↔ θ₁ = θ₂

/-- Law: KL has the Fisher metric as its second-order leading term.

Along every direction `δ`,
`KL(p_θ ‖ p_{θ+tδ}) = (t²/2) · δᵀ I(θ) δ + o(t²)` as `t → 0`, where KL is the
exponential-family closed form (which uses the model's expectation map). -/
abbrev KLSecondOrderTaylor (M : Model) : Prop :=
  ∀ (θ : naturalParameter M.family.d) (δ : Fin M.family.d → ℝ),
    (fun t : ℝ => klClosedForm M θ (perturbParameter θ t δ) -
        t ^ 2 / 2 * fisherMetric M θ δ δ) =o[nhds 0] (fun t : ℝ => t ^ 2)

/-- Law-backed second-order KL/Fisher leading-term theorem. -/
theorem kl_second_order_taylor_of_law
    (M : Model) (hTaylor : KLSecondOrderTaylor M)
    (θ : naturalParameter M.family.d) (δ : Fin M.family.d → ℝ) :
    (fun t : ℝ => klClosedForm M θ (perturbParameter θ t δ) -
        t ^ 2 / 2 * fisherMetric M θ δ δ) =o[nhds 0] (fun t : ℝ => t ^ 2) := by
  -- The analytic statement is supplied by the selected law witness.
  exact hTaylor θ δ

/-- Law: the Fisher metric is symmetric. -/
abbrev FisherMetricSymmetric (M : Model) : Prop :=
  ∀ θ v w, fisherMetric M θ v w = fisherMetric M θ w v

/-- Law: the Fisher metric is positive semidefinite. -/
abbrev FisherMetricPSD (M : Model) : Prop :=
  ∀ θ v, 0 ≤ fisherMetric M θ v v

end

end FisherInformationAPI
