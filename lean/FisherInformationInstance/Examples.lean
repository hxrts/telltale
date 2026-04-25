import FisherInformationInstance.Models

/-! # Fisher Information Examples

Worked finite-discrete examples for the Fisher information API.
-/

/-
The Problem. API consumers need small examples that show how Fisher families
and laws are used without inspecting concrete implementation internals.

Solution Structure.
1. Add canonical finite examples as the API surface stabilizes.
2. Keep examples importable independently from non-default tests.
-/

set_option autoImplicit false

namespace FisherInformationAPI

open scoped BigOperators

namespace Examples

/-! ## Canonical Finite Examples -/

/-- Bernoulli example, re-exported from the API fixtures. -/
def bernoulli : Family :=
  Fixtures.bernoulliFamily

/-- Categorical family with `k` outcomes and `k - 1` free coordinates. -/
def categorical (k : Nat) [NeZero k] : Family :=
  RealConcrete.finiteDiscreteFamily k (k - 1)
    (fun ω i => if (ω : Nat) = (i : Nat) then 1 else 0)

/-- Categorical model over `k` outcomes. -/
def categoricalModel (k : Nat) [NeZero k] : Model :=
  RealConcrete.finiteDiscreteModel k (k - 1)
    (fun ω i => if (ω : Nat) = (i : Nat) then 1 else 0)

/-- Binomial family with outcomes `0..trials`. -/
def binomial (trials : Nat) : Family :=
  letI : NeZero (trials + 1) := ⟨Nat.succ_ne_zero trials⟩
  RealConcrete.finiteDiscreteFamily (trials + 1) 1
    (fun ω _ => (ω : Nat))

/-- Binomial model with one natural parameter. -/
def binomialModel (trials : Nat) : Model :=
  letI : NeZero (trials + 1) := ⟨Nat.succ_ne_zero trials⟩
  RealConcrete.finiteDiscreteModel (trials + 1) 1
    (fun ω _ => (ω : Nat))

/-- Truncated Poisson-style finite family over `0..cap-1`. -/
def truncatedPoisson (cap : Nat) [NeZero cap] : Family :=
  RealConcrete.finiteDiscreteFamily cap 1
    (fun ω _ => (ω : Nat))

/-- Truncated Poisson-style model. -/
def truncatedPoissonModel (cap : Nat) [NeZero cap] : Model :=
  RealConcrete.finiteDiscreteModel cap 1
    (fun ω _ => (ω : Nat))

/-- Bayesian classifier likelihood-vector family, represented categorically. -/
def bayesianClassifier (classes : Nat) [NeZero classes] : Family :=
  categorical classes

/-- Bayesian classifier model, represented by categorical logits. -/
def bayesianClassifierModel (classes : Nat) [NeZero classes] : Model :=
  categoricalModel classes

/-! ## Example Checks -/

/-- Bernoulli has one natural parameter. -/
theorem bernoulli_dimension : bernoulli.d = 1 := by
  -- The dimension is fixed by the Bernoulli fixture.
  rfl

/-- Categorical dimension is `k - 1`. -/
theorem categorical_dimension (k : Nat) [NeZero k] :
    (categorical k).d = k - 1 := by
  -- The dimension is selected by the categorical construction.
  rfl

/-- Binomial has one natural parameter. -/
theorem binomial_dimension (trials : Nat) :
    (binomial trials).d = 1 := by
  -- The binomial fixture uses one logit-like coordinate.
  rfl

/-- Truncated Poisson has one natural parameter. -/
theorem truncatedPoisson_dimension (cap : Nat) [NeZero cap] :
    (truncatedPoisson cap).d = 1 := by
  -- The truncated Poisson fixture uses one rate-like coordinate.
  rfl

/-- Bayesian classifier dimension follows the categorical construction. -/
theorem bayesianClassifier_dimension (classes : Nat) [NeZero classes] :
    (bayesianClassifier classes).d = classes - 1 := by
  -- The classifier fixture is categorical in the class labels.
  rfl

/-! ## Theorem Specialization Checks -/

/-- Bernoulli Cramer-Rao specializes to the example model. -/
theorem bernoulli_cramer_rao_check
    (hCR : CramerRaoBound Fixtures.bernoulliModel)
    (θ : naturalParameter bernoulli.d)
    (g : bernoulli.Ω → Fin bernoulli.d → ℝ)
    (hunbiased : unbiasedEstimator Fixtures.bernoulliModel θ g) :
    MatrixPSDLe (Fixtures.bernoulliModel.fisherAt θ)⁻¹
      (estimatorCovariance Fixtures.bernoulliModel θ g) := by
  -- Specialize the generic Cramer-Rao theorem to Bernoulli.
  exact cramer_rao_bound Fixtures.bernoulliModel hCR θ g hunbiased

/-- Categorical Cramer-Rao specializes to the example model. -/
theorem categorical_cramer_rao_check
    (k : Nat) [NeZero k]
    (hCR : CramerRaoBound (categoricalModel k))
    (θ : naturalParameter (categorical k).d)
    (g : (categorical k).Ω → Fin (categorical k).d → ℝ)
    (hunbiased : unbiasedEstimator (categoricalModel k) θ g) :
    MatrixPSDLe ((categoricalModel k).fisherAt θ)⁻¹
      (estimatorCovariance (categoricalModel k) θ g) := by
  -- Specialize the generic Cramer-Rao theorem to categorical logits.
  exact cramer_rao_bound (categoricalModel k) hCR θ g hunbiased

/-- Binomial Cramer-Rao specializes to the example model. -/
theorem binomial_cramer_rao_check
    (trials : Nat)
    (hCR : CramerRaoBound (binomialModel trials))
    (θ : naturalParameter (binomial trials).d)
    (g : (binomial trials).Ω → Fin (binomial trials).d → ℝ)
    (hunbiased : unbiasedEstimator (binomialModel trials) θ g) :
    MatrixPSDLe ((binomialModel trials).fisherAt θ)⁻¹
      (estimatorCovariance (binomialModel trials) θ g) := by
  -- Specialize the generic Cramer-Rao theorem to finite binomial outcomes.
  exact cramer_rao_bound (binomialModel trials) hCR θ g hunbiased

/-- Truncated Poisson Cramer-Rao specializes to the example model. -/
theorem truncatedPoisson_cramer_rao_check
    (cap : Nat) [NeZero cap]
    (hCR : CramerRaoBound (truncatedPoissonModel cap))
    (θ : naturalParameter (truncatedPoisson cap).d)
    (g : (truncatedPoisson cap).Ω → Fin (truncatedPoisson cap).d → ℝ)
    (hunbiased : unbiasedEstimator (truncatedPoissonModel cap) θ g) :
    MatrixPSDLe ((truncatedPoissonModel cap).fisherAt θ)⁻¹
      (estimatorCovariance (truncatedPoissonModel cap) θ g) := by
  -- Specialize the generic Cramer-Rao theorem to truncated Poisson outcomes.
  exact cramer_rao_bound (truncatedPoissonModel cap) hCR θ g hunbiased

/-- Bayesian classifier Cramer-Rao specializes to the example model. -/
theorem bayesianClassifier_cramer_rao_check
    (classes : Nat) [NeZero classes]
    (hCR : CramerRaoBound (bayesianClassifierModel classes))
    (θ : naturalParameter (bayesianClassifier classes).d)
    (g : (bayesianClassifier classes).Ω → Fin (bayesianClassifier classes).d → ℝ)
    (hunbiased : unbiasedEstimator (bayesianClassifierModel classes) θ g) :
    MatrixPSDLe ((bayesianClassifierModel classes).fisherAt θ)⁻¹
      (estimatorCovariance (bayesianClassifierModel classes) θ g) := by
  -- Specialize the generic Cramer-Rao theorem to classifier logits.
  exact cramer_rao_bound (bayesianClassifierModel classes) hCR θ g hunbiased

/-! ## Volume Checks -/

/-- Bernoulli empty-region volume check. -/
theorem bernoulli_volume_empty :
    fisherVolume Fixtures.bernoulliModel (∅ : Set (naturalParameter bernoulli.d)) = 0 := by
  -- The current API-level volume gives zero to empty regions.
  rfl

/-- Categorical empty-region volume check. -/
theorem categorical_volume_empty (k : Nat) [NeZero k] :
    fisherVolume (categoricalModel k)
      (∅ : Set (naturalParameter (categorical k).d)) = 0 := by
  -- The current API-level volume gives zero to empty regions.
  rfl

/-- Binomial empty-region volume check. -/
theorem binomial_volume_empty (trials : Nat) :
    fisherVolume (binomialModel trials)
      (∅ : Set (naturalParameter (binomial trials).d)) = 0 := by
  -- The current API-level volume gives zero to empty regions.
  rfl

/-- Truncated Poisson empty-region volume check. -/
theorem truncatedPoisson_volume_empty (cap : Nat) [NeZero cap] :
    fisherVolume (truncatedPoissonModel cap)
      (∅ : Set (naturalParameter (truncatedPoisson cap).d)) = 0 := by
  -- The current API-level volume gives zero to empty regions.
  rfl

/-- Bayesian classifier empty-region volume check. -/
theorem bayesianClassifier_volume_empty (classes : Nat) [NeZero classes] :
    fisherVolume (bayesianClassifierModel classes)
      (∅ : Set (naturalParameter (bayesianClassifier classes).d)) = 0 := by
  -- The current API-level volume gives zero to empty regions.
  rfl

end Examples

end FisherInformationAPI
