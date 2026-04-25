import FisherInformationInstance.Examples
import FisherInformationInstance.TheoremPack

/-! # Fisher Information Acceptance Tests

Non-default acceptance checks for the Fisher information API.
-/

/-
The Problem. Public Fisher information operations need lightweight compile-time
checks that downstream users can run explicitly.

Solution Structure.
1. Import the worked examples.
2. Add `example` and `#guard` checks as public operations are introduced.
-/

set_option autoImplicit false

namespace FisherInformationAPI

open scoped BigOperators

namespace Tests

/-! ## Bernoulli API Checks -/

example :
    Fixtures.bernoulliFamily.d = 1 := by
  -- Bernoulli has one natural coordinate.
  rfl

example (θ : naturalParameter Fixtures.bernoulliFamily.d) :
    logPartition Fixtures.bernoulliFamily θ =
      Real.log (1 + Real.exp (θ Fixtures.bernoulliIndex)) := by
  -- Public Bernoulli log-partition fixture.
  simpa [Fixtures.bernoulliIndex] using
    Fixtures.bernoulli_logPartition_eq θ

example (θ : naturalParameter Fixtures.bernoulliFamily.d) :
    fisherInformation Fixtures.bernoulliFamily θ
      Fixtures.bernoulliIndex Fixtures.bernoulliIndex =
        Fixtures.bernoulliSigmoid θ * (1 - Fixtures.bernoulliSigmoid θ) := by
  -- Public Bernoulli Fisher-variance fixture.
  exact Fixtures.bernoulli_fisherInformation_eq_variance θ

example (μ : expectationParameter Fixtures.bernoulliFamily.d)
    (h0 : 0 < μ Fixtures.bernoulliIndex)
    (h1 : μ Fixtures.bernoulliIndex < 1) :
    Fixtures.bernoulliModel.expectationParam
      (Fixtures.bernoulliModel.naturalParam μ) = μ := by
  -- Public Bernoulli sigmoid/logit round trip.
  exact Fixtures.bernoulli_sigmoid_logit μ h0 h1

/-! ## Laws Access Checks -/

example [Laws] :
    FisherPSD (Laws.toModel (self := inferInstance)) :=
  fisher_psd

example [Laws] :
    NaturalGradientExists (Laws.toModel (self := inferInstance)) :=
  natural_gradient_exists

example :
    Model := finiteDiscreteModel

example :
    Laws := finiteDiscreteLaws

/-! ## Theorem-Pack Checks -/

example :
    TheoremPack.FisherTheoremPack finiteDiscreteModel :=
  TheoremPack.buildFisherTheoremPack finiteDiscreteModel

example :
    TheoremPack.DOptimalDesignArtifact finiteDiscreteModel :=
  TheoremPack.dOptimalDesignArtifact finiteDiscreteModel

example :
    ∃ idx : Fin 1,
      ∀ j : Fin 1,
        TheoremPack.fisherDeterminant finiteDiscreteModel
            ((fun _ : Fin 1 =>
              (⟨fun i => Fin.elim0 i⟩ :
                naturalParameter finiteDiscreteModel.family.d)) j) ≤
          TheoremPack.fisherDeterminant finiteDiscreteModel
            ((fun _ : Fin 1 =>
              (⟨fun i => Fin.elim0 i⟩ :
                naturalParameter finiteDiscreteModel.family.d)) idx) := by
  -- The finite D-optimal theorem produces a maximizer for indexed designs.
  exact TheoremPack.dOptimalDesign_exists finiteDiscreteModel
    (fun _ : Fin 1 =>
      (⟨fun i => Fin.elim0 i⟩ :
        naturalParameter finiteDiscreteModel.family.d))

end Tests

end FisherInformationAPI
