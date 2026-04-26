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

open scoped BigOperators Matrix MatrixOrder

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

/-- One-dimensional zero PSD increment for log-det API checks. -/
def zeroCertificatePSDIncrement : CertificatePSDIncrement 1 where
  matrix := 0
  psd := Matrix.PosSemidef.zero
  logdetGain := 0
  logdetGain_nonneg := by norm_num

example :
    (1 : ℝ) ≤
      (1 + (0 : Matrix (Fin 1) (Fin 1) ℝ)).det := by
  -- The matrix-analysis determinant monotonicity support lemma is exported.
  exact matrix_det_one_add_posSemidef_ge_one
    (0 : Matrix (Fin 1) (Fin 1) ℝ) Matrix.PosSemidef.zero

example :
    (1 : Matrix (Fin 1) (Fin 1) ℝ).det ≤
      ((1 : Matrix (Fin 1) (Fin 1) ℝ) +
        (0 : Matrix (Fin 1) (Fin 1) ℝ)).det := by
  -- Loewner determinant monotonicity is available without an external backend contract.
  exact matrix_det_monotone_under_psd_addition
    (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (0 : Matrix (Fin 1) (Fin 1) ℝ)
    Matrix.PosDef.one Matrix.PosSemidef.zero

example :
    Real.log (1 : Matrix (Fin 1) (Fin 1) ℝ).det ≤
      Real.log
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) +
          (0 : Matrix (Fin 1) (Fin 1) ℝ)).det := by
  -- Log-det monotonicity now follows from the checked determinant proof.
  exact matrix_logdet_monotone_under_psd_addition
    (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (0 : Matrix (Fin 1) (Fin 1) ℝ)
    Matrix.PosDef.one Matrix.PosSemidef.zero

example :
    Real.log (1 : Matrix (Fin 1) (Fin 1) ℝ).det ≤
      Real.log
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) +
          ∑ i ∈ (Finset.univ : Finset (Fin 1)),
            (fun _ : Fin 1 => (0 : Matrix (Fin 1) (Fin 1) ℝ)) i).det := by
  -- Finite sums of PSD increments are covered by the matrix log-det surface.
  exact matrix_logdet_monotone_under_psd_finset_sum
    (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (fun _ : Fin 1 => (0 : Matrix (Fin 1) (Fin 1) ℝ))
    Finset.univ Matrix.PosDef.one
    (by intro i hi; exact Matrix.PosSemidef.zero)

example :
    (weightedRankOnePSDIncrement (0 : ℝ)
      (fun _ : Fin 1 => (1 : ℝ))).PosSemidef := by
  -- Weighted rank-one increments expose the D-optimal design increment shape.
  exact weightedRankOnePSDIncrement_posSemidef
    (0 : ℝ) (fun _ : Fin 1 => (1 : ℝ)) (by norm_num)

example :
    certificateMatrixLogdetObjective
        (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (fun _ : Fin 1 => zeroCertificatePSDIncrement) Finset.univ ≤
      certificateMatrixLogdetObjective
        (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (fun _ : Fin 1 => zeroCertificatePSDIncrement) Finset.univ := by
  -- Matrix-backed certificate objectives inherit the proved PSD-sum monotonicity.
  exact certificate_matrix_logdet_objective_monotone
    (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (fun _ : Fin 1 => zeroCertificatePSDIncrement)
    Matrix.PosDef.one
    (by intro i hi; exact hi)

example :
    certificateLogdetObjective 0
        (fun _ : Fin 1 => zeroCertificatePSDIncrement) Finset.univ ≤
      certificateLogdetObjective 0
        (fun _ : Fin 1 => zeroCertificatePSDIncrement) Finset.univ := by
  -- The monotonicity theorem is available to downstream theorem packs.
  exact certificate_logdet_objective_monotone 0
    (fun _ : Fin 1 => zeroCertificatePSDIncrement)
    (by intro i hi; exact hi)

example :
    certificateLogdetMarginal
        (fun _ : Fin 1 => zeroCertificatePSDIncrement)
        Finset.univ 0 ≤
      certificateLogdetMarginal
        (fun _ : Fin 1 => zeroCertificatePSDIncrement)
        Finset.univ 0 := by
  -- The diminishing-returns theorem compiles on the finite API fixture.
  exact certificate_logdet_objective_submodular
    (fun _ : Fin 1 => zeroCertificatePSDIncrement)
    (by intro i hi; exact hi) 0

example :
    Real.log
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) +
          weightedRankOnePSDIncrement 0 (fun _ : Fin 1 => (1 : ℝ))).det -
        Real.log (1 : Matrix (Fin 1) (Fin 1) ℝ).det ≤
      Real.log
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) +
          weightedRankOnePSDIncrement 0 (fun _ : Fin 1 => (1 : ℝ))).det -
        Real.log (1 : Matrix (Fin 1) (Fin 1) ℝ).det := by
  -- Matrix log-det rank-one marginals are antitone in the Loewner base order.
  exact matrix_logdet_rank_one_marginal_antitone
    (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (1 : Matrix (Fin 1) (Fin 1) ℝ)
    0 (fun _ : Fin 1 => (1 : ℝ))
    Matrix.PosDef.one Matrix.PosDef.one
    (le_refl _) (by norm_num)

example :
    Real.log
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) +
          ∑ i ∈ insert 0 (∅ : Finset (Fin 1)),
            weightedRankOnePSDIncrement
              ((fun _ : Fin 1 => (0 : ℝ)) i)
              ((fun _ : Fin 1 => fun _ : Fin 1 => (1 : ℝ)) i)).det -
        Real.log
          ((1 : Matrix (Fin 1) (Fin 1) ℝ) +
            ∑ i ∈ (∅ : Finset (Fin 1)),
              weightedRankOnePSDIncrement
                ((fun _ : Fin 1 => (0 : ℝ)) i)
                ((fun _ : Fin 1 => fun _ : Fin 1 => (1 : ℝ)) i)).det ≤
      Real.log
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) +
          ∑ i ∈ insert 0 (∅ : Finset (Fin 1)),
            weightedRankOnePSDIncrement
              ((fun _ : Fin 1 => (0 : ℝ)) i)
              ((fun _ : Fin 1 => fun _ : Fin 1 => (1 : ℝ)) i)).det -
        Real.log
          ((1 : Matrix (Fin 1) (Fin 1) ℝ) +
            ∑ i ∈ (∅ : Finset (Fin 1)),
              weightedRankOnePSDIncrement
                ((fun _ : Fin 1 => (0 : ℝ)) i)
                ((fun _ : Fin 1 => fun _ : Fin 1 => (1 : ℝ)) i)).det := by
  -- Finite selected-set matrix log-det submodularity is exported.
  exact matrix_logdet_submodular_under_psd_increment
    (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (fun _ : Fin 1 => (0 : ℝ))
    (fun _ : Fin 1 => fun _ : Fin 1 => (1 : ℝ))
    (S := (∅ : Finset (Fin 1)))
    (T := (∅ : Finset (Fin 1)))
    0
    Matrix.PosDef.one
    (by intro i; norm_num)
    (by intro i hi; exact hi)
    (by simp)

example :
    (fun _ : Finset (Fin 1) => (0 : ℝ)) Finset.univ *
        EntropyAPI.classicalGreedyApproximationPermille ≤
      (fun _ : Finset (Fin 1) => (0 : ℝ)) Finset.univ * 1000 := by
  -- The 632-permille greedy approximation corollary is exported upstream.
  exact EntropyAPI.nemhauser_wolsey_fisher_greedy_approximation_permille
    (fun _ : Finset (Fin 1) => (0 : ℝ)) Finset.univ Finset.univ
    (le_refl _) (le_refl _)

example :
    (1 - (Real.exp 1)⁻¹) *
        (fun _ : Finset (Fin 1) => (0 : ℝ)) Finset.univ ≤
      (fun _ : Finset (Fin 1) => (0 : ℝ))
        ((fun _ : Nat => Finset.univ) 1) := by
  -- Cardinality-constrained NWF set-function form is exported upstream.
  exact EntropyAPI.nemhauser_wolsey_fisher_cardinality_constrained_set_greedy_approximation_full
    (fun _ : Finset (Fin 1) => (0 : ℝ))
    (fun _ : Nat => Finset.univ)
    Finset.univ
    1
    (by intro S T hST; simp)
    (by intro S T hST a ha; simp)
    (by simp)
    (by norm_num)
    (by simp)
    (by simp)
    (by intro i hi a ha; exact Finset.mem_univ a)
    (by intro i hi; simp)

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
