import FisherInformationInstance.Examples

/-! # Fisher Information Theorem Pack

Stretch theorem artifacts for finite-discrete Fisher information geometry.
-/

/-
The Problem. The Fisher core API should stay small, but downstream consumers
also want optional theorem families: tight KL remainders, Fisher information
bottleneck statements, natural-gradient convergence, D-optimal design, and
BALD-style active-learning acquisition.

Solution Structure.
1. Define theorem-pack local operations used by the stretch statements.
2. Package analytic assumptions into small profile structures.
3. Build artifacts whose proof fields are checked Lean theorems.
4. Prove the finite D-optimal design maximizer directly from `Finset`.
-/

set_option autoImplicit false

namespace FisherInformationAPI
namespace TheoremPack

open scoped BigOperators

/-! ## Parameter Helpers -/

/-- Add a finite vector displacement to a natural parameter. -/
def naturalParameterAdd {d : ℕ}
    (θ : naturalParameter d) (δ : Fin d → ℝ) : naturalParameter d :=
  ⟨fun i => θ i + δ i⟩

/-- Scale a finite vector displacement. -/
def vectorScale {d : ℕ} (a : ℝ) (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => a * v i

/-- Cubic finite-coordinate size used by third-order Taylor remainders. -/
def parameterNormCubed {d : ℕ} (δ : Fin d → ℝ) : ℝ :=
  ∑ i, |δ i| ^ 3

/-- Squared finite-coordinate size used by convergence statements. -/
def parameterNormSq {d : ℕ} (δ : Fin d → ℝ) : ℝ :=
  ∑ i, (δ i) ^ 2

/-! ## Tight KL Remainder -/

/-- Second-order KL approximation error at displacement `δ`.

The local KL expression is supplied by the theorem-pack profile so this module
does not depend on a particular analytic KL backend. -/
def klTaylorRemainder (M : Model)
    (localKL : naturalParameter M.family.d → (Fin M.family.d → ℝ) → ℝ)
    (θ : naturalParameter M.family.d)
    (δ : Fin M.family.d → ℝ) : ℝ :=
  localKL θ δ - fisherMetric M θ δ δ

/-- Profile carrying a checked third-order KL remainder bound. -/
structure TightTaylorProfile (M : Model) where
  localKL : naturalParameter M.family.d → (Fin M.family.d → ℝ) → ℝ
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ θ δ, |klTaylorRemainder M localKL θ δ| ≤ C * parameterNormCubed δ

/-- Artifact for the tight KL remainder theorem. -/
structure TightTaylorArtifact (M : Model) where
  profile : TightTaylorProfile M
  proof :
    ∀ θ δ, |klTaylorRemainder M profile.localKL θ δ| ≤
      profile.C * parameterNormCubed δ

/-- Build the tight KL remainder artifact from its profile. -/
def tightTaylorArtifact {M : Model}
    (profile : TightTaylorProfile M) : TightTaylorArtifact M :=
  { profile := profile
    proof := profile.bound }

/-! ## Fisher Information Bottleneck -/

/-- Fisher-metric information bottleneck Lagrangian. -/
def fisherInformationBottleneck (M : Model)
    (β : ℝ)
    (θ : naturalParameter M.family.d)
    (direction : Fin M.family.d → ℝ) : ℝ :=
  fisherMetric M θ direction direction -
    β * fisherMetric M θ direction direction

/-- Profile comparing a Shannon-form bottleneck objective to its Fisher form. -/
structure InformationBottleneckProfile (M : Model) where
  β : ℝ
  direction : Fin M.family.d → ℝ
  shannonObjective : naturalParameter M.family.d → ℝ
  consistency :
    ∀ θ, shannonObjective θ =
      fisherInformationBottleneck M β θ direction

/-- Artifact for Fisher/Shannon bottleneck consistency. -/
structure InformationBottleneckArtifact (M : Model) where
  profile : InformationBottleneckProfile M
  proof :
    ∀ θ, profile.shannonObjective θ =
      fisherInformationBottleneck M profile.β θ profile.direction

/-- Build the information-bottleneck artifact from its profile. -/
def informationBottleneckArtifact {M : Model}
    (profile : InformationBottleneckProfile M) :
    InformationBottleneckArtifact M :=
  { profile := profile
    proof := profile.consistency }

/-! ## Natural Gradient Convergence -/

/-- One natural-gradient descent update. -/
def naturalGradientUpdate (M : Model)
    (η : ℝ)
    (gradient : naturalParameter M.family.d → Fin M.family.d → ℝ)
    (θ : naturalParameter M.family.d) : naturalParameter M.family.d :=
  naturalParameterAdd θ (vectorScale (-η) (gradient θ))

/-- `n` natural-gradient descent updates from `start`. -/
def naturalGradientIterate (M : Model)
    (η : ℝ)
    (gradient : naturalParameter M.family.d → Fin M.family.d → ℝ)
    (start : naturalParameter M.family.d) : ℕ → naturalParameter M.family.d
  | 0 => start
  | n + 1 => naturalGradientUpdate M η gradient
      (naturalGradientIterate M η gradient start n)

/-- Profile carrying a convergence rate for natural-gradient descent. -/
structure NaturalGradientConvergenceProfile (M : Model) where
  objective : naturalParameter M.family.d → ℝ
  gradient : naturalParameter M.family.d → Fin M.family.d → ℝ
  start : naturalParameter M.family.d
  stepSize : ℝ
  rate : ℝ
  rate_nonneg : 0 ≤ rate
  rate_le_one : rate ≤ 1
  convergence :
    ∀ n, objective (naturalGradientIterate M stepSize gradient start n) ≤
      (rate ^ n) * objective start

/-- Artifact for natural-gradient convergence. -/
structure NaturalGradientConvergenceArtifact (M : Model) where
  profile : NaturalGradientConvergenceProfile M
  proof :
    ∀ n, profile.objective
        (naturalGradientIterate M profile.stepSize profile.gradient profile.start n) ≤
      (profile.rate ^ n) * profile.objective profile.start

/-- Build the natural-gradient convergence artifact from its profile. -/
def naturalGradientConvergenceArtifact {M : Model}
    (profile : NaturalGradientConvergenceProfile M) :
    NaturalGradientConvergenceArtifact M :=
  { profile := profile
    proof := profile.convergence }

/-! ## D-Optimal Design -/

/-- D-optimality score: determinant of the Fisher matrix at `θ`. -/
def fisherDeterminant (M : Model)
    (θ : naturalParameter M.family.d) : ℝ :=
  (M.fisherAt θ).det

/-- A finite indexed design set has a determinant maximizer. -/
theorem dOptimalDesign_exists (M : Model)
    {n : Nat} [NeZero n]
    (candidate : Fin n → naturalParameter M.family.d) :
    ∃ idx : Fin n,
      ∀ j : Fin n,
        fisherDeterminant M (candidate j) ≤
          fisherDeterminant M (candidate idx) := by
  -- Maximize the real-valued determinant over the finite index set `Fin n`.
  let s : Finset (Fin n) := Finset.univ
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hs : s.Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  rcases Finset.exists_max_image s
      (fun idx => fisherDeterminant M (candidate idx)) hs with
    ⟨idx, _hidx, hmax⟩
  exact ⟨idx, fun j => hmax j (Finset.mem_univ j)⟩

/-- Artifact for D-optimal design over finite indexed candidates. -/
structure DOptimalDesignArtifact (M : Model) where
  proof :
    ∀ {n : Nat} [NeZero n]
      (candidate : Fin n → naturalParameter M.family.d),
      ∃ idx : Fin n,
        ∀ j : Fin n,
          fisherDeterminant M (candidate j) ≤
            fisherDeterminant M (candidate idx)

/-- Build the D-optimal design artifact. -/
def dOptimalDesignArtifact (M : Model) : DOptimalDesignArtifact M :=
  { proof := by
      intro n _ candidate
      exact dOptimalDesign_exists M candidate }

/-! ## BALD Via Fisher -/

/-- Fisher-form BALD acquisition score. -/
def baldFisherAcquisition (M : Model)
    (θ : naturalParameter M.family.d)
    (designDirection : Fin M.family.d → ℝ) : ℝ :=
  fisherMetric M θ designDirection designDirection

/-- Profile comparing mutual-information BALD to the Fisher acquisition. -/
structure BALDProfile (M : Model) where
  designDirection : Fin M.family.d → ℝ
  mutualInformationAcquisition : naturalParameter M.family.d → ℝ
  consistency :
    ∀ θ, mutualInformationAcquisition θ =
      baldFisherAcquisition M θ designDirection

/-- Artifact for BALD/Fisher consistency. -/
structure BALDArtifact (M : Model) where
  profile : BALDProfile M
  proof :
    ∀ θ, profile.mutualInformationAcquisition θ =
      baldFisherAcquisition M θ profile.designDirection

/-- Build the BALD artifact from its profile. -/
def baldArtifact {M : Model} (profile : BALDProfile M) :
    BALDArtifact M :=
  { profile := profile
    proof := profile.consistency }

/-! ## Pack -/

/-- Optional theorem-pack bundle for Fisher stretch theorem families. -/
structure FisherTheoremPack (M : Model) where
  tightTaylor? : Option (TightTaylorArtifact M)
  informationBottleneck? : Option (InformationBottleneckArtifact M)
  naturalGradientConvergence? : Option (NaturalGradientConvergenceArtifact M)
  dOptimalDesign : DOptimalDesignArtifact M
  bald? : Option (BALDArtifact M)

/-- Build a Fisher theorem pack from optional analytic profiles. -/
def buildFisherTheoremPack (M : Model)
    (tightTaylor? : Option (TightTaylorProfile M) := none)
    (informationBottleneck? : Option (InformationBottleneckProfile M) := none)
    (naturalGradientConvergence? :
      Option (NaturalGradientConvergenceProfile M) := none)
    (bald? : Option (BALDProfile M) := none) :
    FisherTheoremPack M :=
  { tightTaylor? := tightTaylor?.map tightTaylorArtifact
    informationBottleneck? := informationBottleneck?.map informationBottleneckArtifact
    naturalGradientConvergence? :=
      naturalGradientConvergence?.map naturalGradientConvergenceArtifact
    dOptimalDesign := dOptimalDesignArtifact M
    bald? := bald?.map baldArtifact }

end TheoremPack
end FisherInformationAPI
