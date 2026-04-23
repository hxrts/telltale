import Classical.Transport.Context
import ClassicalAnalysisInstance
import Classical.Families.FosterLyapunovHarris
import Classical.Families.MaxWeightBackpressure
import Classical.Families.LargeDeviationPrinciple
import Classical.Families.PropagationOfChaos
import Classical.Families.HeavyTrafficDiffusion
import Classical.Families.MixingTimeBounds
import Classical.Families.FluidLimitStability
import Classical.Families.ConcentrationInequalities
import Classical.Families.LittlesLaw
import Classical.Families.FunctionalCLT
import Classical.Families.SpectralGapTermination

set_option autoImplicit false

/-! # Classical.Transport.Contracts

Input and conclusion contracts for transported theorem families.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Classical
namespace Transport

universe u

variable [EntropyAPI.AnalysisLaws]

/-! ## Foster Contracts -/

/-- Foster-Lyapunov transport contract. -/
structure FosterInput (State : Type u) (ctx : TransportCtx State) where
  system : FosterLyapunovHarris.DriftSystem State
  step_agrees : system.step = ctx.step

/-- Naming-normalized alias: assumptions required for the Foster transport family. -/
abbrev FosterAssumptions (State : Type u) (ctx : TransportCtx State) := FosterInput State ctx

def FosterConclusion {State : Type u} {ctx : TransportCtx State}
    (input : FosterInput State ctx) : Prop :=
  ∀ s n, input.system.V (input.system.step^[n] s) ≤ input.system.V s

/-! ## MaxWeight Contracts -/

/-- MaxWeight transport contract. -/
structure MaxWeightInput (ι : Type) [Fintype ι] where
  q : ι → Real
  choice : MaxWeightBackpressure.MaxWeightChoice q

/-- Naming-normalized alias: assumptions required for MaxWeight transport. -/
abbrev MaxWeightAssumptions (ι : Type) [Fintype ι] := MaxWeightInput ι

def MaxWeightConclusion {ι : Type} [Fintype ι]
    (input : MaxWeightInput ι) : Prop :=
  ∀ ν : ι → Real,
    MaxWeightBackpressure.weight input.q ν ≤
      MaxWeightBackpressure.weight input.q input.choice.sched

/-! ## LDP Contracts -/

/-- Large-deviation transport contract. -/
structure LDPInput where
  p : Nat → Real
  witness : LargeDeviationPrinciple.LDPWitness p

/-- Naming-normalized alias: assumptions required for LDP transport. -/
abbrev LDPAssumptions := LDPInput

def LDPConclusion (input : LDPInput) : Prop :=
  ∀ n, input.p (n + 1) ≤
    LargeDeviationPrinciple.exponentialEnvelope input.witness.C input.witness.ρ n

/-! ## Mean-Field Contracts -/

/-- Mean-field transport contract. -/
structure MeanFieldInput (n : Nat) where
  x : Fin n → Real

/-- Naming-normalized alias: assumptions required for mean-field transport. -/
abbrev MeanFieldAssumptions (n : Nat) := MeanFieldInput n

def MeanFieldConclusion {n : Nat} (input : MeanFieldInput n) : Prop :=
  ∀ σ : Equiv.Perm (Fin n),
    PropagationOfChaos.empiricalMean (fun i => input.x (σ i)) =
      PropagationOfChaos.empiricalMean input.x

/-! ## Heavy-Traffic Contracts -/

/-- Heavy-traffic transport contract. -/
structure HeavyTrafficInput where
  σ : Real
  n : Nat

/-- Naming-normalized alias: assumptions required for heavy-traffic transport. -/
abbrev HeavyTrafficAssumptions := HeavyTrafficInput

def HeavyTrafficConclusion (input : HeavyTrafficInput) : Prop :=
  (input.σ * HeavyTrafficDiffusion.diffusionScale input.n) ^ 2 = input.σ ^ 2 * input.n

/-- Named heavy-traffic diffusion-scale law exposed to runtime theorem packs. -/
def HeavyTrafficDiffusionScaleLaw (input : HeavyTrafficInput) : Prop :=
  HeavyTrafficConclusion input

/-! ## Mixing Contracts -/

/-- Mixing-time transport contract. -/
structure MixingInput where
  d : Nat → Real
  witness : MixingTimeBounds.MixingWitness d

/-- Naming-normalized alias: assumptions required for mixing-time transport. -/
abbrev MixingAssumptions := MixingInput

def MixingConclusion (input : MixingInput) : Prop :=
  ∀ n, input.d (n + 1) ≤ MixingTimeBounds.geometricEnvelope input.witness.C input.witness.ρ n

/-! ## Fluid Contracts -/

/-- Fluid-limit transport contract. -/
structure FluidInput where
  x : Nat → Real
  witness : FluidLimitStability.FluidDescentWitness x

/-- Naming-normalized alias: assumptions required for fluid-limit transport. -/
abbrev FluidAssumptions := FluidInput

def FluidConclusion (input : FluidInput) : Prop :=
  ∀ n, FluidLimitStability.energy input.x (n + 1) ≤ FluidLimitStability.energy input.x n

/-! ## Concentration Contracts -/

/-- Concentration transport contract. -/
structure ConcentrationInput where
  p : Real → Real
  witness : ConcentrationInequalities.ConcentrationWitness p

/-- Naming-normalized alias: assumptions required for concentration transport. -/
abbrev ConcentrationAssumptions := ConcentrationInput

def ConcentrationConclusion (input : ConcentrationInput) : Prop :=
  input.p 0 ≤ 2

/-- Full sub-Gaussian concentration tail bound. -/
def ConcentrationTailConclusion (input : ConcentrationInput) : Prop :=
  ∀ t, 0 ≤ t →
    input.p t ≤
      ConcentrationInequalities.subGaussianTail input.witness.σ t

/-! ## Little's Law Contracts -/

/-- Little's law transport contract. -/
abbrev LittlesLawInput := LittlesLaw.LittleInput

/-- Naming-normalized alias: assumptions required for Little's-law transport. -/
abbrev LittlesLawAssumptions := LittlesLawInput

def LittlesLawConclusion (input : LittlesLawInput) : Prop :=
  input.L = input.lam * input.W

/-- Little's-law wait-time corollary. -/
def LittlesLawWaitTimeConclusion (input : LittlesLawInput) : Prop :=
  input.lam ≠ 0 → input.W = input.L / input.lam

/-- Little's-law throughput corollary. -/
def LittlesLawThroughputConclusion (input : LittlesLawInput) : Prop :=
  input.W ≠ 0 → input.lam = input.L / input.W

/-! ## Functional CLT Contracts -/

/-- Functional CLT transport contract. -/
structure FunctionalCLTInput where
  c : Real
  N : Nat
  t : Nat
  N_ne_zero : N ≠ 0
  x : Nat → Real := fun _ => c
  μ : Real := c
  path_eq_const : x = (fun _ : Nat => c)
  mean_eq_const : μ = c

/-- Naming-normalized alias: assumptions required for functional-CLT transport. -/
abbrev FunctionalCLTAssumptions := FunctionalCLTInput

def FunctionalCLTConclusion (input : FunctionalCLTInput) : Prop :=
  FunctionalCLT.scaledProcess input.x input.μ input.N input.t = 0

/-- Named path-level scaled-process centering law exposed to runtime theorem packs. -/
def FunctionalCLTScaledProcessLaw (input : FunctionalCLTInput) : Prop :=
  FunctionalCLTConclusion input

/-! ## Spectral-Gap Termination Contracts -/

/-- Spectral-gap termination transport contract over a finite-state Markov chain. -/
structure SpectralGapInput (State : Type u) [Fintype State] [DecidableEq State] where
  chain : SpectralGapTermination.MarkovChain State
  gap_pos : SpectralGapTermination.SpectralGapPos chain
  termination : SpectralGapTermination.TerminationWitness chain

/-- Naming-normalized alias: assumptions required for spectral-gap termination. -/
abbrev SpectralGapAssumptions
    (State : Type u) [Fintype State] [DecidableEq State] :=
  SpectralGapInput State

/-- Expected termination is bounded by inverse spectral gap. -/
def SpectralGapConclusion
    {State : Type u} [Fintype State] [DecidableEq State]
    (input : SpectralGapInput State) : Prop :=
  ∀ st,
    SpectralGapTermination.expectedTerminationTime input.termination st ≤
      1 / SpectralGapTermination.spectralGap input.chain

/-! ## Certificate Types -/

/-- Uniform certificate container for transported theorem conclusions. -/
structure Certificate (α : Type u) (Conclusion : α → Prop) where
  input : α
  proof : Conclusion input

abbrev FosterCertificate {State : Type u} {ctx : TransportCtx State}
    (input : FosterInput State ctx) :=
  Certificate (FosterInput State ctx) FosterConclusion

abbrev MaxWeightCertificate {ι : Type} [Fintype ι]
    (input : MaxWeightInput ι) :=
  Certificate (MaxWeightInput ι) MaxWeightConclusion

abbrev LDPCertificate (input : LDPInput) :=
  Certificate LDPInput LDPConclusion

abbrev MeanFieldCertificate {n : Nat} (input : MeanFieldInput n) :=
  Certificate (MeanFieldInput n) MeanFieldConclusion

abbrev HeavyTrafficCertificate (input : HeavyTrafficInput) :=
  Certificate HeavyTrafficInput HeavyTrafficConclusion

abbrev MixingCertificate (input : MixingInput) :=
  Certificate MixingInput MixingConclusion

abbrev FluidCertificate (input : FluidInput) :=
  Certificate FluidInput FluidConclusion

abbrev ConcentrationCertificate (input : ConcentrationInput) :=
  Certificate ConcentrationInput ConcentrationConclusion

abbrev LittlesLawCertificate (input : LittlesLawInput) :=
  Certificate LittlesLawInput LittlesLawConclusion

abbrev FunctionalCLTCertificate (input : FunctionalCLTInput) :=
  Certificate FunctionalCLTInput FunctionalCLTConclusion

abbrev SpectralGapCertificate
    {State : Type u} [Fintype State] [DecidableEq State]
    (input : SpectralGapInput State) :=
  Certificate (SpectralGapInput State) SpectralGapConclusion

end Transport
end Classical
