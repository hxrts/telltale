import Classical.Transport.Contracts

set_option autoImplicit false

/-! # Classical.Transport.Theorems

Facade theorem wrappers from family-level witnesses.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

namespace Classical
namespace Transport

universe u

theorem transported_fosterLyapunov {State : Type u} {ctx : TransportCtx State}
    (input : FosterInput State ctx) :
    FosterConclusion input := by
  intro s n
  exact FosterLyapunovHarris.DriftSystem.iterate_nonincrease (S := input.system) s n

theorem transported_maxWeight {ι : Type} [Fintype ι]
    (input : MaxWeightInput ι) :
    MaxWeightConclusion input := by
  intro ν
  exact input.choice.optimal ν

theorem transported_ldp (input : LDPInput) :
    LDPConclusion input := by
  intro n
  exact LargeDeviationPrinciple.one_step_tightening input.witness n

theorem transported_meanField {n : Nat} (input : MeanFieldInput n) :
    MeanFieldConclusion input := by
  intro σ
  exact PropagationOfChaos.empiricalMean_perm (σ := σ) (x := input.x)

theorem transported_heavyTraffic (input : HeavyTrafficInput) :
    HeavyTrafficConclusion input := by
  simpa [HeavyTrafficConclusion] using
    HeavyTrafficDiffusion.variance_scaling input.σ input.n

theorem transported_mixing (input : MixingInput) :
    MixingConclusion input := by
  intro n
  exact MixingTimeBounds.one_step_bound input.witness n

theorem transported_fluidLimit (input : FluidInput) :
    FluidConclusion input := by
  intro n
  exact FluidLimitStability.nonincreasing_energy input.witness n

theorem transported_concentration (input : ConcentrationInput) :
    ConcentrationConclusion input := by
  exact ConcentrationInequalities.at_zero_bound input.witness

theorem transported_littlesLaw (input : LittlesLawInput) :
    LittlesLawConclusion input := by
  exact LittlesLaw.queue_length input

theorem transported_functionalCLT (input : FunctionalCLTInput) :
    FunctionalCLTConclusion input := by
  simpa [FunctionalCLTConclusion] using
    FunctionalCLT.scaledProcess_const_zero input.c input.N input.t input.N_ne_zero

/-! ## Naming-normalized theorem wrappers -/

/-- Canonical Foster theorem wrapper: derive a conclusion from its input assumptions. -/
theorem foster_conclusion_ofInput {State : Type u} {ctx : TransportCtx State}
    (input : FosterInput State ctx) :
    FosterConclusion input :=
  transported_fosterLyapunov input

/-- Canonical MaxWeight theorem wrapper: derive a conclusion from its input assumptions. -/
theorem maxWeight_conclusion_ofInput {ι : Type} [Fintype ι]
    (input : MaxWeightInput ι) :
    MaxWeightConclusion input :=
  transported_maxWeight input

/-- Canonical LDP theorem wrapper: derive a conclusion from its input assumptions. -/
theorem ldp_conclusion_ofInput (input : LDPInput) :
    LDPConclusion input :=
  transported_ldp input

/-- Canonical mean-field theorem wrapper: derive a conclusion from its input assumptions. -/
theorem meanField_conclusion_ofInput {n : Nat} (input : MeanFieldInput n) :
    MeanFieldConclusion input :=
  transported_meanField input

/-- Canonical heavy-traffic theorem wrapper: derive a conclusion from its input assumptions. -/
theorem heavyTraffic_conclusion_ofInput (input : HeavyTrafficInput) :
    HeavyTrafficConclusion input :=
  transported_heavyTraffic input

/-- Canonical mixing-time theorem wrapper: derive a conclusion from its input assumptions. -/
theorem mixing_conclusion_ofInput (input : MixingInput) :
    MixingConclusion input :=
  transported_mixing input

/-- Canonical fluid-limit theorem wrapper: derive a conclusion from its input assumptions. -/
theorem fluid_conclusion_ofInput (input : FluidInput) :
    FluidConclusion input :=
  transported_fluidLimit input

/-- Canonical concentration theorem wrapper: derive a conclusion from its input assumptions. -/
theorem concentration_conclusion_ofInput (input : ConcentrationInput) :
    ConcentrationConclusion input :=
  transported_concentration input

/-- Canonical Little's-law theorem wrapper: derive a conclusion from its input assumptions. -/
theorem littlesLaw_conclusion_ofInput (input : LittlesLawInput) :
    LittlesLawConclusion input :=
  transported_littlesLaw input

/-- Canonical functional-CLT theorem wrapper: derive a conclusion from its input assumptions. -/
theorem functionalCLT_conclusion_ofInput (input : FunctionalCLTInput) :
    FunctionalCLTConclusion input :=
  transported_functionalCLT input

/-- Build a Foster certificate from input assumptions. -/
def foster_certificate {State : Type u} {ctx : TransportCtx State}
    (input : FosterInput State ctx) :
    Certificate (FosterInput State ctx) FosterConclusion :=
  { input := input
  , proof := foster_conclusion_ofInput input
  }

/-- Build a MaxWeight certificate from input assumptions. -/
def maxWeight_certificate {ι : Type} [Fintype ι]
    (input : MaxWeightInput ι) :
    Certificate (MaxWeightInput ι) MaxWeightConclusion :=
  { input := input
  , proof := maxWeight_conclusion_ofInput input
  }

/-- Build an LDP certificate from input assumptions. -/
def ldp_certificate (input : LDPInput) :
    Certificate LDPInput LDPConclusion :=
  { input := input
  , proof := ldp_conclusion_ofInput input
  }

/-- Build a mean-field certificate from input assumptions. -/
def meanField_certificate {n : Nat} (input : MeanFieldInput n) :
    Certificate (MeanFieldInput n) MeanFieldConclusion :=
  { input := input
  , proof := meanField_conclusion_ofInput input
  }

/-- Build a heavy-traffic certificate from input assumptions. -/
def heavyTraffic_certificate (input : HeavyTrafficInput) :
    Certificate HeavyTrafficInput HeavyTrafficConclusion :=
  { input := input
  , proof := heavyTraffic_conclusion_ofInput input
  }

/-- Build a mixing certificate from input assumptions. -/
def mixing_certificate (input : MixingInput) :
    Certificate MixingInput MixingConclusion :=
  { input := input
  , proof := mixing_conclusion_ofInput input
  }

/-- Build a fluid-limit certificate from input assumptions. -/
def fluid_certificate (input : FluidInput) :
    Certificate FluidInput FluidConclusion :=
  { input := input
  , proof := fluid_conclusion_ofInput input
  }

/-- Build a concentration certificate from input assumptions. -/
def concentration_certificate (input : ConcentrationInput) :
    Certificate ConcentrationInput ConcentrationConclusion :=
  { input := input
  , proof := concentration_conclusion_ofInput input
  }

/-- Build a Little's-law certificate from input assumptions. -/
def littlesLaw_certificate (input : LittlesLawInput) :
    Certificate LittlesLawInput LittlesLawConclusion :=
  { input := input
  , proof := littlesLaw_conclusion_ofInput input
  }

/-- Build a functional-CLT certificate from input assumptions. -/
def functionalCLT_certificate (input : FunctionalCLTInput) :
    Certificate FunctionalCLTInput FunctionalCLTConclusion :=
  { input := input
  , proof := functionalCLT_conclusion_ofInput input
  }

end Transport
end Classical
