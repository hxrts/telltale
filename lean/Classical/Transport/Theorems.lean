import Classical.Transport.Contracts

set_option autoImplicit false

/-! # Classical.Transport.Theorems

Conditional theorem wrappers over the transport contracts (Option B).

Every family falls into exactly one of three honest categories:

* **Derived from an assumed input.** The classical result is a field of the
  input's witness; the lemma here derives a *new* consequence from it
  (Foster iterate bound, LDP/mixing one-step tightening, fluid energy
  monotonicity, concentration at zero, Little's-law rearrangements).
  Names end in `_of_input`.
* **Assumed input, no derived lemma.** The conclusion *is* a premise field
  (MaxWeight optimality `input.choice.optimal`, Little's law `input.law`,
  the sub-Gaussian tail `input.witness.tail_upper`, spectral termination
  `input.termination.bounded_by_gap`). No restating theorem is provided;
  callers use the field directly.
* **Elementary identity.** No classical theorem is involved (heavy-traffic
  scaled-variance identity, mean-field permutation invariance, constant-path
  scaled process). Names state the identity.
-/

namespace Classical
namespace Transport

universe u

variable [EntropyAPI.AnalysisLaws]

/-! ## Derived From Assumed Inputs -/

/-- Conditional on the drift-system input, the potential never increases along
iterates (deterministic; not the stochastic Foster-Lyapunov theorem). -/
theorem foster_conclusion_of_input {State : Type u} {ctx : TransportCtx State}
    (input : FosterInput State ctx) :
    FosterConclusion input := by
  intro s n
  exact FosterLyapunovHarris.DriftSystem.iterate_nonincrease (S := input.system) s n

/-- Conditional on the assumed `LDPWitness`, one-step envelope tightening. -/
theorem ldp_conclusion_of_input (input : LDPInput) :
    LDPConclusion input := by
  intro n
  exact LargeDeviationPrinciple.one_step_tightening_of_ldp_witness input.witness n

/-- Conditional on the assumed `MixingWitness`, one-step envelope bound. -/
theorem mixing_conclusion_of_input (input : MixingInput) :
    MixingConclusion input := by
  intro n
  exact MixingTimeBounds.one_step_bound_of_mixing_witness input.witness n

/-- Conditional on the assumed `FluidDescentWitness`, energy is non-increasing. -/
theorem fluid_conclusion_of_input (input : FluidInput) :
    FluidConclusion input := by
  intro n
  exact FluidLimitStability.energy_nonincreasing_of_descent_witness input.witness n

/-- Conditional on the assumed `ConcentrationWitness`, `p 0 ≤ 2`. -/
theorem concentration_conclusion_of_input (input : ConcentrationInput) :
    ConcentrationConclusion input := by
  exact ConcentrationInequalities.at_zero_bound_of_concentration_witness input.witness

/-- Conditional on the assumed `input.law`, the wait-time rearrangement. -/
theorem littles_law_wait_time_of_input (input : LittlesLawInput) :
    LittlesLawWaitTimeConclusion input := by
  intro hlam
  exact LittlesLaw.wait_time_of_little_input input hlam

/-- Conditional on the assumed `input.law`, the throughput rearrangement. -/
theorem littles_law_throughput_of_input (input : LittlesLawInput) :
    LittlesLawThroughputConclusion input := by
  intro hW
  exact LittlesLaw.throughput_of_little_input input hW

/-! ## Elementary Identities -/

/-- Mean-field contract is reindexing invariance of a finite average (elementary;
not propagation of chaos). -/
theorem mean_field_permutation_invariant {n : Nat} (input : MeanFieldInput n) :
    MeanFieldConclusion input := by
  intro σ
  exact PropagationOfChaos.mean_permutation_invariant (σ := σ) (x := input.x)

/-- Heavy-traffic contract is the identity `(σ√n)² = σ²n` (elementary; not a
diffusion limit). -/
theorem heavy_traffic_scaled_variance_identity (input : HeavyTrafficInput) :
    HeavyTrafficConclusion input := by
  simpa [HeavyTrafficConclusion] using
    HeavyTrafficDiffusion.scaled_variance_identity input.σ input.n

/-- Functional-CLT contract is degenerate: the input forces a constant path
centred at its own value, whose scaled process is identically zero. This is
not a functional CLT. -/
theorem constant_path_scaled_process_zero (input : FunctionalCLTInput) :
    FunctionalCLTConclusion input := by
  rw [FunctionalCLTConclusion, input.path_eq_const, input.mean_eq_const]
  simpa using
    FunctionalCLT.scaled_process_const_zero input.c input.N input.t input.N_ne_zero

/-! ## Certificate Builders -/

/-- Foster certificate (derived from the assumed drift-system input). -/
def foster_certificate {State : Type u} {ctx : TransportCtx State}
    (input : FosterInput State ctx) :
    Certificate (FosterInput State ctx) FosterConclusion :=
  { input := input, proof := foster_conclusion_of_input input }

/-- MaxWeight certificate: the proof *is* the assumed `choice.optimal` field. -/
def maxWeight_certificate {ι : Type} [Fintype ι]
    (input : MaxWeightInput ι) :
    Certificate (MaxWeightInput ι) MaxWeightConclusion :=
  { input := input, proof := input.choice.optimal }

/-- LDP certificate (derived from the assumed `LDPWitness`). -/
def ldp_certificate (input : LDPInput) :
    Certificate LDPInput LDPConclusion :=
  { input := input, proof := ldp_conclusion_of_input input }

/-- Mean-field certificate (elementary permutation identity). -/
def meanField_certificate {n : Nat} (input : MeanFieldInput n) :
    Certificate (MeanFieldInput n) MeanFieldConclusion :=
  { input := input, proof := mean_field_permutation_invariant input }

/-- Heavy-traffic certificate (elementary scaled-variance identity). -/
def heavyTraffic_certificate (input : HeavyTrafficInput) :
    Certificate HeavyTrafficInput HeavyTrafficConclusion :=
  { input := input, proof := heavy_traffic_scaled_variance_identity input }

/-- Mixing certificate (derived from the assumed `MixingWitness`). -/
def mixing_certificate (input : MixingInput) :
    Certificate MixingInput MixingConclusion :=
  { input := input, proof := mixing_conclusion_of_input input }

/-- Fluid certificate (derived from the assumed `FluidDescentWitness`). -/
def fluid_certificate (input : FluidInput) :
    Certificate FluidInput FluidConclusion :=
  { input := input, proof := fluid_conclusion_of_input input }

/-- Concentration certificate (derived from the assumed `ConcentrationWitness`). -/
def concentration_certificate (input : ConcentrationInput) :
    Certificate ConcentrationInput ConcentrationConclusion :=
  { input := input, proof := concentration_conclusion_of_input input }

/-- Little's-law certificate: the proof *is* the assumed `law` field. -/
def littlesLaw_certificate (input : LittlesLawInput) :
    Certificate LittlesLawInput LittlesLawConclusion :=
  { input := input, proof := input.law }

/-- Functional-CLT certificate (degenerate constant-path identity). -/
def functionalCLT_certificate (input : FunctionalCLTInput) :
    Certificate FunctionalCLTInput FunctionalCLTConclusion :=
  { input := input, proof := constant_path_scaled_process_zero input }

/-- Spectral-gap certificate: the proof *is* the assumed
`termination.bounded_by_gap` field. -/
def spectralGap_certificate
    {State : Type u} [Fintype State] [DecidableEq State]
    (input : SpectralGapInput State) :
    Certificate (SpectralGapInput State) SpectralGapConclusion :=
  { input := input, proof := input.termination.bounded_by_gap }

end Transport
end Classical
