import Protocol.Classical.TransportLedger

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

section

/-! # Protocol Classical Instantiation: Asymptotics and Appendix D

Protocol-facing instantiations for mixing/fluid/concentration/little/CLT/mean-field
families and the Appendix D discharge wrappers.
-/

/-
The Problem. The transported classical theorem families after large-deviation and
queueing instantiations still need protocol-level bindings for asymptotic regimes
and a concise Appendix D discharge surface.

Solution Structure.
1. Instantiate mixing, fluid, concentration, Little's law, CLT, and mean-field layers.
2. Provide Appendix D wrappers over the conditional lemmas (assumed classical
   inputs are used directly, not restated).
-/

/-! ## Core Development -/

namespace ProtocolClassical

variable [EntropyAPI.AnalysisLaws]

/-! ## Mixing-Time Instantiation -/

/-- Protocol-level model for geometric mixing bounds. -/
structure ProtocolMixingModel where
  d : Nat → Real
  C : Real
  ρ : Real
  C_nonneg : 0 ≤ C
  rho_nonneg : 0 ≤ ρ
  rho_le_one : ρ ≤ 1
  dist_upper : ∀ n, d n ≤ Classical.MixingTimeBounds.geometricEnvelope C ρ n

/-- Distance function on protocol configurations for mixing analysis. -/
def protocolDistance (m : ProtocolMixingModel) : Nat → Real :=
  m.d

/-- Construct `MixingWitness` with contraction rate `ρ`. -/
def protocolMixingWitness (m : ProtocolMixingModel) :
    Classical.MixingTimeBounds.MixingWitness m.d :=
  { C := m.C
    ρ := m.ρ
    C_nonneg := m.C_nonneg
    rho_nonneg := m.rho_nonneg
    rho_le_one := m.rho_le_one
    dist_upper := m.dist_upper }

/-- Instantiate `MixingInput` from protocol-side model data. -/
def mkProtocolMixingInputFromModel (m : ProtocolMixingModel) : MixingInput :=
  { d := m.d
    witness := protocolMixingWitness m }

/-- Conditional on the model's assumed geometric envelope, one-step bound. -/
theorem protocol_mixing_one_step_of_model (m : ProtocolMixingModel) :
    ∀ n, m.d (n + 1) ≤ Classical.MixingTimeBounds.geometricEnvelope m.C m.ρ n := by
  exact
    Classical.Transport.mixing_conclusion_of_input (input := mkProtocolMixingInputFromModel m)

/-! ## Fluid-Limit Instantiation -/

/-- Protocol-level model for fluid-limit trajectory descent. -/
structure ProtocolFluidModel where
  x : Nat → Real
  κ : Real
  kappa_nonneg : 0 ≤ κ
  descent :
    ∀ n, Classical.FluidLimitStability.energy x (n + 1) ≤
      Classical.FluidLimitStability.energy x n - κ * |x n|

/-- Trajectory for aggregate buffer occupancy. -/
def protocolTrajectory (m : ProtocolFluidModel) : Nat → Real :=
  m.x

/-- Construct `FluidDescentWitness` with energy descent. -/
def protocolFluidWitness (m : ProtocolFluidModel) :
    Classical.FluidLimitStability.FluidDescentWitness m.x :=
  { κ := m.κ
    kappa_nonneg := m.kappa_nonneg
    descent := m.descent }

/-- Instantiate `FluidInput` from protocol-side model data. -/
def mkProtocolFluidInputFromModel (m : ProtocolFluidModel) : FluidInput :=
  { x := m.x
    witness := protocolFluidWitness m }

/-- Conditional on the model's assumed descent inequality, energy is non-increasing. -/
theorem protocol_fluid_energy_nonincreasing_of_model (m : ProtocolFluidModel) :
    ∀ n,
      Classical.FluidLimitStability.energy m.x (n + 1) ≤
        Classical.FluidLimitStability.energy m.x n := by
  exact
    Classical.Transport.fluid_conclusion_of_input (input := mkProtocolFluidInputFromModel m)

/-! ## Concentration Instantiation -/

/-- Protocol-level model for concentration tail bounds. -/
structure ProtocolConcentrationModel where
  p : Real → Real
  σ : Real
  sigma_pos : 0 < σ
  tail_upper :
    ∀ t, 0 ≤ t →
      p t ≤ Classical.ConcentrationInequalities.subGaussianTail σ t

/-- Probability function for observable deviations. -/
def protocolDeviationProbability (m : ProtocolConcentrationModel) : Real → Real :=
  m.p

/-- Construct `ConcentrationWitness` with sub-Gaussian parameters. -/
def protocolConcentrationWitness (m : ProtocolConcentrationModel) :
    Classical.ConcentrationInequalities.ConcentrationWitness m.p :=
  { σ := m.σ
    sigma_pos := m.sigma_pos
    tail_upper := m.tail_upper }

/-- Instantiate `ConcentrationInput` from protocol-side model data. -/
def mkProtocolConcentrationInputFromModel
    (m : ProtocolConcentrationModel) : Classical.Transport.ConcentrationInput :=
  { p := m.p
    witness := protocolConcentrationWitness m }

/- The sub-Gaussian tail is the assumed `m.tail_upper`; no restating theorem. -/

/-- Conditional on the model's assumed sub-Gaussian tail, `p 0 ≤ 2`. -/
theorem protocol_concentration_at_zero_of_model (m : ProtocolConcentrationModel) :
    m.p 0 ≤ 2 := by
  exact
    Classical.Transport.concentration_conclusion_of_input
      (input := mkProtocolConcentrationInputFromModel m)

/-! ## Little's Law Instantiation -/

/-- Protocol-level model for Little's Law quantities. -/
structure ProtocolLittleModel where
  lam : Real
  W : Real
  L : Real
  law : L = lam * W

/-- Instantiate `LittleInput` from protocol model quantities. -/
def mkProtocolLittleInput (m : ProtocolLittleModel) : LittlesLawInput :=
  { lam := m.lam
    W := m.W
    L := m.L
    law := m.law }

/-
`L = λW` is the assumed `m.law` (Little's law is not proved). The former
`protocol_littles_law`, `CapacityPlanningMonitoringReady` and
`protocol_capacity_planning_monitoring` only restated it and were removed.
-/

/-! ## Functional CLT Instantiation -/

/-- Degenerate constant-path model (no stochastic path; not a functional CLT). -/
structure ProtocolFunctionalCLTModel where
  c : Real
  N : Nat
  t : Nat
  N_ne_zero : N ≠ 0

/-- Scaled process of the constant path `fun _ => m.c` centred at `m.c`. -/
def protocolScaledProcess (m : ProtocolFunctionalCLTModel) : Real :=
  @Classical.FunctionalCLT.scaledProcess.{0, 0, 0, 0} inferInstance
    (fun _ : Nat => m.c) m.c m.N m.t

/-- Instantiate `FunctionalCLTInput` from protocol model quantities. -/
def mkProtocolFunctionalCLTInput
    (m : ProtocolFunctionalCLTModel) : FunctionalCLTInput :=
  { c := m.c
    N := m.N
    t := m.t
    N_ne_zero := m.N_ne_zero
    path_eq_const := rfl
    mean_eq_const := rfl }

/-- The constant path centred at its own value has zero scaled process. -/
theorem protocol_constant_path_scaled_process_zero (m : ProtocolFunctionalCLTModel) :
    protocolScaledProcess m = 0 := by
  exact
    Classical.Transport.constant_path_scaled_process_zero
      (input := mkProtocolFunctionalCLTInput m)

/-! ## Mean-Field Instantiation -/

/-- Protocol-level model for multi-session mean-field scaling. -/
structure ProtocolMeanFieldModel where
  n : Nat
  x : Fin n → Real

/-- Empirical mean over session states. -/
def protocolEmpiricalMean (m : ProtocolMeanFieldModel) : Real :=
  @Classical.PropagationOfChaos.empiricalMean.{0, 0, 0, 0} m.n inferInstance m.x

/-- Reindexing invariance of the empirical mean (elementary; not a mean-field limit). -/
theorem protocol_mean_permutation_invariant
    (m : ProtocolMeanFieldModel) :
    ∀ σ : Equiv.Perm (Fin m.n),
      @Classical.PropagationOfChaos.empiricalMean.{0, 0, 0, 0}
          m.n inferInstance (fun i => m.x (σ i)) =
        @Classical.PropagationOfChaos.empiricalMean.{0, 0, 0, 0}
          m.n inferInstance m.x := by
  intro σ
  exact Classical.PropagationOfChaos.mean_permutation_invariant (σ := σ) (x := m.x)

/-- Instantiate `MeanFieldInput` from protocol model quantities. -/
def mkProtocolMeanFieldInput (m : ProtocolMeanFieldModel) : MeanFieldInput m.n :=
  { x := m.x }

/-
The former `protocol_transported_mean_field`, `MultiSessionScalabilityLaw` and
`protocol_multi_session_scalability` restated `protocol_mean_permutation_invariant`
under scalability names and were removed.
-/

/-! ## Appendix D Discharge Theorems -/

/-- Appendix D: deterministic Foster potential bound, conditional on the drift input. -/
theorem appendix_d_foster_discharge
    (fw : TransportFramework)
    (system : Classical.FosterLyapunovHarris.DriftSystem CoherenceState)
    (hStep : system.step = fw.step) :
    Classical.Transport.FosterConclusion (mkFosterInput fw system hStep) := by
  exact foster_conclusion_of_framework fw system hStep

/-- Appendix D: mixing one-step bound, conditional on the assumed `MixingWitness`. -/
theorem appendix_d_mixing_discharge
    (input : MixingInput) :
    Classical.Transport.MixingConclusion input := by
  exact Classical.Transport.mixing_conclusion_of_input input

/-- Appendix D: mean-field reindexing invariance (elementary identity). -/
theorem appendix_d_mean_field_discharge
    {n : Nat}
    (input : MeanFieldInput n) :
    Classical.Transport.MeanFieldConclusion input := by
  exact Classical.Transport.mean_field_permutation_invariant input

/-- Conjunction of the four Appendix D obligations. Honest status (Option B):
    Foster and mixing are derived from assumed inputs; the MaxWeight conjunct
    holds only because its conclusion *is* the assumed `choice.optimal` field;
    the mean-field conjunct is an elementary identity. -/
def AppendixDDischargeSetReady : Prop :=
  (∀ (fw : TransportFramework)
      (system : Classical.FosterLyapunovHarris.DriftSystem CoherenceState)
      (hStep : system.step = fw.step),
      Classical.Transport.FosterConclusion (mkFosterInput fw system hStep)) ∧
  (∀ {ι : Type} [Fintype ι] (input : MaxWeightInput ι),
      Classical.Transport.MaxWeightConclusion input) ∧
  (∀ (input : MixingInput), Classical.Transport.MixingConclusion input) ∧
  (∀ {n : Nat} (input : MeanFieldInput n), Classical.Transport.MeanFieldConclusion input)

/-- All Appendix D obligations hold, in the conditional sense documented on
    `AppendixDDischargeSetReady`. -/
theorem appendix_d_discharge_set_ready : AppendixDDischargeSetReady :=
  ⟨appendix_d_foster_discharge, fun input => input.choice.optimal,
    appendix_d_mixing_discharge, fun input => appendix_d_mean_field_discharge input⟩

end ProtocolClassical

end
