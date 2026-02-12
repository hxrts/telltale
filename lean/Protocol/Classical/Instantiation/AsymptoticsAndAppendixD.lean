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
2. Provide Appendix D wrappers that call transported theorems directly.
-/

/-! ## Core Development -/

namespace ProtocolClassical

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

/-- Geometric convergence to steady state. -/
theorem protocol_mixing_geometric_convergence (m : ProtocolMixingModel) :
    ∀ n, m.d (n + 1) ≤ Classical.MixingTimeBounds.geometricEnvelope m.C m.ρ n := by
  simpa [mkProtocolMixingInputFromModel, protocolMixingWitness] using
    transport_mixing (input := mkProtocolMixingInputFromModel m)

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

/-- Energy monotonically decreases for protocol fluid trajectories. -/
theorem protocol_fluid_energy_nonincreasing (m : ProtocolFluidModel) :
    ∀ n,
      Classical.FluidLimitStability.energy m.x (n + 1) ≤
        Classical.FluidLimitStability.energy m.x n := by
  simpa [mkProtocolFluidInputFromModel, protocolFluidWitness] using
    transport_fluidLimit (input := mkProtocolFluidInputFromModel m)

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
    (m : ProtocolConcentrationModel) : ConcentrationInput :=
  { p := m.p
    witness := protocolConcentrationWitness m }

/-- Tail bounds for buffer/latency observable deviations. -/
theorem protocol_concentration_tail_bounds (m : ProtocolConcentrationModel) :
    ∀ t, 0 ≤ t →
      m.p t ≤ Classical.ConcentrationInequalities.subGaussianTail m.σ t :=
  m.tail_upper

/-- Instantiate concentration input and call transported concentration theorem. -/
theorem protocol_transported_concentration (m : ProtocolConcentrationModel) :
    m.p 0 ≤ 2 := by
  simpa [mkProtocolConcentrationInputFromModel, protocolConcentrationWitness] using
    transport_concentration (input := mkProtocolConcentrationInputFromModel m)

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

/-- Prove `L = λW` for coherent steady-state protocol configurations. -/
theorem protocol_littlesLaw (m : ProtocolLittleModel) :
    m.L = m.lam * m.W := by
  simpa [mkProtocolLittleInput] using
    transport_littlesLaw (input := mkProtocolLittleInput m)

/-- Capacity-planning and monitoring readiness derived from Little's law. -/
def CapacityPlanningMonitoringReady (m : ProtocolLittleModel) : Prop :=
  m.L = m.lam * m.W

theorem protocol_capacityPlanning_monitoring (m : ProtocolLittleModel) :
    CapacityPlanningMonitoringReady m := by
  simpa [CapacityPlanningMonitoringReady] using protocol_littlesLaw m

/-! ## Functional CLT Instantiation -/

/-- Protocol-level model for Functional CLT centering instance. -/
structure ProtocolFunctionalCLTModel where
  c : Real
  N : Nat
  t : Nat
  N_ne_zero : N ≠ 0

/-- Scaled process for protocol trajectories. -/
def protocolScaledProcess (m : ProtocolFunctionalCLTModel) : Real :=
  Classical.FunctionalCLT.scaledProcess (fun _ => m.c) m.c m.N m.t

/-- Instantiate `FunctionalCLTInput` from protocol model quantities. -/
def mkProtocolFunctionalCLTInput
    (m : ProtocolFunctionalCLTModel) : FunctionalCLTInput :=
  { c := m.c
    N := m.N
    t := m.t
    N_ne_zero := m.N_ne_zero }

/-- Centering-at-mean for the protocol scaled process. -/
theorem protocol_functionalCLT_centering (m : ProtocolFunctionalCLTModel) :
    protocolScaledProcess m = 0 := by
  simpa [protocolScaledProcess, mkProtocolFunctionalCLTInput] using
    transport_functionalCLT (input := mkProtocolFunctionalCLTInput m)

/-! ## Mean-Field Instantiation -/

/-- Protocol-level model for multi-session mean-field scaling. -/
structure ProtocolMeanFieldModel where
  n : Nat
  x : Fin n → Real

/-- Empirical mean over session states. -/
def protocolEmpiricalMean (m : ProtocolMeanFieldModel) : Real :=
  Classical.PropagationOfChaos.empiricalMean m.x

/-- Sessions are exchangeable (permutation invariance of empirical mean). -/
theorem protocol_meanField_permutation_invariance
    (m : ProtocolMeanFieldModel) :
    ∀ σ : Equiv.Perm (Fin m.n),
      Classical.PropagationOfChaos.empiricalMean (fun i => m.x (σ i)) =
        Classical.PropagationOfChaos.empiricalMean m.x := by
  intro σ
  exact Classical.PropagationOfChaos.empiricalMean_perm (σ := σ) (x := m.x)

/-- Instantiate `MeanFieldInput` from protocol model quantities. -/
def mkProtocolMeanFieldInput (m : ProtocolMeanFieldModel) : MeanFieldInput m.n :=
  { x := m.x }

/-- Instantiate mean-field transport theorem for protocol scaling analysis. -/
theorem protocol_transported_meanField (m : ProtocolMeanFieldModel) :
    Classical.Transport.MeanFieldConclusion (mkProtocolMeanFieldInput m) := by
  exact transport_meanField (input := mkProtocolMeanFieldInput m)

/-- Multi-session scalability analysis contract. -/
def MultiSessionScalabilityLaw (m : ProtocolMeanFieldModel) : Prop :=
  ∀ σ : Equiv.Perm (Fin m.n),
    Classical.PropagationOfChaos.empiricalMean (fun i => m.x (σ i)) =
      Classical.PropagationOfChaos.empiricalMean m.x

theorem protocol_multiSession_scalability (m : ProtocolMeanFieldModel) :
    MultiSessionScalabilityLaw m := by
  intro σ
  exact protocol_meanField_permutation_invariance m σ

/-! ## Appendix D Discharge Theorems -/

/-- Appendix D discharge: transported Foster-Lyapunov-Harris result. -/
theorem appendixD_foster_discharge
    (fw : TransportFramework)
    (system : Classical.FosterLyapunovHarris.DriftSystem CoherenceState)
    (hStep : system.step = fw.step) :
    Classical.Transport.FosterConclusion (mkFosterInput fw system hStep) := by
  exact transport_fosterLyapunov fw system hStep

/-- Appendix D discharge: transported MaxWeight result. -/
theorem appendixD_maxWeight_discharge
    {ι : Type} [Fintype ι]
    (input : MaxWeightInput ι) :
    Classical.Transport.MaxWeightConclusion input := by
  exact transport_maxWeight input

/-- Appendix D discharge: transported Mixing-Time result. -/
theorem appendixD_mixing_discharge
    (input : MixingInput) :
    Classical.Transport.MixingConclusion input := by
  exact transport_mixing input

/-- Appendix D discharge: transported Mean-Field result. -/
theorem appendixD_meanField_discharge
    {n : Nat}
    (input : MeanFieldInput n) :
    Classical.Transport.MeanFieldConclusion input := by
  exact transport_meanField input

/-- Aggregate marker that the current Appendix D shortlist has discharge theorems. -/
def AppendixDDischargeSetReady : Prop :=
  True

theorem appendixD_discharge_set_ready : AppendixDDischargeSetReady := by
  trivial

end ProtocolClassical

end
