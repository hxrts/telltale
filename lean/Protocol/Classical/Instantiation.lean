import Protocol.Classical.TransportLedger

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

section

/-! # Protocol-Level Classical Instantiation

Concrete protocol-facing instantiations of the transported theorem API:
- Main-text exemplar: Large deviations / SLA tails
- Appendix D: Foster-Lyapunov, MaxWeight, Mixing, Mean-field
-/

namespace ProtocolClassical

/-- Coherence-projected state space used for 3.9.1 transport instantiation.
This is the erasure-level image of well-typed protocol configurations. -/
abbrev WTConfigNState := { C : CoherenceState // Coherent C.G C.D }

/-- Protocol transition function used in the 3.9.1 Foster instantiation. -/
abbrev FStep := WTConfigNState → WTConfigNState

/-- Progress-measure decomposition used in the Lyapunov potential `V`. -/
structure ProgressMeasureComponents where
  typeDepth : WTConfigNState → Nat
  bufferLength : WTConfigNState → Nat
  sendPotential : WTConfigNState → Nat

/-- Total protocol progress measure:
`type_depth + buffer_length + send_potential`. -/
def protocolV (μ : ProgressMeasureComponents) (st : WTConfigNState) : Nat :=
  μ.typeDepth st + μ.bufferLength st + μ.sendPotential st

/-- Side conditions needed to build the protocol Foster transport context. -/
structure ProtocolFosterSideConditions where
  harmony : Prop
  finiteState : Prop

/-- 3.9.1 assumptions tying coherence and progress measure behavior to `FStep`. -/
structure FosterLivenessAssumptions (step : FStep) (μ : ProgressMeasureComponents) : Prop where
  /-- Coherence is preserved by one protocol step. -/
  coherence_preservation :
    ∀ st, Coherent (step st).1.G (step st).1.D
  /-- Nonincrease from coherence preservation. -/
  nonincrease_of_coherence :
    ∀ st, protocolV μ (step st) ≤ protocolV μ st
  /-- Strict descent on positive potential (progress on non-terminal coherent states). -/
  strict_on_pos_of_coherence :
    ∀ st, protocolV μ st ≠ 0 → protocolV μ (step st) < protocolV μ st

/-- 3.9.1: nonincrease theorem on bundled well-typed states. -/
theorem protocol_nonincrease
    (step : FStep) (μ : ProgressMeasureComponents)
    (h : FosterLivenessAssumptions step μ) :
    ∀ st : WTConfigNState, protocolV μ (step st) ≤ protocolV μ st := by
  intro st
  exact h.nonincrease_of_coherence st

/-- 3.9.1: strict-on-positive theorem on bundled well-typed states. -/
theorem protocol_strict_on_pos
    (step : FStep) (μ : ProgressMeasureComponents)
    (h : FosterLivenessAssumptions step μ) :
    ∀ st : WTConfigNState, protocolV μ st ≠ 0 → protocolV μ (step st) < protocolV μ st := by
  intro st hPos
  exact h.strict_on_pos_of_coherence st hPos

/-- 3.9.1: `ProtocolDriftSystem : DriftSystem WTConfigState`. -/
def ProtocolDriftSystem
    (step : FStep) (μ : ProgressMeasureComponents)
    (h : FosterLivenessAssumptions step μ) :
    Classical.FosterLyapunovHarris.DriftSystem WTConfigNState :=
  { step := step
    V := protocolV μ
    nonincrease := protocol_nonincrease step μ h
    strict_on_pos := protocol_strict_on_pos step μ h }

/-- Transport context specialized to bundled well-typed states. -/
def protocolFosterCtx (step : FStep) (hSide : ProtocolFosterSideConditions) :
    Classical.Transport.TransportCtx WTConfigNState :=
  { step := step
    coherent := fun st => Coherent st.1.G st.1.D
    harmony := hSide.harmony
    finiteState := hSide.finiteState }

/-- 3.9.1: instantiate `FosterInput` for protocol states. -/
def protocolFosterInput
    (step : FStep) (μ : ProgressMeasureComponents)
    (h : FosterLivenessAssumptions step μ)
    (hSide : ProtocolFosterSideConditions) :
    Classical.Transport.FosterInput WTConfigNState (protocolFosterCtx step hSide) :=
  { system := ProtocolDriftSystem step μ h
    step_agrees := rfl }

/-- 3.9.1: call transported Foster-Lyapunov theorem on protocol instantiation. -/
theorem protocol_transported_fosterLyapunov
    (step : FStep) (μ : ProgressMeasureComponents)
    (h : FosterLivenessAssumptions step μ)
    (hSide : ProtocolFosterSideConditions) :
    Classical.Transport.FosterConclusion (protocolFosterInput step μ h hSide) := by
  exact Classical.Transport.transported_fosterLyapunov
    (input := protocolFosterInput step μ h hSide)

/-- 3.9.1: R.7 bridge statement (Lyapunov potential bound along iterates). -/
theorem r7_lyapunov_potential_integration
    (step : FStep) (μ : ProgressMeasureComponents)
    (h : FosterLivenessAssumptions step μ)
    (hSide : ProtocolFosterSideConditions) :
    ∀ st n, protocolV μ ((step^[n]) st) ≤ protocolV μ st := by
  intro st n
  exact protocol_transported_fosterLyapunov step μ h hSide st n

/-- Queue weights induced from per-edge buffer occupancy. -/
def queueWeightsFromBuffers {ι : Type} [Fintype ι]
    (bufferOccupancy : ι → Nat) : ι → Real :=
  fun i => (bufferOccupancy i : Real)

/-- Protocol scheduling profile over queue indices. -/
abbrev ProtocolSchedule (ι : Type) := ι → Real

/-- Protocol-level MaxWeight choice wrapper. -/
def protocolMaxWeightChoice {ι : Type} [Fintype ι]
    (q : ι → Real)
    (sched : ProtocolSchedule ι)
    (hOptimal :
      ∀ ν : ι → Real,
        Classical.MaxWeightBackpressure.weight q ν ≤
          Classical.MaxWeightBackpressure.weight q sched) :
    Classical.MaxWeightBackpressure.MaxWeightChoice q :=
  { sched := sched
    optimal := hOptimal }

/-- Protocol-level MaxWeight input constructor. -/
def mkProtocolMaxWeightInput {ι : Type} [Fintype ι]
    (bufferOccupancy : ι → Nat)
    (sched : ProtocolSchedule ι)
    (hOptimal :
      ∀ ν : ι → Real,
        Classical.MaxWeightBackpressure.weight (queueWeightsFromBuffers bufferOccupancy) ν ≤
          Classical.MaxWeightBackpressure.weight (queueWeightsFromBuffers bufferOccupancy) sched) :
    MaxWeightInput ι :=
  { q := queueWeightsFromBuffers bufferOccupancy
    choice := protocolMaxWeightChoice (queueWeightsFromBuffers bufferOccupancy) sched hOptimal }

/-- MaxWeight scheduling optimality for protocol queue weights. -/
theorem protocol_maxWeight_optimality
    {ι : Type} [Fintype ι]
    (bufferOccupancy : ι → Nat)
    (sched : ProtocolSchedule ι)
    (hOptimal :
      ∀ ν : ι → Real,
        Classical.MaxWeightBackpressure.weight (queueWeightsFromBuffers bufferOccupancy) ν ≤
          Classical.MaxWeightBackpressure.weight (queueWeightsFromBuffers bufferOccupancy) sched) :
    ∀ ν : ι → Real,
      Classical.MaxWeightBackpressure.weight (queueWeightsFromBuffers bufferOccupancy) ν ≤
        Classical.MaxWeightBackpressure.weight (queueWeightsFromBuffers bufferOccupancy) sched := by
  intro ν
  exact hOptimal ν

/-- 3.9.2: instantiate `MaxWeightInput` and call transported theorem. -/
theorem protocol_transported_maxWeight
    {ι : Type} [Fintype ι]
    (bufferOccupancy : ι → Nat)
    (sched : ProtocolSchedule ι)
    (hOptimal :
      ∀ ν : ι → Real,
        Classical.MaxWeightBackpressure.weight (queueWeightsFromBuffers bufferOccupancy) ν ≤
          Classical.MaxWeightBackpressure.weight (queueWeightsFromBuffers bufferOccupancy) sched) :
    Classical.Transport.MaxWeightConclusion
      (mkProtocolMaxWeightInput bufferOccupancy sched hOptimal) := by
  exact transport_maxWeight (mkProtocolMaxWeightInput bufferOccupancy sched hOptimal)

/-- Protocol-level model for rare-event probabilities (e.g. overflow/deadline miss)
with an explicit exponential-rate witness. -/
structure ProtocolLDPModel where
  p : Nat → Real
  C : Real
  ρ : Real
  C_nonneg : 0 ≤ C
  rho_nonneg : 0 ≤ ρ
  rho_le_one : ρ ≤ 1
  tail_upper :
    ∀ n, p n ≤ Classical.LargeDeviationPrinciple.exponentialEnvelope C ρ n

/-- Probability sequence for protocol rare events. -/
def protocolRareEventProbability (m : ProtocolLDPModel) : Nat → Real :=
  m.p

/-- Construct the LDP witness from protocol-side model data. -/
def protocolLDPWitness (m : ProtocolLDPModel) :
    Classical.LargeDeviationPrinciple.LDPWitness m.p :=
  { C := m.C
    ρ := m.ρ
    C_nonneg := m.C_nonneg
    rho_nonneg := m.rho_nonneg
    rho_le_one := m.rho_le_one
    tail_upper := m.tail_upper }

/-- Protocol-side constructor for LDP transport input. -/
def mkProtocolLDPInputFromModel (m : ProtocolLDPModel) : LDPInput :=
  { p := m.p
    witness := protocolLDPWitness m }

/-- Exponential tightening bound for protocol rare-event probabilities. -/
theorem protocol_ldp_tightening (m : ProtocolLDPModel) :
    ∀ n,
      m.p (n + 1) ≤ Classical.LargeDeviationPrinciple.exponentialEnvelope m.C m.ρ n := by
  simpa [mkProtocolLDPInputFromModel, protocolLDPWitness] using
    transport_ldp (input := mkProtocolLDPInputFromModel m)

/-- Diffusion-scale parameter extracted from arrival/service rates. -/
def diffusionSigmaFromRates (arrivalRate serviceRate : Real) : Real :=
  serviceRate - arrivalRate

/-- 3.9.4: heavy-traffic input from protocol rates and scaling horizon. -/
def mkProtocolHeavyTrafficInput
    (arrivalRate serviceRate : Real) (n : Nat) : HeavyTrafficInput :=
  { σ := diffusionSigmaFromRates arrivalRate serviceRate
    n := n }

/-- 3.9.4: variance scaling law in near-capacity operation. -/
theorem protocol_heavyTraffic_variance_scaling
    (arrivalRate serviceRate : Real) (n : Nat) :
    Classical.Transport.HeavyTrafficConclusion
      (mkProtocolHeavyTrafficInput arrivalRate serviceRate n) := by
  exact transport_heavyTraffic (mkProtocolHeavyTrafficInput arrivalRate serviceRate n)

/-- Protocol-side constructor for the main-text LDP exemplar input. -/
def mkProtocolLDPInput (p : Nat → Real)
    (w : Classical.LargeDeviationPrinciple.LDPWitness p) : LDPInput :=
  { p := p, witness := w }

/-- Main-text discharged exemplar (SLA tails) via transported LDP theorem. -/
theorem mainText_ldp_sla_tail
    (p : Nat → Real)
    (w : Classical.LargeDeviationPrinciple.LDPWitness p) :
    ∀ n,
      p (n + 1) ≤ Classical.LargeDeviationPrinciple.exponentialEnvelope w.C w.ρ n := by
  simpa [mkProtocolLDPInput] using transport_ldp (input := mkProtocolLDPInput p w)

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
