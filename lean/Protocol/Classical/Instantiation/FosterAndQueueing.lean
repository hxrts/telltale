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

/-
The Problem. Classical queueing theory results (Foster-Lyapunov, large deviations)
apply to session-typed protocols, but we need concrete instantiations that connect
coherence and progress measures to the abstract transport API.

Solution Structure. We define:
1. `WTConfigNState`: coherence-projected state space (erasure-level image)
2. `protocolV`: progress measure from type depth + buffer length + send potential
3. `FosterLivenessAssumptions`: side conditions for Foster transport
4. Concrete theorem instantiations for each classical family
-/

/-! ## Core Development -/

namespace ProtocolClassical

/-! ## Foster-Lyapunov State and Assumptions -/

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

/-! ## Foster Drift System Wiring -/

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

/-! ## Foster Iterate Bound (R.7) -/

/-- 3.9.1: R.7 bridge statement (Lyapunov potential bound along iterates). -/
theorem r7_lyapunov_potential_integration
    (step : FStep) (μ : ProgressMeasureComponents)
    (h : FosterLivenessAssumptions step μ)
    (hSide : ProtocolFosterSideConditions) :
    ∀ st n, protocolV μ ((step^[n]) st) ≤ protocolV μ st := by
  intro st n
  exact protocol_transported_fosterLyapunov step μ h hSide st n

/-! ## MaxWeight Instantiation -/

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

/-! ## Large-Deviation and Heavy-Traffic Instantiation -/

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

end ProtocolClassical

end
