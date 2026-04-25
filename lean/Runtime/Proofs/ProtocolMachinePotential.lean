import Runtime.Proofs.Lyapunov
import Runtime.ProtocolMachine.Runtime.Failure
import Classical.Transport.API
import Runtime.Proofs.InvariantSpace

/-! # Protocol-Machine Lyapunov Potential Integration

Runtime-level potential used to connect protocol-machine execution to Paper 2's quantitative
liveness story.

This module provides:
- `protocolMachineCreditBank`, `protocolMachinePotential`
- topology-change nonincrease lemmas
- productive-step work decrease lemma
- explicit bridge to Paper 2 work measure
- protocol-machine instantiation of transported Foster-Lyapunov (3.9.1) -/

/-
The Problem. The abstract Lyapunov/progress measure theory needs to be instantiated
at the protocol-machine level with concrete definitions (credit banks, potential functions) that
connect to the quantitative liveness bounds from the mathematical physics transport.

Solution Structure. Defines `totalTypeDepth` and `totalTraceLoad` measuring protocol-machine state
complexity, then `protocolMachineWorkMeasure` combining them as `2 * Σ depth + Σ trace-length`.
Proves topology-change nonincrease and productive-step decrease lemmas, bridging to
the Paper 2 work measure and Foster-Lyapunov transport.
-/

set_option autoImplicit false

section

universe u

/-! ## Core Potential Measures -/

def totalTypeDepth {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) : Nat :=
  ((SessionStore.toGEnv st.sessions).map (fun p => p.2.depth)).foldl (· + ·) 0

def totalTraceLoad {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) : Nat :=
  ((SessionStore.toDEnv st.sessions).list.map (fun p => p.2.length)).foldl (· + ·) 0

/-- Productive-work measure aligned with Paper 2:
`2 * Σ depth + Σ trace-length`. -/
def protocolMachineWorkMeasure {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) : Nat :=
  2 * totalTypeDepth st + totalTraceLoad st

/-- Credit bank for scheduler/administrative overhead. -/
def protocolMachineCreditBank {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) : Nat :=
  st.sched.readyQueue.length + st.sched.blockedSet.toList.length

/-- Global protocol-machine potential = productive work + credit bank. -/
def protocolMachinePotential {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) : Nat :=
  protocolMachineWorkMeasure st + protocolMachineCreditBank st

/-! ## Topology-Change Invariance -/

theorem protocol_machine_work_measure_apply_topology_change_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (tc : TopologyChange (ι := ι)) :
    protocolMachineWorkMeasure (applyTopologyChange st tc) = protocolMachineWorkMeasure st := by
  cases tc with
  | crash site =>
      by_cases hmem : site ∈ st.crashedSites
      · simp [applyTopologyChange, crashSite, hmem, protocolMachineWorkMeasure, totalTypeDepth, totalTraceLoad]
      · simp [applyTopologyChange, crashSite, hmem, protocolMachineWorkMeasure, totalTypeDepth, totalTraceLoad]
  | partition edges =>
      simp [applyTopologyChange, disconnectEdges, protocolMachineWorkMeasure, totalTypeDepth, totalTraceLoad]
  | heal edges =>
      simp [applyTopologyChange, reconnectEdges, protocolMachineWorkMeasure, totalTypeDepth, totalTraceLoad]

theorem protocol_machine_credit_bank_apply_topology_change_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (tc : TopologyChange (ι := ι)) :
    protocolMachineCreditBank (applyTopologyChange st tc) = protocolMachineCreditBank st := by
  cases tc with
  | crash site =>
      by_cases hmem : site ∈ st.crashedSites
      · simp [applyTopologyChange, crashSite, hmem, protocolMachineCreditBank]
      · simp [applyTopologyChange, crashSite, hmem, protocolMachineCreditBank]
  | partition edges =>
      simp [applyTopologyChange, disconnectEdges, protocolMachineCreditBank]
  | heal edges =>
      simp [applyTopologyChange, reconnectEdges, protocolMachineCreditBank]

/-- Topology changes do not increase global potential. -/
theorem topology_change_nonincreasing_potential {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (tc : TopologyChange (ι := ι)) :
    protocolMachinePotential (applyTopologyChange st tc) ≤ protocolMachinePotential st := by
  simp [protocolMachinePotential, protocol_machine_work_measure_apply_topology_change_eq, protocol_machine_credit_bank_apply_topology_change_eq]

/-! ## Productive-Step Work Decrease -/

/-- Productive protocol-machine steps are scheduler steps that strictly decrease work measure. -/
def ProtocolMachineProductiveStep {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st st' : ProtocolMachineState ι γ π ε ν) : Prop :=
  schedStep st = some st' ∧ protocolMachineWorkMeasure st' < protocolMachineWorkMeasure st

theorem productive_steps_decrease_work_measure {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    {st st' : ProtocolMachineState ι γ π ε ν}
    (hProd : ProtocolMachineProductiveStep st st') :
    protocolMachineWorkMeasure st' + 1 ≤ protocolMachineWorkMeasure st := by
  exact Nat.succ_le_of_lt hProd.2

/-! ## Paper 2 Work-Measure Bridge -/

/-- Paper 2 work measure instantiated at protocol-machine level. -/
def paper2WorkMeasure {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) : Nat :=
  protocolMachineWorkMeasure st

theorem protocol_machine_work_measure_eq_paper2_work_measure {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) :
    protocolMachineWorkMeasure st = paper2WorkMeasure st := rfl

theorem protocol_machine_potential_extends_paper2_work_measure {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) :
    paper2WorkMeasure st ≤ protocolMachinePotential st := by
  unfold paper2WorkMeasure protocolMachinePotential
  exact Nat.le_add_right (protocolMachineWorkMeasure st) (protocolMachineCreditBank st)

/-! ## Protocol-Machine Foster-Lyapunov (3.9.1) -/
/-! ### Drift Assumptions and Systems -/

structure ProtocolMachineFosterAssumptions {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (step : ProtocolMachineState ι γ π ε ν → ProtocolMachineState ι γ π ε ν) : Prop where
  nonincrease : ∀ st, protocolMachinePotential (step st) ≤ protocolMachinePotential st
  strict_on_pos : ∀ st, protocolMachinePotential st ≠ 0 → protocolMachinePotential (step st) < protocolMachinePotential st

def ProtocolMachineDriftSystem {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (step : ProtocolMachineState ι γ π ε ν → ProtocolMachineState ι γ π ε ν)
    (h : ProtocolMachineFosterAssumptions step) :
    Classical.FosterLyapunovHarris.DriftSystem (ProtocolMachineState ι γ π ε ν) :=
  { step := step
    V := protocolMachinePotential
    nonincrease := h.nonincrease
    strict_on_pos := h.strict_on_pos }

/-! ### Transport Context and Input -/

def protocolMachineFosterCtx {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (step : ProtocolMachineState ι γ π ε ν → ProtocolMachineState ι γ π ε ν)
    (w : Runtime.Proofs.ClassicalTransportWitness (ProtocolMachineState ι γ π ε ν)) :
    Classical.Transport.TransportCtx (ProtocolMachineState ι γ π ε ν) :=
  { step := step
    coherent := w.coherent
    harmony := w.harmony
    finiteState := w.finiteState }

def protocolMachineFosterInput {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (step : ProtocolMachineState ι γ π ε ν → ProtocolMachineState ι γ π ε ν)
    (h : ProtocolMachineFosterAssumptions step)
    (w : Runtime.Proofs.ClassicalTransportWitness (ProtocolMachineState ι γ π ε ν)) :
    Classical.Transport.FosterInput (ProtocolMachineState ι γ π ε ν) (protocolMachineFosterCtx step w) :=
  { system := ProtocolMachineDriftSystem step h
    step_agrees := rfl }

/-! ### Transported Foster Conclusions -/

theorem protocol_machine_transported_foster_lyapunov {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (step : ProtocolMachineState ι γ π ε ν → ProtocolMachineState ι γ π ε ν)
    (h : ProtocolMachineFosterAssumptions step)
    (w : Runtime.Proofs.ClassicalTransportWitness (ProtocolMachineState ι γ π ε ν)) :
    Classical.Transport.FosterConclusion (protocolMachineFosterInput step h w) := by
  -- Prove the transported conclusion directly to avoid leaving universe
  -- metavariables from the polymorphic facade theorem in this wrapper.
  intro s n
  exact Classical.FosterLyapunovHarris.DriftSystem.iterate_nonincrease
    (S := (protocolMachineFosterInput step h w).system) s n

theorem r7_protocol_machine_potential_integration {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (step : ProtocolMachineState ι γ π ε ν → ProtocolMachineState ι γ π ε ν)
    (h : ProtocolMachineFosterAssumptions step)
    (w : Runtime.Proofs.ClassicalTransportWitness (ProtocolMachineState ι γ π ε ν)) :
    ∀ st n, protocolMachinePotential ((step^[n]) st) ≤ protocolMachinePotential st := by
  intro st n
  exact protocol_machine_transported_foster_lyapunov step h w st n
