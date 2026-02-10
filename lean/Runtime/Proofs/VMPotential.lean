import Runtime.Proofs.Lyapunov
import Runtime.VM.Runtime.Failure
import Classical.Transport.API
import Runtime.Proofs.InvariantSpace

/-!
# VM Lyapunov Potential Integration

Runtime-level potential used to connect VM execution to Paper 2's quantitative
liveness story.

This module provides:
- `vmCreditBank`, `vmPotential`
- topology-change nonincrease lemmas
- productive-step work decrease lemma
- explicit bridge to Paper 2 work measure
- VM-level instantiation of transported Foster-Lyapunov (3.9.1)
-/

/-
The Problem. The abstract Lyapunov/progress measure theory needs to be instantiated
at the VM level with concrete definitions (credit banks, potential functions) that
connect to the quantitative liveness bounds from the mathematical physics transport.

Solution Structure. Defines `totalTypeDepth` and `totalTraceLoad` measuring VM state
complexity, then `vmWorkMeasure` combining them as `2 * Σ depth + Σ trace-length`.
Proves topology-change nonincrease and productive-step decrease lemmas, bridging to
the Paper 2 work measure and Foster-Lyapunov transport.
-/

set_option autoImplicit false

section

universe u

def totalTypeDepth {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Nat :=
  ((SessionStore.toGEnv st.sessions).map (fun p => p.2.depth)).foldl (· + ·) 0

def totalTraceLoad {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Nat :=
  ((SessionStore.toDEnv st.sessions).list.map (fun p => p.2.length)).foldl (· + ·) 0

/-- Productive-work measure aligned with Paper 2:
`2 * Σ depth + Σ trace-length`. -/
def vmWorkMeasure {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Nat :=
  2 * totalTypeDepth st + totalTraceLoad st

/-- Credit bank for scheduler/administrative overhead. -/
def vmCreditBank {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Nat :=
  st.sched.readyQueue.length + st.sched.blockedSet.length

/-- Global VM potential = productive work + credit bank. -/
def vmPotential {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Nat :=
  vmWorkMeasure st + vmCreditBank st

theorem vmWorkMeasure_applyTopologyChange_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (tc : TopologyChange (ι := ι)) :
    vmWorkMeasure (applyTopologyChange st tc) = vmWorkMeasure st := by
  cases tc with
  | crash site =>
      by_cases hmem : site ∈ st.crashedSites
      · simp [applyTopologyChange, crashSite, hmem, vmWorkMeasure, totalTypeDepth, totalTraceLoad]
      · simp [applyTopologyChange, crashSite, hmem, vmWorkMeasure, totalTypeDepth, totalTraceLoad]
  | partition edges =>
      simp [applyTopologyChange, disconnectEdges, vmWorkMeasure, totalTypeDepth, totalTraceLoad]
  | heal edges =>
      simp [applyTopologyChange, reconnectEdges, vmWorkMeasure, totalTypeDepth, totalTraceLoad]

theorem vmCreditBank_applyTopologyChange_eq {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (tc : TopologyChange (ι := ι)) :
    vmCreditBank (applyTopologyChange st tc) = vmCreditBank st := by
  cases tc with
  | crash site =>
      by_cases hmem : site ∈ st.crashedSites
      · simp [applyTopologyChange, crashSite, hmem, vmCreditBank]
      · simp [applyTopologyChange, crashSite, hmem, vmCreditBank]
  | partition edges =>
      simp [applyTopologyChange, disconnectEdges, vmCreditBank]
  | heal edges =>
      simp [applyTopologyChange, reconnectEdges, vmCreditBank]

/-- Topology changes do not increase global potential. -/
theorem topology_change_nonincreasing_potential {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (tc : TopologyChange (ι := ι)) :
    vmPotential (applyTopologyChange st tc) ≤ vmPotential st := by
  simp [vmPotential, vmWorkMeasure_applyTopologyChange_eq, vmCreditBank_applyTopologyChange_eq]

/-- Productive VM steps are scheduler steps that strictly decrease work measure. -/
def VMProductiveStep {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st st' : VMState ι γ π ε ν) : Prop :=
  schedStep st = some st' ∧ vmWorkMeasure st' < vmWorkMeasure st

theorem productive_steps_decrease_work_measure {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    {st st' : VMState ι γ π ε ν}
    (hProd : VMProductiveStep st st') :
    vmWorkMeasure st' + 1 ≤ vmWorkMeasure st := by
  exact Nat.succ_le_of_lt hProd.2

/-- Paper 2 work measure instantiated at VM level. -/
def paper2WorkMeasure {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Nat :=
  vmWorkMeasure st

theorem vmWorkMeasure_eq_paper2WorkMeasure {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) :
    vmWorkMeasure st = paper2WorkMeasure st := rfl

theorem vmPotential_extends_paper2WorkMeasure {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) :
    paper2WorkMeasure st ≤ vmPotential st := by
  unfold paper2WorkMeasure vmPotential
  exact Nat.le_add_right (vmWorkMeasure st) (vmCreditBank st)

/-! ## VM-Level Foster-Lyapunov (3.9.1) -/

structure VMFosterAssumptions {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (step : VMState ι γ π ε ν → VMState ι γ π ε ν) : Prop where
  nonincrease : ∀ st, vmPotential (step st) ≤ vmPotential st
  strict_on_pos : ∀ st, vmPotential st ≠ 0 → vmPotential (step st) < vmPotential st

def VMDriftSystem {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (step : VMState ι γ π ε ν → VMState ι γ π ε ν)
    (h : VMFosterAssumptions step) :
    Classical.FosterLyapunovHarris.DriftSystem (VMState ι γ π ε ν) :=
  { step := step
    V := vmPotential
    nonincrease := h.nonincrease
    strict_on_pos := h.strict_on_pos }

def vmFosterCtx {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (step : VMState ι γ π ε ν → VMState ι γ π ε ν)
    (w : Runtime.Proofs.ClassicalTransportWitness (VMState ι γ π ε ν)) :
    Classical.Transport.TransportCtx (VMState ι γ π ε ν) :=
  { step := step
    coherent := w.coherent
    harmony := w.harmony
    finiteState := w.finiteState }

def vmFosterInput {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (step : VMState ι γ π ε ν → VMState ι γ π ε ν)
    (h : VMFosterAssumptions step)
    (w : Runtime.Proofs.ClassicalTransportWitness (VMState ι γ π ε ν)) :
    Classical.Transport.FosterInput (VMState ι γ π ε ν) (vmFosterCtx step w) :=
  { system := VMDriftSystem step h
    step_agrees := rfl }

theorem vm_transported_fosterLyapunov {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (step : VMState ι γ π ε ν → VMState ι γ π ε ν)
    (h : VMFosterAssumptions step)
    (w : Runtime.Proofs.ClassicalTransportWitness (VMState ι γ π ε ν)) :
    Classical.Transport.FosterConclusion (vmFosterInput step h w) := by
  exact Classical.Transport.transported_fosterLyapunov (input := vmFosterInput step h w)

theorem r7_vm_potential_integration {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (step : VMState ι γ π ε ν → VMState ι γ π ε ν)
    (h : VMFosterAssumptions step)
    (w : Runtime.Proofs.ClassicalTransportWitness (VMState ι γ π ε ν)) :
    ∀ st n, vmPotential ((step^[n]) st) ≤ vmPotential st := by
  intro st n
  exact vm_transported_fosterLyapunov step h w st n
