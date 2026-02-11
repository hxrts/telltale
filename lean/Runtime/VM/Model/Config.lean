import Runtime.VM.Model.TypeClasses
import Runtime.VM.Model.Domain
import Runtime.VM.Model.Core
import Runtime.VM.Model.OutputCondition
import Runtime.VM.Model.Knowledge
import Runtime.Resources.ResourceModel
import Runtime.VM.Model.SchedulerTypes
import Runtime.VM.Model.Violation
import Runtime.VM.Runtime.Monitor
import Runtime.Resources.BufferRA

/-!
# VM Configuration

`CostModel` and `VMConfig`, the static configuration that parameterizes a VM instance.
`VMConfig` bundles buffer policies, scheduling policy, violation handling, knowledge flow
policy, spatial requirement hooks, handler transport-spec checks, guard chain configuration,
signing keys, cost metering, and speculation settings. All five domain interfaces
(`ι`, `γ`, `π`, `ε`, `ν`) plus their bridge classes appear as typeclass constraints.

This file imports only spec-level types (no proof modules). The `VMConfig` record is
threaded through `VMState` and read by every instruction stepper.
-/

set_option autoImplicit false

universe u

/-! ## Cost model -/

structure CostModel (γ ε : Type u) [GuardLayer γ] [EffectRuntime ε] where
  -- Cost per instruction, used for budgeting and bounds.
  stepCost : Instr γ ε → Nat
  -- Minimum cost for any non-halt instruction.
  minCost : Nat
  -- Default budget for newly spawned coroutines.
  defaultBudget : Nat
  -- Every non-halt instruction costs at least `minCost`.
  hMinCost : ∀ i, i ≠ .halt → stepCost i ≥ minCost
  -- Minimum cost is positive.
  hMinPos : minCost ≥ 1

/-! ## VM configuration -/

structure VMRuntimeConfig (ι γ π ε ν : Type u) [VMDomain ι γ π ε ν] where
  -- Migration-safe config schema version.
  configVersion : Nat := 1
  -- VM configuration fields for policies and hooks.
  bufferConfig : Edge → BufferConfig
  schedPolicy : SchedPolicy := .cooperative
  violationPolicy : ViolationPolicy
  flowPolicy : FlowPolicy := .allowAll
  spatialOk : RoleSet → Bool
  transportOk : HandlerId → SignedBuffers ν → Bool
  complianceProof : Resource ν → ComplianceProof ν
  maxCoroutines : Nat := 1024
  maxSessions : Nat := 256
  monitorMode : MonitorMode := .sessionTypePrecheck
  guardChain : GuardChain γ
  roleSigningKey : Role → VerificationModel.SigningKey ν
  outputCondition : OutputConditionConfig := {}
  costModel : CostModel γ ε
  speculationEnabled : Bool
  maxSpeculationDepth : Nat := 16

structure VMProofConfig (γ : Type u) [GuardLayer γ] (guardChain : GuardChain γ) where
  -- Well-formedness witnesses kept separate from executable runtime fields.
  guardChainWf : GuardChain.wf guardChain

structure VMConfig (ι γ π ε ν : Type u) [VMDomain ι γ π ε ν]
    extends VMRuntimeConfig ι γ π ε ν where
  proofConfig : VMProofConfig γ toVMRuntimeConfig.guardChain

def VMConfig.guardChainWf {ι γ π ε ν : Type u} [VMDomain ι γ π ε ν]
    (cfg : VMConfig ι γ π ε ν) : GuardChain.wf cfg.guardChain :=
  cfg.proofConfig.guardChainWf

def deterministic_finalization_ok {ι γ π ε ν : Type u}
    [VMDomain ι γ π ε ν]
    (_cfg : VMConfig ι γ π ε ν) : Prop :=
  -- Safety violations halt execution deterministically.
  (∀ msg, _cfg.violationPolicy.allow (.safety msg) = false) ∧
  -- Speculation depth is bounded when enabled.
  (_cfg.speculationEnabled → _cfg.maxSpeculationDepth > 0) ∧
  -- Cost budget supports at least one minimum-cost step.
  (_cfg.costModel.defaultBudget ≥ _cfg.costModel.minCost) ∧
  -- Persistence deltas commute (deterministic state reconstruction).
  (∀ (s : PersistenceModel.PState (π := π))
     (d1 d2 : PersistenceModel.Delta (π := π)),
    PersistenceModel.apply (PersistenceModel.apply s d1) d2 =
    PersistenceModel.apply (PersistenceModel.apply s d2) d1)
