import Runtime.VM.TypeClasses
import Runtime.VM.Core
import Runtime.VM.Knowledge
import Runtime.Resources.ResourceModel
import Runtime.VM.SchedulerTypes
import Runtime.VM.Violation
import Runtime.VM.DomainComposition
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

structure CostModel (γ ε : Type u) [GuardLayer γ] [EffectModel ε] where
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

structure VMConfig (ι γ π ε ν : Type u)
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectModel ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν] where
  -- VM configuration fields for policies and hooks.
  bufferConfig : Edge → BufferConfig
  schedPolicy : SchedPolicy
  violationPolicy : ViolationPolicy
  flowPolicy : FlowPolicy
  spatialOk : RoleSet → Bool
  transportOk : HandlerId → SignedBuffers ν → Bool
  complianceProof : Resource ν → ComplianceProof ν
  maxCoroutines : Nat
  maxSessions : Nat
  guardChain : GuardChain γ
  guardChainWf : GuardChain.wf guardChain
  roleSigningKey : Role → VerificationModel.SigningKey ν
  costModel : CostModel γ ε
  speculationEnabled : Bool
  maxSpeculationDepth : Nat := 16

def deterministic_finalization_ok {ι γ π ε ν : Type u}
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectModel ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (_cfg : VMConfig ι γ π ε ν) : Prop :=
  -- Placeholder: deterministic handlers, agreed time, no nondet reads, persistence commutes.
  True
