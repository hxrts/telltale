import Runtime.VM.TypeClasses
import Runtime.VM.Core
import Runtime.VM.SchedulerTypes
import Runtime.VM.Violation
import Runtime.Monitor.DomainComposition
import Runtime.Resources.BufferRA

/-
The Problem. The VM needs a configuration record that ties together domain
interfaces, scheduling, buffering, and policy hooks while staying parametric.

Solution Structure. Define a small `CostModel` and a `VMConfig` structure
that references spec-level types only (no proof imports).
-/

set_option autoImplicit false

universe u

/-! ## Cost model -/

structure CostModel (γ ε : Type u) [GuardLayer γ] [EffectModel ε] where
  -- Cost per instruction; used for budgeting and bounds.
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

structure VMConfig (ι γ π ε : Type u)
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectModel ε]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] where
  -- Buffering policy per edge.
  bufferConfig : Edge → BufferConfig
  -- Scheduling policy.
  schedPolicy : SchedPolicy
  -- Violation handling policy.
  violationPolicy : ViolationPolicy
  -- Resource bounds.
  maxCoroutines : Nat
  maxSessions : Nat
  -- Guard chain configuration.
  guardChain : GuardChain γ
  guardChainWf : GuardChain.wf guardChain
  -- Cost metering policy (§21).
  costModel : CostModel γ ε
  -- Speculation toggle and bound (§17).
  speculationEnabled : Bool
  maxSpeculationDepth : Nat := 16
