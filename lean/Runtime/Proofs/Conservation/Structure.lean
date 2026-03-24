import Protocol.Deployment.LinkingTheorems
import Runtime.Proofs.Concurrency
import Runtime.Proofs.ProtocolMachine.Scheduler

set_option autoImplicit false

/-!
# Runtime.Proofs.Conservation.Structure

Direct theorem surface for structure conservation.
-/

namespace Runtime
namespace Proofs
namespace Conservation

theorem composed_protocol_structure_preserved_by_delegation
    (G₁ G₁' G₂ : GEnv) (D₁ D₁' D₂ : DEnv)
    (s : SessionId) (A B : Role)
    (hDeleg : DelegationStep G₁ G₁' D₁ D₁' s A B)
    (hCoh₁ : Coherent G₁ D₁)
    (hCoh₂ : Coherent G₂ D₂)
    (hDisjG : DisjointG G₁ G₂)
    (hDisjG' : DisjointG G₁' G₂)
    (hCons₁ : DConsistent G₁ D₁)
    (hCons₁' : DConsistent G₁' D₁')
    (hCons₂ : DConsistent G₂ D₂) :
    Coherent (mergeGEnv G₁ G₂) (mergeDEnv D₁ D₂) ∧
      Coherent (mergeGEnv G₁' G₂) (mergeDEnv D₁' D₂) :=
  flagship_composed_system_conservation
    G₁ G₁' G₂ D₁ D₁' D₂ s A B hDeleg hCoh₁ hCoh₂ hDisjG hDisjG' hCons₁ hCons₁' hCons₂

theorem cooperative_scheduler_refines_concurrent_structure
    {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) :
    cooperative_refines_concurrent st :=
  cooperative_refines_concurrent_holds st

theorem per_session_trace_is_invariant_under_scheduler_round_normalization
    {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν)
    (hWf : WFVMState st) (sid : SessionId) (fuel n₁ n₂ : Nat)
    (hN₁ : n₁ ≥ 1) (hN₂ : n₂ ≥ 1) :
    filterBySid sid (Runtime.ProtocolMachine.normalizeTrace (runScheduled fuel n₁ st).obsTrace) =
      filterBySid sid (Runtime.ProtocolMachine.normalizeTrace (runScheduled fuel n₂ st).obsTrace) :=
  per_session_trace_n_invariant st hWf sid fuel n₁ n₂ hN₁ hN₂

end Conservation
end Proofs
end Runtime
