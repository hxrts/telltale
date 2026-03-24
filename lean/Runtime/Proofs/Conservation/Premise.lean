import Runtime.Proofs.ProgressApi
import Runtime.Proofs.ProtocolMachine.Effects
import Runtime.Proofs.ProtocolMachine.Scheduler
import Runtime.Proofs.ProtocolMachine.SemanticObjects.ProgressContracts

set_option autoImplicit false

/-!
# Runtime.Proofs.Conservation.Premise

Direct theorem surface for premise conservation.
-/

namespace Runtime
namespace Proofs
namespace Conservation

open Runtime.ProtocolMachine.Model

theorem blocking_effects_require_explicit_timeout
    (metadata : EffectInterfaceMetadata)
    (hLegal : metadata.architecturallyLegal)
    (hMayBlock : metadata.totality = .mayBlock) :
    metadata.timeoutRequired :=
  Runtime.ProtocolMachine.Model.mayBlock_requires_timeout metadata hLegal hMayBlock

theorem retrying_effects_require_explicit_timeout
    (metadata : EffectInterfaceMetadata)
    (hLegal : metadata.architecturallyLegal)
    (hRetry : metadata.hasExplicitRetryRule) :
    metadata.timeoutRequired :=
  Runtime.ProtocolMachine.Model.retry_requires_timeout metadata hLegal hRetry

theorem progress_contract_has_synthetic_progress_until_terminal
    (contract : ProgressContract)
    (hNonTerminal : ¬ contract.isTerminal) :
    ∃ next, contract.syntheticStep = some next :=
  Runtime.ProtocolMachine.Model.syntheticStep_progress contract hNonTerminal

theorem progress_contract_is_scheduling_bound_compatible
    (contract : ProgressContract) :
    contract.schedulingBoundCompatible :=
  Runtime.ProtocolMachine.Model.schedulingBoundCompatible_of_progressContract contract

theorem scheduler_is_starvation_free
    {ι γ π ε ν : Type} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) :
    starvation_free st :=
  starvation_free_holds st

theorem fairness_bundle_yields_termination
    {ν : Type} [VerificationModel ν]
    {store₀ : SessionStore ν}
    (bundle : ProtocolMachineLivenessBundle store₀) :
    ∃ (n : Nat) (storeFinal : SessionStore ν),
      storeFinal = executeSchedule bundle.model.step store₀ bundle.fairness.sched n ∧
      AllSessionsComplete storeFinal ∧
      n ≤ bundle.fairness.k * protocolMachineMeasure store₀ :=
  protocol_machine_termination_from_bundle bundle

end Conservation
end Proofs
end Runtime
