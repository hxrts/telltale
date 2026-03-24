import Runtime.Proofs.SchedulerTheoremPack

set_option autoImplicit false

namespace Runtime
namespace Proofs
namespace Examples

section

variable {ι γ π ε ν : Type}
variable [IdentityModel ι] [GuardLayer γ]
variable [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
variable [AuthTree ν] [AccumulatedSet ν]
variable [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
variable [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
variable [IdentityVerificationBridge ι ν]

/-- Round-robin scheduler bundle gates the round-robin artifact on. -/
example (st₀ : ProtocolMachineState ι γ π ε ν)
    (hpol : st₀.sched.policy = .roundRobin) :
    (buildProtocolMachineSchedulerArtifact
      ({ policy := .roundRobin, policyPinned := hpol } : ProtocolMachineSchedulerBundle st₀)
    ).roundRobin?.isSome = true := by
  rfl

/-- Cooperative scheduler bundle gates cooperative normalization on. -/
example (st₀ : ProtocolMachineState ι γ π ε ν)
    (hpol : st₀.sched.policy = .cooperative) :
    (buildProtocolMachineSchedulerArtifact
      ({ policy := .cooperative, policyPinned := hpol } : ProtocolMachineSchedulerBundle st₀)
    ).cooperative?.isSome = true := by
  rfl

/-- Priority scheduler bundle gates the priority artifact on. -/
example (st₀ : ProtocolMachineState ι γ π ε ν)
    (f : CoroutineId → Nat)
    (hpol : st₀.sched.policy = .priority f) :
    (buildProtocolMachineSchedulerArtifact
      ({ policy := .priority f, policyPinned := hpol } : ProtocolMachineSchedulerBundle st₀)
    ).priority?.isSome = true := by
  rfl

/-- Progress-aware scheduler bundle gates the progress-aware artifact on. -/
example (st₀ : ProtocolMachineState ι γ π ε ν)
    (hpol : st₀.sched.policy = .progressAware) :
    (buildProtocolMachineSchedulerArtifact
      ({ policy := .progressAware, policyPinned := hpol } : ProtocolMachineSchedulerBundle st₀)
    ).progressAware?.isSome = true := by
  rfl

end

end Examples
end Proofs
end Runtime
