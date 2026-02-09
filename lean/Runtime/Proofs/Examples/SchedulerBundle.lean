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
example (st₀ : VMState ι γ π ε ν)
    (hpol : st₀.sched.policy = .roundRobin) :
    (buildVMSchedulerArtifact
      ({ policy := .roundRobin, policyPinned := hpol } : VMSchedulerBundle st₀)
    ).roundRobin?.isSome = true := by
  rfl

/-- Cooperative scheduler bundle gates cooperative normalization on. -/
example (st₀ : VMState ι γ π ε ν)
    (hpol : st₀.sched.policy = .cooperative) :
    (buildVMSchedulerArtifact
      ({ policy := .cooperative, policyPinned := hpol } : VMSchedulerBundle st₀)
    ).cooperative?.isSome = true := by
  rfl

/-- Priority scheduler bundle gates the priority artifact on. -/
example (st₀ : VMState ι γ π ε ν)
    (f : CoroutineId → Nat)
    (hpol : st₀.sched.policy = .priority f) :
    (buildVMSchedulerArtifact
      ({ policy := .priority f, policyPinned := hpol } : VMSchedulerBundle st₀)
    ).priority?.isSome = true := by
  rfl

/-- Progress-aware scheduler bundle gates the progress-aware artifact on. -/
example (st₀ : VMState ι γ π ε ν)
    (hpol : st₀.sched.policy = .progressAware) :
    (buildVMSchedulerArtifact
      ({ policy := .progressAware, policyPinned := hpol } : VMSchedulerBundle st₀)
    ).progressAware?.isSome = true := by
  rfl

end

end Examples
end Proofs
end Runtime
