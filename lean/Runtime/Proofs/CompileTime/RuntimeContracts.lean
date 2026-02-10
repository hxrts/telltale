import Runtime.Proofs.SchedulerTheoremPack
import Runtime.VM.Runtime.Scheduler

set_option autoImplicit false

/-! # Runtime.Proofs.CompileTime.RuntimeContracts

Lean-facing runtime contract surface for proof-carrying VM admission and
capability gating. This module packages the contract classes referenced by the
runtime architecture plan:

- protocol admission (composition/linking + theorem-pack evidence),
- delegation/capability-only cross-lane handoff discipline,
- proof-guided concurrency eligibility hooks,
- scheduler profile certification,
- theorem-pack capability inventory exposure.
-/

namespace Runtime
namespace Proofs

section

variable {ι γ π ε ν : Type}
variable [IdentityModel ι] [GuardLayer γ]
variable [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
variable [AuthTree ν] [AccumulatedSet ν]
variable [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
variable [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
variable [IdentityVerificationBridge ι ν]

/-- Cross-lane handoffs must represent actual delegation/capability transfer and
never a no-op self-handoff. -/
def DelegationOnlyCrossLaneHandoff (st : VMState ι γ π ε ν) : Prop :=
  ∀ h ∈ st.sched.crossLaneHandoffs, h.fromCoro ≠ h.toCoro ∧ h.endpoint.sid = h.sid

/-- Proof-carrying protocol admission contract:
requires scheduler evidence plus theorem-pack evidence in one proof space. -/
structure ProtocolAdmissionContract (store₀ : SessionStore ν) where
  proofSpace : VMProtocolProofSpace (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀
  proofPack : VMProtocolProofPack (proofSpace := proofSpace)

/-- Proof-guided concurrency contract: runtime may step coroutines in parallel
only when a proof-level eligibility predicate certifies the pair. -/
structure ProofGuidedConcurrencyContract (st₀ : VMState ι γ π ε ν) where
  eligible : CoroutineId → CoroutineId → Prop
  symmetric : ∀ a b, eligible a b → eligible b a
  irreflexive : ∀ a, ¬ eligible a a
  frameGuarded : ∀ a b, eligible a b → a ≠ b

/-- Scheduler profile contract: runtime policy selection is backed by a certified
scheduler bundle and profile extraction theorem. -/
structure SchedulerProfileContract (st₀ : VMState ι γ π ε ν) where
  bundle : VMSchedulerBundle st₀
  profilePinned : schedulerPolicyProfileOf st₀.sched.policy = bundle.profile

/-- Theorem-pack capability contract: advanced runtime modes are gated by the
inventory materialized from theorem-pack evidence. -/
structure TheoremPackCapabilityContract
    {store₀ : SessionStore ν} {State : Type}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State) where
  theoremPack : VMTheoremPack (space := space)
  capabilityInventory : List (String × Bool)

/-- Combined runtime contract bundle threaded into VM admission/runtime policy. -/
structure VMRuntimeContracts (store₀ : SessionStore ν) where
  admission : ProtocolAdmissionContract (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀
  delegationOnly :
    DelegationOnlyCrossLaneHandoff (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν)
      admission.proofSpace.st₀
  concurrency :
    ProofGuidedConcurrencyContract (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν)
      admission.proofSpace.st₀
  scheduler :
    SchedulerProfileContract admission.proofSpace.st₀
  capabilities :
    TheoremPackCapabilityContract admission.proofSpace.profiles

/-- Build a scheduler profile contract from bundle evidence. -/
def SchedulerProfileContract.ofBundle {st₀ : VMState ι γ π ε ν}
    (bundle : VMSchedulerBundle st₀) :
    SchedulerProfileContract st₀ :=
  { bundle := bundle
  , profilePinned := scheduler_profilePinned_from_bundle bundle
  }

/-- Build a theorem-pack capability contract from a proof space. -/
def TheoremPackCapabilityContract.ofProofSpace
    {store₀ : SessionStore ν} {State : Type}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    TheoremPackCapabilityContract space :=
  let pack := Runtime.Proofs.TheoremPackAPI.mk (space := space)
  { theoremPack := pack
  , capabilityInventory := Runtime.Proofs.TheoremPackAPI.capabilities (space := space) pack
  }

end

end Proofs
end Runtime
