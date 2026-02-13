import Runtime.Proofs.SchedulerApi
import Runtime.Proofs.TheoremPack.API

set_option autoImplicit false

/-! # Scheduler Theorem Pack

Packaged scheduler artifacts and policy-specific theorem bundles. -/

/-
The Problem. Scheduler correctness proofs involve multiple properties (confluence,
starvation freedom, refinement) that depend on the specific scheduling policy.
Users need packaged artifacts that bundle these properties for each policy type.

Solution Structure. Defines policy-specific artifact structures (RoundRobinPolicyArtifact,
CooperativePolicyArtifact, etc.) with their characteristic properties. The
`VMSchedulerArtifact` bundles all scheduler theorems for a given initial state
with optional policy-specific extensions.
-/

-- Core Development

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

-- Policy-Specific Artifacts

/-- Round-robin profile artifact. -/
structure RoundRobinPolicyArtifact (st₀ : VMState ι γ π ε ν) : Type where
  pinned : SchedulerPolicyPinned st₀ .roundRobin

/-- Cooperative profile artifact. -/
structure CooperativePolicyArtifact (st₀ : VMState ι γ π ε ν) : Type where
  pinned : SchedulerPolicyPinned st₀ .cooperative
  normalization : cooperative_refines_concurrent st₀

/-- Priority profile artifact. -/
structure PriorityPolicyArtifact (st₀ : VMState ι γ π ε ν) : Type where
  priority : CoroutineId → Nat
  pinned : SchedulerPolicyPinned st₀ (.priority priority)

/-- Progress-aware profile artifact. -/
structure ProgressAwarePolicyArtifact (st₀ : VMState ι γ π ε ν) : Type where
  pinned : SchedulerPolicyPinned st₀ .progressAware

/-- Packaged scheduler artifact derived from one scheduler bundle. -/
structure VMSchedulerArtifact (st₀ : VMState ι γ π ε ν) where
  policy : SchedPolicy
  profile : SchedulerPolicyProfile
  policyPinned : SchedulerPolicyPinned st₀ policy
  scheduleConfluence : schedule_confluence st₀
  starvationFree : starvation_free st₀
  cooperativeRefinement : cooperative_refines_concurrent st₀
  roundRobin? : Option (RoundRobinPolicyArtifact (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀)
  cooperative? : Option (CooperativePolicyArtifact (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀)
  priority? : Option (PriorityPolicyArtifact (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀)
  progressAware? :
    Option (ProgressAwarePolicyArtifact (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀)

-- Scheduler Artifact Construction

/-- Build scheduler theorem artifact from a scheduler bundle. -/
def buildVMSchedulerArtifact {st₀ : VMState ι γ π ε ν}
    (bundle : VMSchedulerBundle st₀) : VMSchedulerArtifact st₀ :=
  let roundRobin? :=
    match hpol : bundle.policy with
    | .roundRobin =>
        let pinned : SchedulerPolicyPinned st₀ .roundRobin := by
          simpa [SchedulerPolicyPinned, hpol] using bundle.policyPinned
        some { pinned := pinned }
    | .cooperative => none
    | .priority _ => none
    | .progressAware => none
  let cooperative? :=
    match hpol : bundle.policy with
    | .roundRobin => none
    | .cooperative =>
        let pinned : SchedulerPolicyPinned st₀ .cooperative := by
          simpa [SchedulerPolicyPinned, hpol] using bundle.policyPinned
        some
          { pinned := pinned
          , normalization := cooperative_refines_concurrent_holds st₀
          }
    | .priority _ => none
    | .progressAware => none

  -- Scheduler Artifact Construction: Remaining Policy Cases

  let priority? :=
    match hpol : bundle.policy with
    | .roundRobin => none
    | .cooperative => none
    | .priority f =>
        let pinned : SchedulerPolicyPinned st₀ (.priority f) := by
          simpa [SchedulerPolicyPinned, hpol] using bundle.policyPinned
        some
          { priority := f
          , pinned := pinned
          }
    | .progressAware => none
  let progressAware? :=
    match hpol : bundle.policy with
    | .roundRobin => none
    | .cooperative => none
    | .priority _ => none
    | .progressAware =>
        let pinned : SchedulerPolicyPinned st₀ .progressAware := by
          simpa [SchedulerPolicyPinned, hpol] using bundle.policyPinned
        some
          { pinned := pinned }
  { policy := bundle.policy
  , profile := bundle.profile
  , policyPinned := scheduler_policyPinned_from_bundle bundle
  , scheduleConfluence := scheduler_confluence_from_bundle bundle
  , starvationFree := scheduler_starvationFree_from_bundle bundle
  , cooperativeRefinement := scheduler_cooperativeRefinement_from_bundle bundle
  , roundRobin? := roundRobin?
  , cooperative? := cooperative?
  , priority? := priority?
  , progressAware? := progressAware?
  }

-- Protocol Proof-Space Packaging

/-- Protocol proof space that combines scheduler evidence with invariant-space
profiles for distributed/classical theorem derivation. -/
structure VMProtocolProofSpace (store₀ : SessionStore ν) where
  st₀ : VMState ι γ π ε ν
  store_eq : st₀.sessions = store₀
  scheduler : VMSchedulerBundle st₀
  profiles : VMInvariantSpaceWithProfiles (ν := ν) store₀ (VMState ι γ π ε ν)

/-- Combined proof pack: scheduler artifact + profile-derived theorem pack. -/
structure VMProtocolProofPack
    {store₀ : SessionStore ν}
    (proofSpace : VMProtocolProofSpace (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀)
    where
  scheduler : VMSchedulerArtifact (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) proofSpace.st₀
  theorems : VMTheoremPack (space := proofSpace.profiles)

/-- Build a combined protocol proof pack from one proof space. -/
def buildVMProtocolProofPack
    {store₀ : SessionStore ν}
    (proofSpace : VMProtocolProofSpace (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀) :
    VMProtocolProofPack (proofSpace := proofSpace) :=
  { scheduler := buildVMSchedulerArtifact proofSpace.scheduler
  , theorems := Runtime.Proofs.TheoremPackAPI.mk (space := proofSpace.profiles)
  }

-- Combined Inventory and Iris Bridge

/-- Compact inventory for the combined proof pack. -/
def protocolProofInventory
    {store₀ : SessionStore ν}
    {proofSpace : VMProtocolProofSpace (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀}
    (pack : VMProtocolProofPack (proofSpace := proofSpace)) : List (String × Bool) :=
  [ ("scheduler_policy_pinned", true)
  , ("scheduler_profile_round_robin", pack.scheduler.roundRobin?.isSome)
  , ("scheduler_profile_cooperative", pack.scheduler.cooperative?.isSome)
  , ("scheduler_profile_priority", pack.scheduler.priority?.isSome)
  , ("scheduler_profile_progress_aware", pack.scheduler.progressAware?.isSome)
  , ("scheduler_confluence", true)
  , ("scheduler_starvation_free", true)
  , ("scheduler_cooperative_refinement", true)
  , ("scheduler_cooperative_normalization", pack.scheduler.cooperative?.isSome)
  ] ++ Runtime.Proofs.TheoremPackAPI.capabilities (space := proofSpace.profiles) pack.theorems

/-- Iris scheduler invariance extracted from protocol proof-space scheduler evidence. -/
theorem scheduler_irisInvariant_from_protocolSpace [Telltale.TelltaleIris]
    {store₀ : SessionStore ν}
    (proofSpace : VMProtocolProofSpace (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀) :
    SchedulerIrisInvariant (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) proofSpace.st₀ :=
  scheduler_irisInvariant_from_bundle proofSpace.scheduler

/-- Iris scheduler invariance extracted from a built protocol proof pack. -/
theorem scheduler_irisInvariant_from_protocolPack [Telltale.TelltaleIris]
    {store₀ : SessionStore ν}
    {proofSpace : VMProtocolProofSpace (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀}
    (_pack : VMProtocolProofPack (proofSpace := proofSpace)) :
    SchedulerIrisInvariant (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) proofSpace.st₀ :=
  scheduler_irisInvariant_from_bundle proofSpace.scheduler

end

end Proofs
end Runtime
