import Runtime.Proofs.SchedulerTheoremPack
import Runtime.Proofs.Contracts.DeterminismApi
import Runtime.VM.Runtime.Scheduler
import Runtime.VM.Runtime.ThreadedRunner

set_option autoImplicit false

/-! # Runtime.Proofs.Contracts.RuntimeContracts

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

/-! ## Contract Components -/

/-- Cross-lane handoffs must represent actual delegation/capability transfer and
never a no-op self-handoff. -/
def DelegationOnlyCrossLaneHandoff (st : VMState ι γ π ε ν) : Prop :=
  ∀ h ∈ st.sched.crossLaneHandoffs,
    h.fromCoro ≠ h.toCoro ∧
    h.reason.startsWith "transfer " ∧
    h.delegationWitness.length > 0

/-- Proof-carrying protocol admission contract:
requires scheduler evidence plus theorem-pack evidence in one proof space. -/
structure ProtocolAdmissionContract (store₀ : SessionStore ν) where
  proofSpace : VMProtocolProofSpace (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀
  proofPack : VMProtocolProofPack (proofSpace := proofSpace)

/-- Proof-guided concurrency contract: runtime may step coroutines in parallel
only when a proof-level eligibility predicate certifies the pair. -/
structure ProofGuidedConcurrencyContract (st₀ : VMState ι γ π ε ν) where
  eligible : CoroutineId → CoroutineId → Prop
  eligibleDecidable : DecidableRel eligible
  symmetric : ∀ a b, eligible a b → eligible b a
  irreflexive : ∀ a, ¬ eligible a a
  frameGuarded : ∀ a b, eligible a b → a ≠ b

/-- Boolean eligibility hook extracted from the proof-guided contract. -/
def proofGuidedEligibleB {st₀ : VMState ι γ π ε ν}
    (contract : ProofGuidedConcurrencyContract (ι := ι) (γ := γ)
      (π := π) (ε := ε) (ν := ν) st₀)
    (a b : CoroutineId) : Bool :=
  let _ := contract.eligibleDecidable
  decide (contract.eligible a b)

/-- Connect deterministic wave planning to proof-guided eligibility. -/
def planDeterministicWavesByContract {st₀ : VMState ι γ π ε ν}
    (contract : ProofGuidedConcurrencyContract (ι := ι) (γ := γ)
      (π := π) (ε := ε) (ν := ν) st₀) :
    List (List CoroutineId) :=
  planDeterministicWavesEligible st₀ (proofGuidedEligibleB contract)

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

/-! ## Combined Runtime Bundle -/

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

/-- Runtime admission mode classifier: multi-lane scheduling or speculation
requires proof-carrying runtime contracts. -/
private def schedPolicyRequiresContracts : SchedPolicy → Bool
  | .cooperative => false
  | _ => true

def requiresVMRuntimeContracts (cfg : VMConfig ι γ π ε ν) : Bool :=
  schedPolicyRequiresContracts cfg.schedPolicy || cfg.speculationEnabled

/-- VM admission result for advanced runtime mode checks. -/
inductive VMAdmissionResult where
  | admitted
  | rejectedMissingContracts
  deriving Repr, DecidableEq

/-- VM admission path: advanced runtime modes require `VMRuntimeContracts`. -/
def admitVMRuntime
    (cfg : VMConfig ι γ π ε ν)
    {store₀ : SessionStore ν}
    (contracts? : Option (VMRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀)) :
    VMAdmissionResult :=
  if requiresVMRuntimeContracts cfg then
    match contracts? with
    | some _ => .admitted
    | none => .rejectedMissingContracts
  else
    .admitted

/-- Advanced-mode admission succeeds only when contracts are supplied. -/
theorem admitVMRuntime_requires_contracts
    (cfg : VMConfig ι γ π ε ν) {store₀ : SessionStore ν}
    (hReq : requiresVMRuntimeContracts cfg = true)
    (contracts? : Option (VMRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀)) :
    admitVMRuntime cfg contracts? = .admitted ↔ contracts?.isSome = true := by
  unfold admitVMRuntime
  simp [hReq]
  cases contracts? <;> simp

/-- Live migration request payload. -/
structure LiveMigrationRequest where
  sid : SessionId
  role : Role
  fromLane : LaneId
  toLane : LaneId

/-- Theorem-gated live migration capability check. -/
def canUseLiveMigration
    {store₀ : SessionStore ν}
    (contracts : VMRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀) :
    Bool :=
  Runtime.Proofs.TheoremPackAPI.canLiveMigrate contracts.capabilities.theoremPack

/-- Theorem-gated placement-refinement switch. -/
def canUsePlacementRefinement
    {store₀ : SessionStore ν}
    (contracts : VMRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀) :
    Bool :=
  Runtime.Proofs.TheoremPackAPI.canRefinePlacement contracts.capabilities.theoremPack

/-- Theorem-gated relaxed-reordering switch. -/
def canUseRelaxedReordering
    {store₀ : SessionStore ν}
    (contracts : VMRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀) :
    Bool :=
  Runtime.Proofs.TheoremPackAPI.canRelaxReordering contracts.capabilities.theoremPack

/-- Theorem-gated live migration API: only admits requests when capability
evidence is present in the theorem pack. -/
def requestLiveMigration
    {store₀ : SessionStore ν}
    (contracts : VMRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀)
    (req : LiveMigrationRequest) : Option LiveMigrationRequest :=
  if canUseLiveMigration contracts then some req else none

/-- Autoscale/repartition request payload. -/
structure AutoscaleRequest where
  targetShards : Nat
  reason : String

/-- Theorem-gated autoscale/repartition capability check. -/
def canUseAutoscaleOrRepartition
    {store₀ : SessionStore ν}
    (contracts : VMRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀) :
    Bool :=
  Runtime.Proofs.TheoremPackAPI.canAutoscaleOrRepartition
    contracts.capabilities.theoremPack

/-- Theorem-gated autoscale/repartition API. -/
def requestAutoscaleOrRepartition
    {store₀ : SessionStore ν}
    (contracts : VMRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀)
    (req : AutoscaleRequest) : Option AutoscaleRequest :=
  if canUseAutoscaleOrRepartition contracts then some req else none

/-- Theorem-gated refinement switch API. -/
def requestPlacementRefinement
    {store₀ : SessionStore ν}
    (contracts : VMRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀)
    (enabled : Bool) : Option Bool :=
  if canUsePlacementRefinement contracts then some enabled else none

/-- Theorem-gated reordering switch API. -/
def requestRelaxedReordering
    {store₀ : SessionStore ν}
    (contracts : VMRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀)
    (enabled : Bool) : Option Bool :=
  if canUseRelaxedReordering contracts then some enabled else none

/-- Runtime capability snapshot emitted at startup. -/
def runtimeCapabilitySnapshot
    {store₀ : SessionStore ν}
    (contracts : VMRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀) :
    List (String × Bool) :=
  contracts.capabilities.capabilityInventory ++
    [ ("live_migration", canUseLiveMigration contracts)
    , ("autoscale_repartition", canUseAutoscaleOrRepartition contracts)
    , ("placement_refinement", canUsePlacementRefinement contracts)
    , ("relaxed_reordering", canUseRelaxedReordering contracts)
    ]

/-- Artifact check for one runtime determinism profile. -/
def determinismProfileSupported
    (artifacts : VMDeterminismArtifacts)
    (profile : VMDeterminismProfile) : Bool :=
  match profile with
  | .full => artifacts.full
  | .moduloEffectTrace => artifacts.moduloEffectTrace
  | .moduloCommutativity => artifacts.moduloCommutativity
  | .replay => artifacts.replay

/-- Runtime profile selection gate for
`full`, `moduloEffectTrace`, `moduloCommutativity`, and `replay`. -/
def requestDeterminismProfile
    {store₀ : SessionStore ν}
    (contracts : VMRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀)
    (artifacts : VMDeterminismArtifacts)
    (profile : VMDeterminismProfile) : Option VMDeterminismProfile :=
  let mixedOk :=
    Runtime.Proofs.TheoremPackAPI.canUseMixedDeterminismProfiles
      contracts.capabilities.theoremPack
  let supported := determinismProfileSupported artifacts profile
  let allowed :=
    match profile with
    | .full => supported
    | .moduloEffectTrace | .moduloCommutativity | .replay => mixedOk && supported
  if allowed then some profile else none

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
  let minimal :=
    Runtime.Proofs.TheoremPackAPI.minimalCapabilities (space := space) pack
  { theoremPack := pack
  , capabilityInventory := minimal.map (fun name => (name, true))
  }

end

end Proofs
end Runtime
