import Runtime.Proofs.SchedulerTheoremPack
import Runtime.Proofs.Contracts.DeterminismApi
import Runtime.ProtocolMachine.Runtime.Scheduler
import Runtime.ProtocolMachine.Runtime.ThreadedRunner

set_option autoImplicit false

/-! # Runtime.Proofs.Contracts.RuntimeContracts

Lean-facing runtime contract surface for proof-carrying protocol machine admission and
capability gating. This module packages the contract classes referenced by the
runtime architecture plan:

- protocol admission (composition/linking + theorem-pack evidence),
- delegation/capability-only cross-lane handoff discipline,
- proof-guided concurrency eligibility hooks,
- scheduler profile certification,
- theorem-pack capability inventory exposure.
-/

/-
The Problem. Runtime admission and capability gating need one Lean-facing contract
surface that runtime code can query without importing internal proof-pack modules.

Solution Structure. This file defines small contract records and gate functions,
then groups API-level checks (admission, migration, autoscaling, determinism) in
separate sections so the runtime boundary is explicit.
-/

namespace Runtime
namespace Proofs

universe u v

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
def DelegationOnlyCrossLaneHandoff (st : ProtocolMachineState ι γ π ε ν) : Prop :=
  ∀ h ∈ st.sched.crossLaneHandoffs,
    h.fromCoro ≠ h.toCoro ∧
    h.reason.startsWith "transfer " ∧
    h.delegationWitness.length > 0

/-- Proof-carrying protocol admission contract:
requires scheduler evidence plus theorem-pack evidence in one proof space. -/
structure ProtocolAdmissionContract (store₀ : SessionStore ν) where
  proofSpace : ProtocolMachineProofSpace (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀
  proofPack : ProtocolMachineProofPack (proofSpace := proofSpace)

/-- Proof-guided concurrency contract: runtime may step coroutines in parallel
only when a proof-level eligibility predicate certifies the pair. -/
structure ProofGuidedConcurrencyContract (st₀ : ProtocolMachineState ι γ π ε ν) where
  eligible : CoroutineId → CoroutineId → Prop
  eligibleDecidable : DecidableRel eligible
  symmetric : ∀ a b, eligible a b → eligible b a
  irreflexive : ∀ a, ¬ eligible a a
  frameGuarded : ∀ a b, eligible a b → a ≠ b

/-- Boolean eligibility hook extracted from the proof-guided contract. -/
def proofGuidedEligibleB {st₀ : ProtocolMachineState ι γ π ε ν}
    (contract : ProofGuidedConcurrencyContract (ι := ι) (γ := γ)
      (π := π) (ε := ε) (ν := ν) st₀)
    (a b : CoroutineId) : Bool :=
  let _ := contract.eligibleDecidable
  decide (contract.eligible a b)

/-- Connect deterministic wave planning to proof-guided eligibility. -/
def planDeterministicWavesByContract {st₀ : ProtocolMachineState ι γ π ε ν}
    (contract : ProofGuidedConcurrencyContract (ι := ι) (γ := γ)
      (π := π) (ε := ε) (ν := ν) st₀) :
    List (List CoroutineId) :=
  planDeterministicWavesEligible st₀ (proofGuidedEligibleB contract)

/-- Scheduler profile contract: runtime policy selection is backed by a certified
scheduler bundle and profile extraction theorem. -/
structure SchedulerProfileContract (st₀ : ProtocolMachineState ι γ π ε ν) where
  bundle : ProtocolMachineSchedulerBundle st₀
  profilePinned : schedulerPolicyProfileOf st₀.sched.policy = bundle.profile

/-- Theorem-pack capability contract: advanced runtime modes are gated by the
inventory materialized from theorem-pack evidence. -/
structure TheoremPackCapabilityContract
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) where
  theoremPack : ProtocolMachineTheoremPack (space := space)

/-- Runtime-facing compact capability inventory derived from theorem-pack evidence. -/
def TheoremPackCapabilityContract.capabilityInventory
    {store₀ : SessionStore ν} {State : Type v}
    {space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (contract : TheoremPackCapabilityContract space) : List (String × Bool) :=
  Runtime.Proofs.TheoremPackAPI.capabilities
    (space := space) contract.theoremPack

/-- Runtime-facing semantic-object theorem inventory derived from theorem-pack evidence. -/
def TheoremPackCapabilityContract.semanticObjectInventory
    {store₀ : SessionStore ν} {State : Type v}
    {space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (contract : TheoremPackCapabilityContract space) : List (String × Bool) :=
  Runtime.Proofs.TheoremPackAPI.semanticObjectInventory
    (pack := contract.theoremPack)

/-- Runtime-facing list of enabled semantic-object theorem attachment points. -/
def TheoremPackCapabilityContract.semanticAttachmentPoints
    {store₀ : SessionStore ν} {State : Type v}
    {space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (contract : TheoremPackCapabilityContract space) : List String :=
  Runtime.Proofs.TheoremPackAPI.semanticObjectCapabilities
    (pack := contract.theoremPack)

/-! ## Combined Runtime Bundle -/

/-- Combined runtime contract bundle threaded into protocol machine admission/runtime policy. -/
structure ProtocolMachineRuntimeContracts (store₀ : SessionStore ν) where
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

def requiresProtocolMachineRuntimeContracts (cfg : ProtocolMachineConfig ι γ π ε ν) : Bool :=
  schedPolicyRequiresContracts cfg.schedPolicy || cfg.speculationEnabled

/-- protocol machine admission result for advanced runtime mode checks. -/
inductive ProtocolMachineAdmissionResult where
  | admitted
  | rejectedMissingContracts
  deriving Repr, DecidableEq

/-- protocol machine admission path: advanced runtime modes require `ProtocolMachineRuntimeContracts`. -/
def admitProtocolMachineRuntime
    (cfg : ProtocolMachineConfig ι γ π ε ν)
    {store₀ : SessionStore ν}
    (contracts? : Option (ProtocolMachineRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀)) :
    ProtocolMachineAdmissionResult :=
  if requiresProtocolMachineRuntimeContracts cfg then
    match contracts? with
    | some _ => .admitted
    | none => .rejectedMissingContracts
  else
    .admitted

/-- Advanced-mode admission succeeds only when contracts are supplied. -/
theorem admit_vm_runtime_requires_contracts
    (cfg : ProtocolMachineConfig ι γ π ε ν) {store₀ : SessionStore ν}
    (hReq : requiresProtocolMachineRuntimeContracts cfg = true)
    (contracts? : Option (ProtocolMachineRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀)) :
    admitProtocolMachineRuntime cfg contracts? = .admitted ↔ contracts?.isSome = true := by
  unfold admitProtocolMachineRuntime
  simp [hReq]
  cases contracts? <;> simp

/-! ### Capability-Gated Runtime APIs -/

/-- Live migration request payload. -/
structure LiveMigrationRequest where
  sid : SessionId
  role : Role
  fromLane : LaneId
  toLane : LaneId

/-- Theorem-gated live migration capability check. -/
def canUseLiveMigration
    {store₀ : SessionStore ν}
    (contracts : ProtocolMachineRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀) :
    Bool :=
  Runtime.Proofs.TheoremPackAPI.canLiveMigrate contracts.capabilities.theoremPack

/-- Theorem-gated placement-refinement switch. -/
def canUsePlacementRefinement
    {store₀ : SessionStore ν}
    (contracts : ProtocolMachineRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀) :
    Bool :=
  Runtime.Proofs.TheoremPackAPI.canRefinePlacement contracts.capabilities.theoremPack

/-- Theorem-gated relaxed-reordering switch. -/
def canUseRelaxedReordering
    {store₀ : SessionStore ν}
    (contracts : ProtocolMachineRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀) :
    Bool :=
  Runtime.Proofs.TheoremPackAPI.canRelaxReordering contracts.capabilities.theoremPack

/-- Theorem-gated live migration API: only admits requests when capability
evidence is present in the theorem pack. -/
def requestLiveMigration
    {store₀ : SessionStore ν}
    (contracts : ProtocolMachineRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀)
    (req : LiveMigrationRequest) : Option LiveMigrationRequest :=
  if canUseLiveMigration contracts then some req else none

/-! ### Scaling and Placement Gates -/

/-- Autoscale/repartition request payload. -/
structure AutoscaleRequest where
  targetShards : Nat
  reason : String

/-- Theorem-gated autoscale/repartition capability check. -/
def canUseAutoscaleOrRepartition
    {store₀ : SessionStore ν}
    (contracts : ProtocolMachineRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀) :
    Bool :=
  Runtime.Proofs.TheoremPackAPI.canAutoscaleOrRepartition
    contracts.capabilities.theoremPack

/-- Theorem-gated autoscale/repartition API. -/
def requestAutoscaleOrRepartition
    {store₀ : SessionStore ν}
    (contracts : ProtocolMachineRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀)
    (req : AutoscaleRequest) : Option AutoscaleRequest :=
  if canUseAutoscaleOrRepartition contracts then some req else none

/-- Theorem-gated refinement switch API. -/
def requestPlacementRefinement
    {store₀ : SessionStore ν}
    (contracts : ProtocolMachineRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀)
    (enabled : Bool) : Option Bool :=
  if canUsePlacementRefinement contracts then some enabled else none

/-- Theorem-gated reordering switch API. -/
def requestRelaxedReordering
    {store₀ : SessionStore ν}
    (contracts : ProtocolMachineRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀)
    (enabled : Bool) : Option Bool :=
  if canUseRelaxedReordering contracts then some enabled else none

/-- Runtime capability snapshot emitted at startup. -/
def runtimeCapabilitySnapshot
    {store₀ : SessionStore ν}
    (contracts : ProtocolMachineRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀) :
    List (String × Bool) :=
  contracts.capabilities.capabilityInventory ++
    [ ("live_migration", canUseLiveMigration contracts)
    , ("autoscale_repartition", canUseAutoscaleOrRepartition contracts)
    , ("placement_refinement", canUsePlacementRefinement contracts)
    , ("relaxed_reordering", canUseRelaxedReordering contracts)
    ]

/-! ### Determinism Profile Gates -/

/-- Artifact check for one runtime determinism profile. -/
def determinismProfileSupported
    (artifacts : ProtocolMachineDeterminismArtifacts)
    (profile : ProtocolMachineDeterminismProfile) : Bool :=
  match profile with
  | .full => artifacts.full
  | .moduloEffectTrace => artifacts.moduloEffectTrace
  | .moduloCommutativity => artifacts.moduloCommutativity
  | .replay => artifacts.replay

/-- Runtime profile selection gate for
`full`, `moduloEffectTrace`, `moduloCommutativity`, and `replay`. -/
def requestDeterminismProfile
    {store₀ : SessionStore ν}
    (contracts : ProtocolMachineRuntimeContracts (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) store₀)
    (artifacts : ProtocolMachineDeterminismArtifacts)
    (profile : ProtocolMachineDeterminismProfile) : Option ProtocolMachineDeterminismProfile :=
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
def SchedulerProfileContract.ofBundle {st₀ : ProtocolMachineState ι γ π ε ν}
    (bundle : ProtocolMachineSchedulerBundle st₀) :
    SchedulerProfileContract st₀ :=
  { bundle := bundle
  , profilePinned := scheduler_profile_pinned_from_bundle bundle
  }

/-- Build a theorem-pack capability contract from a proof space. -/
def TheoremPackCapabilityContract.ofProofSpace
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    TheoremPackCapabilityContract space :=
  let pack := Runtime.Proofs.TheoremPackAPI.mk (space := space)
  { theoremPack := pack }

end

end Proofs
end Runtime
