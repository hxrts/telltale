import Runtime.Proofs.TheoremPack.Inventory
import Runtime.Proofs.TheoremPack.ReleaseConformance
import Runtime.Proofs.VM.Speculation

/-! # Runtime.Proofs.TheoremPack.API

Public facade for theorem-pack construction and inventory.

Downstream modules should prefer this API layer over directly importing
builder/artifact internals.
-/

set_option autoImplicit false

namespace Runtime
namespace Proofs
namespace TheoremPackAPI

universe u v

variable {ν : Type u} [VerificationModel ν]

/-! ## Construction and Inventory Aliases -/

/-- API alias: build theorem-pack artifacts from a profile space. -/
abbrev mk
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State} :
    VMTheoremPack (space := space) :=
  buildVMTheoremPack (space := space)

/-- API alias: compact capability inventory. -/
abbrev capabilities
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : List (String × Bool) :=
  theoremInventory (space := space) pack

/-- API alias: capability inventory augmented with determinism flags. -/
abbrev capabilitiesWithDeterminism
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space))
    (determinism : VMDeterminismArtifacts) : List (String × Bool) :=
  theoremInventoryWithDeterminism (space := space) pack determinism

/-- Deterministic minimal capability inventory:
retain only capability names with proved evidence. -/
def minimalCapabilities
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : List String :=
  (capabilities (space := space) pack).foldr
    (fun entry acc => if entry.2 then entry.1 :: acc else acc) []

/-! ## WS7 Release Conformance Surface -/

/-- API alias for optimization-eligible runtime transformation envelope classes. -/
abbrev RuntimeTransformationEnvelopeClass :=
  Runtime.Proofs.RuntimeTransformationEnvelopeClass

/-- API alias for certified replay equivalence classes. -/
abbrev CertifiedReplayEquivalenceClass :=
  Runtime.Proofs.CertifiedReplayEquivalenceClass

/-- API alias for default certified replay equivalence classes. -/
abbrev defaultCertifiedReplayClasses :=
  Runtime.Proofs.defaultCertifiedReplayClasses

/-- API alias: eligibility snapshot for optimization transformation classes. -/
abbrev transformationEligibilitySnapshot :=
  Runtime.Proofs.transformationEligibilitySnapshot

/-- API alias: replay conformance check for one certified equivalence class. -/
abbrev replayConformsToCertifiedClass :=
  @Runtime.Proofs.replayConformsToCertifiedClass

/-- API alias: replay conformance check across certified equivalence classes. -/
abbrev replayConformsToClasses :=
  @Runtime.Proofs.replayConformsToClasses

/-- API alias: optimization-class bisim witness preserves observer behavior. -/
abbrev transformationClassPreservesObserverBehavior :=
  @Runtime.Proofs.transformationClass_preserves_observer_behavior

/-- API alias for release conformance report versioning tag. -/
abbrev releaseConformanceReportVersion :=
  Runtime.Proofs.releaseConformanceReportVersion

/-- API alias for release conformance report payload. -/
abbrev ReleaseConformanceReport :=
  Runtime.Proofs.ReleaseConformanceReport

/-- API alias: build release conformance report keyed by theorem-pack inventory. -/
abbrev releaseConformanceReport :=
  @Runtime.Proofs.buildReleaseConformanceReport

/-- API alias: release-tag build gate for conformance witnesses. -/
abbrev releaseBuildGate :=
  @Runtime.Proofs.releaseBuildGate

/-- API alias: failure-envelope cross-target witness gate. -/
abbrev hasFailureEnvelopeCrossTargetWitness :=
  @Runtime.Proofs.hasFailureEnvelopeCrossTargetWitness

/-- API alias: restart/structured-error adequacy witness gate. -/
abbrev hasRestartStructuredErrorAdequacyWitness :=
  @Runtime.Proofs.hasRestartStructuredErrorAdequacyWitness

/-- API alias: single-thread evidence gate. -/
abbrev hasSingleThreadEvidence :=
  @Runtime.Proofs.hasSingleThreadEvidence

/-- API alias: multi-thread evidence gate. -/
abbrev hasMultiThreadEvidence :=
  @Runtime.Proofs.hasMultiThreadEvidence

/-- API alias: sharded evidence gate. -/
abbrev hasShardedEvidence :=
  @Runtime.Proofs.hasShardedEvidence

/-! ## Runtime Capability Gates -/

/-! ## Speculation Proof Surface -/

/-- Theorem-pack API alias: successful fork decreases speculation depth. -/
abbrev forkDepthMonotone :=
  @stepFork_depth_monotone_success

/-- Theorem-pack API alias: reconciled join erases speculation session/checkpoint state. -/
abbrev joinCleanupReconciled :=
  @stepJoin_cleanup_when_reconciled

/-- Theorem-pack API alias: abort restores scoped checkpoint trace/nonce fields. -/
abbrev abortRestoresScopedCheckpoint :=
  @stepAbort_restores_scoped_checkpoint

/-! ## Proof-Space Composer -/

/-- Attach liveness bundle evidence to a combined proof space. -/
def withLivenessBundle
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (bundle : VMLivenessBundle store₀) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with
      toVMInvariantSpace := VMInvariantSpace.withLiveness space.toVMInvariantSpace bundle }

/-- Attach output-condition witness evidence to a combined proof space. -/
def withOutputCondition
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (w : OutputConditionWitness) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with
      toVMInvariantSpace :=
        VMInvariantSpace.withOutputConditionWitness space.toVMInvariantSpace w }

/-- Composer API for liveness/distributed/classical/output-condition spaces. -/
def composeProofSpaces
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (liveness? : Option (VMLivenessBundle store₀))
    (distributed? : Option Adapters.DistributedProfiles)
    (classical? : Option (Adapters.ClassicalProfiles State))
    (output? : Option OutputConditionWitness) :
    VMInvariantSpaceWithProfiles store₀ State :=
  let s₁ :=
    match liveness? with
    | some b => withLivenessBundle (space := space) b
    | none => space
  let s₂ :=
    match distributed? with
    | some d => VMInvariantSpaceWithProfiles.withDistributedProfiles s₁ d
    | none => s₁
  let s₃ :=
    match classical? with
    | some c => VMInvariantSpaceWithProfiles.withClassicalProfiles s₂ c
    | none => s₂
  match output? with
  | some w => withOutputCondition (space := s₃) w
  | none => s₃

/-- Runtime gate: shard-placement admission requires protocol-envelope bridge evidence. -/
def canAdmitShardPlacement
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : Bool :=
  pack.protocolEnvelopeBridge?.isSome

/-- Runtime gate: live migration requires delegation-preserves-envelope evidence. -/
def canLiveMigrate
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : Bool :=
  pack.protocolEnvelopeBridge?.isSome

/-- Runtime gate: placement/refinement updates require spatial monotonicity evidence. -/
def canRefinePlacement
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : Bool :=
  pack.protocolEnvelopeBridge?.isSome

/-- Runtime gate: relaxed reordering requires exchange-normalization capability evidence. -/
def canRelaxReordering
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : Bool :=
  pack.protocolEnvelopeBridge?.isSome

/-- Runtime gate: mixed determinism profiles require adherence + admission capabilities. -/
def canUseMixedDeterminismProfiles
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : Bool :=
  pack.vmEnvelopeAdherence?.isSome && pack.vmEnvelopeAdmission?.isSome

/-- Runtime gate: Byzantine-safe operation requires Byzantine + VM adherence artifacts. -/
def canOperateUnderByzantineEnvelope
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : Bool :=
  pack.byzantineSafety?.isSome && pack.vmEnvelopeAdherence?.isSome

/-- Runtime gate: autoscaling/repartitioning requires compositional-envelope evidence. -/
def canAutoscaleOrRepartition
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : Bool :=
  pack.protocolEnvelopeBridge?.isSome

/-! ## Inventory Conformance Helpers -/

/-- CI helper: claimed capability tags must be supported by theorem-pack inventory. -/
def claimedCapabilitiesWithinInventory
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space))
    (claimed : List String) : Bool :=
  let inv := capabilities (space := space) pack
  claimed.all (fun name => (inv.find? (fun p => p.1 = name)).map Prod.snd |>.getD false)

/-- Artifact-level snapshot for envelope capability conformance checks. -/
def envelopeCapabilitySnapshot
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : List (String × Bool) :=
  (capabilities (space := space) pack).filter (fun p =>
    p.1 = "byzantine_safety_characterization" ||
    p.1 = "protocol_envelope_bridge" ||
    p.1 = "vm_envelope_adherence" ||
    p.1 = "vm_envelope_admission")

end TheoremPackAPI
end Proofs
end Runtime
