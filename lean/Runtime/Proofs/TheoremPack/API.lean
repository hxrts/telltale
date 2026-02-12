import Runtime.Proofs.TheoremPack.Inventory

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

/-- Runtime gate: autoscaling/repartitioning requires compositional-envelope evidence. -/
def canAutoscaleOrRepartition
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : Bool :=
  pack.protocolEnvelopeBridge?.isSome

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
    p.1 = "protocol_envelope_bridge" ||
    p.1 = "vm_envelope_adherence" ||
    p.1 = "vm_envelope_admission")

end TheoremPackAPI
end Proofs
end Runtime
