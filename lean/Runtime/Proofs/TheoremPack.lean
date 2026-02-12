import Runtime.Proofs.TheoremPack.Profiles
import Runtime.Proofs.TheoremPack.Artifacts
import Runtime.Proofs.TheoremPack.Build
import Runtime.Proofs.TheoremPack.Inventory

/-! # Runtime.Proofs.TheoremPack

Facade module exposing theorem-pack capability bits and selected
artifact projections at a stable import path. -/

/-
The Problem. The theorem-pack implementation is split across profile,
artifact, build, and inventory modules, while conformance checks scan
this façade file for capability exposure.

Solution Structure. Define compact façade views that project capability
bits and selected failure-envelope witnesses from `VMTheoremPack`.
-/

set_option autoImplicit false

namespace Runtime
namespace Proofs

universe u v

section

variable {ν : Type u} [VerificationModel ν]

/-! ## Facade Capability Views -/

/-- Facade-level view exposing the optional failure-envelope slot shape. -/
structure FailureEnvelopeSlot where
  failureEnvelope? : Option FailureEnvelopeArtifact

/-- Build the failure-envelope slot view from a theorem pack. -/
def failureEnvelopeSlot
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : FailureEnvelopeSlot :=
  { failureEnvelope? := pack.failureEnvelope? }

/-- Capability bits used by conformance scripts at the façade layer. -/
def envelopeCapabilityBits
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : List (String × Bool) :=
  [ ("failure_envelope", pack.failureEnvelope?.isSome)
  , ("byzantine_safety_characterization", pack.byzantineSafety?.isSome)
  , ("vm_envelope_adherence", pack.vmEnvelopeAdherence?.isSome)
  , ("vm_envelope_admission", pack.vmEnvelopeAdmission?.isSome)
  , ("protocol_envelope_bridge", pack.protocolEnvelopeBridge?.isSome)
  ]

/-- Facade projection of the optional Byzantine-safety artifact slot. -/
def byzantineSafetyArtifact?
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) :
    Option ByzantineSafetyArtifact :=
  pack.byzantineSafety?

/-- Facade projection of the failure-envelope cross-target theorem witness. -/
def failureEnvelopeCrossTargetConformance?
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) :
    Option Runtime.Adequacy.CrossTargetFailureConformance :=
  pack.failureEnvelope?.map (fun artifact => artifact.crossTargetConformance)

/-- Facade projection of restart structured-error adequacy witness. -/
def failureEnvelopeRestartStructuredErrorAdequacy?
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) :
    Option Runtime.Adequacy.RestartRefinementStructuredErrorAdequacy :=
  pack.failureEnvelope?.map (fun artifact => artifact.restartStructuredErrorAdequacy)

end

end Proofs
end Runtime
