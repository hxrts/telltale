import Runtime.Proofs.Adapters.Distributed.CoreProfiles
import Runtime.Proofs.Adapters.Distributed.EnvelopeTheorems

/-! # Runtime.Proofs.Adapters.Distributed

Facade module exposing distributed adapter profile slots and attachment
helpers expected by conformance tooling. -/

/-
The Problem. Core distributed profile machinery lives in
`CoreProfiles.lean`, but conformance checks scan this façade path.
Without explicit projections here, checks can report false negatives.

Solution Structure. Re-export lightweight slot projections and an
attachment helper that forward directly to the canonical implementations.
-/

set_option autoImplicit false

namespace Runtime
namespace Proofs
namespace Adapters

universe u v

section

variable {ν : Type u} [VerificationModel ν]

/-! ## Distributed Slot Projections -/

/-- Facade projection of the optional failure-envelope profile slot. -/
def failureEnvelope?
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State) :
    Option FailureEnvelopeProfile :=
  space.distributed.failureEnvelope?

/-- Facade projection of the optional Byzantine-safety profile slot. -/
def byzantineSafety?
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State) :
    Option ByzantineSafetyProfile :=
  space.distributed.byzantineSafety?

/-- Facade projection of the optional VM-envelope adherence profile slot. -/
def vmEnvelopeAdherence?
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State) :
    Option VMEnvelopeAdherenceProfile :=
  space.distributed.vmEnvelopeAdherence?

/-- Facade projection of the optional VM-envelope admission profile slot. -/
def vmEnvelopeAdmission?
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State) :
    Option VMEnvelopeAdmissionProfile :=
  space.distributed.vmEnvelopeAdmission?

/-- Facade projection of the optional protocol-envelope bridge profile slot. -/
def protocolEnvelopeBridge?
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State) :
    Option ProtocolEnvelopeBridgeProfile :=
  space.distributed.protocolEnvelopeBridge?

/-! ## Attachment Helper -/

/-- Facade helper forwarding to the canonical failure-envelope attachment. -/
def withFailureEnvelope
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : FailureEnvelopeProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  VMInvariantSpaceWithDistributed.withFailureEnvelope space p

/-- Facade helper forwarding to the canonical Byzantine-safety attachment. -/
def withByzantineSafety
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : ByzantineSafetyProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  VMInvariantSpaceWithDistributed.withByzantineSafety space p

end

end Adapters
end Proofs
end Runtime
