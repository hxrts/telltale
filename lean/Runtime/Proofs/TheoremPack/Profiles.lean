import Runtime.Proofs.Adapters.Progress
import Runtime.Proofs.Adapters.Distributed.ProfileWrappers
import Runtime.Proofs.Adapters.Classical
import Runtime.Proofs.Contracts.DeterminismApi
import Runtime.Adequacy.EnvelopeCore.AdmissionLogic

set_option autoImplicit false

/-! # Runtime.Proofs.TheoremPack

One-shot theorem packaging from a protocol machine invariant space carrying distributed and
classical optional profiles.
-/

/-
The Problem. Users need a single entry point to obtain all applicable runtime
theorems for a given protocol machine state, including optional distributed impossibility
results and classical analysis bounds.

Solution Structure. Defines `ProtocolMachineInvariantSpaceWithProfiles` combining distributed
and classical profiles. Provides projection functions to view the space as
distributed-only or classical-only. The packaging functions generate theorem
bundles from the combined invariant space in one shot.
-/

/-! ## Core Development -/

namespace Runtime
namespace Proofs

universe u v

section

variable {ν : Type u} [VerificationModel ν]
variable [EntropyAPI.AnalysisLaws]

/-- Combined invariant space carrying distributed and classical profiles. -/
structure ProtocolMachineInvariantSpaceWithProfiles
    (store₀ : SessionStore ν) (State : Type v)
    extends Adapters.ProtocolMachineInvariantSpaceWithDistributedProfiles (ν := ν) store₀ State where
  classical : Adapters.ClassicalProfiles State := {}

/-! ## Space Views and Generic Updaters -/

/-- Forget classical profiles and view the space as distributed-only. -/
def ProtocolMachineInvariantSpaceWithProfiles.toDistributedSpace
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    Adapters.ProtocolMachineInvariantSpaceWithDistributedProfiles store₀ State :=
  { toProtocolMachineInvariantSpace := space.toProtocolMachineInvariantSpace
  , distributed := space.distributed
  }

/-- Forget distributed profiles and view the space as classical-only. -/
def ProtocolMachineInvariantSpaceWithProfiles.toClassicalSpace
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    Adapters.ProtocolMachineInvariantSpaceWithClassicalProfiles store₀ State :=
  { toProtocolMachineInvariantSpace := space.toProtocolMachineInvariantSpace
  , classical := space.classical
  }

/-- Attach distributed profiles to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withDistributedProfiles
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (distributed : Adapters.DistributedProfiles) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := distributed }

/-- Attach classical profiles to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withClassicalProfiles
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (classical : Adapters.ClassicalProfiles State) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  { space with classical := classical }

/-- Generic distributed-profile updater used by profile-specific setters. -/
def ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (update : Adapters.DistributedProfiles → Adapters.DistributedProfiles) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := update space.distributed }

/-- Generic classical-profile updater used by profile-specific setters. -/
def ProtocolMachineInvariantSpaceWithProfiles.updateClassicalProfiles
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (update : Adapters.ClassicalProfiles State → Adapters.ClassicalProfiles State) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  { space with classical := update space.classical }

/-! ## Distributed Profile Setters: Impossibility and Liveness -/

/-- Attach an FLP distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withFLP
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.FLPProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with flp? := some p })

/-- Attach a CAP distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withCAP
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.CAPProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with cap? := some p })

/-- Attach a quorum-geometry distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withQuorumGeometry
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.QuorumGeometryProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with quorumGeometry? := some p })

/-- Attach a partial-synchrony distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withPartialSynchrony
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.PartialSynchronyProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with partialSynchrony? := some p })

/-- Attach a responsiveness distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withResponsiveness
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ResponsivenessProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with responsiveness? := some p })

/-! ## Distributed Profile Setters: Chain and Commit Safety -/

/-- Attach a Nakamoto distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withNakamoto
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.NakamotoProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with nakamoto? := some p })

/-- Attach a reconfiguration distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withReconfiguration
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ReconfigurationProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with reconfiguration? := some p })

/-- Attach an atomic-broadcast distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withAtomicBroadcast
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.AtomicBroadcastProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with atomicBroadcast? := some p })

/-- Attach an accountable-safety distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withAccountableSafety
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.AccountableSafetyProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with accountableSafety? := some p })

/-- Attach a failure-detector distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withFailureDetectors
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.FailureDetectorsProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with failureDetectors? := some p })

/-! ## Distributed Profile Setters: Data and Coordination -/

/-- Attach a data-availability distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withDataAvailability
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.DataAvailabilityProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with dataAvailability? := some p })

/-- Attach a coordination distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withCoordination
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.CoordinationProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with coordination? := some p })

/-- Attach a CRDT distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withCRDT
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.CRDTProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with crdt? := some p })

/-- Attach a CRDT OpCore-erasure distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withCRDTErasure
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.CRDTErasureProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with crdtErasure? := some p })

/-- Attach a triangle-of-forgetting distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withTriangleOfForgetting
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.TriangleOfForgettingProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with triangleOfForgetting? := some p })

/-- Attach a Byzantine-safety distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withByzantineSafety
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ByzantineSafetyProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with byzantineSafety? := some p })

/-! ## Distributed Profile Setters: Envelope Families -/

/-- Attach a consensus-envelope distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withConsensusEnvelope
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ConsensusEnvelopeProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with consensusEnvelope? := some p })

/-- Attach a failure-envelope distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withFailureEnvelope
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.FailureEnvelopeProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with failureEnvelope? := some p })

/-- Attach a protocol machine-envelope-adherence distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withProtocolMachineEnvelopeAdherence
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ProtocolMachineEnvelopeAdherenceProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with protocolMachineEnvelopeAdherence? := some p })

/-- Attach a protocol machine-envelope-admission distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withProtocolMachineEnvelopeAdmission
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ProtocolMachineEnvelopeAdmissionProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with protocolMachineEnvelopeAdmission? := some p })

/-- Attach a protocol-envelope-bridge distributed profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withProtocolEnvelopeBridge
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ProtocolEnvelopeBridgeProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with protocolEnvelopeBridge? := some p })

/-! ## Classical Profile Setters -/

/-- Attach a Foster profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withFoster
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.FosterProfile State) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateClassicalProfiles space
    (fun classical => { classical with foster? := some p })

/-- Attach a MaxWeight profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withMaxWeight
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.MaxWeightProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateClassicalProfiles space
    (fun classical => { classical with maxWeight? := some p })

/-- Attach a large-deviation profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withLDP
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.LDPProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateClassicalProfiles space
    (fun classical => { classical with ldp? := some p })

/-- Attach a mean-field profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withMeanField
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.MeanFieldProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateClassicalProfiles space
    (fun classical => { classical with meanField? := some p })

/-- Attach a heavy-traffic profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withHeavyTraffic
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.HeavyTrafficProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateClassicalProfiles space
    (fun classical => { classical with heavyTraffic? := some p })

/-- Attach a mixing-time profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withMixing
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.MixingProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateClassicalProfiles space
    (fun classical => { classical with mixing? := some p })

/-- Attach a fluid-limit profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withFluid
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.FluidProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateClassicalProfiles space
    (fun classical => { classical with fluid? := some p })

/-- Attach a concentration profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withConcentration
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ConcentrationProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateClassicalProfiles space
    (fun classical => { classical with concentration? := some p })

/-- Attach a Little's-law profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withLittlesLaw
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.LittlesLawProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateClassicalProfiles space
    (fun classical => { classical with littlesLaw? := some p })

/-- Attach a functional-CLT profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withFunctionalCLT
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.FunctionalCLTProfile) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateClassicalProfiles space
    (fun classical => { classical with functionalCLT? := some p })

/-- Attach a spectral-gap termination profile to a combined space. -/
def ProtocolMachineInvariantSpaceWithProfiles.withSpectralGap
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.SpectralGapProfile State) :
    ProtocolMachineInvariantSpaceWithProfiles store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.updateClassicalProfiles space
    (fun classical => { classical with spectralGap? := some p })

/-! ## Execution Profiles -/

/-- Canonical fairness assumptions fixed by one proof-carrying execution profile. -/
inductive ProtocolMachineFairnessAssumption where
  | scheduleConfluence
  | starvationFreedom
  | livenessFairness
  deriving Repr, DecidableEq, Inhabited

/-- Canonical admissibility classes fixed by one proof-carrying execution profile. -/
inductive ProtocolMachineAdmissibilityClass where
  | localEnvelope
  | shardedEnvelope
  | protocolEnvelopeBridge
  deriving Repr, DecidableEq, Inhabited

/-- Canonical escalation-window classes fixed by one proof-carrying execution profile. -/
inductive ProtocolMachineEscalationWindowClass where
  | progressContractBounded
  | admissionComplexityBounded
  | protocolBridgeBounded
  deriving Repr, DecidableEq, Inhabited

/-- Profile-level proof-carrying execution context for theorem-pack derivation. -/
structure ProtocolMachineExecutionProfile where
  fairnessAssumptions : List ProtocolMachineFairnessAssumption
  admissibilityClasses : List ProtocolMachineAdmissibilityClass
  escalationWindowClasses : List ProtocolMachineEscalationWindowClass
  theoremPackEligibility : List (String × Bool)
  necessityCatalog : List Runtime.Adequacy.TransportNecessityProfile := []
  deriving Repr, Inhabited

/-- Whether this execution profile carries one theorem-pack key. -/
def ProtocolMachineExecutionProfile.supportsKey
    (profile : ProtocolMachineExecutionProfile) (key : String) : Bool :=
  (profile.theoremPackEligibility.find? (fun entry =>
    entry.1 = key)).map Prod.snd |>.getD false

/-- Whether this execution profile carries protocol-machine adherence eligibility. -/
def ProtocolMachineExecutionProfile.supportsProtocolMachineEnvelopeAdherence
    (profile : ProtocolMachineExecutionProfile) : Bool :=
  profile.supportsKey "protocol_machine_envelope_adherence"

/-- Whether this execution profile carries protocol-machine admission eligibility. -/
def ProtocolMachineExecutionProfile.supportsProtocolMachineEnvelopeAdmission
    (profile : ProtocolMachineExecutionProfile) : Bool :=
  profile.supportsKey "protocol_machine_envelope_admission"

/-- Whether this execution profile carries protocol-envelope bridge eligibility. -/
def ProtocolMachineExecutionProfile.supportsProtocolEnvelopeBridge
    (profile : ProtocolMachineExecutionProfile) : Bool :=
  profile.supportsKey "protocol_envelope_bridge"

/-- Catalog-level necessity hardening attached to an execution profile. -/
def ProtocolMachineExecutionProfile.necessityHardened
    (profile : ProtocolMachineExecutionProfile) : Prop :=
  Runtime.Adequacy.transportCatalogNecessityHardened profile.necessityCatalog

/-- Catalog-level minimal-basis closure attached to an execution profile. -/
def ProtocolMachineExecutionProfile.necessityMinimalBasis
    (profile : ProtocolMachineExecutionProfile) : Prop :=
  Runtime.Adequacy.transportCatalogMinimalBasis profile.necessityCatalog

/-- Build the canonical execution profile carried by one invariant space. -/
def ProtocolMachineInvariantSpaceWithProfiles.executionProfile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    ProtocolMachineExecutionProfile :=
  { fairnessAssumptions :=
      [ .scheduleConfluence
      , .starvationFreedom
      ] ++
      match space.toProtocolMachineInvariantSpace.liveness? with
      | some _ => [ .livenessFairness ]
      | none => []
  , admissibilityClasses :=
      [ .localEnvelope
      , .shardedEnvelope
      ] ++
      match space.distributed.protocolEnvelopeBridge? with
      | some _ => [ .protocolEnvelopeBridge ]
      | none => []
  , escalationWindowClasses :=
      [ .progressContractBounded ] ++
      (match space.distributed.protocolMachineEnvelopeAdmission? with
      | some _ => [ .admissionComplexityBounded ]
      | none => []) ++
      (match space.distributed.protocolEnvelopeBridge? with
      | some _ => [ .protocolBridgeBounded ]
      | none => [])
  , theoremPackEligibility :=
      [ ("termination", space.toProtocolMachineInvariantSpace.liveness?.isSome)
      , ("protocol_machine_envelope_adherence",
          space.distributed.protocolMachineEnvelopeAdherence?.isSome)
      , ("protocol_machine_envelope_admission",
          space.distributed.protocolMachineEnvelopeAdmission?.isSome)
      , ("protocol_envelope_bridge", space.distributed.protocolEnvelopeBridge?.isSome)
      , ("classical_foster", space.classical.foster?.isSome)
      , ("classical_maxweight", space.classical.maxWeight?.isSome)
      , ("classical_ldp", space.classical.ldp?.isSome)
      , ("classical_mean_field", space.classical.meanField?.isSome)
      , ("classical_heavy_traffic", space.classical.heavyTraffic?.isSome)
      , ("classical_mixing", space.classical.mixing?.isSome)
      , ("classical_fluid", space.classical.fluid?.isSome)
      , ("classical_concentration", space.classical.concentration?.isSome)
      , ("classical_littles_law", space.classical.littlesLaw?.isSome)
      , ("classical_functional_clt", space.classical.functionalCLT?.isSome)
      , ("classical_spectral_gap_termination", space.classical.spectralGap?.isSome)
      ]
  }

/-- If every transport assumption in the execution profile is marked proven-necessary,
the profile is necessity-hardened. -/
theorem executionProfile_necessity_hardened_of_all_proven_necessary
    (profile : ProtocolMachineExecutionProfile)
    (hAll : ∀ p, p ∈ profile.necessityCatalog →
      Runtime.Adequacy.profileNecessityHardened p) :
    profile.necessityHardened := by
  exact Runtime.Adequacy.transport_catalog_necessity_hardened_of_profiles
    profile.necessityCatalog hAll

/-- Build minimal-basis closure for an execution profile from hardened transport
profiles plus dropped-assumption oracles. -/
theorem executionProfile_necessity_minimal_basis_of_hardened_and_oracles
    (profile : ProtocolMachineExecutionProfile)
    (hHard : profile.necessityHardened)
    (hOracle : ∀ p, p ∈ profile.necessityCatalog →
      Runtime.Adequacy.TransportProfileMinimalityOracle p) :
    profile.necessityMinimalBasis := by
  exact Runtime.Adequacy.transport_catalog_minimal_basis_of_hardened_and_oracles
    profile.necessityCatalog hHard hOracle

end

end Proofs
end Runtime
