import Runtime.Proofs.Adapters.Progress
import Runtime.Proofs.Adapters.Distributed.ProfileWrappers
import Runtime.Proofs.Adapters.Classical
import Runtime.Proofs.Contracts.DeterminismApi
import Runtime.Adequacy.EnvelopeCore.AdmissionLogic
import Runtime.Proofs.TheoremPack.ProfilesCore


set_option autoImplicit false
namespace Runtime
namespace Proofs
universe u v
section
variable {ν : Type u} [VerificationModel ν]
variable [EntropyAPI.AnalysisLaws]

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
