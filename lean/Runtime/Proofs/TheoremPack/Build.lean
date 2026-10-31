import Runtime.Proofs.TheoremPack.Artifacts
import Runtime.Proofs.TheoremPack.BuildCore

/-! # Theorem Pack Building

`ProtocolMachineTheoremPack` structure bundling all optional proof artifacts for
a protocol machine invariant space, enabling certificate generation and validation. -/

set_option autoImplicit false
namespace Runtime
namespace Proofs
universe u v
section
variable {ν : Type u} [VerificationModel ν]
variable [EntropyAPI.AnalysisLaws]

/-- Theorem-pack adherence artifact presence matches the canonical execution-profile flag. -/
theorem protocolMachineEnvelopeAdherence_matches_execution_profile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    (buildProtocolMachineTheoremPack (space := space)).protocolMachineEnvelopeAdherence?.isSome =
      space.executionProfile.supportsProtocolMachineEnvelopeAdherence := by
  cases h : space.distributed.protocolMachineEnvelopeAdherence? <;>
    simp [buildProtocolMachineTheoremPack,
      ProtocolMachineInvariantSpaceWithProfiles.executionProfile,
      ProtocolMachineExecutionProfile.supportsProtocolMachineEnvelopeAdherence,
      ProtocolMachineExecutionProfile.supportsKey, h]

/-- Theorem-pack admission artifact presence matches the canonical execution-profile flag. -/
theorem protocolMachineEnvelopeAdmission_matches_execution_profile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    (buildProtocolMachineTheoremPack (space := space)).protocolMachineEnvelopeAdmission?.isSome =
      space.executionProfile.supportsProtocolMachineEnvelopeAdmission := by
  cases h : space.distributed.protocolMachineEnvelopeAdmission? <;>
    simp [buildProtocolMachineTheoremPack,
      ProtocolMachineInvariantSpaceWithProfiles.executionProfile,
      ProtocolMachineExecutionProfile.supportsProtocolMachineEnvelopeAdmission,
      ProtocolMachineExecutionProfile.supportsKey, h]

/-- Theorem-pack bridge artifact presence matches the canonical execution-profile flag. -/
theorem protocolEnvelopeBridge_matches_execution_profile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    (buildProtocolMachineTheoremPack (space := space)).protocolEnvelopeBridge?.isSome =
      space.executionProfile.supportsProtocolEnvelopeBridge := by
  cases h : space.distributed.protocolEnvelopeBridge? <;>
    simp [buildProtocolMachineTheoremPack,
      ProtocolMachineInvariantSpaceWithProfiles.executionProfile,
      ProtocolMachineExecutionProfile.supportsProtocolEnvelopeBridge,
      ProtocolMachineExecutionProfile.supportsKey, h]

/-! ## Classical Artifact Agreement -/

/-- Classical Foster artifact presence matches the canonical execution-profile flag. -/
theorem classicalFoster_matches_execution_profile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    (buildProtocolMachineTheoremPack (space := space)).foster?.isSome =
      space.executionProfile.supportsKey "classical_foster" := by
  cases h : space.classical.foster? <;>
    simp [buildProtocolMachineTheoremPack,
      Adapters.buildProtocolMachineClassicalTheoremPack,
      ProtocolMachineInvariantSpaceWithProfiles.toClassicalSpace,
      ProtocolMachineInvariantSpaceWithProfiles.executionProfile,
      ProtocolMachineExecutionProfile.supportsKey, h]

/-- Classical MaxWeight artifact presence matches the canonical execution-profile flag. -/
theorem classicalMaxWeight_matches_execution_profile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    (buildProtocolMachineTheoremPack (space := space)).maxWeight?.isSome =
      space.executionProfile.supportsKey "classical_maxweight" := by
  cases h : space.classical.maxWeight? <;>
    simp [buildProtocolMachineTheoremPack,
      Adapters.buildProtocolMachineClassicalTheoremPack,
      ProtocolMachineInvariantSpaceWithProfiles.toClassicalSpace,
      ProtocolMachineInvariantSpaceWithProfiles.executionProfile,
      ProtocolMachineExecutionProfile.supportsKey, h]

/-- Classical LDP artifact presence matches the canonical execution-profile flag. -/
theorem classicalLDP_matches_execution_profile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    (buildProtocolMachineTheoremPack (space := space)).ldp?.isSome =
      space.executionProfile.supportsKey "classical_ldp" := by
  cases h : space.classical.ldp? <;>
    simp [buildProtocolMachineTheoremPack,
      Adapters.buildProtocolMachineClassicalTheoremPack,
      ProtocolMachineInvariantSpaceWithProfiles.toClassicalSpace,
      ProtocolMachineInvariantSpaceWithProfiles.executionProfile,
      ProtocolMachineExecutionProfile.supportsKey, h]

/-- Classical mean-field artifact presence matches the canonical execution-profile flag. -/
theorem classicalMeanField_matches_execution_profile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    (buildProtocolMachineTheoremPack (space := space)).meanField?.isSome =
      space.executionProfile.supportsKey "classical_mean_field" := by
  cases h : space.classical.meanField? <;>
    simp [buildProtocolMachineTheoremPack,
      Adapters.buildProtocolMachineClassicalTheoremPack,
      ProtocolMachineInvariantSpaceWithProfiles.toClassicalSpace,
      ProtocolMachineInvariantSpaceWithProfiles.executionProfile,
      ProtocolMachineExecutionProfile.supportsKey, h]

/-- Classical heavy-traffic artifact presence matches the canonical execution-profile flag. -/
theorem classicalHeavyTraffic_matches_execution_profile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    (buildProtocolMachineTheoremPack (space := space)).heavyTraffic?.isSome =
      space.executionProfile.supportsKey "classical_heavy_traffic" := by
  cases h : space.classical.heavyTraffic? <;>
    simp [buildProtocolMachineTheoremPack,
      Adapters.buildProtocolMachineClassicalTheoremPack,
      ProtocolMachineInvariantSpaceWithProfiles.toClassicalSpace,
      ProtocolMachineInvariantSpaceWithProfiles.executionProfile,
      ProtocolMachineExecutionProfile.supportsKey, h]

/-- Classical mixing artifact presence matches the canonical execution-profile flag. -/
theorem classicalMixing_matches_execution_profile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    (buildProtocolMachineTheoremPack (space := space)).mixing?.isSome =
      space.executionProfile.supportsKey "classical_mixing" := by
  cases h : space.classical.mixing? <;>
    simp [buildProtocolMachineTheoremPack,
      Adapters.buildProtocolMachineClassicalTheoremPack,
      ProtocolMachineInvariantSpaceWithProfiles.toClassicalSpace,
      ProtocolMachineInvariantSpaceWithProfiles.executionProfile,
      ProtocolMachineExecutionProfile.supportsKey, h]

/-- Classical fluid artifact presence matches the canonical execution-profile flag. -/
theorem classicalFluid_matches_execution_profile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    (buildProtocolMachineTheoremPack (space := space)).fluid?.isSome =
      space.executionProfile.supportsKey "classical_fluid" := by
  cases h : space.classical.fluid? <;>
    simp [buildProtocolMachineTheoremPack,
      Adapters.buildProtocolMachineClassicalTheoremPack,
      ProtocolMachineInvariantSpaceWithProfiles.toClassicalSpace,
      ProtocolMachineInvariantSpaceWithProfiles.executionProfile,
      ProtocolMachineExecutionProfile.supportsKey, h]

/-- Classical concentration artifact presence matches the canonical execution-profile flag. -/
theorem classicalConcentration_matches_execution_profile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    (buildProtocolMachineTheoremPack (space := space)).concentration?.isSome =
      space.executionProfile.supportsKey "classical_concentration" := by
  cases h : space.classical.concentration? <;>
    simp [buildProtocolMachineTheoremPack,
      Adapters.buildProtocolMachineClassicalTheoremPack,
      ProtocolMachineInvariantSpaceWithProfiles.toClassicalSpace,
      ProtocolMachineInvariantSpaceWithProfiles.executionProfile,
      ProtocolMachineExecutionProfile.supportsKey, h]

/-- Classical Little's-law artifact presence matches the canonical execution-profile flag. -/
theorem classicalLittlesLaw_matches_execution_profile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    (buildProtocolMachineTheoremPack (space := space)).littlesLaw?.isSome =
      space.executionProfile.supportsKey "classical_littles_law" := by
  cases h : space.classical.littlesLaw? <;>
    simp [buildProtocolMachineTheoremPack,
      Adapters.buildProtocolMachineClassicalTheoremPack,
      ProtocolMachineInvariantSpaceWithProfiles.toClassicalSpace,
      ProtocolMachineInvariantSpaceWithProfiles.executionProfile,
      ProtocolMachineExecutionProfile.supportsKey, h]

/-- Classical functional-CLT artifact presence matches the canonical execution-profile flag. -/
theorem classicalFunctionalCLT_matches_execution_profile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    (buildProtocolMachineTheoremPack (space := space)).functionalCLT?.isSome =
      space.executionProfile.supportsKey "classical_functional_clt" := by
  cases h : space.classical.functionalCLT? <;>
    simp [buildProtocolMachineTheoremPack,
      Adapters.buildProtocolMachineClassicalTheoremPack,
      ProtocolMachineInvariantSpaceWithProfiles.toClassicalSpace,
      ProtocolMachineInvariantSpaceWithProfiles.executionProfile,
      ProtocolMachineExecutionProfile.supportsKey, h]

/-- Classical spectral-gap termination artifact presence matches the execution-profile flag. -/
theorem classicalSpectralGap_matches_execution_profile
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    (buildProtocolMachineTheoremPack (space := space)).spectralGapTermination?.isSome =
      space.executionProfile.supportsKey "classical_spectral_gap_termination" := by
  cases h : space.classical.spectralGap? <;>
    simp [buildProtocolMachineTheoremPack,
      Adapters.buildProtocolMachineClassicalTheoremPack,
      ProtocolMachineInvariantSpaceWithProfiles.toClassicalSpace,
      ProtocolMachineInvariantSpaceWithProfiles.executionProfile,
      ProtocolMachineExecutionProfile.supportsKey, h]

end

end Proofs
end Runtime
