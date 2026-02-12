import Runtime.Adequacy.EnvelopeCore.VMAdherence

/-! # Envelope Admission Logic

Program capability inference and admission checking for envelope
certification, computing `D_prog` from static analysis. -/

/-
The Problem. To issue envelope certificates, we need to infer what
envelopes a program satisfies (`D_prog`) and check admission against
user-requested capabilities (`D_user`). This requires static analysis
of determinism profiles and divergence bounds.

Solution Structure. Define `ProgramCapabilityInput` for analysis inputs.
Compute `DProg_local` and `DProg_shard` capabilities. Provide soundness
specifications ensuring inferred capabilities are conservative.
-/

set_option autoImplicit false

namespace Runtime
namespace Adequacy

universe u v

/-! ## Program Capability Inference -/

structure ProgramCapabilityInput where
  localMaxDiff : Nat
  shardedMaxDiff : Nat
  requiresEqSafeOnly : Bool := true
  localProfiles : List DeterminismProfileClass := []
  shardedProfiles : List DeterminismProfileClass := []
  deriving Repr, DecidableEq, Inhabited

/-- E4: inferred local program capability (`D_prog_local`). -/
def DProg_local (input : ProgramCapabilityInput) : CertifiedEnvelopeCapability :=
  { maxDiff := input.localMaxDiff
  , supportsEqSafeOnly := input.requiresEqSafeOnly
  , supportedProfiles := input.localProfiles
  }

/-- E4: inferred sharded program capability (`D_prog_shard`). -/
def DProg_shard (input : ProgramCapabilityInput) : CertifiedEnvelopeCapability :=
  { maxDiff := input.shardedMaxDiff
  , supportsEqSafeOnly := input.requiresEqSafeOnly
  , supportedProfiles := input.shardedProfiles
  }

/-! ## Admission Soundness and Completeness Contracts -/

/-- E4: soundness form for local capability inference. -/
def DProgInferenceSoundness_local
    {State : Type u} {Obs : Type v}
    (input : ProgramCapabilityInput)
    (h : VMLocalEnvelopeHypotheses State Obs) : Prop :=
  ∀ dUser, dUserContained dUser (DProg_local input) = true →
    LocalEnvelopeSoundness h.localEnvelope h.refRun h.vmRun

/-- E4: soundness form for sharded capability inference. -/
def DProgInferenceSoundness_shard
    {State : Type u} {Obs : Type v}
    (input : ProgramCapabilityInput)
    (h : VMShardedEnvelopeHypotheses State Obs) : Prop :=
  ∀ dUser, dUserContained dUser (DProg_shard input) = true →
    ShardedEnvelopeSoundness h.shardedEnvelope h.refRun h.vmRun

/-- E4: principal-capability property over an inferred capability. -/
def PrincipalCapabilityProperty
    (inferred : CertifiedEnvelopeCapability)
    (precise : CertifiedEnvelopeCapability → Prop) : Prop :=
  precise inferred ∧ ∀ c, precise c → CapabilityStrengthens inferred c

/-- E4: admission soundness form (containment implies runtime compliance). -/
def AdmissionSoundness
    (dProg : CertifiedEnvelopeCapability)
    (runtimeCompliance : DUser → Prop) : Prop :=
  ∀ dUser, dUserContained dUser dProg = true → runtimeCompliance dUser

/-- E4: admission completeness form (admitted iff principal containment). -/
def AdmissionCompleteness
    (dProg : CertifiedEnvelopeCapability)
    (runtimeCompliance : DUser → Prop) : Prop :=
  ∀ dUser, runtimeCompliance dUser ↔ dUserContained dUser dProg = true

/-! ## Admission Diagnostics Vocabulary -/

/-- E4: admission-check obligations used by diagnostics. -/
inductive AdmissionObligation where
  | withinMaxDiff
  | eqSafeSupported
  | requiredProfilesSupported
  deriving Repr, DecidableEq, Inhabited

/-- E4: machine-visible rejection reasons for failed admission checks. -/
inductive AdmissionRejectionReason where
  | maxDiffExceeded
  | eqSafeNotSupported
  | missingRequiredProfiles
  deriving Repr, DecidableEq, Inhabited

/-- E4: rejection reason to failed obligation correspondence. -/
def rejectionReasonObligation : AdmissionRejectionReason → AdmissionObligation
  | .maxDiffExceeded => .withinMaxDiff
  | .eqSafeNotSupported => .eqSafeSupported
  | .missingRequiredProfiles => .requiredProfilesSupported

/-- E4: derive rejection reasons from user capability request + inferred capability. -/
def admissionRejectionReasons
    (dUser : DUser) (dProg : CertifiedEnvelopeCapability) :
    List AdmissionRejectionReason :=
  let r₁ :=
    if dUser.maxRequestedDiff ≤ dProg.maxDiff then [] else [.maxDiffExceeded]
  let r₂ :=
    if (!dUser.eqSafeOnly || dProg.supportsEqSafeOnly) then [] else [.eqSafeNotSupported]
  let r₃ :=
    if dUser.requiredProfiles.all (fun p => p ∈ dProg.supportedProfiles) then [] else [.missingRequiredProfiles]
  r₁ ++ r₂ ++ r₃

/-- E4: diagnostics theorem/spec form for rejection reasons. -/
def DiagnosticsSoundness
    (dUser : DUser) (dProg : CertifiedEnvelopeCapability)
    (failed : AdmissionObligation → Prop) : Prop :=
  ∀ r, r ∈ admissionRejectionReasons dUser dProg → failed (rejectionReasonObligation r)

/-- E4: diagnostics completeness form (every failed obligation is diagnosed). -/
def DiagnosticsCompleteness
    (dUser : DUser) (dProg : CertifiedEnvelopeCapability)
    (failed : AdmissionObligation → Prop) : Prop :=
  ∀ o, failed o → ∃ r, r ∈ admissionRejectionReasons dUser dProg ∧
    rejectionReasonObligation r = o

/-- E4: decidability theorem form for inference/admission procedures. -/
def InferenceAdmissionDecidable
    (input : ProgramCapabilityInput)
    (dUser : DUser) : Type :=
  Prod
    (Decidable (dUserContained dUser (DProg_local input) = true))
    (Decidable (dUserContained dUser (DProg_shard input) = true))

/-- E4: complexity-bound theorem form for inference/admission procedures. -/
def InferenceComplexityBound
    (input : ProgramCapabilityInput)
    (bound : Nat) : Prop :=
  input.localProfiles.length + input.shardedProfiles.length ≤ bound

/-- E4: conservative-extension theorem form for reduced-regime collapse. -/
def ConservativeExtension
    (baseline strengthened : ProgramCapabilityInput) : Prop :=
  baseline = strengthened →
    DProg_local baseline = DProg_local strengthened ∧
    DProg_shard baseline = DProg_shard strengthened

/-! ## Hypothesis Necessity Skeleton -/

/-- E4: major hypotheses tracked for necessity/minimality analysis. -/
inductive EnvelopeMajorHypothesis where
  | localAdherence
  | shardedAdherence
  | schedulerDeterminism
  | monotonicity
  | fullAbstraction
  deriving Repr, DecidableEq, Inhabited

/-- E4: explicit counterexample witness object for dropped hypotheses. -/
structure HypothesisCounterexample where
  witnessId : String
  explanation : String
  deriving Repr, DecidableEq, Inhabited

/-- E4: hypothesis necessity/minimality theorem form with explicit counterexamples. -/
def HypothesisNecessityMinimality : Prop :=
  ∀ h : EnvelopeMajorHypothesis, ∃ cex : HypothesisCounterexample, cex.explanation ≠ ""

/-! ## Transport Assumption Necessity Tagging -/

/-- Necessity status used to tag transport assumptions theorem-by-theorem. -/
inductive AssumptionNecessityTag where
  | provenNecessary
  | sufficientOnly
  deriving Repr, DecidableEq, Inhabited

/-- A tagged transport assumption entry. -/
structure TaggedTransportAssumption where
  name : String
  tag : AssumptionNecessityTag
  deriving Repr, DecidableEq, Inhabited

/-- Necessity profile for one transported theorem statement. -/
structure TransportNecessityProfile where
  theoremName : String
  assumptions : List TaggedTransportAssumption
  deriving Repr, DecidableEq, Inhabited

/-- Profile-level hardening: all assumptions are marked proven-necessary. -/
def profileNecessityHardened (p : TransportNecessityProfile) : Prop :=
  ∀ a, a ∈ p.assumptions → a.tag = .provenNecessary

/-- Catalog-level hardening: every profile is necessity-hardened. -/
def transportCatalogNecessityHardened
    (catalog : List TransportNecessityProfile) : Prop :=
  ∀ p, p ∈ catalog → profileNecessityHardened p

/-! ## Transport Hardening Theorems -/

/-- Theorem-form tag semantics: if every assumption in a profile is tagged
    `provenNecessary`, the profile is necessity-hardened. -/
theorem profileNecessityHardened_of_allProvenNecessary
    (p : TransportNecessityProfile)
    (hAll : ∀ a, a ∈ p.assumptions → a.tag = .provenNecessary) :
    profileNecessityHardened p :=
  hAll

/-- Catalog theorem-form lifting of profile hardening. -/
theorem transportCatalogNecessityHardened_of_profiles
    (catalog : List TransportNecessityProfile)
    (hAll : ∀ p, p ∈ catalog → profileNecessityHardened p) :
    transportCatalogNecessityHardened catalog :=
  hAll

/-! ## Dropped-Assumption Witness Model -/

/-- Dropped-assumption failure witness for one transport profile.
    Intended reading: removing `dropped` invalidates the transported theorem. -/
structure DroppedTransportAssumptionFailureWitness
    (p : TransportNecessityProfile) where
  dropped : TaggedTransportAssumption
  droppedInProfile : dropped ∈ p.assumptions
  witnessId : String
  failureMode : String
  failureMode_nonempty : failureMode ≠ ""
  deriving Repr, DecidableEq

/-- Oracle interface: every `provenNecessary` assumption has a dropped-assumption
    strict-failure witness. -/
def TransportProfileMinimalityOracle
    (p : TransportNecessityProfile) : Prop :=
  ∀ a, a ∈ p.assumptions → a.tag = .provenNecessary →
    Nonempty { w : DroppedTransportAssumptionFailureWitness p // w.dropped = a }

/-- Joint minimal-basis closure for one transport profile:
    all assumptions are necessity-hardened, and each admits a dropped-assumption
    strict-failure witness. -/
def profileNecessityMinimalBasis
    (p : TransportNecessityProfile) : Prop :=
  profileNecessityHardened p ∧
  ∀ a, a ∈ p.assumptions →
    Nonempty { w : DroppedTransportAssumptionFailureWitness p // w.dropped = a }

/-- Catalog-level minimal-basis closure for necessity-tagged transport profiles. -/
def transportCatalogMinimalBasis
    (catalog : List TransportNecessityProfile) : Prop :=
  ∀ p, p ∈ catalog → profileNecessityMinimalBasis p

/-! ## Minimal-Basis Closure Theorems -/

/-- Build profile-level minimal-basis closure from hardened tags + dropped-assumption oracle. -/
theorem profileNecessityMinimalBasis_of_hardened_and_oracle
    (p : TransportNecessityProfile)
    (hHard : profileNecessityHardened p)
    (hOracle : TransportProfileMinimalityOracle p) :
    profileNecessityMinimalBasis p := by
  refine ⟨hHard, ?_⟩
  intro a hIn
  exact hOracle a hIn (hHard a hIn)

/-- Any minimal-basis profile is necessity-hardened. -/
theorem profileNecessityHardened_of_minimalBasis
    (p : TransportNecessityProfile)
    (hMin : profileNecessityMinimalBasis p) :
    profileNecessityHardened p :=
  hMin.1

/-- Build catalog-level minimal-basis closure from profile-level hardening + oracles. -/
theorem transportCatalogMinimalBasis_of_hardened_and_oracles
    (catalog : List TransportNecessityProfile)
    (hHard : transportCatalogNecessityHardened catalog)
    (hOracle : ∀ p, p ∈ catalog → TransportProfileMinimalityOracle p) :
    transportCatalogMinimalBasis catalog := by
  intro p hIn
  exact profileNecessityMinimalBasis_of_hardened_and_oracle
    p (hHard p hIn) (hOracle p hIn)

/-! ## E4 Premise Bundle -/

/-- E4: premise bundle for capability inference/admission theorem extraction. -/
structure VMEnvelopeAdmissionPremises (State : Type u) (Obs : Type v) where
  input : ProgramCapabilityInput
  localHypotheses : VMLocalEnvelopeHypotheses State Obs
  shardedHypotheses : VMShardedEnvelopeHypotheses State Obs
  runtimeComplianceLocal : DUser → Prop
  runtimeComplianceSharded : DUser → Prop
  failedObligation : AdmissionObligation → Prop
  localInferenceSoundnessWitness :
    DProgInferenceSoundness_local input localHypotheses
  shardedInferenceSoundnessWitness :
    DProgInferenceSoundness_shard input shardedHypotheses
  localPrincipalCapabilityWitness :
    PrincipalCapabilityProperty (DProg_local input)
      (fun c => CapabilityStrengthens (DProg_local input) c ∧
                CapabilityStrengthens c (DProg_local input))
  shardedPrincipalCapabilityWitness :
    PrincipalCapabilityProperty (DProg_shard input)
      (fun c => CapabilityStrengthens (DProg_shard input) c ∧
                CapabilityStrengthens c (DProg_shard input))
  localAdmissionSoundnessWitness :
    AdmissionSoundness (DProg_local input) runtimeComplianceLocal
  shardedAdmissionSoundnessWitness :
    AdmissionSoundness (DProg_shard input) runtimeComplianceSharded
  localAdmissionCompletenessWitness :
    AdmissionCompleteness (DProg_local input) runtimeComplianceLocal
  shardedAdmissionCompletenessWitness :
    AdmissionCompleteness (DProg_shard input) runtimeComplianceSharded
  diagnosticsSoundnessLocal :
    ∀ dUser, DiagnosticsSoundness dUser (DProg_local input) failedObligation
  diagnosticsSoundnessSharded :
    ∀ dUser, DiagnosticsSoundness dUser (DProg_shard input) failedObligation
  diagnosticsCompletenessLocal :
    ∀ dUser, DiagnosticsCompleteness dUser (DProg_local input) failedObligation
  diagnosticsCompletenessSharded :
    ∀ dUser, DiagnosticsCompleteness dUser (DProg_shard input) failedObligation
  decidabilityWitness :
    ∀ dUser, InferenceAdmissionDecidable input dUser
  complexityBound : Nat
  complexityBoundWitness :
    InferenceComplexityBound input complexityBound
  conservativeExtensionWitness :
    ∀ baseline, ConservativeExtension baseline input
  necessityMinimalityWitness : HypothesisNecessityMinimality

/-! ## E4 Packaged Protocol -/

/-- E4: packaged capability inference/admission theorem family. -/
structure VMEnvelopeAdmissionProtocol where
  State : Type u
  Obs : Type v
  premises : VMEnvelopeAdmissionPremises State Obs
  localInferenceSoundness :
    DProgInferenceSoundness_local premises.input premises.localHypotheses :=
      premises.localInferenceSoundnessWitness
  shardedInferenceSoundness :
    DProgInferenceSoundness_shard premises.input premises.shardedHypotheses :=
      premises.shardedInferenceSoundnessWitness
  localPrincipalCapability :
    PrincipalCapabilityProperty (DProg_local premises.input)
      (fun c => CapabilityStrengthens (DProg_local premises.input) c ∧
                CapabilityStrengthens c (DProg_local premises.input)) :=
      premises.localPrincipalCapabilityWitness
  shardedPrincipalCapability :
    PrincipalCapabilityProperty (DProg_shard premises.input)
      (fun c => CapabilityStrengthens (DProg_shard premises.input) c ∧
                CapabilityStrengthens c (DProg_shard premises.input)) :=
      premises.shardedPrincipalCapabilityWitness
  localAdmissionSoundness :
    AdmissionSoundness (DProg_local premises.input) premises.runtimeComplianceLocal :=
      premises.localAdmissionSoundnessWitness
  shardedAdmissionSoundness :
    AdmissionSoundness (DProg_shard premises.input) premises.runtimeComplianceSharded :=
      premises.shardedAdmissionSoundnessWitness
  localAdmissionCompleteness :
    AdmissionCompleteness (DProg_local premises.input) premises.runtimeComplianceLocal :=
      premises.localAdmissionCompletenessWitness
  shardedAdmissionCompleteness :
    AdmissionCompleteness (DProg_shard premises.input) premises.runtimeComplianceSharded :=
      premises.shardedAdmissionCompletenessWitness
  decidability :
    ∀ dUser, InferenceAdmissionDecidable premises.input dUser :=
      premises.decidabilityWitness
  complexity :
    InferenceComplexityBound premises.input premises.complexityBound :=
      premises.complexityBoundWitness
  conservativeExtension :
    ∀ baseline, ConservativeExtension baseline premises.input :=
      premises.conservativeExtensionWitness
  necessityMinimality : HypothesisNecessityMinimality :=
    premises.necessityMinimalityWitness

end Adequacy
end Runtime
