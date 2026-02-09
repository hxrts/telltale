import Consensus.Core

set_option autoImplicit false

/-! # Consensus.Examples

Small executable-style examples for consensus hypothesis validation.
-/

namespace Consensus
namespace Examples

/-- A representative quorum-based BFT protocol profile. -/
def bftSpec : ProtocolSpec :=
  { n := 4
  , f := 1
  , timing := .partialSync
  , evidenceAccumulation := .intersection
  , conflictExclusionLaw := .quorumIntersection
  , finalizationWitnessRule := .thresholdCertificate
  , witnessMonotonicity := true
  , certificate := .quorum
  , quorumSize := 3
  , authentication := .signatures
  , faultModel := .byzantine
  , adversaryKind := .adaptive
  , partitionPolicy := .safetyFirst
  , deterministicFinality := true
  , probabilisticFinality := false
  , responsivePath := true
  , adversarialWeightPermille := 250
  , timingAuthContractDeclared := true
  , quorumIntersectionWitnessed := true
  , thresholdRegimeDeclared := true
  , classificationHeuristicTagged := true
  , logicalTimeSemanticsDeclared := true
  , orderParameterDeclared := true
  , phaseBoundaryModelDeclared := true
  , interactiveDistanceDeclared := true
  , universalityClassDeclared := true
  , classicalTransportProfileDeclared := true
  }

/-- A representative Nakamoto-style profile. -/
def nakamotoSpec : ProtocolSpec :=
  { n := 100
  , f := 49
  , timing := .partialSync
  , evidenceAccumulation := .additiveWeight
  , conflictExclusionLaw := .weightDominance
  , finalizationWitnessRule := .confirmationDepth
  , witnessMonotonicity := false
  , certificate := .work
  , quorumSize := 0
  , authentication := .none
  , faultModel := .byzantine
  , adversaryKind := .adaptive
  , partitionPolicy := .livenessFirst
  , deterministicFinality := false
  , probabilisticFinality := true
  , responsivePath := false
  , adversarialWeightPermille := 450
  , thresholdRegimeDeclared := true
  , classificationHeuristicTagged := true
  , logicalTimeSemanticsDeclared := true
  , orderParameterDeclared := true
  , phaseBoundaryModelDeclared := true
  , interactiveDistanceDeclared := true
  , universalityClassDeclared := true
  , classicalTransportProfileDeclared := true
  }

/-- Minimal evidence profile that supports a subset of classical transport checks. -/
def classicalEvidenceBasic : ClassicalEvidence :=
  { finiteState := true
  , coherentInvariant := true
  , harmonyCommutation := true
  , markovAbstraction := true
  , driftWitness := true
  , mixingWitness := true
  , exponentialTailWitness := true
  , queueRateWaitInputs := true
  , spectralGapPos := true
  }

example : classify bftSpec = .bft := by
  native_decide

example : classify nakamotoSpec = .nakamoto := by
  native_decide

example : (runValidation bftSpec bftHypotheses).1 = .bft := by
  native_decide

example : (runValidation bftSpec bftHypotheses).2.2 = true := by
  native_decide

example : (validateClassicalProperty bftSpec classicalEvidenceBasic .fosterLyapunov).passed = true := by
  native_decide

example : (validateClassicalProperty bftSpec classicalEvidenceBasic .mixingTime).passed = true := by
  native_decide

example : (validateClassicalProperty bftSpec classicalEvidenceBasic .littlesLaw).passed = true := by
  native_decide

example : (validateClassicalProperty bftSpec classicalEvidenceBasic .functionalCLT).passed = false := by
  native_decide

example : (validateAsBFT bftSpec).allPassed = true := by
  native_decide

example : (validateWithClassicalCore bftSpec classicalEvidenceBasic).allPassed = true := by
  native_decide

end Examples
end Consensus
