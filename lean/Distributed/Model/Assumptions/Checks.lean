import Distributed.Model.Classifier

set_option autoImplicit false

/-! # Distributed.Model.Assumptions.Checks

Internal boolean checks used by assumption validators.
-/

namespace Distributed

/-! ## Internal Consistency Checks -/

/-- Internal helper: finality-mode coherence with certificate mode. -/
def finalityModeConsistentCheck (p : ProtocolSpec) : Bool :=
  match inferredCertificate? p with
  | none => false
  | some .quorum => p.deterministicFinality && !p.probabilisticFinality
  | some .work => p.probabilisticFinality && !p.deterministicFinality
  | some .hybrid => p.probabilisticFinality && p.deterministicFinality

/-- Internal helper: primitive evidence selection is one coherent family. -/
def evidencePrimitiveConsistentCheck (p : ProtocolSpec) : Bool :=
  intersectionPrimitive p || additivePrimitive p || coupledPrimitive p

/-- Internal helper: conflict-exclusion law matches evidence accumulation. -/
def conflictExclusionPrimitiveConsistentCheck (p : ProtocolSpec) : Bool :=
  match p.evidenceAccumulation with
  | .intersection => p.conflictExclusionLaw = .quorumIntersection
  | .additiveWeight => p.conflictExclusionLaw = .weightDominance
  | .coupled => p.conflictExclusionLaw = .coupledRule

/-- Internal helper: finalization witness rule matches evidence accumulation. -/
def finalizationWitnessPrimitiveConsistentCheck (p : ProtocolSpec) : Bool :=
  match p.evidenceAccumulation with
  | .intersection => p.finalizationWitnessRule = .thresholdCertificate
  | .additiveWeight => p.finalizationWitnessRule = .confirmationDepth
  | .coupled => p.finalizationWitnessRule = .coupledWitness

/-- Internal helper: witness monotonicity is coherent with evidence regime. -/
def witnessMonotonicityConsistentCheck (p : ProtocolSpec) : Bool :=
  match p.evidenceAccumulation with
  | .intersection => p.witnessMonotonicity
  | .additiveWeight => !p.witnessMonotonicity
  | .coupled => p.witnessMonotonicity

/-- Internal helper: coarse certificate tag agrees with primitive model. -/
def certificateDerivedConsistentCheck (p : ProtocolSpec) : Bool :=
  Distributed.certificateDerivedConsistent p

/-! ## Internal Checks: Threshold/Timing/CAP Preconditions -/

/-- Internal helper: quorum intersection assumptions are explicit and plausible. -/
def quorumIntersectionWitnessedCheck (p : ProtocolSpec) : Bool :=
  if additivePrimitive p then
    false
  else
    (intersectionPrimitive p || coupledPrimitive p) &&
      p.quorumIntersectionWitnessed && quorumSane p && bftThresholdOk p

/-- Internal helper: timing/auth model is explicitly declared and compatible. -/
def timingAuthCompatibleCheck (p : ProtocolSpec) : Bool :=
  if additivePrimitive p then
    p.timingAuthContractDeclared
  else
    p.timingAuthContractDeclared &&
    p.authentication ≠ .none &&
    bftThresholdOk p

/-- Internal helper: CAP policy aligns with certificate pressure. -/
def capPressureConsistentCheck (p : ProtocolSpec) : Bool :=
  match inferredCertificate? p, p.partitionPolicy with
  | some .quorum, .livenessFirst => false
  | some .work, .safetyFirst => false
  | some .hybrid, .adaptive => true
  | some .hybrid, _ => true
  | _, _ => true

/-- Internal helper: if responsive path is claimed, preconditions must hold. -/
def responsivePreconditionsCheck (p : ProtocolSpec) : Bool :=
  if !p.responsivePath then
    true
  else
    (intersectionPrimitive p || coupledPrimitive p) &&
    (p.timing = .sync || p.timing = .partialSync) &&
    p.authentication = .signatures &&
    p.faultModel = .byzantine &&
    basicWellFormed p

/-- Internal helper: adversarial-budget check across count and weight regimes. -/
def adversarialBudgetBoundedCheck (p : ProtocolSpec) : Bool :=
  let countOk :=
    if additivePrimitive p then true else bftThresholdOk p
  let weightOk :=
    if intersectionPrimitive p then true else p.adversarialWeightPermille < 500
  basicWellFormed p && countOk && weightOk

/-- Internal helper: hybrid finalized-prefix/available-prefix invariant status. -/
def hybridFrontInvariantCheck (p : ProtocolSpec) : Bool :=
  if coupledPrimitive p then
    p.hybridFrontInvariantHolds
  else
    true

/-- Internal helper: classical transport profile eligibility. -/
def classicalTransportEligibleCheck (p : ProtocolSpec) : Bool :=
  isSoundConsensus p &&
  p.classicalTransportProfileDeclared &&
  p.logicalTimeSemanticsDeclared &&
  p.orderParameterDeclared &&
  p.phaseBoundaryModelDeclared

end Distributed
