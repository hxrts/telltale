import Distributed.Model.Classifier

set_option autoImplicit false

/-! # Distributed.Model.Assumptions

Core consensus assumption family and assumption-validation routines.
-/

/-
The Problem. Distributed systems proofs depend on assumptions (timing, fault model,
consensus properties) that must be explicitly stated and validated. Ad-hoc assumption
handling leads to unsound theorem application.

Solution Structure. We define:
1. `Assumption`: enumeration of all supported distributed assumptions
2. `AssumptionResult`: validation result with witness/counterexample
3. Validation routines that check protocol configurations against required assumptions
This enables assumption-aware theorem transport from the Classical layer.
-/

/-! ## Core Development -/

namespace Distributed

/-- Built-in assumptions supported by the validator. -/
inductive Assumption where
  | soundConsensus
  | bftSpace
  | nakamotoSpace
  | hybridSpace
  | deterministicFinality
  | probabilisticFinality
  | responsiveCandidate
  | cpBiased
  | apBiased
  | byzantineFaultModel
  | crashFaultOnly
  | evidencePrimitiveConsistent
  | conflictExclusionPrimitiveConsistent
  | finalizationWitnessPrimitiveConsistent
  | witnessMonotonicityConsistent
  | certificateDerivedConsistent
  | finalityModeConsistent
  | quorumIntersectionWitnessed
  | timingAuthCompatible
  | capPressureConsistent
  | responsivePreconditions
  | hybridFrontInvariant
  | adversarialBudgetBounded
  | faultThresholdDeclared
  | spaceConfidenceTagged
  | logicalTimeSemanticsDeclared
  | orderParameterDeclared
  | phaseBoundaryModelDeclared
  | interactiveDistanceDeclared
  | universalityClassDeclared
  | classicalTransportEligible
  deriving Repr, DecidableEq, Inhabited

/-- Result of validating one assumption. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

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

/-! ## Built-In Assumption Bundles -/

/-! ## Bundles: Core and Space-Specific -/

/-- Built-in core assumption set (general-purpose). -/
def coreAssumptions : List Assumption :=
  [ .soundConsensus
  , .certificateDerivedConsistent
  , .finalityModeConsistent
  , .adversarialBudgetBounded
  ]

/-- Built-in assumption set for BFT-oriented checks. -/
def bftAssumptions : List Assumption :=
  [ .soundConsensus
  , .bftSpace
  , .deterministicFinality
  , .cpBiased
  , .responsiveCandidate
  , .quorumIntersectionWitnessed
  , .timingAuthCompatible
  ]

/-- Built-in assumption set for Nakamoto-style checks. -/
def nakamotoAssumptions : List Assumption :=
  [ .soundConsensus
  , .nakamotoSpace
  , .probabilisticFinality
  , .apBiased
  , .adversarialBudgetBounded
  ]

/-! ## Bundles: Hybrid and Characterization -/

/-- Built-in assumption set for hybrid availability/finality checks. -/
def hybridAssumptions : List Assumption :=
  [ .soundConsensus
  , .hybridSpace
  , .deterministicFinality
  , .probabilisticFinality
  , .hybridFrontInvariant
  ]

/-- Assumptions for the consensus-stat-mech characterization layer. -/
def characterizationAssumptions : List Assumption :=
  [ .evidencePrimitiveConsistent
  , .conflictExclusionPrimitiveConsistent
  , .finalizationWitnessPrimitiveConsistent
  , .witnessMonotonicityConsistent
  , .certificateDerivedConsistent
  , .logicalTimeSemanticsDeclared
  , .orderParameterDeclared
  , .phaseBoundaryModelDeclared
  , .interactiveDistanceDeclared
  , .universalityClassDeclared
  , .spaceConfidenceTagged
  , .faultThresholdDeclared
  , .capPressureConsistent
  , .responsivePreconditions
  , .classicalTransportEligible
  ]

/-- Assumptions for Byzantine safety characterization and envelope admission. -/
def byzantineSafetyAssumptions : List Assumption :=
  [ .byzantineFaultModel
  , .evidencePrimitiveConsistent
  , .conflictExclusionPrimitiveConsistent
  , .finalizationWitnessPrimitiveConsistent
  , .quorumIntersectionWitnessed
  , .timingAuthCompatible
  , .adversarialBudgetBounded
  ]

/-! ## Assumption Validation -/

private def mkAssumptionResult
    (h : Assumption) (passed : Bool) (detail : String) : AssumptionResult :=
  { assumption := h, passed := passed, detail := detail }

/-! ## Validation Group: Space and Finality -/

private def validateAssumptionSpaceFinality?
    (p : ProtocolSpec) (h : Assumption) : Option AssumptionResult :=
  match h with
  | .soundConsensus =>
      some <| mkAssumptionResult h (isSoundConsensus p)
        "Model-level soundness: basic well-formedness plus BFT/Nakamoto/Hybrid classification."
  | .bftSpace =>
      some <| mkAssumptionResult h (inBFTSpace p)
        "BFT space check: intersection-style evidence primitive, Byzantine faults, authentication, and threshold constraints."
  | .nakamotoSpace =>
      some <| mkAssumptionResult h (inNakamotoSpace p)
        "Nakamoto space check: additive-weight evidence primitive, probabilistic finality, and adversarial weight below 50%."
  | .hybridSpace =>
      some <| mkAssumptionResult h (inHybridSpace p)
        "Hybrid space check: coupled quorum/work assumptions with both deterministic and probabilistic finality."
  | .deterministicFinality =>
      some <| mkAssumptionResult h p.deterministicFinality
        "Deterministic finality characteristic flag."
  | .probabilisticFinality =>
      some <| mkAssumptionResult h p.probabilisticFinality
        "Probabilistic finality characteristic flag."
  | .responsiveCandidate =>
      some <| mkAssumptionResult h p.responsivePath
        "Responsive-path flag under the chosen timing/leader assumptions."
  | .cpBiased =>
      some <| mkAssumptionResult h (p.partitionPolicy = .safetyFirst)
        "CP-leaning partition policy (safety-first)."
  | .apBiased =>
      some <| mkAssumptionResult h (p.partitionPolicy = .livenessFirst)
        "AP-leaning partition policy (liveness-first)."
  | _ => none

/-! ## Validation Group: Fault Model -/

private def validateAssumptionFaultModel?
    (p : ProtocolSpec) (h : Assumption) : Option AssumptionResult :=
  match h with
  | .byzantineFaultModel =>
      some <| mkAssumptionResult h (p.faultModel = .byzantine)
        "Byzantine fault model assumption."
  | .crashFaultOnly =>
      some <| mkAssumptionResult h (p.faultModel = .crash)
        "Crash-only fault model assumption."
  | _ => none

/-! ## Validation Group: Primitive Coherence -/

private def validateAssumptionPrimitiveCoherence?
    (p : ProtocolSpec) (h : Assumption) : Option AssumptionResult :=
  match h with
  | .evidencePrimitiveConsistent =>
      some <| mkAssumptionResult h (evidencePrimitiveConsistentCheck p)
        "Evidence primitive profile is coherent (intersection, additive-weight, or coupled)."
  | .conflictExclusionPrimitiveConsistent =>
      some <| mkAssumptionResult h (conflictExclusionPrimitiveConsistentCheck p)
        "Conflict-exclusion law is consistent with declared evidence-accumulation primitive."
  | .finalizationWitnessPrimitiveConsistent =>
      some <| mkAssumptionResult h (finalizationWitnessPrimitiveConsistentCheck p)
        "Finalization witness rule is consistent with declared evidence-accumulation primitive."
  | .witnessMonotonicityConsistent =>
      some <| mkAssumptionResult h (witnessMonotonicityConsistentCheck p)
        "Witness monotonicity is consistent with the declared evidence regime."
  | .certificateDerivedConsistent =>
      some <| mkAssumptionResult h (certificateDerivedConsistentCheck p)
        "Coarse certificate tag is consistent with primitive evidence assumptions."
  | .finalityModeConsistent =>
      some <| mkAssumptionResult h (finalityModeConsistentCheck p)
        "Derived evidence mode and finality mode are consistent (intersection=deterministic, additive=probabilistic, coupled=both)."
  | .quorumIntersectionWitnessed =>
      some <| mkAssumptionResult h (quorumIntersectionWitnessedCheck p)
        "Quorum-intersection obligations are explicitly witnessed and threshold-compatible."
  | .timingAuthCompatible =>
      some <| mkAssumptionResult h (timingAuthCompatibleCheck p)
        "Timing/authentication assumptions are explicit and compatible with threshold claims."
  | _ => none

/-! ## Validation Group: Pressure and Budget -/

private def validateAssumptionPressureBudget?
    (p : ProtocolSpec) (h : Assumption) : Option AssumptionResult :=
  match h with
  | .capPressureConsistent =>
      some <| mkAssumptionResult h (capPressureConsistentCheck p)
        "CAP policy is consistent with evidence-driven partition pressure."
  | .responsivePreconditions =>
      some <| mkAssumptionResult h (responsivePreconditionsCheck p)
        "If responsiveness is claimed, timing/auth/fault preconditions are satisfied."
  | .hybridFrontInvariant =>
      some <| mkAssumptionResult h (hybridFrontInvariantCheck p)
        "Hybrid availability/finality front invariant is satisfied."
  | .adversarialBudgetBounded =>
      some <| mkAssumptionResult h (adversarialBudgetBoundedCheck p)
        "Adversarial budget bounds are within declared count/weight regimes."
  | _ => none

/-! ## Validation Group: Declarations and Transport -/

private def validateAssumptionDeclarations?
    (p : ProtocolSpec) (h : Assumption) : Option AssumptionResult :=
  match h with
  | .faultThresholdDeclared =>
      some <| mkAssumptionResult h p.thresholdRegimeDeclared
        "Fault-threshold regime is explicitly declared."
  | .spaceConfidenceTagged =>
      some <| mkAssumptionResult h p.classificationHeuristicTagged
        "Protocol-space claims are tagged with heuristic/confidence scope."
  | .logicalTimeSemanticsDeclared =>
      some <| mkAssumptionResult h p.logicalTimeSemanticsDeclared
        "Logical-time semantics declaration (`t_logical`, `T_logical`)."
  | .orderParameterDeclared =>
      some <| mkAssumptionResult h p.orderParameterDeclared
        "At least one order parameter is declared."
  | .phaseBoundaryModelDeclared =>
      some <| mkAssumptionResult h p.phaseBoundaryModelDeclared
        "Phase-boundary model declaration is present."
  | .interactiveDistanceDeclared =>
      some <| mkAssumptionResult h p.interactiveDistanceDeclared
        "Interactive distance declaration (`d_int`) is present."
  | .universalityClassDeclared =>
      some <| mkAssumptionResult h p.universalityClassDeclared
        "Universality-class declaration is present."
  | .classicalTransportEligible =>
      some <| mkAssumptionResult h (classicalTransportEligibleCheck p)
        "Classical transport profile is declared and consensus/model prerequisites are satisfied."
  | _ => none

/-! ## Validation Dispatcher -/

/-- Validate one built-in assumption against a protocol spec. -/
def validateAssumption (p : ProtocolSpec) (h : Assumption) : AssumptionResult :=
  match validateAssumptionSpaceFinality? p h with
  | some r => r
  | none =>
      match validateAssumptionFaultModel? p h with
      | some r => r
      | none =>
          match validateAssumptionPrimitiveCoherence? p h with
          | some r => r
          | none =>
              match validateAssumptionPressureBudget? p h with
              | some r => r
              | none =>
                  match validateAssumptionDeclarations? p h with
                  | some r => r
                  | none =>
                      mkAssumptionResult h false
                        "Unhandled assumption (update validator groups)."

/-! ## Validation Summary API -/

/-- Validate a list of assumptions. -/
def validateAssumptions (p : ProtocolSpec) (hs : List Assumption) : List AssumptionResult :=
  hs.map (validateAssumption p)

/-- True iff every assumption in the result list passed. -/
def allPassed (rs : List AssumptionResult) : Bool :=
  rs.all (fun r => r.passed)

/-- Summary of assumption validation for one protocol spec. -/
structure AssumptionSummary where
  space : ProtocolSpace
  results : List AssumptionResult
  allPassed : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Convenience API: validate and summarize. -/
def runAssumptionValidation (p : ProtocolSpec) (hs : List Assumption) :
    AssumptionSummary :=
  let space := classify p
  let results := validateAssumptions p hs
  { space := space
  , results := results
  , allPassed := allPassed results
  }

/-! ## Byzantine Bool-to-Prop Bridge Lemmas -/

/-- Validator bridge: byzantine-fault-model check is exact. -/
theorem validateAssumption_byzantineFaultModel_passed_iff
    (p : ProtocolSpec) :
    (validateAssumption p .byzantineFaultModel).passed = true ↔
      p.faultModel = .byzantine := by
  -- Unfold the validator branch and normalize booleans.
  simp [validateAssumption]

/-- Validator bridge: evidence-primitive consistency check is exact. -/
theorem validateAssumption_evidencePrimitiveConsistent_passed_iff
    (p : ProtocolSpec) :
    (validateAssumption p .evidencePrimitiveConsistent).passed = true ↔
      evidencePrimitiveConsistentCheck p = true := by
  -- The branch is a direct projection of the internal checker.
  simp [validateAssumption]

/-- Validator bridge: conflict-exclusion primitive check is exact. -/
theorem validateAssumption_conflictExclusionPrimitiveConsistent_passed_iff
    (p : ProtocolSpec) :
    (validateAssumption p .conflictExclusionPrimitiveConsistent).passed = true ↔
      conflictExclusionPrimitiveConsistentCheck p = true := by
  -- The branch is a direct projection of the internal checker.
  simp [validateAssumption]

/-- Validator bridge: finalization-witness primitive check is exact. -/
theorem validateAssumption_finalizationWitnessPrimitiveConsistent_passed_iff
    (p : ProtocolSpec) :
    (validateAssumption p .finalizationWitnessPrimitiveConsistent).passed = true ↔
      finalizationWitnessPrimitiveConsistentCheck p = true := by
  -- The branch is a direct projection of the internal checker.
  simp [validateAssumption]

/-- Validator bridge: quorum-intersection witness check is exact. -/
theorem validateAssumption_quorumIntersectionWitnessed_passed_iff
    (p : ProtocolSpec) :
    (validateAssumption p .quorumIntersectionWitnessed).passed = true ↔
      quorumIntersectionWitnessedCheck p = true := by
  -- The branch is a direct projection of the internal checker.
  simp [validateAssumption]

/-- Validator bridge: timing/auth compatibility check is exact. -/
theorem validateAssumption_timingAuthCompatible_passed_iff
    (p : ProtocolSpec) :
    (validateAssumption p .timingAuthCompatible).passed = true ↔
      timingAuthCompatibleCheck p = true := by
  -- The branch is a direct projection of the internal checker.
  simp [validateAssumption]

/-- Validator bridge: adversarial-budget check is exact. -/
theorem validateAssumption_adversarialBudgetBounded_passed_iff
    (p : ProtocolSpec) :
    (validateAssumption p .adversarialBudgetBounded).passed = true ↔
      adversarialBudgetBoundedCheck p = true := by
  -- The branch is a direct projection of the internal checker.
  simp [validateAssumption]

end Distributed
