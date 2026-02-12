import Distributed.Model.Assumptions.Checks

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

/-- Regime-aware Byzantine assumption bundle keyed by evidence accumulation mode. -/
def byzantineSafetyAssumptionsFor (p : ProtocolSpec) : List Assumption :=
  match p.evidenceAccumulation with
  | .intersection =>
      byzantineSafetyAssumptions
  | .additiveWeight =>
      -- Additive-weight regimes use budget/timing checks in place of quorum intersection.
      [ .byzantineFaultModel
      , .evidencePrimitiveConsistent
      , .conflictExclusionPrimitiveConsistent
      , .finalizationWitnessPrimitiveConsistent
      , .timingAuthCompatible
      , .adversarialBudgetBounded
      ]
  | .coupled =>
      byzantineSafetyAssumptions

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
  -- Unfold the grouped validator cascade and normalize boolean equality.
  simp [validateAssumption, validateAssumptionSpaceFinality?,
    validateAssumptionFaultModel?, mkAssumptionResult]

/-- Validator bridge: evidence-primitive consistency check is exact. -/
theorem validateAssumption_evidencePrimitiveConsistent_passed_iff
    (p : ProtocolSpec) :
    (validateAssumption p .evidencePrimitiveConsistent).passed = true ↔
      evidencePrimitiveConsistentCheck p = true := by
  -- Unfold the grouped validator cascade and normalize boolean equality.
  simp [validateAssumption, validateAssumptionSpaceFinality?, validateAssumptionFaultModel?,
    validateAssumptionPrimitiveCoherence?, mkAssumptionResult]

/-- Validator bridge: conflict-exclusion primitive check is exact. -/
theorem validateAssumption_conflictExclusionPrimitiveConsistent_passed_iff
    (p : ProtocolSpec) :
    (validateAssumption p .conflictExclusionPrimitiveConsistent).passed = true ↔
      conflictExclusionPrimitiveConsistentCheck p = true := by
  -- Unfold the grouped validator cascade and normalize boolean equality.
  simp [validateAssumption, validateAssumptionSpaceFinality?, validateAssumptionFaultModel?,
    validateAssumptionPrimitiveCoherence?, mkAssumptionResult]

/-- Validator bridge: finalization-witness primitive check is exact. -/
theorem validateAssumption_finalizationWitnessPrimitiveConsistent_passed_iff
    (p : ProtocolSpec) :
    (validateAssumption p .finalizationWitnessPrimitiveConsistent).passed = true ↔
      finalizationWitnessPrimitiveConsistentCheck p = true := by
  -- Unfold the grouped validator cascade and normalize boolean equality.
  simp [validateAssumption, validateAssumptionSpaceFinality?, validateAssumptionFaultModel?,
    validateAssumptionPrimitiveCoherence?, mkAssumptionResult]

/-- Validator bridge: quorum-intersection witness check is exact. -/
theorem validateAssumption_quorumIntersectionWitnessed_passed_iff
    (p : ProtocolSpec) :
    (validateAssumption p .quorumIntersectionWitnessed).passed = true ↔
      quorumIntersectionWitnessedCheck p = true := by
  -- Unfold the grouped validator cascade and normalize boolean equality.
  simp [validateAssumption, validateAssumptionSpaceFinality?, validateAssumptionFaultModel?,
    validateAssumptionPrimitiveCoherence?, mkAssumptionResult]

/-- Validator bridge: timing/auth compatibility check is exact. -/
theorem validateAssumption_timingAuthCompatible_passed_iff
    (p : ProtocolSpec) :
    (validateAssumption p .timingAuthCompatible).passed = true ↔
      timingAuthCompatibleCheck p = true := by
  -- Unfold the grouped validator cascade and normalize boolean equality.
  simp [validateAssumption, validateAssumptionSpaceFinality?, validateAssumptionFaultModel?,
    validateAssumptionPrimitiveCoherence?, mkAssumptionResult]

/-- Validator bridge: adversarial-budget check is exact. -/
theorem validateAssumption_adversarialBudgetBounded_passed_iff
    (p : ProtocolSpec) :
    (validateAssumption p .adversarialBudgetBounded).passed = true ↔
      adversarialBudgetBoundedCheck p = true := by
  -- Unfold the grouped validator cascade and normalize boolean equality.
  simp [validateAssumption, validateAssumptionSpaceFinality?, validateAssumptionFaultModel?,
    validateAssumptionPrimitiveCoherence?, validateAssumptionPressureBudget?, mkAssumptionResult]

end Distributed
