import Distributed.Model.Classifier

set_option autoImplicit false

/-! # Distributed.Model.Assumptions

Core consensus assumption family and assumption-validation routines.
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

/-- Validate one built-in assumption against a protocol spec. -/
def validateAssumption (p : ProtocolSpec) (h : Assumption) : AssumptionResult :=
  match h with
  | .soundConsensus =>
      { assumption := h
      , passed := isSoundConsensus p
      , detail := "Model-level soundness: basic well-formedness plus BFT/Nakamoto/Hybrid classification."
      }
  | .bftSpace =>
      { assumption := h
      , passed := inBFTSpace p
      , detail := "BFT space check: intersection-style evidence primitive, Byzantine faults, authentication, and threshold constraints."
      }
  | .nakamotoSpace =>
      { assumption := h
      , passed := inNakamotoSpace p
      , detail := "Nakamoto space check: additive-weight evidence primitive, probabilistic finality, and adversarial weight below 50%."
      }
  | .hybridSpace =>
      { assumption := h
      , passed := inHybridSpace p
      , detail := "Hybrid space check: coupled quorum/work assumptions with both deterministic and probabilistic finality."
      }
  | .deterministicFinality =>
      { assumption := h
      , passed := p.deterministicFinality
      , detail := "Deterministic finality characteristic flag."
      }
  | .probabilisticFinality =>
      { assumption := h
      , passed := p.probabilisticFinality
      , detail := "Probabilistic finality characteristic flag."
      }
  | .responsiveCandidate =>
      { assumption := h
      , passed := p.responsivePath
      , detail := "Responsive-path flag under the chosen timing/leader assumptions."
      }
  | .cpBiased =>
      { assumption := h
      , passed := p.partitionPolicy = .safetyFirst
      , detail := "CP-leaning partition policy (safety-first)."
      }
  | .apBiased =>
      { assumption := h
      , passed := p.partitionPolicy = .livenessFirst
      , detail := "AP-leaning partition policy (liveness-first)."
      }
  | .byzantineFaultModel =>
      { assumption := h
      , passed := p.faultModel = .byzantine
      , detail := "Byzantine fault model assumption."
      }
  | .crashFaultOnly =>
      { assumption := h
      , passed := p.faultModel = .crash
      , detail := "Crash-only fault model assumption."
      }
  | .evidencePrimitiveConsistent =>
      { assumption := h
      , passed := evidencePrimitiveConsistentCheck p
      , detail := "Evidence primitive profile is coherent (intersection, additive-weight, or coupled)."
      }
  | .conflictExclusionPrimitiveConsistent =>
      { assumption := h
      , passed := conflictExclusionPrimitiveConsistentCheck p
      , detail := "Conflict-exclusion law is consistent with declared evidence-accumulation primitive."
      }
  | .finalizationWitnessPrimitiveConsistent =>
      { assumption := h
      , passed := finalizationWitnessPrimitiveConsistentCheck p
      , detail := "Finalization witness rule is consistent with declared evidence-accumulation primitive."
      }
  | .witnessMonotonicityConsistent =>
      { assumption := h
      , passed := witnessMonotonicityConsistentCheck p
      , detail := "Witness monotonicity is consistent with the declared evidence regime."
      }
  | .certificateDerivedConsistent =>
      { assumption := h
      , passed := certificateDerivedConsistentCheck p
      , detail := "Coarse certificate tag is consistent with primitive evidence assumptions."
      }
  | .finalityModeConsistent =>
      { assumption := h
      , passed := finalityModeConsistentCheck p
      , detail := "Derived evidence mode and finality mode are consistent (intersection=deterministic, additive=probabilistic, coupled=both)."
      }
  | .quorumIntersectionWitnessed =>
      { assumption := h
      , passed := quorumIntersectionWitnessedCheck p
      , detail := "Quorum-intersection obligations are explicitly witnessed and threshold-compatible."
      }
  | .timingAuthCompatible =>
      { assumption := h
      , passed := timingAuthCompatibleCheck p
      , detail := "Timing/authentication assumptions are explicit and compatible with threshold claims."
      }
  | .capPressureConsistent =>
      { assumption := h
      , passed := capPressureConsistentCheck p
      , detail := "CAP policy is consistent with evidence-driven partition pressure."
      }
  | .responsivePreconditions =>
      { assumption := h
      , passed := responsivePreconditionsCheck p
      , detail := "If responsiveness is claimed, timing/auth/fault preconditions are satisfied."
      }
  | .hybridFrontInvariant =>
      { assumption := h
      , passed := hybridFrontInvariantCheck p
      , detail := "Hybrid availability/finality front invariant is satisfied."
      }
  | .adversarialBudgetBounded =>
      { assumption := h
      , passed := adversarialBudgetBoundedCheck p
      , detail := "Adversarial budget bounds are within declared count/weight regimes."
      }
  | .faultThresholdDeclared =>
      { assumption := h
      , passed := p.thresholdRegimeDeclared
      , detail := "Fault-threshold regime is explicitly declared."
      }
  | .spaceConfidenceTagged =>
      { assumption := h
      , passed := p.classificationHeuristicTagged
      , detail := "Protocol-space claims are tagged with heuristic/confidence scope."
      }
  | .logicalTimeSemanticsDeclared =>
      { assumption := h
      , passed := p.logicalTimeSemanticsDeclared
      , detail := "Logical-time semantics declaration (`t_logical`, `T_logical`)."
      }
  | .orderParameterDeclared =>
      { assumption := h
      , passed := p.orderParameterDeclared
      , detail := "At least one order parameter is declared."
      }
  | .phaseBoundaryModelDeclared =>
      { assumption := h
      , passed := p.phaseBoundaryModelDeclared
      , detail := "Phase-boundary model declaration is present."
      }
  | .interactiveDistanceDeclared =>
      { assumption := h
      , passed := p.interactiveDistanceDeclared
      , detail := "Interactive distance declaration (`d_int`) is present."
      }
  | .universalityClassDeclared =>
      { assumption := h
      , passed := p.universalityClassDeclared
      , detail := "Universality-class declaration is present."
      }
  | .classicalTransportEligible =>
      { assumption := h
      , passed := classicalTransportEligibleCheck p
      , detail := "Classical transport profile is declared and consensus/model prerequisites are satisfied."
      }

/-- Validate a list of assumptions. -/
def validateAssumptions (p : ProtocolSpec) (hs : List Assumption) : List AssumptionResult :=
  hs.map (validateAssumption p)

/-- True iff every assumption in the result list passed. -/
def allPassed (rs : List AssumptionResult) : Bool :=
  rs.all (fun r => r.passed)

/-- Convenience API: validate and summarize. -/
def runAssumptionValidation (p : ProtocolSpec) (hs : List Assumption) :
    ProtocolSpace × List AssumptionResult × Bool :=
  let space := classify p
  let results := validateAssumptions p hs
  (space, results, allPassed results)

end Distributed
