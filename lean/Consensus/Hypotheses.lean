import Consensus.Classifier

set_option autoImplicit false

/-! # Consensus.Hypotheses

Built-in hypothesis families and validation routines.
-/

namespace Consensus

/-- Built-in hypotheses supported by the validator. -/
inductive Hypothesis where
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

/-- Result of validating one hypothesis. -/
structure ValidationResult where
  hypothesis : Hypothesis
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Internal helper: finality-mode coherence with certificate mode. -/
def finalityModeConsistentCheck (p : ProtocolSpec) : Bool :=
  match p.certificate with
  | .quorum => p.deterministicFinality && !p.probabilisticFinality
  | .work => p.probabilisticFinality && !p.deterministicFinality
  | .hybrid => p.probabilisticFinality && p.deterministicFinality

/-- Internal helper: quorum intersection assumptions are explicit and plausible. -/
def quorumIntersectionWitnessedCheck (p : ProtocolSpec) : Bool :=
  match p.certificate with
  | .work => false
  | .quorum | .hybrid =>
      p.quorumIntersectionWitnessed && quorumSane p && bftThresholdOk p

/-- Internal helper: timing/auth model is explicitly declared and compatible. -/
def timingAuthCompatibleCheck (p : ProtocolSpec) : Bool :=
  match p.certificate with
  | .work => p.timingAuthContractDeclared
  | .quorum | .hybrid =>
      p.timingAuthContractDeclared &&
      p.authentication ≠ .none &&
      bftThresholdOk p

/-- Internal helper: CAP policy aligns with certificate pressure. -/
def capPressureConsistentCheck (p : ProtocolSpec) : Bool :=
  match p.certificate, p.partitionPolicy with
  | .quorum, .livenessFirst => false
  | .work, .safetyFirst => false
  | .hybrid, .adaptive => true
  | .hybrid, _ => true
  | _, _ => true

/-- Internal helper: if responsive path is claimed, preconditions must hold. -/
def responsivePreconditionsCheck (p : ProtocolSpec) : Bool :=
  if !p.responsivePath then
    true
  else
    (p.certificate = .quorum || p.certificate = .hybrid) &&
    (p.timing = .sync || p.timing = .partialSync) &&
    p.authentication = .signatures &&
    p.faultModel = .byzantine &&
    basicWellFormed p

/-- Internal helper: adversarial-budget check across count and weight regimes. -/
def adversarialBudgetBoundedCheck (p : ProtocolSpec) : Bool :=
  let countOk :=
    match p.certificate with
    | .work => true
    | .quorum | .hybrid => bftThresholdOk p
  let weightOk :=
    match p.certificate with
    | .quorum => true
    | .work | .hybrid => p.adversarialWeightPermille < 500
  basicWellFormed p && countOk && weightOk

/-- Internal helper: hybrid finalized-prefix/available-prefix invariant status. -/
def hybridFrontInvariantCheck (p : ProtocolSpec) : Bool :=
  if p.certificate = .hybrid then
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

/-- Built-in core hypothesis set (general-purpose). -/
def coreHypotheses : List Hypothesis :=
  [ .soundConsensus
  , .finalityModeConsistent
  , .adversarialBudgetBounded
  ]

/-- Built-in hypothesis set for BFT-oriented checks. -/
def bftHypotheses : List Hypothesis :=
  [ .soundConsensus
  , .bftSpace
  , .deterministicFinality
  , .cpBiased
  , .responsiveCandidate
  , .quorumIntersectionWitnessed
  , .timingAuthCompatible
  ]

/-- Built-in hypothesis set for Nakamoto-style checks. -/
def nakamotoHypotheses : List Hypothesis :=
  [ .soundConsensus
  , .nakamotoSpace
  , .probabilisticFinality
  , .apBiased
  , .adversarialBudgetBounded
  ]

/-- Built-in hypothesis set for hybrid availability/finality checks. -/
def hybridHypotheses : List Hypothesis :=
  [ .soundConsensus
  , .hybridSpace
  , .deterministicFinality
  , .probabilisticFinality
  , .hybridFrontInvariant
  ]

/-- Hypotheses for the consensus-stat-mech characterization layer. -/
def characterizationHypotheses : List Hypothesis :=
  [ .logicalTimeSemanticsDeclared
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

/-- Validate one built-in hypothesis against a protocol spec. -/
def validateHypothesis (p : ProtocolSpec) (h : Hypothesis) : ValidationResult :=
  match h with
  | .soundConsensus =>
      { hypothesis := h
      , passed := isSoundConsensus p
      , detail := "Model-level soundness: basic well-formedness plus BFT/Nakamoto/Hybrid classification."
      }
  | .bftSpace =>
      { hypothesis := h
      , passed := inBFTSpace p
      , detail := "BFT space check: Byzantine faults, quorum-style certificate, authentication, and threshold constraints."
      }
  | .nakamotoSpace =>
      { hypothesis := h
      , passed := inNakamotoSpace p
      , detail := "Nakamoto space check: work certificate, probabilistic finality, and adversarial weight below 50%."
      }
  | .hybridSpace =>
      { hypothesis := h
      , passed := inHybridSpace p
      , detail := "Hybrid space check: coupled quorum/work assumptions with both deterministic and probabilistic finality."
      }
  | .deterministicFinality =>
      { hypothesis := h
      , passed := p.deterministicFinality
      , detail := "Deterministic finality characteristic flag."
      }
  | .probabilisticFinality =>
      { hypothesis := h
      , passed := p.probabilisticFinality
      , detail := "Probabilistic finality characteristic flag."
      }
  | .responsiveCandidate =>
      { hypothesis := h
      , passed := p.responsivePath
      , detail := "Responsive-path flag under the chosen timing/leader assumptions."
      }
  | .cpBiased =>
      { hypothesis := h
      , passed := p.partitionPolicy = .safetyFirst
      , detail := "CP-leaning partition policy (safety-first)."
      }
  | .apBiased =>
      { hypothesis := h
      , passed := p.partitionPolicy = .livenessFirst
      , detail := "AP-leaning partition policy (liveness-first)."
      }
  | .byzantineFaultModel =>
      { hypothesis := h
      , passed := p.faultModel = .byzantine
      , detail := "Byzantine fault model assumption."
      }
  | .crashFaultOnly =>
      { hypothesis := h
      , passed := p.faultModel = .crash
      , detail := "Crash-only fault model assumption."
      }
  | .finalityModeConsistent =>
      { hypothesis := h
      , passed := finalityModeConsistentCheck p
      , detail := "Certificate/finality mode consistency (quorum=deterministic, work=probabilistic, hybrid=both)."
      }
  | .quorumIntersectionWitnessed =>
      { hypothesis := h
      , passed := quorumIntersectionWitnessedCheck p
      , detail := "Quorum-intersection obligations are explicitly witnessed and threshold-compatible."
      }
  | .timingAuthCompatible =>
      { hypothesis := h
      , passed := timingAuthCompatibleCheck p
      , detail := "Timing/authentication assumptions are explicit and compatible with threshold claims."
      }
  | .capPressureConsistent =>
      { hypothesis := h
      , passed := capPressureConsistentCheck p
      , detail := "CAP policy is consistent with certificate-driven partition pressure."
      }
  | .responsivePreconditions =>
      { hypothesis := h
      , passed := responsivePreconditionsCheck p
      , detail := "If responsiveness is claimed, timing/auth/fault preconditions are satisfied."
      }
  | .hybridFrontInvariant =>
      { hypothesis := h
      , passed := hybridFrontInvariantCheck p
      , detail := "Hybrid availability/finality front invariant is satisfied."
      }
  | .adversarialBudgetBounded =>
      { hypothesis := h
      , passed := adversarialBudgetBoundedCheck p
      , detail := "Adversarial budget bounds are within declared count/weight regimes."
      }
  | .faultThresholdDeclared =>
      { hypothesis := h
      , passed := p.thresholdRegimeDeclared
      , detail := "Fault-threshold regime is explicitly declared."
      }
  | .spaceConfidenceTagged =>
      { hypothesis := h
      , passed := p.classificationHeuristicTagged
      , detail := "Protocol-space claims are tagged with heuristic/confidence scope."
      }
  | .logicalTimeSemanticsDeclared =>
      { hypothesis := h
      , passed := p.logicalTimeSemanticsDeclared
      , detail := "Logical-time semantics declaration (`t_logical`, `T_logical`)."
      }
  | .orderParameterDeclared =>
      { hypothesis := h
      , passed := p.orderParameterDeclared
      , detail := "At least one order parameter is declared."
      }
  | .phaseBoundaryModelDeclared =>
      { hypothesis := h
      , passed := p.phaseBoundaryModelDeclared
      , detail := "Phase-boundary model declaration is present."
      }
  | .interactiveDistanceDeclared =>
      { hypothesis := h
      , passed := p.interactiveDistanceDeclared
      , detail := "Interactive distance declaration (`d_int`) is present."
      }
  | .universalityClassDeclared =>
      { hypothesis := h
      , passed := p.universalityClassDeclared
      , detail := "Universality-class declaration is present."
      }
  | .classicalTransportEligible =>
      { hypothesis := h
      , passed := classicalTransportEligibleCheck p
      , detail := "Classical transport profile is declared and consensus/model prerequisites are satisfied."
      }

/-- Validate a list of hypotheses. -/
def validateHypotheses (p : ProtocolSpec) (hs : List Hypothesis) : List ValidationResult :=
  hs.map (validateHypothesis p)

/-- True iff every hypothesis in the result list passed. -/
def allPassed (rs : List ValidationResult) : Bool :=
  rs.all (fun r => r.passed)

/-- Convenience API: validate and summarize. -/
def runValidation (p : ProtocolSpec) (hs : List Hypothesis) :
    ProtocolSpace × List ValidationResult × Bool :=
  let space := classify p
  let results := validateHypotheses p hs
  (space, results, allPassed results)

end Consensus

