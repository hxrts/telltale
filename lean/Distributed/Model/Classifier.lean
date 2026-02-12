import Distributed.Model.Types

set_option autoImplicit false

/-! # Distributed.Classifier

Coarse protocol-space checks and classification.
-/

/-
The Problem. We need a lightweight, deterministic classifier that checks basic
protocol consistency before deeper theorem-specific analyses.
Solution Structure. Encode primitive checks, derive certificate consistency, and
compose these into coarse protocol-space predicates plus a final classifier.
-/

namespace Distributed

/-! ## Baseline Sanity Checks -/

/-- Generic well-formedness checks for protocol specs. -/
def basicWellFormed (p : ProtocolSpec) : Bool :=
  0 < p.n &&
  p.f < p.n &&
  p.adversarialWeightPermille <= 1000

/-- Primitive evidence profile for intersection-dominant safety witnesses. -/
def intersectionPrimitive (p : ProtocolSpec) : Bool :=
  p.evidenceAccumulation = .intersection &&
  p.conflictExclusionLaw = .quorumIntersection &&
  p.finalizationWitnessRule = .thresholdCertificate &&
  p.witnessMonotonicity

/-- Primitive evidence profile for additive-weight safety witnesses. -/
def additivePrimitive (p : ProtocolSpec) : Bool :=
  p.evidenceAccumulation = .additiveWeight &&
  p.conflictExclusionLaw = .weightDominance &&
  p.finalizationWitnessRule = .confirmationDepth &&
  !p.witnessMonotonicity

/-- Primitive evidence profile for coupled safety witnesses. -/
def coupledPrimitive (p : ProtocolSpec) : Bool :=
  p.evidenceAccumulation = .coupled &&
  p.conflictExclusionLaw = .coupledRule &&
  p.finalizationWitnessRule = .coupledWitness

/-! ## Certificate Inference and Consistency -/

/-- Infer the coarse certificate tag from fundamental evidence primitives. -/
def inferredCertificate? (p : ProtocolSpec) : Option CertificateModel :=
  if coupledPrimitive p then
    some .hybrid
  else if intersectionPrimitive p then
    some .quorum
  else if additivePrimitive p then
    some .work
  else
    none

/-- Coarse certificate tag agrees with primitive evidence assumptions. -/
def certificateDerivedConsistent (p : ProtocolSpec) : Bool :=
  match inferredCertificate? p with
  | some c => p.certificate = c
  | none => false

/-- Quorum sanity check for quorum-style certificates. -/
def quorumSane (p : ProtocolSpec) : Bool :=
  p.quorumSize <= p.n && p.quorumSize > p.n / 2

/-- BFT threshold check under timing/authentication assumptions. -/
def bftThresholdOk (p : ProtocolSpec) : Bool :=
  match p.timing, p.authentication with
  | .sync, .signatures => 2 * p.f < p.n
  | .sync, .oral => 3 * p.f < p.n
  | .partialSync, .signatures => 3 * p.f + 1 <= p.n
  | .async, .signatures => 3 * p.f + 1 <= p.n
  | _, _ => false

/-! ## Protocol Space Classification -/

/-- Heuristic classifier for BFT protocol space. -/
def inBFTSpace (p : ProtocolSpec) : Bool :=
  basicWellFormed p &&
  intersectionPrimitive p &&
  p.faultModel = .byzantine &&
  p.authentication ≠ .none &&
  bftThresholdOk p &&
  quorumSane p

/-- Heuristic classifier for Nakamoto-style protocol space. -/
def inNakamotoSpace (p : ProtocolSpec) : Bool :=
  basicWellFormed p &&
  additivePrimitive p &&
  p.faultModel = .byzantine &&
  p.probabilisticFinality &&
  p.adversarialWeightPermille < 500

/-- Heuristic classifier for coupled hybrid protocols. -/
def inHybridSpace (p : ProtocolSpec) : Bool :=
  basicWellFormed p &&
  coupledPrimitive p &&
  p.faultModel = .byzantine &&
  p.authentication = .signatures &&
  p.probabilisticFinality &&
  p.deterministicFinality &&
  p.adversarialWeightPermille < 500 &&
  (3 * p.f + 1 <= p.n) &&
  quorumSane p

/-- Coarse soundness predicate at the model-validation level. -/
def isSoundConsensus (p : ProtocolSpec) : Bool :=
  basicWellFormed p &&
  certificateDerivedConsistent p &&
  (inBFTSpace p || inNakamotoSpace p || inHybridSpace p)

/-! ## Final Coarse Tag -/

/-- Classify a protocol spec into one of the built-in spaces. -/
def classify (p : ProtocolSpec) : ProtocolSpace :=
  if inHybridSpace p then
    .hybrid
  else if inBFTSpace p then
    .bft
  else if inNakamotoSpace p then
    .nakamoto
  else
    .outside

end Distributed
