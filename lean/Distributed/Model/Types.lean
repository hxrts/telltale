set_option autoImplicit false

/-! # Distributed.Types

Core types for consensus model validation.
-/

/-
The Problem. Consensus protocols vary along multiple dimensions (timing, certificates,
fault models, finality), and we need a systematic way to classify and validate
protocol configurations.

Solution Structure. We define core type families:
1. `TimingModel`: sync, partial-sync, async
2. `CertificateModel`: quorum, work, hybrid
3. `FaultModel`: crash vs byzantine
4. Evidence/finalization models for finality reasoning
These types form the vocabulary for assumption validation.
-/

/-! ## Core Development -/

namespace Distributed

/-! ## Timing and Certificate Axes -/

/-- Timing assumptions for protocol execution. -/
inductive TimingModel where
  | sync
  | partialSync
  | async
  deriving Repr, DecidableEq, Inhabited

/-- Certificate family used for finality evidence. -/
inductive CertificateModel where
  | quorum
  | work
  | hybrid
  deriving Repr, DecidableEq, Inhabited

/-- Primitive evidence accumulation regime. -/
inductive EvidenceAccumulationModel where
  | intersection
  | additiveWeight
  | coupled
  deriving Repr, DecidableEq, Inhabited

/-- Primitive conflict-exclusion law for incompatible decisions. -/
inductive ConflictExclusionLaw where
  | quorumIntersection
  | weightDominance
  | coupledRule
  deriving Repr, DecidableEq, Inhabited

/-- Primitive finalization witness rule. -/
inductive FinalizationWitnessRule where
  | thresholdCertificate
  | confirmationDepth
  | coupledWitness
  deriving Repr, DecidableEq, Inhabited

/-! ## Fault and Authentication Axes -/

/-- Fault model for the protocol participants. -/
inductive FaultModel where
  | crash
  | byzantine
  deriving Repr, DecidableEq, Inhabited

/-- Adversary adaptation model. -/
inductive AdversaryKind where
  | static
  | adaptive
  deriving Repr, DecidableEq, Inhabited

/-- Authentication capability assumed by the model. -/
inductive AuthenticationModel where
  | none
  | oral
  | signatures
  deriving Repr, DecidableEq, Inhabited

/-- Policy under partition pressure (CAP posture). -/
inductive PartitionPolicy where
  | safetyFirst
  | livenessFirst
  | adaptive
  deriving Repr, DecidableEq, Inhabited

/-! ## Protocol Specification Record -/

/-- Coarse protocol specification for hypothesis validation. -/
structure ProtocolSpec where
  /-- Number of participants (or committee size). -/
  n : Nat
  /-- Fault budget used by the protocol model. -/
  f : Nat
  timing : TimingModel
  evidenceAccumulation : EvidenceAccumulationModel
  conflictExclusionLaw : ConflictExclusionLaw
  finalizationWitnessRule : FinalizationWitnessRule
  /-- Whether finality witnesses are monotone under allowed extensions. -/
  witnessMonotonicity : Bool := false
  /-- Coarse/derived presentation-layer certificate tag. -/
  certificate : CertificateModel
  /-- Quorum threshold (used for quorum/hybrid checks). -/
  quorumSize : Nat := 0
  authentication : AuthenticationModel := .none
  faultModel : FaultModel := .byzantine
  adversaryKind : AdversaryKind := .static
  partitionPolicy : PartitionPolicy := .adaptive
  /-- Deterministic finality flag (checkpoint/commit style). -/
  deterministicFinality : Bool := false
  /-- Probabilistic finality flag (confirmation-depth style). -/
  probabilisticFinality : Bool := false
  /-- Whether protocol has a responsive fast path in its model. -/
  responsivePath : Bool := false
  /-- Adversarial work/stake share in permille [0, 1000]. -/
  adversarialWeightPermille : Nat := 0
  /-- Whether the model declares logical-time semantics (`t_logical`, `T_logical`). -/
  logicalTimeSemanticsDeclared : Bool := false
  /-- Whether at least one order parameter is explicitly declared. -/
  orderParameterDeclared : Bool := false
  /-- Whether explicit phase-boundary functions are declared. -/
  phaseBoundaryModelDeclared : Bool := false
  /-- Whether interactive distance (`d_int`) is explicitly declared. -/
  interactiveDistanceDeclared : Bool := false
  /-- Whether a universality-class claim is explicitly declared. -/
  universalityClassDeclared : Bool := false
  /-- Whether class claims are tagged as heuristic/confidence-scoped. -/
  classificationHeuristicTagged : Bool := false
  /-- Whether threshold regime assumptions are explicitly declared. -/
  thresholdRegimeDeclared : Bool := false
  /-- Whether timing/authentication compatibility assumptions are explicit. -/
  timingAuthContractDeclared : Bool := false
  /-- Whether quorum intersection obligations are explicitly witnessed. -/
  quorumIntersectionWitnessed : Bool := false
  /-- For hybrid systems: whether finalized-prefix <= available-prefix is witnessed. -/
  hybridFrontInvariantHolds : Bool := false
  /-- Whether a classical-transport assumption profile has been declared. -/
  classicalTransportProfileDeclared : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-! ## Coarse Protocol Spaces -/

/-- Coarse protocol-space classification. -/
inductive ProtocolSpace where
  | bft
  | nakamoto
  | hybrid
  | outside
  deriving Repr, DecidableEq, Inhabited

end Distributed
