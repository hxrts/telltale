import Consensus.Types

set_option autoImplicit false

/-! # Consensus.Classifier

Coarse protocol-space checks and classification.
-/

namespace Consensus

/-- Generic well-formedness checks for protocol specs. -/
def basicWellFormed (p : ProtocolSpec) : Bool :=
  0 < p.n &&
  p.f < p.n &&
  p.adversarialWeightPermille <= 1000

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

/-- Heuristic classifier for BFT protocol space. -/
def inBFTSpace (p : ProtocolSpec) : Bool :=
  basicWellFormed p &&
  p.faultModel = .byzantine &&
  (p.certificate = .quorum || p.certificate = .hybrid) &&
  p.authentication ≠ .none &&
  bftThresholdOk p &&
  quorumSane p

/-- Heuristic classifier for Nakamoto-style protocol space. -/
def inNakamotoSpace (p : ProtocolSpec) : Bool :=
  basicWellFormed p &&
  p.certificate = .work &&
  p.faultModel = .byzantine &&
  p.probabilisticFinality &&
  p.adversarialWeightPermille < 500

/-- Heuristic classifier for coupled hybrid protocols. -/
def inHybridSpace (p : ProtocolSpec) : Bool :=
  basicWellFormed p &&
  p.certificate = .hybrid &&
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
  (inBFTSpace p || inNakamotoSpace p || inHybridSpace p)

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

end Consensus
