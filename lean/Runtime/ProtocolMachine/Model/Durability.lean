import Runtime.ProtocolMachine.Model.Effects
import Runtime.ProtocolMachine.Model.SemanticObjects.AgreementCore

set_option autoImplicit false

namespace Runtime.ProtocolMachine.Model

/-- Canonical Lean mirror of the internal `wal_sync` effect metadata. -/
def walSyncMetadata : EffectInterfaceMetadata :=
  { interfaceName := "Wal"
  , operationName := "sync"
  , authorityClass := .authoritative
  , semanticClass := .authoritative
  , admissibility := .internalOnly
  , totality := .mayBlock
  , timeoutPolicy := .required none
  , retryShape := .bounded 3
  , reentrancyPolicy := .rejectSameFragment
  , handlerDomain := .internal
  }

/-- Lean mirror of the Rust durable recovery action vocabulary. -/
inductive DurableRecoveryAction where
  | reexecuteFromScratch
  | resumeFromEvidenceBoundary
  | reuseFinalized
  | preserveTerminal
  deriving Repr, DecidableEq

/-- Lean mirror of one typed durable recovery decision. -/
structure DurableRecoveryDecision where
  operationId : String
  checkpointLevel : AgreementLevel
  recoveredLevel : AgreementLevel
  gateLevel : AgreementLevel
  gateCrossed : Bool
  finalization : Option FinalizationOutcome := none
  action : DurableRecoveryAction
  deriving Repr, DecidableEq

/-- Soundness predicate for one durable recovery decision. -/
def DurableRecoveryDecision.sound (decision : DurableRecoveryDecision) : Prop :=
  decision.checkpointLevel.rank ≤ decision.recoveredLevel.rank ∧
  (decision.gateCrossed = true →
      decision.recoveredLevel.atLeast decision.gateLevel) ∧
  (decision.action = .reuseFinalized →
      decision.recoveredLevel = .finalized ∧
      decision.finalization = some .finalized) ∧
  (decision.action = .preserveTerminal →
      decision.finalization = some .aborted ∨
      decision.finalization = some .rejected ∨
      decision.finalization = some .timedOut)

end Runtime.ProtocolMachine.Model
