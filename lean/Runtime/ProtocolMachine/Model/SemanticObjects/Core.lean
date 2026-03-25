set_option autoImplicit false

/-!
# Runtime.ProtocolMachine.Model.SemanticObjects.Core

The Problem.
The protocol-machine architecture needs first-class semantic objects for
operation identity, outstanding effects, handoff, publication, and progress.
Those objects must be readable as an implementation surface in their own right,
without requiring theorem files to understand the executable data model.

Solution Structure.
This module defines the canonical semantic-object datatypes that mirror the Rust
implementation vocabulary. The companion `Discipline` module states semantic
predicates over these objects, and proof theorems over that discipline live
under `Runtime/Proofs/ProtocolMachine/`.
-/

namespace Runtime.ProtocolMachine.Model

/-! ## Phase and Status Enums -/

inductive OperationPhase where
  | pending
  | blocked
  | succeeded
  | failed
  | cancelled
  | timedOut
  | handedOff
  deriving Repr, DecidableEq

inductive OutstandingEffectStatus where
  | pending
  | blocked
  | succeeded
  | failed
  | cancelled
  | invalidated
  deriving Repr, DecidableEq

inductive AuthoritativeReadKind where
  | readiness
  | cancellation
  | timeout
  | outputCondition
  deriving Repr, DecidableEq

inductive AuthoritativeReadLifecycle where
  | issued
  | consumed
  | rejected
  | verified
  deriving Repr, DecidableEq

inductive CanonicalHandleKind where
  | materialization
  | handoff
  deriving Repr, DecidableEq

inductive PublicationObserverClass where
  | canonical
  | audit
  deriving Repr, DecidableEq

inductive PublicationStatus where
  | published
  | rejected
  deriving Repr, DecidableEq

inductive ProgressState where
  | pending
  | blocked
  | noProgress
  | degraded
  | succeeded
  | failed
  | cancelled
  | timedOut
  | handedOff
  deriving Repr, DecidableEq

inductive OperationVisibility where
  | immediate
  | pending
  | blockedUntilFinalized
  deriving Repr, DecidableEq

inductive AgreementLevel where
  | none
  | provisional
  | softSafe
  | finalized
  deriving Repr, DecidableEq

inductive AgreementRule where
  | noAgreement
  | anyParticipant
  | unanimous
  | threshold (requiredParticipants : Nat)
  | named (ruleName : String)
  deriving Repr, DecidableEq

inductive AgreementEvidenceKind where
  | witness
  | certificate
  | commitFact
  | publication
  | materialization
  deriving Repr, DecidableEq

inductive FinalizationOutcome where
  | finalized
  | aborted
  | rejected
  | timedOut
  deriving Repr, DecidableEq

inductive OwnershipScope where
  | session
  | fragments (roles : List String)
  deriving Repr, DecidableEq

inductive DelegationStatus where
  | committed
  | rolledBack
  deriving Repr, DecidableEq

/-! ## Core Semantic Objects -/

structure OperationInstance where
  operationId : String
  session : Option Nat
  ownerId : Option String
  kind : String
  phase : OperationPhase
  handlerIdentity : Option String
  effectIds : List Nat
  dependentOperationIds : List String
  terminalPublication : Option String
  budgetTicks : Option Nat
  requiresProof : Bool
  deriving Repr, DecidableEq

structure OutstandingEffect where
  effectId : Nat
  operationId : String
  session : Option Nat
  ownerId : Option String
  effectInterface : Option String
  effectOperation : Option String
  effectKind : String
  handlerIdentity : String
  status : OutstandingEffectStatus
  orderingKey : Nat
  budgetTicks : Option Nat
  retryPolicy : String
  invalidationToken : String
  completedAtTick : Option Nat
  inputs : String
  outputs : String
  deriving Repr, DecidableEq

structure SemanticHandoff where
  handoffId : Nat
  session : Nat
  fromCoro : Nat
  toCoro : Nat
  revokedOwnerId : String
  activatedOwnerId : String
  scope : OwnershipScope
  status : DelegationStatus
  tick : Nat
  reason : Option String
  deriving Repr, DecidableEq

structure TransformationObligation where
  obligationId : String
  handoffId : Nat
  session : Nat
  transformedFragments : List String
  affectedOperationIds : List String
  affectedEffectIds : List Nat
  transportedEffectIds : List Nat
  invalidatedEffectIds : List Nat
  witnessPolicy : String
  publicationRevokedFrom : String
  publicationActivatedTo : String
  scope : OwnershipScope
  status : DelegationStatus
  tick : Nat
  reason : Option String
  deriving Repr, DecidableEq

structure AuthoritativeRead where
  readId : String
  session : Option Nat
  ownerId : Option String
  kind : AuthoritativeReadKind
  lifecycle : AuthoritativeReadLifecycle
  predicateRef : Option String
  witnessId : Option Nat
  generation : Option Nat
  reason : Option String
  deriving Repr, DecidableEq

structure ObservedRead where
  readId : String
  session : Option Nat
  effectId : Nat
  effectInterface : Option String
  effectOperation : Option String
  handlerIdentity : String
  status : OutstandingEffectStatus
  deriving Repr, DecidableEq

structure MaterializationProof where
  proofId : String
  session : Option Nat
  predicateRef : String
  witnessRef : Option String
  outputDigest : String
  passed : Bool
  deriving Repr, DecidableEq

structure CanonicalHandle where
  handleId : String
  session : Option Nat
  ownerId : Option String
  kind : CanonicalHandleKind
  proofRef : Option String
  deriving Repr, DecidableEq

structure PublicationEvent where
  publicationId : String
  session : Option Nat
  operationId : String
  ownerId : Option String
  publication : String
  observerClass : PublicationObserverClass
  status : PublicationStatus
  proofRef : Option String
  handleRef : Option String
  reason : Option String
  deriving Repr, DecidableEq

structure PrestateBinding where
  bindingId : String
  operationId : String
  session : Option Nat
  stateDigest : String
  epochRef : Option String
  participantDigest : Option String
  deriving Repr, DecidableEq

structure AgreementProfile where
  profileName : String
  visibility : OperationVisibility
  rule : AgreementRule
  usableAt : AgreementLevel
  finalizedAt : AgreementLevel
  requiredEvidenceKind : AgreementEvidenceKind
  deriving Repr, DecidableEq

structure AgreementContract where
  contractName : String
  operationId : String
  session : Option Nat
  ownerId : Option String
  profileName : Option String
  visibility : OperationVisibility
  rule : AgreementRule
  usableAt : AgreementLevel
  finalizedAt : AgreementLevel
  requiredEvidenceKind : AgreementEvidenceKind
  deriving Repr, DecidableEq

structure AgreementEvidence where
  evidenceId : String
  operationId : String
  session : Option Nat
  ownerId : Option String
  level : AgreementLevel
  kind : AgreementEvidenceKind
  reference : String
  authoritative : Bool
  deriving Repr, DecidableEq

structure AgreementState where
  operationId : String
  session : Option Nat
  ownerId : Option String
  contractName : String
  level : AgreementLevel
  finalization : Option FinalizationOutcome
  evidenceIds : List String
  lastUpdatedTick : Option Nat
  reason : Option String
  deriving Repr, DecidableEq

structure Region where
  regionId : String
  session : Option Nat
  ownerId : Option String
  scope : OwnershipScope
  operationIds : List String
  effectIds : List Nat
  authoritativeReadIds : List String
  handleIds : List String
  publicationIds : List String
  deriving Repr, DecidableEq

structure ProgressContract where
  operationId : String
  session : Option Nat
  state : ProgressState
  lastOrderingKey : Option Nat
  bounded : Bool
  budgetTicks : Option Nat
  lastProgressTick : Option Nat
  escalatedAtTick : Option Nat
  reason : Option String
  deriving Repr, DecidableEq

structure ProgressTransition where
  operationId : String
  session : Option Nat
  fromState : ProgressState
  toState : ProgressState
  tick : Nat
  reason : Option String
  deriving Repr, DecidableEq

structure ProtocolMachineSemanticObjects where
  operationInstances : List OperationInstance
  outstandingEffects : List OutstandingEffect
  semanticHandoffs : List SemanticHandoff
  transformationObligations : List TransformationObligation
  authoritativeReads : List AuthoritativeRead
  observedReads : List ObservedRead
  materializationProofs : List MaterializationProof
  canonicalHandles : List CanonicalHandle
  publicationEvents : List PublicationEvent
  prestateBindings : List PrestateBinding
  agreementProfiles : List AgreementProfile
  agreementContracts : List AgreementContract
  agreementEvidence : List AgreementEvidence
  agreementStates : List AgreementState
  regions : List Region
  progressContracts : List ProgressContract
  progressTransitions : List ProgressTransition
  deriving Repr, DecidableEq

end Runtime.ProtocolMachine.Model
