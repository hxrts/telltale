set_option autoImplicit false

namespace Runtime.VM.Model

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

inductive ProgressState where
  | pending
  | blocked
  | succeeded
  | failed
  | cancelled
  | timedOut
  | handedOff
  deriving Repr, DecidableEq

inductive OwnershipScope where
  | session
  | fragments (roles : List String)
  deriving Repr, DecidableEq

inductive DelegationStatus where
  | committed
  | rolledBack
  deriving Repr, DecidableEq

structure OperationInstance where
  operationId : String
  session : Option Nat
  ownerId : Option String
  kind : String
  phase : OperationPhase
  handlerIdentity : Option String
  effectIds : List Nat
  deriving Repr, DecidableEq

structure OutstandingEffect where
  effectId : Nat
  operationId : String
  session : Option Nat
  effectInterface : Option String
  effectOperation : Option String
  effectKind : String
  handlerIdentity : String
  status : OutstandingEffectStatus
  orderingKey : Nat
  inputs : String
  outputs : String
  deriving Repr, DecidableEq

structure SemanticHandoff where
  handoffId : Nat
  session : Nat
  fromCoro : Nat
  toCoro : Nat
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

structure ProgressContract where
  operationId : String
  session : Option Nat
  state : ProgressState
  lastOrderingKey : Option Nat
  bounded : Bool
  deriving Repr, DecidableEq

structure ProtocolMachineSemanticObjects where
  operationInstances : List OperationInstance
  outstandingEffects : List OutstandingEffect
  semanticHandoffs : List SemanticHandoff
  authoritativeReads : List AuthoritativeRead
  observedReads : List ObservedRead
  materializationProofs : List MaterializationProof
  canonicalHandles : List CanonicalHandle
  progressContracts : List ProgressContract
  deriving Repr, DecidableEq

end Runtime.VM.Model
