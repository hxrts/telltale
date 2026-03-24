set_option autoImplicit false

namespace Runtime.ProtocolMachine.Model

inductive EffectAuthorityClass where
  | authoritative
  | command
  | observe
  deriving Repr, DecidableEq

inductive EffectSemanticClass where
  | authoritative
  | observational
  | bestEffort
  deriving Repr, DecidableEq

inductive EffectAdmissibility where
  | always
  | declaredUseOnly
  | internalOnly
  deriving Repr, DecidableEq

inductive EffectTotality where
  | mustTerminate
  | mayBlock
  deriving Repr, DecidableEq

inductive EffectTimeoutPolicy where
  | none
  | inheritOperationBudget
  | required (budgetTicks : Option Nat)
  deriving Repr, DecidableEq

inductive EffectReentrancyPolicy where
  | allow
  | rejectSameOperation
  | rejectSameFragment
  deriving Repr, DecidableEq

inductive EffectRetryShape where
  | forbidden
  | bounded (maxRetries : Nat)
  | untilTimeout
  deriving Repr, DecidableEq

inductive EffectHandlerDomain where
  | internal
  | external
  deriving Repr, DecidableEq

structure EffectResponsibilityDomain where
  footprintKey : String
  operationId : Option String := none
  fragmentId : Option String := none
  ownerId : Option String := none
  deriving Repr, DecidableEq

def EffectTimeoutPolicy.requiresExplicitTimeout : EffectTimeoutPolicy → Prop
  | .required _ => True
  | .none | .inheritOperationBudget => False

def EffectRetryShape.hasExplicitRule : EffectRetryShape → Prop
  | .forbidden => False
  | .bounded _ | .untilTimeout => True

def EffectResponsibilityDomain.sameSemanticFootprint
    (left right : EffectResponsibilityDomain) : Prop :=
  left.footprintKey = right.footprintKey

def EffectResponsibilityDomain.sameOperation
    (left right : EffectResponsibilityDomain) : Prop :=
  left.operationId.isSome ∧ left.operationId = right.operationId

def EffectResponsibilityDomain.sameFragment
    (left right : EffectResponsibilityDomain) : Prop :=
  left.fragmentId.isSome ∧ left.fragmentId = right.fragmentId

def EffectReentrancyPolicy.admits
    (policy : EffectReentrancyPolicy)
    (active incoming : EffectResponsibilityDomain) : Prop :=
  match policy with
  | .allow => True
  | .rejectSameOperation =>
      ¬ EffectResponsibilityDomain.sameOperation active incoming
  | .rejectSameFragment =>
      ¬ EffectResponsibilityDomain.sameSemanticFootprint active incoming

structure EffectInterfaceMetadata where
  interfaceName : String
  operationName : String
  authorityClass : EffectAuthorityClass
  semanticClass : EffectSemanticClass
  admissibility : EffectAdmissibility
  totality : EffectTotality
  timeoutPolicy : EffectTimeoutPolicy
  retryShape : EffectRetryShape
  reentrancyPolicy : EffectReentrancyPolicy
  handlerDomain : EffectHandlerDomain
  deriving Repr, DecidableEq

def EffectInterfaceMetadata.timeoutRequired
    (metadata : EffectInterfaceMetadata) : Prop :=
  metadata.timeoutPolicy.requiresExplicitTimeout

def EffectInterfaceMetadata.hasExplicitRetryRule
    (metadata : EffectInterfaceMetadata) : Prop :=
  metadata.retryShape.hasExplicitRule

def EffectInterfaceMetadata.architecturallyLegal
    (metadata : EffectInterfaceMetadata) : Prop :=
  (metadata.semanticClass = .observational →
      metadata.authorityClass ≠ .authoritative) ∧
  (metadata.semanticClass = .bestEffort →
      metadata.authorityClass ≠ .authoritative) ∧
  (metadata.totality = .mayBlock → metadata.timeoutRequired) ∧
  (metadata.hasExplicitRetryRule → metadata.timeoutRequired) ∧
  (metadata.admissibility = .internalOnly →
      metadata.handlerDomain = .internal)

def EffectInterfaceMetadata.architecturallyIllegal
    (metadata : EffectInterfaceMetadata) : Prop :=
  ¬ metadata.architecturallyLegal

def EffectInterfaceMetadata.reentrancyAdmissible
    (metadata : EffectInterfaceMetadata)
    (active incoming : EffectResponsibilityDomain) : Prop :=
  metadata.architecturallyLegal ∧
  metadata.reentrancyPolicy.admits active incoming

inductive EffectRequestBody where
  | sendDecision (role partner label : String) (state : List String) (payload : Option String)
  | receive (role partner label : String) (state : List String) (payload : String)
  | choose (role partner : String) (labels state : List String)
  | invokeStep (role : String) (state : List String)
  | acquire (role layer : String) (state : List String)
  | release (role layer evidence : String) (state : List String)
  | topologyEvents (tick : Nat)
  | outputConditionHint (role : String) (state : List String)
  deriving Repr, DecidableEq

structure EffectRequest where
  effectId : Option Nat
  tick : Nat
  session : Option Nat
  operationId : Option String
  metadata : EffectInterfaceMetadata
  body : EffectRequestBody
  deriving Repr, DecidableEq

def EffectRequest.architecturallyLegal (request : EffectRequest) : Prop :=
  request.metadata.architecturallyLegal

def EffectRequest.reentrancyAdmissible
    (request : EffectRequest)
    (active incoming : EffectResponsibilityDomain) : Prop :=
  request.metadata.reentrancyAdmissible active incoming

inductive EffectOutcomeStatus where
  | success
  | blocked
  | failure (kind message : String)
  deriving Repr, DecidableEq

inductive EffectResponse where
  | sendDecision (decision : String)
  | receive (state : List String)
  | choose (label : String)
  | invokeStep (state : List String)
  | acquire (evidence : String)
  | release
  | topologyEvents (events : List String)
  | outputConditionHint (hint : Option String)
  deriving Repr, DecidableEq

structure EffectOutcome where
  status : EffectOutcomeStatus
  response : Option EffectResponse
  deriving Repr, DecidableEq

structure EffectExchangeRecord where
  effectId : Nat
  handlerIdentity : String
  orderingKey : Nat
  request : EffectRequest
  outcome : EffectOutcome
  deriving Repr, DecidableEq

end Runtime.ProtocolMachine.Model
