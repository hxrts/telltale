set_option autoImplicit false

namespace Runtime.VM.Model

inductive EffectAuthorityClass where
  | authoritative
  | command
  | observe
  deriving Repr, DecidableEq

inductive EffectAdmissibility where
  | always
  | declaredUseOnly
  | internalOnly
  deriving Repr, DecidableEq

inductive EffectTotality where
  | immediate
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

inductive EffectHandlerDomain where
  | internal
  | external
  deriving Repr, DecidableEq

structure EffectInterfaceMetadata where
  interfaceName : String
  operationName : String
  authorityClass : EffectAuthorityClass
  admissibility : EffectAdmissibility
  totality : EffectTotality
  timeoutPolicy : EffectTimeoutPolicy
  reentrancyPolicy : EffectReentrancyPolicy
  handlerDomain : EffectHandlerDomain
  deriving Repr, DecidableEq

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

end Runtime.VM.Model
