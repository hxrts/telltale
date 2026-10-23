import Runtime.ProtocolMachine.Model.SemanticObjects.Core
import Protocol.Values

set_option autoImplicit false

namespace Runtime.ProtocolMachine.Model

-- Retained result equality compares the original error or success constructor.
deriving instance DecidableEq for Except

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

/-- Serializable nominal descriptors are observations, not issued session owners. -/
structure NominalCommandDeclaration where
  interfaceName : String
  operationName : String
  mayBlock : Bool
  readinessPredicate : Option String := none
  deriving Repr, DecidableEq

def NominalCommandDeclaration.readinessWellFormed (declaration : NominalCommandDeclaration) : Bool :=
  match declaration.readinessPredicate with
  | none => true
  | some predicate => predicate == declaration.interfaceName ++ "." ++ declaration.operationName && declaration.mayBlock

/-- Static call operands. Neither a descriptor nor its serialization issues authority. -/
structure NominalCommandCall where
  declaration : NominalCommandDeclaration
  enclosingOperation : String
  agreementProfile : AgreementProfile
  role : String
  progressContract : String
  progressWindow : String
  budgetTicks : Nat
  result : Nat
  onOk : Nat
  onErr : Nat
  deriving Repr, DecidableEq

/-- A Boolean application result is never readiness authority. -/
inductive NominalCommandValue where
  | bool (value : Bool)
  | readiness (witness : SessionTypes.ReadinessWitness)
  deriving Repr, DecidableEq

instance : Coe Bool NominalCommandValue := ⟨NominalCommandValue.bool⟩

def NominalCommandValue.toValue : NominalCommandValue → Value
  | .bool value => .bool value
  | .readiness witness => .readiness witness

def NominalCommandValue.matchesDeclaration (value : NominalCommandValue)
    (declaration : NominalCommandDeclaration) : Bool :=
  match value, declaration.readinessPredicate with
  | .bool _, none => true
  | .readiness witness, some predicate => declaration.readinessWellFormed && witness.predicateRef == predicate
  | _, _ => false

/-- Original protocol occurrence, retained on the canonical coroutine.
Rust additionally retains its issued host owner; that runtime-only custody is
not reconstructed or proved by this protocol-model record. -/
structure NominalCommandContinuation where
  invocation : Nat
  coroutine : Nat
  pc : Nat
  call : NominalCommandCall
  issuedAt : Nat
  returned : Option (Except String NominalCommandValue)
  handlerIdentity : String
  /-- Original admitted model owner; returned witness fields cannot supply it. -/
  originalOwner : Option SessionTypes.ModelOwner := none
  /-- Independent semantic validation refusal, never a native error owner. -/
  validationFailure : Option (String × String) := none
  deriving Repr, DecidableEq

def NominalCommandContinuation.withinOriginalWindowAt
    (original : NominalCommandContinuation) (tick : Nat) : Bool :=
  decide (tick ≤ original.issuedAt + original.call.budgetTicks)

structure NominalCommandRequest where
  invocation : Nat
  session : Nat
  coroutine : Nat
  declaration : NominalCommandDeclaration
  role : String
  deriving Repr, DecidableEq

structure NominalCommandReply where
  invocation : Nat
  result : Except String NominalCommandValue
  deriving Repr, DecidableEq

inductive EffectRequestBody where
  | sendDecision (role partner label : String) (state : List String) (payload : Option String)
  | receive (role partner label : String) (state : List String) (payload : String)
  | choose (role partner : String) (labels state : List String)
  | invokeStep (role : String) (state : List String)
  | nominalCommand (request : NominalCommandRequest)
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
  | nominalCommand (reply : NominalCommandReply)
  | acquire (evidence : String)
  | release
  | topologyEvents (events : List String)
  | outputConditionHint (hint : Option String)
  deriving Repr, DecidableEq

structure EffectOutcome where
  status : EffectOutcomeStatus
  response : Option EffectResponse
  deriving Repr, DecidableEq

/-! Typed acceptance is distinct from retaining an untrusted raw exchange.
This adapter does not yet connect abstract EffectRuntime.exec to typed outcomes. -/
inductive EffectResponseKind where
  | sendDecision | receive | choose | invokeStep | nominalCommand | acquire | release
  | topologyEvents | outputConditionHint
  deriving Repr, DecidableEq, BEq

def EffectRequestBody.responseKind : EffectRequestBody → EffectResponseKind
  | .sendDecision _ _ _ _ _ => .sendDecision
  | .receive _ _ _ _ _ => .receive
  | .choose _ _ _ _ => .choose
  | .invokeStep _ _ => .invokeStep
  | .nominalCommand _ => .nominalCommand
  | .acquire _ _ _ => .acquire
  | .release _ _ _ _ => .release
  | .topologyEvents _ => .topologyEvents
  | .outputConditionHint _ _ => .outputConditionHint

def EffectResponse.responseKind : EffectResponse → EffectResponseKind
  | .sendDecision _ => .sendDecision
  | .receive _ => .receive
  | .choose _ => .choose
  | .invokeStep _ => .invokeStep
  | .nominalCommand _ => .nominalCommand
  | .acquire _ => .acquire
  | .release => .release
  | .topologyEvents _ => .topologyEvents
  | .outputConditionHint _ => .outputConditionHint

def EffectOutcome.acceptedStatusFor (outcome : EffectOutcome)
    (request : EffectRequestBody) : EffectOutcomeStatus :=
  match outcome.status, outcome.response with
  | .success, some response =>
      match request, response with
      | .nominalCommand original, .nominalCommand reply =>
          if original.invocation == reply.invocation then
            match reply.result with
            | .error _ => .success
            | .ok value => if value.matchesDeclaration original.declaration then .success
                else .failure "contract_violation" "nominal result does not match its declared readiness predicate/type"
          else .failure "contract_violation" "nominal reply belongs to a different invocation"
      | _, _ =>
          if request.responseKind == response.responseKind then .success
          else .failure "contract_violation" "effect response kind does not match the original request"
  | .success, none => .failure "contract_violation" "successful effect outcome is missing response"
  | status, _ => status

def EffectOutcome.invokeStepState (outcome : EffectOutcome) : Option (List String) :=
  match outcome.status, outcome.response with
  | .success, some (.invokeStep state) => some state
  | _, _ => none

structure EffectExchangeRecord where
  effectId : Nat
  handlerIdentity : String
  orderingKey : Nat
  request : EffectRequest
  outcome : EffectOutcome
  /-- Actual callback observation tick, distinct from the original window key. -/
  observedAt : Option Nat := none
  deriving Repr, DecidableEq

end Runtime.ProtocolMachine.Model
