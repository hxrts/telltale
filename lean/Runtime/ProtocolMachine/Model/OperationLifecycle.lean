import Runtime.ProtocolMachine.Model.Effects
import Protocol.Values

/-! Source operations own an enclosing occurrence independently of their child
host effects. This state belongs to the canonical coroutine. ModelOwner is
protocol-model authority admitted in the same session state, not a serialized
Rust host capability or evidence of physical host cleanup. -/
set_option autoImplicit false
namespace Runtime.ProtocolMachine.Model

structure DeclaredOperationChild where
  pc : Nat
  call : NominalCommandCall
  deriving Repr, DecidableEq

structure SourceOperationDeclaration where
  name : String
  role : String
  agreementProfile : AgreementProfile
  progressContract : String
  progressWindow : String
  budgetTicks : Nat
  requiresProof : Bool
  requiredChildren : List DeclaredOperationChild := []
  deriving Repr, DecidableEq

def SourceOperationDeclaration.supported (declaration : SourceOperationDeclaration) : Bool :=
  decide (declaration.name ≠ "" ∧ declaration.role ≠ "" ∧
    declaration.progressContract ≠ "" ∧ declaration.progressWindow ≠ "" ∧
    declaration.budgetTicks > 0 ∧ declaration.requiresProof = true ∧
    declaration.agreementProfile.profileName ≠ "" ∧
    declaration.agreementProfile.visibility = .immediate ∧
    declaration.agreementProfile.rule = .noAgreement ∧
    declaration.agreementProfile.usableAt = .none ∧
    declaration.agreementProfile.finalizedAt = .none ∧
    declaration.agreementProfile.requiredEvidenceKind = .witness)

inductive SourceOperationResolution where
  | success (register : Option Nat)
  | failure (register : Option Nat)
  | timeout (register : Option Nat)
  | cancelled
  deriving Repr, DecidableEq

inductive SourceOperationOutcome where
  | success (value : Option Value)
  | failure (value : Option Value)
  | timeout (value : Option Value)
  | cancelled
  deriving Repr, DecidableEq

inductive OperationAction where
  | begin (declaration : SourceOperationDeclaration)
  | await (operation : String)
  | resolve (operation : String) (resolution : SourceOperationResolution)
  | invalidate (operation : String)
  /-- A product action cannot silently execute one component and erase another. -/
  | unsupportedComposition
  deriving Repr, DecidableEq

structure OriginalOperationContinuation where
  owner : SessionTypes.ModelOwner
  declaration : SourceOperationDeclaration
  operationId : String
  issuedAt : Nat
  originalPc : Nat
  children : List Nat := []
  admittedSlots : List Nat := []
  outcome : Option SourceOperationOutcome := none
  resolved : Bool := false
  completedChildren : List (Nat × EffectOutcome) := []
  invalidated : Bool := false
  /-- Semantic refusal only; never a host teardown acknowledgment. -/
  validationFailure : Option String := none
  deriving Repr, DecidableEq

namespace OriginalOperationContinuation

def withinOriginalWindowAt (original : OriginalOperationContinuation) (tick : Nat) : Bool :=
  decide (tick ≤ original.issuedAt + original.declaration.budgetTicks)

def begin (owner : SessionTypes.ModelOwner) (declaration : SourceOperationDeclaration)
    (coroutine pc tick : Nat) :
    OriginalOperationContinuation × OperationInstance × ProgressContract :=
  let id := s!"operation:{owner.sessionId}:{coroutine}:{pc}:{tick}"
  let original : OriginalOperationContinuation :=
    { owner, declaration, operationId := id, issuedAt := tick, originalPc := pc }
  let record : OperationInstance :=
    { agreementProfile := some declaration.agreementProfile, operationId := id,
      session := some owner.sessionId, ownerId := some owner.ownerId, kind := declaration.name,
      phase := .pending, handlerIdentity := none, effectIds := [], dependentOperationIds := [],
      terminalPublication := none, budgetTicks := some declaration.budgetTicks,
      requiresProof := declaration.requiresProof }
  let progress : ProgressContract :=
    { operationId := id, session := some owner.sessionId, state := .pending,
      lastOrderingKey := some tick, bounded := true, budgetTicks := some declaration.budgetTicks,
      lastProgressTick := some tick, escalatedAtTick := none, reason := none }
  (original, record, progress)

def identityValid (original : OriginalOperationContinuation)
    (authority : SessionTypes.ModelOwnershipState) (record : OperationInstance)
    (progress : ProgressContract) : Bool :=
  authority.admits original.owner && !original.resolved && !original.invalidated &&
    decide (record.operationId = original.operationId ∧
      record.session = some original.owner.sessionId ∧ record.ownerId = some original.owner.ownerId ∧
      record.kind = original.declaration.name ∧
      record.agreementProfile = some original.declaration.agreementProfile ∧
      record.budgetTicks = some original.declaration.budgetTicks ∧
      record.requiresProof = original.declaration.requiresProof ∧ record.effectIds = original.children ∧
      (record.phase = .pending ∨ record.phase = .blocked) ∧
      progress.operationId = original.operationId ∧ progress.session = record.session ∧
      progress.budgetTicks = some original.declaration.budgetTicks ∧
      progress.lastOrderingKey = some original.issuedAt)

def admissibleAt (original : OriginalOperationContinuation)
    (authority : SessionTypes.ModelOwnershipState) (record : OperationInstance)
    (progress : ProgressContract) (tick : Nat) : Bool :=
  original.identityValid authority record progress && original.withinOriginalWindowAt tick &&
    original.validationFailure.isNone

/-- Static slot identity does not issue authority: the caller also validates
same-session owner/current original continuation before admitting this child. -/
def admitChild (original : OriginalOperationContinuation) (pc : Nat)
    (call : NominalCommandCall) (child : OutstandingEffect) :
    Except String OriginalOperationContinuation :=
  if !(original.declaration.requiredChildren.any (fun slot => decide (slot = ⟨pc, call⟩))) ||
      original.admittedSlots.contains pc || original.children.contains child.effectId then
    .error "source child is absent, changed or already admitted"
  else if child.session != some original.owner.sessionId ||
      child.ownerId != some original.owner.ownerId ||
      !(child.status == .pending || child.status == .blocked) then
    .error "source child does not belong to the original admitted owner"
  else .ok { original with
    children := original.children ++ [child.effectId],
    admittedSlots := original.admittedSlots ++ [pc] }

def retainChildOutcome (original : OriginalOperationContinuation) (id : Nat)
    (outcome : EffectOutcome) : Except String OriginalOperationContinuation :=
  if !original.children.contains id then .error "outcome has no original admitted child"
  else if original.completedChildren.any (fun entry => entry.1 == id) then
    .error "original child outcome already retained"
  else match outcome.status with
    | .blocked => .error "nonterminal child outcome cannot complete original child"
    | _ => .ok { original with completedChildren := original.completedChildren ++ [(id, outcome)] }

inductive AwaitResult where
  | pending
  | ready
  | failed (kind message : String)
  deriving Repr, DecidableEq

private def observeChild (original : OriginalOperationContinuation)
    (effects : List OutstandingEffect) (id : Nat) : Except String AwaitResult := do
  let matches := effects.filter (fun effect => effect.effectId == id)
  let child ← match matches with
    | [child] => .ok child
    | _ => .error "original admitted child missing or ambiguous"
  if child.session != some original.owner.sessionId || child.ownerId != some original.owner.ownerId then
    .error "original admitted child owner changed"
  else match child.status with
    | .pending | .blocked => .ok .pending
    | .succeeded =>
      match original.completedChildren.find? (fun entry => entry.1 == id) with
      | some (_, outcome) => match outcome.status with
        | .success => .ok .ready
        | _ => .error "successful child record has no successful original outcome"
      | none => .error "terminal child has no retained original outcome"
    | _ =>
      match original.completedChildren.find? (fun entry => entry.1 == id) with
      | some (_, outcome) => match outcome.status with
        | .failure kind message => .ok (.failed kind message)
        | _ => .error "unsuccessful child has no retained original failure"
      | none => .error "unsuccessful child has no retained original outcome"

def observeChildren (original : OriginalOperationContinuation)
    (effects : List OutstandingEffect) : Except String AwaitResult := do
  if original.declaration.requiredChildren.length != original.admittedSlots.length ||
      original.declaration.requiredChildren.any (fun slot => !original.admittedSlots.contains slot.pc) then
    .error "required source child never admitted"
  else
    let observations ← original.children.mapM (observeChild original effects)
    if observations.any (fun observation => decide (observation = .pending)) then .ok .pending
    else match observations.find? (fun observation => match observation with
        | .failed _ _ => true | _ => false) with
      | some failure => .ok failure
      | none => .ok .ready

/-- Resolve only terminalizes the application operation observation. It does not
issue a readiness witness, canonical publication, or materialization handle. -/
def resolutionPhase : SourceOperationOutcome → OperationPhase
  | .success _ => .succeeded
  | .failure _ => .failed
  | .timeout _ => .timedOut
  | .cancelled => .cancelled

end OriginalOperationContinuation
end Runtime.ProtocolMachine.Model

namespace Runtime.ProtocolMachine.Model
/-- Rebase every required installed child slot and its exact typed branch
operands. A missing target refuses; source applicability is never dropped. -/
def OperationAction.mapTargets? (target : Nat → Option Nat) : OperationAction → Option OperationAction
  | .begin declaration => do
      let children ← declaration.requiredChildren.mapM (fun child => do
        let pc ← target child.pc
        let ok ← target child.call.onOk
        let err ← target child.call.onErr
        pure { child with pc, call := { child.call with onOk := ok, onErr := err } })
      pure (.begin { declaration with requiredChildren := children })
  | action => some action
end Runtime.ProtocolMachine.Model
