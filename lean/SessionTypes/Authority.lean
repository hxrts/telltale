import SessionTypes.ValType

/-! Canonical typed readiness evidence data. These fields are not a live host
capability or an issuance proof. Runtime admission additionally requires the
original registered witness and the actual live owner; wire values cannot
reconstruct them. -/
namespace SessionTypes

inductive OwnershipScope where
  | session
  | fragments (roles : List String)
  deriving Repr, DecidableEq, BEq

structure ReadinessWitness where
  witnessId : Nat
  sessionId : Nat
  ownerId : String
  generation : Nat
  scope : OwnershipScope
  predicateRef : String
  deriving Repr, DecidableEq, BEq

end SessionTypes

namespace SessionTypes

/-- Protocol-model owner data. This is not a Rust issued host handle. -/
structure ModelOwner where
  sessionId : Nat
  ownerId : String
  generation : Nat
  scope : OwnershipScope
  deriving Repr, DecidableEq, BEq

/-- Genuine issuer/consumer observation, retained by the same model owner. -/
structure ModelReadinessAudit where
  witness : ReadinessWitness
  event : String
  tick : Option Nat
  reason : Option String := none
  deriving Repr, DecidableEq, BEq

/-- Canonical session-local authority state; observations never reconstruct it. -/
structure ModelOwnershipState where
  current : Option ModelOwner := none
  transferPending : Bool := false
  issuedReadiness : List ReadinessWitness := []
  consumedWitnesses : List Nat := []
  nextWitnessId : Nat := 1
  readinessAudit : List ModelReadinessAudit := []
  deriving Repr, DecidableEq, BEq

namespace ModelOwnershipState

def admits (state : ModelOwnershipState) (owner : ModelOwner) : Bool :=
  state.current == some owner && !state.transferPending && owner.scope == .session

/-- Explicit model ownership admission, independent of any returned witness. -/
def claim (state : ModelOwnershipState) (sid : Nat) (ownerId : String) :
    Except String (ModelOwnershipState × ModelOwner) :=
  if state.current.isSome || state.transferPending then .error "session already owned"
  else
    let owner : ModelOwner := ⟨sid, ownerId, 0, .session⟩
    .ok ({ state with current := some owner }, owner)

/-- Sole model issuer: derives evidence from an admitted current owner. -/
def issueReadiness (state : ModelOwnershipState) (owner : ModelOwner) (predicate : String) (tick : Option Nat := none) :
    Except String (ModelOwnershipState × ReadinessWitness) :=
  if !state.admits owner then .error "readiness issuer lacks current ownership"
  else
    let witness : ReadinessWitness :=
      ⟨state.nextWitnessId, owner.sessionId, owner.ownerId, owner.generation, owner.scope, predicate⟩
    .ok ({ state with
      issuedReadiness := witness :: state.issuedReadiness,
      nextWitnessId := state.nextWitnessId + 1,
      readinessAudit := state.readinessAudit ++ [⟨witness, "Issued", tick, none⟩] }, witness)

/-- Retain actual failed attempts as well as successful canonical consumption. -/
def attemptConsumeReadiness (state : ModelOwnershipState) (owner : ModelOwner)
    (witness : ReadinessWitness) (tick : Option Nat := none) :
    ModelOwnershipState × Except String Unit :=
  let refuse := fun reason failure =>
    ({ state with readinessAudit := state.readinessAudit ++ [⟨witness, "Rejected", tick, some reason⟩] }, .error failure)
  let invalid := fun reason =>
    "InvalidWitness { session_id: " ++ toString owner.sessionId ++ ", witness_id: " ++
      toString witness.witnessId ++ ", reason: \"" ++ reason ++ "\" }"
  if !state.admits owner then (state, .error "readiness consumer lacks current ownership")
  else if state.consumedWitnesses.contains witness.witnessId then
    refuse "witness already consumed" ("WitnessConsumed { session_id: " ++ toString witness.sessionId ++
      ", witness_id: " ++ toString witness.witnessId ++ " }")
  else match state.issuedReadiness.find? (fun issued => issued.witnessId == witness.witnessId) with
    | none => refuse "witness was never issued" (invalid "witness was never issued")
    | some issued =>
      if issued != witness then refuse "witness payload mismatch" (invalid "witness payload mismatch")
      else if witness.sessionId != owner.sessionId || witness.ownerId != owner.ownerId ||
          witness.generation != owner.generation || witness.scope != owner.scope then
        refuse "live ownership no longer matches witness" (invalid "live ownership no longer matches witness")
      else ({ state with
        issuedReadiness := state.issuedReadiness.filter (fun original => original.witnessId != witness.witnessId),
        consumedWitnesses := witness.witnessId :: state.consumedWitnesses,
        readinessAudit := state.readinessAudit ++ [⟨witness, "Consumed", tick, none⟩] }, .ok ())

/-- Pure convenience view. Stateful machine settlement retains both components
of attemptConsumeReadiness even when it refuses. -/
def consumeReadiness (state : ModelOwnershipState) (owner : ModelOwner)
    (witness : ReadinessWitness) (tick : Option Nat := none) : Except String ModelOwnershipState :=
  let (next, result) := state.attemptConsumeReadiness owner witness tick
  result.map (fun _ => next)

end ModelOwnershipState
end SessionTypes
