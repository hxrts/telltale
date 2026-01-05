/-! # RumpsteakV2.Protocol.Core

Core protocol types for the V2 development.

## Expose

The following definitions form the semantic interface for proofs:

- `Role`
- `Action`
- `Action.origin`
- `Action.destination`
- `Action.label`
- `LocalKind`
- `LocalAction`
- `LocalType`
- `LocalKind.swap`
- `LocalAction.dual`
- `LocalType.dual`
-/

namespace RumpsteakV2.Protocol.Core

/-- A role represents a named participant in a choreography. -/
structure Role where
  name : String
  deriving Inhabited, Repr, DecidableEq, BEq

/-- An action represents a message exchange in the global choreography. -/
abbrev Action := String × String × String

/-- Extract the sender role name from an action. -/
def Action.origin (act : Action) : String := act.fst

/-- Extract the receiver role name from an action. -/
def Action.destination (act : Action) : String := (act.snd : String × String).fst

/-- Extract the message label from an action. -/
def Action.label (act : Action) : String := (act.snd : String × String).snd

/-- Direction of a local action. -/
inductive LocalKind
  | send
  | recv
  deriving Inhabited, Repr, DecidableEq, BEq

/-- Per-role view of a message exchange. -/
structure LocalAction where
  kind : LocalKind
  partner : String
  label : String
  deriving Inhabited, Repr, DecidableEq, BEq

/-- Flat local type for the runner. -/
structure LocalType where
  actions : List LocalAction
  deriving Inhabited, Repr, BEq

/-- Flip send to recv and vice versa. -/
def LocalKind.swap : LocalKind → LocalKind
  | LocalKind.send => LocalKind.recv
  | LocalKind.recv => LocalKind.send

/-- Dualize a local action. -/
def LocalAction.dual (action : LocalAction) : LocalAction :=
  ⟨action.kind.swap, action.partner, action.label⟩

/-- Dualize every action in a local type. -/
def LocalType.dual (lt : LocalType) : LocalType :=
  { actions := lt.actions.map LocalAction.dual }

end RumpsteakV2.Protocol.Core
