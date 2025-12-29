/-! # Rumpsteak.Protocol.Core

Core types shared across the protocol verification system.

## Overview

This module defines the fundamental types used throughout the Rumpsteak
verification pipeline: roles, actions, and local type components.

This module provides the "flat" (non-recursive) types used by the runner
for validating exported programs. For recursive types with full session
type semantics, see `GlobalType` and `LocalTypeR`.

## Expose

The following definitions form the semantic interface for proofs:

- `Role`: Named participant in a choreography
- `Action`: Triple of (origin, destination, label) representing a message exchange
- `LocalKind`: Direction of a local action (send or recv)
- `LocalAction`: Per-role view of a message exchange (kind, partner, label)
- `LocalType`: Sequence of local actions representing a role's protocol view (flat)

## Main Definitions

- `Role` - Structure wrapping a role name
- `Action` - Type alias for (String × String × String) triples
- `Action.origin`, `Action.destination`, `Action.label` - Accessors
- `LocalKind` - Inductive with `send` and `recv` constructors
- `LocalAction` - Structure with kind, partner, and label fields
- `LocalType` - Structure wrapping a list of local actions (flat, non-recursive)

## See Also

- `Rumpsteak.Protocol.GlobalType` - Recursive global types with branching
- `Rumpsteak.Protocol.LocalTypeR` - Recursive local types with choice
-/

namespace Rumpsteak.Protocol.Core

/-- A role represents a named participant in a choreography.
    Roles are compared by name equality. -/
structure Role where
  /-- The identifier for this role. -/
  name : String
deriving Inhabited, Repr, DecidableEq, BEq

/-- An action represents a message exchange in the global choreography.
    The triple encodes (sender, receiver, message-label). -/
abbrev Action := String × String × String

/-- Extract the sender role name from an action. -/
def Action.origin (act : Action) : String := act.fst

/-- Extract the receiver role name from an action. -/
def Action.destination (act : Action) : String := (act.snd : String × String).fst

/-- Extract the message label from an action. -/
def Action.label (act : Action) : String := (act.snd : String × String).snd

/-- LocalKind models the direction of a local action from one role's perspective.
    A `send` means this role initiates; a `recv` means this role receives. -/
inductive LocalKind
  | send
  | recv
deriving Inhabited, Repr, DecidableEq, BEq

/-- LocalAction represents a single protocol step from one role's viewpoint.
    It records the direction (send/recv), the communication partner, and the message label. -/
structure LocalAction where
  /-- Whether this role sends or receives. -/
  kind : LocalKind
  /-- The other role involved in this exchange. -/
  partner : String
  /-- The message label identifying this exchange. -/
  label : String
deriving Inhabited, Repr, DecidableEq, BEq

/-- LocalType is a sequence of local actions representing a role's complete
    protocol view after projection from the global choreography. -/
structure LocalType where
  /-- The ordered sequence of actions this role performs. -/
  actions : List LocalAction
deriving Inhabited, Repr, BEq

/-- Flip send to recv and vice versa. Used for duality operations. -/
def LocalKind.swap : LocalKind → LocalKind
  | LocalKind.send => LocalKind.recv
  | LocalKind.recv => LocalKind.send

/-- Dualize an action by flipping its kind while preserving partner and label.
    If role A sends to B, the dual from B's perspective is receiving from A. -/
def LocalAction.dual (action : LocalAction) : LocalAction :=
  ⟨action.kind.swap, action.partner, action.label⟩

/-- Dualize every action in a local type.
    Used for verifying that communicating roles have dual protocol views. -/
def LocalType.dual (lt : LocalType) : LocalType :=
  { actions := lt.actions.map LocalAction.dual }

end Rumpsteak.Protocol.Core
