import Rumpsteak.Protocol.Core
import Rumpsteak.Protocol.Choreography

/-! # Rumpsteak.Protocol.Projection

Projection logic computes per-role local types from global choreographies.

## Overview

Projection transforms a global choreography into a local type for a specific role.
Each role sees only the actions it participates in, with send/recv directions
determined by whether the role is the sender or receiver in each exchange.

## Expose

The following definitions form the semantic interface for proofs:

- `project`: Computes the local type for a given role
- `traceForRole`: Convenience wrapper that handles role lookup
- `LocalAction.fromGlobal`: Converts a global action to a local action for a role
- `subLabelsOf`: Checks if all actions in one type appear in another
- `labels`: Extracts labels from a local type
- `matchesActionTrace`: Compares local type actions to an expected sequence

Internal helpers are implementation details.

## Main Definitions

- `project` - The core projection function
- `subLabelsOf` - Label subset checking for verification
- `labels` - Label extraction for comparison
-/

namespace Rumpsteak.Protocol.Projection

open Rumpsteak.Protocol.Core
open Rumpsteak.Protocol.Choreography

/-- Convert a global action to a local action from a specific role's perspective.
    Returns `some` if the role participates, `none` otherwise.
    - If the role is the sender, returns a `send` action to the receiver.
    - If the role is the receiver, returns a `recv` action from the sender. -/
def LocalAction.fromGlobal (act : Action) (roleName : String) : Option LocalAction :=
  match act with
  | ⟨origin, destination, label⟩ =>
    if origin == roleName then
      some { kind := LocalKind.send, partner := destination, label }
    else if destination == roleName then
      some { kind := LocalKind.recv, partner := origin, label }
    else
      none

/-- Project a choreography to a local type for a specific role.
    Filters the global action sequence to include only actions where the role
    participates, converting each to the appropriate local action. -/
def project (ch : Choreography) (role : Role) : LocalType :=
  { actions := ch.actions.filterMap fun act => LocalAction.fromGlobal act role.name }

/-- Extract labels from a local type for comparison or logging. -/
def labels (lt : LocalType) : List String :=
  lt.actions.map (·.label)

/-- Check if all actions in `lt` appear somewhere in `sup`.
    Used for verifying that exported programs don't introduce new actions. -/
def subLabelsOf (lt : LocalType) (sup : LocalType) : Bool :=
  lt.actions.all fun action => sup.actions.any fun b => decide (b = action)

/-- Compare local type actions to an expected sequence for exact matching. -/
def matchesActionTrace (lt : LocalType) (expected : List LocalAction) : Bool :=
  lt.actions == expected

/-- Convenience function: look up a role by name and project.
    Returns an empty local type if the role is not found. -/
def traceForRole (ch : Choreography) (roleName : String) : LocalType :=
  match findRole ch roleName with
  | some r => project ch r
  | none => { actions := [] }

end Rumpsteak.Protocol.Projection
