import Rumpsteak.Protocol.Core

/-! # Rumpsteak.Protocol.Choreography

Choreography AST and well-formedness predicates.

## Overview

This module provides a lightweight choreography representation consumed by the
Lean runner. Each choreography tracks its participant roles and the flat sequence
of actions (message exchanges) between them.

## Expose

The following definitions form the semantic interface for proofs:

- `Choreography`: Structure holding roles and actions
- `roleNames`: Extract role identifiers as strings
- `findRole`: Look up a role by name
- `hasUniqueRoles`: Check for duplicate role declarations
- `hasValidActions`: Check that all action endpoints reference declared roles
- `isWellFormed`: Combined well-formedness predicate

Internal helpers like `participatingActions` and `describeRoleTrace` are
implementation details for diagnostics.

## Main Definitions

- `Choreography` - The core AST structure
- Well-formedness predicates for validation
- Helper functions for role and action queries
-/

namespace Rumpsteak.Protocol.Choreography

open Rumpsteak.Protocol.Core

/-- A choreography is a global protocol specification consisting of
    participating roles and the sequence of message exchanges between them. -/
structure Choreography where
  /-- The roles participating in this protocol. -/
  roles : List Role
  /-- The ordered sequence of message exchanges. -/
  actions : List Action
deriving Inhabited, Repr

/-- Extract role names as a list of strings for comparison and lookup. -/
def roleNames (ch : Choreography) : List String :=
  ch.roles.map (·.name)

/-- Look up a role by name, returning `none` if not found. -/
def findRole (ch : Choreography) (name : String) : Option Role :=
  ch.roles.find? (fun role => role.name == name)

/-- Extract all message labels from the choreography. -/
def actionLabels (ch : Choreography) : List String :=
  ch.actions.map (·.label)

/-- Get actions where the specified role participates (as sender or receiver).
    Used for building per-role trace summaries. -/
def participatingActions (ch : Choreography) (roleName : String) : List Action :=
  ch.actions.filter (fun act =>
    Action.origin act == roleName || Action.destination act == roleName)

/-- Check that all role names are unique. Duplicate declarations are invalid. -/
def hasUniqueRoles (ch : Choreography) : Bool :=
  (roleNames ch).eraseDups == roleNames ch

/-- Check that every action references only declared roles.
    Both sender and receiver must be valid role names. -/
def hasValidActions (ch : Choreography) : Bool :=
  ch.actions.all (fun act =>
    let validOrigin := findRole ch (Action.origin act) |>.isSome
    let validDestination := findRole ch (Action.destination act) |>.isSome
    validOrigin && validDestination)

/-- Produce a textual trace summary for diagnostics.
    Lists the labels of all actions involving the specified role. -/
def describeRoleTrace (ch : Choreography) (roleName : String) : String :=
  let actions := participatingActions ch roleName
  let summary := actions.map fun act => Action.label act
  if summary.isEmpty then
    s!"{roleName} has no actions"
  else
    String.intercalate ", " summary

/-- Combined well-formedness check: unique roles and valid action endpoints. -/
def isWellFormed (ch : Choreography) : Bool :=
  hasUniqueRoles ch && hasValidActions ch

end Rumpsteak.Protocol.Choreography
