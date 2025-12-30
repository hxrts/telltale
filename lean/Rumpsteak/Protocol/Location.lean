import Batteries.Data.RBMap

/-! # Rumpsteak.Protocol.Location

Location and topology types for deployment configuration.

## Overview

This module defines types for specifying where protocol roles are deployed.
Topology is kept separate from choreography to enable:
- Same choreography, multiple deployment configs
- Version topologies independently
- Dev/staging/prod without touching protocol logic
- Projection correctness is location-independent

## Rust Correspondence

This module corresponds to `rust/choreography/src/topology/mod.rs`:
- `Location` ↔ Rust's `Location` enum
- `TopologyConstraint` ↔ Rust's `TopologyConstraint` enum
- `Topology` ↔ Rust's `Topology` struct

## Main Definitions

- `Location`: Where a role is deployed (local, remote, colocated)
- `TopologyConstraint`: Deployment constraints (separated, pinned, region)
- `Topology`: Maps roles to locations with constraints
- `TopologyMode`: Shorthand for common deployment patterns
-/

namespace Rumpsteak.Protocol.Location

/-- Location specifies where a role is deployed.

    - `local`: In-process, using channels
    - `remote endpoint`: Network endpoint (host:port or URL)
    - `colocated peer`: Same node as another role (shared memory)
-/
inductive Location where
  /-- In-process execution using channels -/
  | local : Location
  /-- Remote endpoint (e.g., "localhost:8080", "service.internal:9000") -/
  | remote : String → Location
  /-- Colocated with another role on the same node -/
  | colocated : String → Location
deriving Repr, DecidableEq, BEq, Inhabited

/-- Display a location as a string -/
def Location.toString : Location → String
  | .local => "local"
  | .remote endpoint => endpoint
  | .colocated peer => s!"colocated({peer})"

instance : ToString Location := ⟨Location.toString⟩

/-- Topology constraints specify requirements on role placement.

    These are validated at deployment time, not projection time.
-/
inductive TopologyConstraint where
  /-- Two roles must be on the same node -/
  | colocated : String → String → TopologyConstraint
  /-- Two roles must be on different nodes -/
  | separated : String → String → TopologyConstraint
  /-- A role must be at a specific location -/
  | pinned : String → Location → TopologyConstraint
  /-- A role must be in a specific region/zone -/
  | region : String → String → TopologyConstraint
deriving Repr, DecidableEq, BEq

/-- Display a constraint as a string -/
def TopologyConstraint.toString : TopologyConstraint → String
  | .colocated r1 r2 => s!"colocated({r1}, {r2})"
  | .separated r1 r2 => s!"separated({r1}, {r2})"
  | .pinned role loc => s!"pinned({role}, {loc})"
  | .region role reg => s!"region({role}, {reg})"

instance : ToString TopologyConstraint := ⟨TopologyConstraint.toString⟩

/-- Common deployment modes for quick configuration -/
inductive TopologyMode where
  /-- All roles in-process (testing) -/
  | local : TopologyMode
  /-- Each role in separate process -/
  | perRole : TopologyMode
  /-- Discover via Kubernetes services -/
  | kubernetes : String → TopologyMode  -- namespace
  /-- Discover via Consul -/
  | consul : String → TopologyMode  -- datacenter
deriving Repr, DecidableEq, BEq

/-- Topology maps roles to their deployment locations.

    Uses RBMap for deterministic iteration order.
-/
structure Topology where
  /-- Optional mode for shorthand configuration -/
  mode : Option TopologyMode := none
  /-- Role → Location mapping -/
  locations : Batteries.RBMap String Location compare := Batteries.RBMap.empty
  /-- Deployment constraints -/
  constraints : List TopologyConstraint := []
deriving Repr

namespace Topology

/-- Create an empty topology -/
def empty : Topology := {}

/-- Create a local-only topology (all roles in-process) -/
def localMode : Topology := { mode := some .local }

/-- Add a role location to the topology -/
def withRole (t : Topology) (role : String) (loc : Location) : Topology :=
  { t with locations := t.locations.insert role loc }

/-- Add a constraint to the topology -/
def withConstraint (t : Topology) (c : TopologyConstraint) : Topology :=
  { t with constraints := c :: t.constraints }

/-- Get the location for a role (defaults to local) -/
def getLocation (t : Topology) (role : String) : Location :=
  match t.mode with
  | some .local => .local
  | _ => t.locations.find? role |>.getD .local

/-- Check if a role is local -/
def isLocal (t : Topology) (role : String) : Bool :=
  match t.getLocation role with
  | .local => true
  | .colocated _ => true  -- colocated is effectively local
  | .remote _ => false

/-- Get all roles defined in the topology -/
def roles (t : Topology) : List String :=
  t.locations.toList.map (·.1)

/-- Check if topology is valid for a set of choreography roles.
    All referenced roles must exist in the choreography. -/
def validForRoles (t : Topology) (choreoRoles : List String) : Bool :=
  -- All topology roles must be in choreography
  let topoRoles := t.roles
  let rolesOk := topoRoles.all (choreoRoles.contains ·)
  -- All constraint roles must be in choreography
  let constraintRoles := t.constraints.flatMap fun
    | .colocated r1 r2 => [r1, r2]
    | .separated r1 r2 => [r1, r2]
    | .pinned r _ => [r]
    | .region r _ => [r]
  let constraintsOk := constraintRoles.all (choreoRoles.contains ·)
  rolesOk && constraintsOk

end Topology

/-- Result of topology validation -/
inductive TopologyValidation where
  | valid : TopologyValidation
  | unknownRole : String → TopologyValidation
  | constraintViolation : TopologyConstraint → String → TopologyValidation
deriving Repr

/-- Helper: check constraint roles against known roles -/
private def checkConstraintRoles (choreoRoles : List String)
    : List TopologyConstraint → TopologyValidation
  | [] => .valid
  | c :: rest =>
    match c with
    | .colocated r1 r2 =>
      if !choreoRoles.contains r1 then .unknownRole r1
      else if !choreoRoles.contains r2 then .unknownRole r2
      else checkConstraintRoles choreoRoles rest
    | .separated r1 r2 =>
      if !choreoRoles.contains r1 then .unknownRole r1
      else if !choreoRoles.contains r2 then .unknownRole r2
      else checkConstraintRoles choreoRoles rest
    | .pinned r _ =>
      if !choreoRoles.contains r then .unknownRole r
      else checkConstraintRoles choreoRoles rest
    | .region r _ =>
      if !choreoRoles.contains r then .unknownRole r
      else checkConstraintRoles choreoRoles rest

/-- Validate a topology against choreography roles -/
def validateTopology (t : Topology) (choreoRoles : List String) : TopologyValidation :=
  -- Check all topology roles exist
  let rec checkRoles : List String → TopologyValidation
    | [] => checkConstraintRoles choreoRoles t.constraints
    | role :: rest =>
      if !choreoRoles.contains role then .unknownRole role
      else checkRoles rest
  checkRoles t.roles

end Rumpsteak.Protocol.Location
