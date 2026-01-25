import Effects.Monitor
import Effects.DeadlockFreedom
import Effects.Spatial
import Effects.Determinism

/-!
# MPST Deployed Protocol Bundle

This module defines the structure for a deployed protocol: a bundle containing
the protocol specification, projected local types, initial monitor state, and
all required certificates for safe execution.

## Overview

A **deployed protocol** is the artifact produced when a developer:
1. Defines a protocol (currently as local types, later as global type)
2. Provides proofs of well-formedness
3. Sets up initial monitor state
4. Declares the protocol's interface for composition

## Key Structures

- `InterfaceType`: What a protocol exports/imports for composition
- `DeployedProtocol`: Complete bundle with all certificates
- `ProtocolBundle`: Lightweight bundle without proofs (for runtime)

## Composition

Two deployed protocols can be composed if their interfaces are compatible:
- Disjoint session IDs
- Matching exports/imports
- Merged environments remain coherent

See Phase 12 for the full linking judgment.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Interface Type

The interface declares what endpoints a protocol exports (makes available
to composition partners) and what it imports (expects from partners).
-/

/-- Interface type for protocol composition.

A protocol's interface specifies:
- Which sessions it owns (for disjointness checking)
- Which endpoints it exports (available for external use)
- Which endpoints it imports (expected from composition partners)
-/
structure InterfaceType where
  /-- Sessions this protocol owns. -/
  sessionIds : List SessionId
  /-- Endpoints available for external use with their current types. -/
  exports : List (Endpoint × LocalType)
  /-- Endpoints expected from composition partner with their required types. -/
  imports : List (Endpoint × LocalType)
  deriving Inhabited

namespace InterfaceType

/-- Empty interface (no exports, no imports). -/
def empty : InterfaceType where
  sessionIds := []
  exports := []
  imports := []

/-- Check if two interfaces have disjoint session IDs. -/
def disjointSessions (i₁ i₂ : InterfaceType) : Bool :=
  i₁.sessionIds.all fun s => !i₂.sessionIds.contains s

/-- Propositional version of disjoint sessions. -/
def DisjointSessions (i₁ i₂ : InterfaceType) : Prop :=
  ∀ s, s ∈ i₁.sessionIds → s ∉ i₂.sessionIds

/-- Check if i₁'s exports match i₂'s imports (by endpoint only). -/
def exportsMatchImports (i₁ i₂ : InterfaceType) : Bool :=
  i₂.imports.all fun (e, _) => i₁.exports.any fun (e', _) => e == e'

/-! ### Type Compatibility (6.7.1)

Two endpoint-type pairs are compatible if they have the same endpoint
and dual types. For composition, i₁'s exports should be dual to i₂'s imports.
-/

/-- Check if two local types are dual (one sends what the other receives).
    For now, we use a simplified structural check at the head. -/
def dualTypes (L₁ L₂ : LocalType) : Bool :=
  match L₁, L₂ with
  | .send r₁ T₁ _, .recv r₂ T₂ _ =>
    r₁ == r₂ && T₁ == T₂
  | .recv r₁ T₁ _, .send r₂ T₂ _ =>
    r₁ == r₂ && T₁ == T₂
  | .select r₁ bs₁, .branch r₂ bs₂ =>
    r₁ == r₂ && bs₁.length == bs₂.length &&
    (bs₁.zip bs₂).all fun ((ℓ₁, _), (ℓ₂, _)) => ℓ₁ == ℓ₂
  | .branch r₁ bs₁, .select r₂ bs₂ =>
    r₁ == r₂ && bs₁.length == bs₂.length &&
    (bs₁.zip bs₂).all fun ((ℓ₁, _), (ℓ₂, _)) => ℓ₁ == ℓ₂
  | .end_, .end_ => true
  | _, _ => false

/-- Check if an export from i₁ is compatible with an import from i₂.
    Compatible means same endpoint and dual types. -/
def compatiblePair (exp : Endpoint × LocalType) (imp : Endpoint × LocalType) : Bool :=
  exp.1 == imp.1 && dualTypes exp.2 imp.2

/-- Check if i₁'s exports are compatible with i₂'s imports.
    Every import in i₂ must have a compatible export in i₁. -/
def exportsCompatibleWithImports (i₁ i₂ : InterfaceType) : Bool :=
  i₂.imports.all fun imp =>
    i₁.exports.any fun exp => compatiblePair exp imp

/-- Propositional version: i₁'s exports satisfy i₂'s imports with type compatibility. -/
def ExportsCompatibleWithImports (i₁ i₂ : InterfaceType) : Prop :=
  ∀ imp, imp ∈ i₂.imports →
    ∃ exp, exp ∈ i₁.exports ∧ exp.1 = imp.1 ∧ dualTypes exp.2 imp.2 = true

/-- Merge two interfaces (for composed protocols). -/
def merge (i₁ i₂ : InterfaceType) : InterfaceType where
  sessionIds := i₁.sessionIds ++ i₂.sessionIds
  -- After composition, matched imports become internal
  exports := i₁.exports.filter (fun (e, _) => !i₂.imports.any (fun (e', _) => e == e')) ++
             i₂.exports.filter (fun (e, _) => !i₁.imports.any (fun (e', _) => e == e'))
  imports := i₁.imports.filter (fun (e, _) => !i₂.exports.any (fun (e', _) => e == e')) ++
             i₂.imports.filter (fun (e, _) => !i₁.exports.any (fun (e', _) => e == e'))

/-- All session IDs in the interface. -/
def allSessionIds (i : InterfaceType) : List SessionId := i.sessionIds

/-- Check if an endpoint belongs to this interface. -/
def hasEndpoint (i : InterfaceType) (e : Endpoint) : Bool :=
  i.exports.any (fun (e', _) => e == e') || i.imports.any (fun (e', _) => e == e')

end InterfaceType

/-! ## Deployed Protocol

The complete bundle for a deployed protocol with all certificates.
-/

/-- A deployed protocol bundle with all certificates.

This structure contains everything needed to safely execute a protocol:
- The protocol specification (local types per role)
- Initial monitor state with coherence proof
- Interface for composition
- Deadlock freedom certificate

**Note**: GlobalType integration is in Phase 8+. Currently we work with
local types directly. The `globalTypeHash` field is a placeholder for
content-addressed global type reference.
-/
structure DeployedProtocol where
  /-- Protocol name/identifier. -/
  name : String

  /-- Roles participating in this protocol. -/
  roles : RoleSet

  /-- Local type for each role. -/
  localTypes : Role → LocalType

  /-- Session ID for this protocol instance. -/
  sessionId : SessionId

  /-- Initial GEnv (endpoints → local types). -/
  initGEnv : GEnv

  /-- Initial DEnv (edges → type traces). -/
  initDEnv : DEnv

  /-- Initial linear context (tokens for all endpoints). -/
  initLin : LinCtx

  /-- Initial buffers (all empty). -/
  initBufs : Buffers

  /-- Coherence certificate: G and D are coherent. -/
  coherence_cert : Coherent initGEnv initDEnv

  /-- Buffers are typed according to D. -/
  buffers_typed_cert : BuffersTyped initGEnv initDEnv initBufs

  /-- Interface for composition. -/
  interface : InterfaceType

  /-- Deadlock freedom: all local types can reach communication. -/
  reachesComm_cert : ∀ r, r ∈ roles → ReachesComm (localTypes r)

  /-- Spatial requirements for this protocol. -/
  spatialReq : SpatialReq

  /-- Unique branch labels for determinism. -/
  uniqueLabels_cert : ∀ r, r ∈ roles → reachesCommDecide (localTypes r) = true

  /-- The session ID is registered in the interface. -/
  sessionId_in_interface : sessionId ∈ interface.sessionIds

namespace DeployedProtocol

/-- Get the initial monitor state for this protocol. -/
def initMonitorState (p : DeployedProtocol) : MonitorState where
  G := p.initGEnv
  D := p.initDEnv
  bufs := p.initBufs
  Lin := p.initLin
  supply := p.sessionId + 1

/-- The initial monitor state is well-typed. -/
theorem initMonitorState_wellTyped (p : DeployedProtocol) :
    WTMon p.initMonitorState := by
  constructor
  · exact p.coherence_cert
  · -- headCoherent: buffer heads match expected receive types
    sorry  -- Requires HeadCoherent for initial state
  · -- validLabels: branch labels in buffers are valid
    sorry  -- Requires ValidLabels for initial state
  · exact p.buffers_typed_cert
  · -- lin_valid: tokens match G
    intro e S hIn
    sorry  -- Proof requires showing initLin entries match initGEnv
  · -- lin_unique: no duplicate endpoints
    sorry  -- Requires initLin has no duplicates
  · -- supply_fresh: Lin endpoints below supply
    intro e S hIn
    sorry  -- Requires initLin endpoints have sid < supply
  · -- supply_fresh_G: G endpoints below supply
    intro e S hIn
    sorry  -- Requires initGEnv endpoints have sid < supply

/-- Get all endpoints for this protocol. -/
def endpoints (p : DeployedProtocol) : List Endpoint :=
  RoleSet.allEndpoints p.sessionId p.roles

/-- Get all edges for this protocol. -/
def edges (p : DeployedProtocol) : List Edge :=
  RoleSet.allEdges p.sessionId p.roles

end DeployedProtocol

/-! ## Protocol Bundle (Lightweight)

A lightweight bundle without proofs, suitable for runtime use.
-/

/-- Lightweight protocol bundle for runtime (no proof terms). -/
structure ProtocolBundle where
  name : String
  roles : RoleSet
  localTypes : Role → LocalType
  sessionId : SessionId
  interface : InterfaceType
  spatialReq : SpatialReq

namespace ProtocolBundle

/-- Extract lightweight bundle from deployed protocol. -/
def fromDeployed (p : DeployedProtocol) : ProtocolBundle where
  name := p.name
  roles := p.roles
  localTypes := p.localTypes
  sessionId := p.sessionId
  interface := p.interface
  spatialReq := p.spatialReq

end ProtocolBundle

/-! ## Smart Constructors

Helper functions for creating deployed protocols with proof obligations.
-/

/-- Create initial GEnv from roles and local types. -/
def mkInitGEnv (roles : RoleSet) (sid : SessionId) (localTypes : Role → LocalType) : GEnv :=
  roles.map fun r => ({ sid := sid, role := r }, localTypes r)

/-- Create initial DEnv with empty traces for all edges. -/
def mkInitDEnv (roles : RoleSet) (sid : SessionId) : DEnv :=
  initDEnv sid roles

/-- Create initial LinCtx with tokens for all endpoints. -/
def mkInitLin (roles : RoleSet) (sid : SessionId) (localTypes : Role → LocalType) : LinCtx :=
  roles.map fun r => ({ sid := sid, role := r }, localTypes r)

/-- Create initial empty buffers for all edges. -/
def mkInitBufs (roles : RoleSet) (sid : SessionId) : Buffers :=
  (RoleSet.allEdges sid roles).map fun e => (e, [])

/-- Create a default interface from roles. -/
def mkDefaultInterface (roles : RoleSet) (sid : SessionId) (localTypes : Role → LocalType) : InterfaceType where
  sessionIds := [sid]
  exports := roles.map fun r => ({ sid := sid, role := r }, localTypes r)
  imports := []

/-! ## Linking Judgment (6.7.2)

The linking judgment determines when two protocols can be safely composed.
This is the full LinkOK predicate with all required conditions.
-/

/-- Decidable version: Two protocols can be linked if their interfaces are compatible. -/
def linkOK (p₁ p₂ : DeployedProtocol) : Bool :=
  -- Disjoint sessions
  p₁.interface.disjointSessions p₂.interface &&
  -- Compatible exports/imports (with type checking)
  p₁.interface.exportsCompatibleWithImports p₂.interface &&
  p₂.interface.exportsCompatibleWithImports p₁.interface

/-- Two protocols can be linked if their interfaces are compatible (legacy, Bool version). -/
def LinkOK (p₁ p₂ : DeployedProtocol) : Prop :=
  -- Disjoint sessions
  p₁.interface.disjointSessions p₂.interface = true ∧
  -- Compatible exports/imports
  p₁.interface.exportsMatchImports p₂.interface = true ∧
  p₂.interface.exportsMatchImports p₁.interface = true


end
