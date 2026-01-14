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

/-- Check if i₁'s exports match i₂'s imports (by endpoint). -/
def exportsMatchImports (i₁ i₂ : InterfaceType) : Bool :=
  i₂.imports.all fun (e, _) => i₁.exports.any fun (e', _) => e == e'

/-- Merge two interfaces (for composed protocols). -/
def merge (i₁ i₂ : InterfaceType) : InterfaceType where
  sessionIds := i₁.sessionIds ++ i₂.sessionIds
  -- After composition, matched imports become internal
  exports := i₁.exports.filter (fun (e, _) => !i₂.imports.any (fun (e', _) => e == e')) ++
             i₂.exports.filter (fun (e, _) => !i₁.imports.any (fun (e', _) => e == e'))
  imports := i₁.imports.filter (fun (e, _) => !i₂.exports.any (fun (e', _) => e == e')) ++
             i₂.imports.filter (fun (e, _) => !i₁.exports.any (fun (e', _) => e == e'))

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
  · exact p.buffers_typed_cert
  · -- lin_valid: tokens match G
    intro e S hIn
    sorry  -- Proof requires showing initLin entries match initGEnv

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
  (RoleSet.allEdges sid roles).map fun e => (e, [])

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

/-! ## Linking Judgment (Preview)

The linking judgment determines when two protocols can be safely composed.
Full implementation is in Phase 12.
-/

/-- Two protocols can be linked if their interfaces are compatible. -/
def LinkOK (p₁ p₂ : DeployedProtocol) : Prop :=
  -- Disjoint sessions
  p₁.interface.disjointSessions p₂.interface = true ∧
  -- Compatible exports/imports
  p₁.interface.exportsMatchImports p₂.interface = true ∧
  p₂.interface.exportsMatchImports p₁.interface = true

/-- Linking preserves well-typedness (placeholder). -/
theorem link_preserves_WTMon (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOK p₁ p₂)
    (hWT₁ : WTMon p₁.initMonitorState)
    (hWT₂ : WTMon p₂.initMonitorState) :
    True := by  -- Placeholder: actual theorem would prove merged state is well-typed
  trivial

/-! ## Composition Preserves Deadlock Freedom (Preview)

The key theorem for safe composition: if both protocols are deadlock-free,
their composition is also deadlock-free.
-/

/-- Composition preserves deadlock freedom (placeholder). -/
theorem compose_deadlock_free (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOK p₁ p₂)
    (hDF₁ : ∀ r, r ∈ p₁.roles → ReachesComm (p₁.localTypes r))
    (hDF₂ : ∀ r, r ∈ p₂.roles → ReachesComm (p₂.localTypes r)) :
    True := by  -- Placeholder: actual theorem would prove composed protocol is deadlock-free
  trivial

end

