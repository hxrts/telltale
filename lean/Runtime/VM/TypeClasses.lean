import Protocol.Basic
import Protocol.LocalType
import Protocol.Values
import Protocol.Spatial
import SessionTypes.GlobalType
import Runtime.Compat.Inv
import Runtime.Compat.RA

set_option autoImplicit false

universe u

/-!
# Task 10: Domain Model Type Classes

Parametric type class interfaces from iris_runtime_2.md §2.
Pure Lean definitions — no Iris primitives.

## Definitions

- `IdentityModel ι` — participants, sites, capabilities
- `GuardLayer γ` — hierarchical locking
- `PersistenceModel π` — durable state
- `EffectModel ε` — side effects
- `SessionId`, `Endpoint`, `Edge`, `Role`
- `LocalType`, `GlobalType`, `Label`, `Value`, `ValType`
-/

/-! ## Shared protocol types -/

abbrev GlobalType := SessionTypes.GlobalType.GlobalType

/-! ## Domain model interfaces -/

class IdentityModel (ι : Type u) where
  /-- Persistent participant identity (survives session boundaries). -/
  ParticipantId : Type
  /-- Physical execution site (may differ from participant). -/
  SiteId : Type
  /-- A participant may span multiple sites. -/
  sites : ParticipantId → List SiteId
  /-- Capabilities available at each site. -/
  siteCapabilities : SiteId → SiteCapabilities
  /-- Reliable edges between sites. -/
  reliableEdges : List (SiteId × SiteId)
  /-- Decidable equality on participants and sites. -/
  decEqP : DecidableEq ParticipantId
  decEqS : DecidableEq SiteId

class GuardLayer (γ : Type u) where
  /-- Namespace for this layer's invariant. -/
  layerNs : γ → Namespace
  /-- Resource this layer protects. -/
  Resource : Type
  /-- Evidence produced on successful evaluation. -/
  Evidence : Type
  /-- Open the layer: inspect the resource, produce evidence or abort. -/
  open_ : Resource → Option Evidence
  /-- Close the layer: update the resource after commit. -/
  close : Resource → Evidence → Resource

class PersistenceModel (π : Type u) where
  /-- Persistent state carrier. -/
  PState : Type
  /-- Delta type for incremental persistence. -/
  Delta : Type
  /-- Session state representation for reconstruction. -/
  SessionState : Type
  /-- Apply a delta to persistent state. -/
  apply : PState → Delta → PState
  /-- Derive session state from persistent state. -/
  derive : PState → SessionId → Option SessionState
  /-- Empty persistent state. -/
  empty : PState

class EffectModel (ε : Type u) where
  /-- Effect actions and their mutable context. -/
  EffectAction : Type
  EffectCtx : Type
  /-- Execute an action in the effect context. -/
  exec : EffectAction → EffectCtx → EffectCtx
  /-- Pre- and post-conditions for effects. -/
  pre : EffectAction → EffectCtx → iProp
  post : EffectAction → EffectCtx → iProp
  /-- Session type associated with an effect handler. -/
  handlerType : EffectAction → LocalType
