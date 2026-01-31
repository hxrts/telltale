import Std
import Protocol.Basic
import Protocol.LocalType
import Protocol.Values
import Protocol.Spatial
import SessionTypes.GlobalType
import Runtime.Compat.Inv
import Runtime.Compat.RA

set_option autoImplicit false

universe u

/-
The Problem. The runtime must be parametric over identity, guard, persistence,
and effect models while staying independent of any particular domain.

Solution Structure. Define lean typeclasses and small helper defs that expose
just enough structure to wire the VM and keep later proofs modular.
-/

/-! ## Shared protocol types -/

abbrev GlobalType := SessionTypes.GlobalType.GlobalType

/-! ## Domain model interfaces -/

-- Identity model for session participants and sites.
class IdentityModel (ι : Type u) where
  /-- Persistent participant identity (survives session boundaries). -/
  ParticipantId : Type
  /-- Physical execution site (may differ from participant). -/
  SiteId : Type
  /-- A participant may span multiple sites. -/
  sites : ParticipantId → List SiteId
  /-- Render a site id as a protocol-level site name. -/
  siteName : SiteId → Site
  /-- Partial inverse from protocol site names to site ids. -/
  siteOf : Site → Option SiteId
  /-- Capabilities available at each site. -/
  siteCapabilities : SiteId → SiteCapabilities
  /-- Reliable edges between sites. -/
  reliableEdges : List (SiteId × SiteId)
  /-- Decidable equality on participants and sites. -/
  decEqP : DecidableEq ParticipantId
  decEqS : DecidableEq SiteId

-- Guard layer interface for invariant-protected resources.
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

/-! ## Identity utilities -/

def IdentityModel.deployedSites {ι : Type u} [IdentityModel ι]
    (roles : RoleSet) (assignment : Role → IdentityModel.ParticipantId ι) : List Site := by
  -- Collect all sites for assigned participants, then remove duplicates.
  classical
  let _ : DecidableEq Site := inferInstance
  let siteLists :=
    roles.map (fun r =>
      (IdentityModel.sites (ι:=ι) (assignment r)).map (IdentityModel.siteName (ι:=ι)))
  let flat := siteLists.foldl (fun acc xs => acc ++ xs) []
  exact flat.eraseDups

def IdentityModel.toTopology {ι : Type u} [IdentityModel ι]
    (roles : RoleSet)
    (assignment : Role → IdentityModel.ParticipantId ι)
    (siteChoice : IdentityModel.ParticipantId ι → IdentityModel.SiteId ι)
    (_hSiteChoice : ∀ p, siteChoice p ∈ IdentityModel.sites p) : Topology :=
  -- Build a topology from the induced deployment and reliable edges.
  let deployed := IdentityModel.deployedSites roles assignment
  let edges := (IdentityModel.reliableEdges (ι:=ι)).map (fun p =>
    (IdentityModel.siteName (ι:=ι) p.fst, IdentityModel.siteName (ι:=ι) p.snd))
  { sites := deployed
  , assign := fun r => IdentityModel.siteName (ι:=ι) (siteChoice (assignment r))
  , edges := edges.filter (fun p => p.fst ∈ deployed ∧ p.snd ∈ deployed)
  , capabilities := fun s =>
      match IdentityModel.siteOf (ι:=ι) s with
      | some sid => IdentityModel.siteCapabilities (ι:=ι) sid
      | none => default }

def canCreate {ι : Type u} [IdentityModel ι] (spatialReq : SpatialReq)
    (roles : RoleSet)
    (assignment : Role → IdentityModel.ParticipantId ι)
    (siteChoice : IdentityModel.ParticipantId ι → IdentityModel.SiteId ι)
    (_hSiteChoice : ∀ p, siteChoice p ∈ IdentityModel.sites p) : Prop :=
  -- Check spatial requirements on the induced topology.
  Satisfies (IdentityModel.toTopology roles assignment siteChoice _hSiteChoice) spatialReq

/-! ## Guard chains -/

structure GuardChain (γ : Type u) [GuardLayer γ] where
  /-- Ordered list of guard layers. -/
  layers : List γ
  /-- Active predicate for hot-swappable layers. -/
  active : γ → Bool

def GuardChain.namespaces {γ : Type u} [GuardLayer γ] (chain : GuardChain γ) : List Namespace :=
  -- Extract namespaces in order for disjointness checks.
  chain.layers.map GuardLayer.layerNs

def GuardChain.wf {γ : Type u} [GuardLayer γ] (chain : GuardChain γ) : Prop :=
  -- Pairwise namespace disjointness ensures safe invariant stacking.
  List.Pairwise
    (fun n₁ n₂ => Mask.disjoint (namespace_to_mask n₁) (namespace_to_mask n₂))
    (GuardChain.namespaces chain)

inductive GuardCommand where
  -- Commands emitted by guard evaluation.
  | chargeBudget (amount : Nat)
  | appendJournal (facts : List Nat)
  | recordLeakage (ext ngh grp : Nat)
  | custom (tag : Nat) (data : List Nat)
  deriving Repr

-- Persistence interface for durable state and reconstruction.
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

-- Effect interface with Iris pre/postconditions.
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
