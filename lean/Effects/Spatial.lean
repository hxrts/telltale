import Effects.Environments

/-!
# MPST Spatial Type System

This module defines spatial requirements, topologies, and the satisfaction judgment
that determines whether a deployment topology satisfies a protocol's spatial needs.

## Design Principles

- Spatial requirements are structural, not dynamic
- Topology is an external witness (not computed by the library)
- Spatial subtyping forms a preorder with monotonicity

## Key Definitions

- `SpatialReq` - Spatial requirement language
- `Topology` - Deployment topology (site assignment)
- `Satisfies` - Satisfaction judgment `topo ⊨ R`
- `SpatialLe` - Spatial subtyping preorder `R₁ ≤ R₂`
- `spatial_le_sound` - Monotonicity theorem

Ported from RumpsteakV2.Protocol.Spatial.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-! ## Spatial Requirements

Atomic spatial requirements compose via conjunction. The language is intentionally
simple and structural—no temporal operators, no dynamic constraints.
-/

/-- A site represents a deployment location (machine, region, datacenter). -/
abbrev Site := String

/-- A role name in the protocol (matches Effects' Role). -/
abbrev RoleName := Role

/-- Atomic and composite spatial requirements.

Requirements express structural constraints on protocol deployments:
- `netCapable`: site has network access
- `timeoutCapable`: site can fire timeout events
- `colocated`: two roles share a deployment site
- `reliableEdge`: reliable transport between two roles
- `conj`: conjunction of requirements
- `top`: always satisfied (unit for conjunction)
- `bot`: never satisfied (for contradiction)
-/
inductive SpatialReq where
  | netCapable : Site → SpatialReq
  | timeoutCapable : Site → SpatialReq
  | colocated : RoleName → RoleName → SpatialReq
  | reliableEdge : RoleName → RoleName → SpatialReq
  | conj : SpatialReq → SpatialReq → SpatialReq
  | top : SpatialReq
  | bot : SpatialReq
  deriving Inhabited, Repr, DecidableEq, BEq

namespace SpatialReq

/-- Conjunction notation for spatial requirements. -/
instance : HAnd SpatialReq SpatialReq SpatialReq where
  hAnd := conj

/-- Check if a requirement is trivially satisfied. -/
def isTop : SpatialReq → Bool
  | top => true
  | _ => false

/-- Check if a requirement is trivially unsatisfiable. -/
def isBot : SpatialReq → Bool
  | bot => true
  | _ => false

/-- Flatten nested conjunctions into a list of atomic requirements. -/
partial def atoms : SpatialReq → List SpatialReq
  | conj r₁ r₂ => atoms r₁ ++ atoms r₂
  | top => []
  | r => [r]

/-- Build a conjunction from a list of requirements. -/
def fromList : List SpatialReq → SpatialReq
  | [] => top
  | [r] => r
  | r :: rs => conj r (fromList rs)

end SpatialReq

/-! ## Topology

A topology assigns roles to sites and declares reliable edges between sites.
This is the deployment configuration that protocols execute over.
-/

/-- Site capability flags. -/
structure SiteCapabilities where
  hasNetwork : Bool := true
  hasTimeout : Bool := true
  deriving Inhabited, Repr, DecidableEq, BEq

/-- Deployment topology: assignment of roles to sites with edge declarations.

The `assign` function maps role names to site names. Roles not explicitly
assigned are implicitly placed at a default site (their own name as site).
-/
structure Topology where
  /-- All declared sites. -/
  sites : List Site
  /-- Role-to-site assignment. -/
  assign : RoleName → Site
  /-- Edges with reliable transport (ordered pairs). -/
  edges : List (Site × Site)
  /-- Per-site capabilities. -/
  capabilities : Site → SiteCapabilities := fun _ => default
  deriving Inhabited

namespace Topology

/-- Default topology where each role is its own site. -/
def trivial : Topology where
  sites := []
  assign := id
  edges := []

/-- Check if two sites are connected by a reliable edge. -/
def hasEdge (topo : Topology) (s₁ s₂ : Site) : Bool :=
  (s₁, s₂) ∈ topo.edges || (s₂, s₁) ∈ topo.edges

/-- Check if a site has network capability. -/
def siteHasNetwork (topo : Topology) (s : Site) : Bool :=
  (topo.capabilities s).hasNetwork

/-- Check if a site has timeout capability. -/
def siteHasTimeout (topo : Topology) (s : Site) : Bool :=
  (topo.capabilities s).hasTimeout

/-- Get the site for a role. -/
def siteOf (topo : Topology) (role : RoleName) : Site :=
  topo.assign role

/-- Check if two roles are colocated. -/
def rolesColocated (topo : Topology) (r₁ r₂ : RoleName) : Bool :=
  topo.siteOf r₁ == topo.siteOf r₂

end Topology

/-! ## Satisfaction Judgment

The satisfaction judgment `Satisfies topo R` determines whether a topology
provides the capabilities required by a spatial requirement.
-/

/-- Satisfaction judgment: topology satisfies spatial requirement.

This is the semantic interpretation of spatial requirements. A topology
satisfies a requirement if it provides all the required capabilities.
-/
def Satisfies (topo : Topology) : SpatialReq → Prop
  | .netCapable s => topo.siteHasNetwork s = true
  | .timeoutCapable s => topo.siteHasTimeout s = true
  | .colocated r₁ r₂ => topo.siteOf r₁ = topo.siteOf r₂
  | .reliableEdge r₁ r₂ => topo.hasEdge (topo.siteOf r₁) (topo.siteOf r₂) = true
  | .conj r₁ r₂ => Satisfies topo r₁ ∧ Satisfies topo r₂
  | .top => True
  | .bot => False

namespace SpatialNotation
/-- Notation for satisfaction: `topo ⊨ R` -/
scoped notation:50 topo " ⊨ " req => Satisfies topo req
end SpatialNotation

open SpatialNotation

/-- Decidable satisfaction for atomic requirements. -/
def satisfiesBool (topo : Topology) : SpatialReq → Bool
  | .netCapable s => topo.siteHasNetwork s
  | .timeoutCapable s => topo.siteHasTimeout s
  | .colocated r₁ r₂ => topo.rolesColocated r₁ r₂
  | .reliableEdge r₁ r₂ => topo.hasEdge (topo.siteOf r₁) (topo.siteOf r₂)
  | .conj r₁ r₂ => satisfiesBool topo r₁ && satisfiesBool topo r₂
  | .top => true
  | .bot => false

/-- Boolean satisfaction reflects propositional satisfaction. -/
theorem satisfiesBool_iff_Satisfies (topo : Topology) (req : SpatialReq) :
    satisfiesBool topo req = true ↔ Satisfies topo req := by
  induction req with
  | netCapable s => simp [satisfiesBool, Satisfies]
  | timeoutCapable s => simp [satisfiesBool, Satisfies]
  | colocated r₁ r₂ =>
      simp only [satisfiesBool, Satisfies, Topology.rolesColocated]
      constructor
      · intro h; exact beq_iff_eq.mp h
      · intro h; exact beq_iff_eq.mpr h
  | reliableEdge r₁ r₂ => simp [satisfiesBool, Satisfies]
  | conj r₁ r₂ ih₁ ih₂ =>
      simp only [satisfiesBool, Satisfies, Bool.and_eq_true]
      constructor
      · intro ⟨h₁, h₂⟩; exact ⟨ih₁.mp h₁, ih₂.mp h₂⟩
      · intro ⟨h₁, h₂⟩; exact ⟨ih₁.mpr h₁, ih₂.mpr h₂⟩
  | top => simp [satisfiesBool, Satisfies]
  | bot => simp [satisfiesBool, Satisfies]

/-! ## Spatial Subtyping

The spatial subtyping preorder captures when one requirement is at least as
demanding as another. More demanding requirements have fewer satisfying topologies.

Key intuition:
- `R₁ ≤ R₂` means `R₁` implies `R₂` (R₁ is stronger)
- Stronger requirements → more portable protocols
- Weaker requirements → more deployment flexibility
-/

/-- Spatial subtyping: `R₁ ≤ R₂` means R₁ is at least as demanding as R₂.

If a topology satisfies R₁, it also satisfies R₂.
-/
inductive SpatialLe : SpatialReq → SpatialReq → Prop where
  /-- Reflexivity: every requirement implies itself. -/
  | refl {r : SpatialReq} : SpatialLe r r
  /-- Top is the weakest requirement (satisfied by all topologies). -/
  | top_max {r : SpatialReq} : SpatialLe r .top
  /-- Conjunction is stronger than its left component. -/
  | conj_left {r₁ r₂ : SpatialReq} : SpatialLe (.conj r₁ r₂) r₁
  /-- Conjunction is stronger than its right component. -/
  | conj_right {r₁ r₂ : SpatialReq} : SpatialLe (.conj r₁ r₂) r₂
  /-- Transitivity: chaining implications. -/
  | trans {r₁ r₂ r₃ : SpatialReq} : SpatialLe r₁ r₂ → SpatialLe r₂ r₃ → SpatialLe r₁ r₃
  /-- Bot is the strongest requirement (satisfied by no topology). -/
  | bot_min {r : SpatialReq} : SpatialLe .bot r
  /-- Congruence: conjunction preserves ordering. -/
  | conj_mono {r₁ r₁' r₂ r₂' : SpatialReq} : SpatialLe r₁ r₁' → SpatialLe r₂ r₂' →
                SpatialLe (.conj r₁ r₂) (.conj r₁' r₂')

namespace SpatialLe

/-- Notation for spatial subtyping: `R₁ ≤ₛ R₂` -/
scoped notation:50 r₁ " ≤ₛ " r₂ => SpatialLe r₁ r₂

/-- Spatial subtyping is reflexive. -/
theorem rfl' {r : SpatialReq} : r ≤ₛ r := refl

/-- Conjunction is idempotent under subtyping. -/
theorem conj_idem (r : SpatialReq) : (r.conj r) ≤ₛ r := conj_left

/-- Semantic equivalence: both requirements have same satisfying topologies. -/
def SpatialEquiv (r₁ r₂ : SpatialReq) : Prop :=
  (r₁ ≤ₛ r₂) ∧ (r₂ ≤ₛ r₁)

/-- Notation for spatial equivalence. -/
scoped notation:50 r₁ " ≈ₛ " r₂ => SpatialEquiv r₁ r₂

end SpatialLe

open SpatialLe

/-! ## Monotonicity Theorem

The key soundness property: spatial subtyping is semantically correct.
If R₁ ≤ R₂ and topo ⊨ R₁, then topo ⊨ R₂.
-/

/-- Monotonicity: spatial subtyping is sound with respect to satisfaction.

This is the main semantic soundness theorem for spatial subtyping.
-/
theorem spatial_le_sound {topo : Topology} {r₁ r₂ : SpatialReq}
    (hle : r₁ ≤ₛ r₂) (hsat : topo ⊨ r₁) : topo ⊨ r₂ := by
  induction hle with
  | refl => exact hsat
  | top_max => trivial
  | conj_left => exact hsat.1
  | conj_right => exact hsat.2
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hsat)
  | bot_min => exact False.elim hsat
  | conj_mono _ _ ih₁ ih₂ => exact ⟨ih₁ hsat.1, ih₂ hsat.2⟩

/-- Contrapositive of monotonicity: if R₂ is unsatisfied, so is any stronger R₁. -/
theorem spatial_le_contrapositive {topo : Topology} {r₁ r₂ : SpatialReq}
    (hle : r₁ ≤ₛ r₂) (hunsat : ¬(topo ⊨ r₂)) : ¬(topo ⊨ r₁) :=
  fun hsat => hunsat (spatial_le_sound hle hsat)

/-! ## Requirement Extraction

Utilities for computing spatial requirements from protocol structure.
These will be used when integrating with GlobalType.
-/

/-- Requirement for a point-to-point communication. -/
def commReq (sender receiver : RoleName) : SpatialReq :=
  .netCapable sender &&& .netCapable receiver

/-- Requirement for a choice with timeout. -/
def timedChoiceReq (decider : RoleName) : SpatialReq :=
  .timeoutCapable decider

/-- Combine requirements from a list of branches. -/
def branchesReq (reqs : List SpatialReq) : SpatialReq :=
  SpatialReq.fromList reqs

/-! ## Topology Builders

Convenience functions for constructing topologies.
-/

/-- Default capabilities with network and timeout enabled. -/
def SiteCapabilities.enabled : SiteCapabilities where
  hasNetwork := true
  hasTimeout := true

/-- Create a topology where all roles share a single site. -/
def Topology.allColocated (site : Site) : Topology where
  sites := [site]
  assign := fun _ => site
  edges := [(site, site)]
  capabilities := fun _ => SiteCapabilities.enabled

/-- Create a topology with each role on its own site, fully connected. -/
def Topology.fullyConnected (roles : List RoleName) : Topology where
  sites := roles
  assign := id
  edges := roles.flatMap fun r₁ => roles.map fun r₂ => (r₁, r₂)

/-- Colocated roles always have reliable edges between them (if self-loops exist). -/
theorem colocated_implies_edge (topo : Topology) (r₁ r₂ : RoleName)
    (hcolo : topo ⊨ .colocated r₁ r₂)
    (hself : topo.hasEdge (topo.siteOf r₁) (topo.siteOf r₁) = true) :
    topo ⊨ .reliableEdge r₁ r₂ := by
  simp only [Satisfies] at hcolo ⊢
  rw [← hcolo]
  exact hself

/-! ## Integration with Effects Types

Bridge definitions connecting Spatial requirements to Effects session types.
-/

/-- Spatial requirement for a session endpoint.

An endpoint requires network capability at its assigned site.
-/
def endpointReq (e : Endpoint) : SpatialReq :=
  .netCapable e.role

/-- Spatial requirement for an edge (directed communication channel).

Both sender and receiver sites need network capability.
-/
def edgeReq (edge : Edge) : SpatialReq :=
  .netCapable edge.sender &&& .netCapable edge.receiver

/-- Check if a topology supports all edges in a GEnv. -/
def supportsGEnv (topo : Topology) (G : GEnv) : Prop :=
  ∀ e, e ∈ G.map Prod.fst → topo ⊨ endpointReq e

/-- Decidable check for GEnv support. -/
def supportsGEnvBool (topo : Topology) (G : GEnv) : Bool :=
  G.all fun (e, _) => satisfiesBool topo (endpointReq e)

