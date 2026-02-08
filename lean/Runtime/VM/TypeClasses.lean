import Std
import Protocol.Basic
import Protocol.LocalType
import Protocol.Values
import Protocol.Spatial
import SessionTypes.GlobalType

set_option autoImplicit false

universe u

/-!
# Domain Model Interfaces

The VM is parameterized by six interfaces:
`IdentityModel`, `GuardLayer`, `PersistenceModel`, `EffectRuntime`, `EffectSpec`,
and `VerificationModel`.

`EffectRuntime` and `EffectSpec` are split intentionally:
- `EffectRuntime` contains executable effect semantics (`EffectAction`, `EffectCtx`, `exec`)
- `EffectSpec` contains typing-level effect obligations (`handlerType`)

This file also defines authenticated data structure interfaces (`AuthTree`,
`AccumulatedSet`) and `ScopeId` used for scoped resource views.
-/

/-! ## Shared protocol types -/

abbrev GlobalType := SessionTypes.GlobalType.GlobalType
abbrev LayerId := String

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
  /-- Runtime identifier for this guard layer. -/
  layerId : γ → LayerId
  /-- Resource this layer protects. -/
  Resource : Type
  /-- Evidence produced on successful evaluation. -/
  Evidence : Type
  /-- Open the layer: inspect the resource, produce evidence or abort. -/
  open_ : Resource → Option Evidence
  /-- Close the layer: update the resource after commit. -/
  close : Resource → Evidence → Resource
  /-- Encode evidence for register storage. -/
  encodeEvidence : Evidence → Value
  /-- Decode evidence from a register value. -/
  decodeEvidence : Value → Option Evidence
  /-- Decidable equality on layer tags. -/
  decEq : DecidableEq γ

instance (γ : Type u) [GuardLayer γ] : DecidableEq γ :=
  -- Use the guard layer's decidable equality.
  GuardLayer.decEq

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

def GuardChain.layerIds {γ : Type u} [GuardLayer γ] (chain : GuardChain γ) : List LayerId :=
  -- Extract layer identifiers in order for disjointness checks.
  chain.layers.map GuardLayer.layerId

def GuardChain.wf {γ : Type u} [GuardLayer γ] (chain : GuardChain γ) : Prop :=
  -- Layer identifiers are unique in the chain.
  List.Nodup (GuardChain.layerIds chain)

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
  /-- Delta emitted on session open. -/
  openDelta : SessionId → Delta
  /-- Delta emitted on session close. -/
  closeDelta : SessionId → Delta

-- Runtime effect interface used by executable VM semantics.
class EffectRuntime (ε : Type u) where
  /-- Effect actions and their mutable context. -/
  EffectAction : Type
  EffectCtx : Type
  /-- Execute an action in the effect context. -/
  exec : EffectAction → EffectCtx → EffectCtx

-- Spec-only view of effects (typing obligations).
class EffectSpec (ε : Type u) [EffectRuntime ε] where
  /-- Typing-level handler signature. -/
  handlerType : EffectRuntime.EffectAction ε → LocalType

/-! ## Cryptography and authenticated structures -/

abbrev Data := Value

inductive HashTag where
  -- Domain-separated hash contexts for resources and proofs.
  | merkleNode
  | smtLeaf
  | smtEmpty
  | traceEvent
  | contentId
  | resourceKind
  | commitment
  | nullifier
  deriving Repr, DecidableEq

class VerificationModel (ν : Type u) where
  -- Cryptographic primitives and V1 defaults.
  Hash : Type
  hash : Data → Hash
  hashTagged : HashTag → Data → Hash
  decEqH : DecidableEq Hash
  SigningKey : Type
  VerifyKey : Type
  Signature : Type
  sign : SigningKey → Data → Signature
  verifySignature : VerifyKey → Data → Signature → Bool
  verifyKeyOf : SigningKey → VerifyKey
  CommitmentKey : Type
  Commitment : Type
  CommitmentProof : Type
  Nonce : Type
  NullifierKey : Type
  Nullifier : Type
  commit : CommitmentKey → Data → Nonce → Commitment
  nullify : Data → NullifierKey → Nullifier
  verifyCommitment : Commitment → CommitmentProof → Data → Bool
  decEqC : DecidableEq Commitment
  decEqN : DecidableEq Nullifier
  defaultCommitmentKey : CommitmentKey
  defaultNullifierKey : NullifierKey
  defaultNonce : Nonce

/-! ## Signed message wrapper -/

structure SignedValue (ν : Type u) [VerificationModel ν] where
  -- Payload paired with its authentication tag.
  payload : Value
  signature : VerificationModel.Signature ν

abbrev SignedBuffer (ν : Type u) [VerificationModel ν] :=
  -- Buffer of signed payloads per edge.
  List (SignedValue ν)

abbrev SignedBuffers (ν : Type u) [VerificationModel ν] :=
  -- Edge-indexed signed buffers.
  List (Edge × SignedBuffer ν)

class AuthTree (ν : Type u) [VerificationModel ν] where
  -- Authenticated tree interface for structured data.
  Root : Type
  Leaf : Type
  Path : Type
  verifyPath : Root → Leaf → Path → Bool

class AccumulatedSet (ν : Type u) [VerificationModel ν] where
  -- Accumulated set interface with member/non-member proofs.
  Key : Type
  State : Type
  ProofMember : Type
  ProofNonMember : Type
  empty : State
  keyOfHash : VerificationModel.Hash ν → Key
  insert : State → Key → State
  verifyMember : State → Key → ProofMember → Bool
  verifyNonMember : State → Key → ProofNonMember → Bool

structure ScopeId where
  -- Scope identifier for local resource views.
  id : Nat
  deriving Repr, DecidableEq
