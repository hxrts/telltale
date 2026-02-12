import Runtime.VM.Model.TypeClasses

/-! # Domain Model Composition

Unit, sum, and product instances for all five domain interfaces, plus the bridge
classes that connect them. This is the Lean counterpart of `runtime.md` §20.

**Unit instances** (`GuardLayer Unit`, `EffectRuntime Unit`, `VerificationModel Unit`,
`AuthTree Unit`, `AccumulatedSet Unit`) provide trivial no-op implementations used
as identity elements in composition and as defaults for testing.

**Sum/product instances** let independent domain models be combined. Sum instances
dispatch on the chosen side. Product instances run both components. This enables
protocol federation: a VM configured with `EffectRuntime (ε₁ ⊕ ε₂)` can execute
effects from either domain without either domain knowing about the other.

**Bridge classes** (`IdentityGuardBridge`, `EffectGuardBridge`, `PersistenceEffectBridge`,
`IdentityPersistenceBridge`, `IdentityVerificationBridge`) capture the cross-model
obligations that domain instantiations must satisfy. Bridge composition instances
automatically lift bridges over sums so that composed domains inherit their
component bridges. -/

/-
The Problem. The VM is parameterized over five domain interfaces (identity, guard,
persistence, effect, verification). We need composition operators to combine
independent domain implementations while preserving their contracts.

Solution Structure. Provides unit instances as identity elements, sum instances for
coproduct composition (dispatch on tag), and product instances for parallel execution.
Bridge classes define cross-model obligations. Composition instances automatically
lift bridges over sums, enabling protocol federation across domains.
-/

set_option autoImplicit false

universe u

/-! ## Unit instances -/

def combineLayerId (id₁ id₂ : LayerId) : LayerId :=
  -- Deterministic layer identifier combination for product guards.
  id₁ ++ "::" ++ id₂

instance : GuardLayer Unit where
  -- Unit guard layer: trivial id and resource.
  layerId := fun _ => "unit"
  Resource := Unit
  Evidence := Unit
  open_ := fun _ => some ()
  close := fun _ _ => ()
  encodeEvidence := fun _ => Value.unit
  decodeEvidence := fun v =>
    -- Only unit values decode as unit evidence.
    match v with
    | .unit => some ()
    | _ => none
  decEq := by infer_instance

/-! ## Unit Effect Instances -/

instance : EffectRuntime Unit where
  -- Unit effect model: no-op effects.
  EffectAction := Unit
  EffectCtx := Unit
  exec := fun _ _ => ()

instance : EffectSpec Unit where
  -- Unit effect typing: handlers are terminal.
  handlerType := fun _ => LocalType.end_

/-! ## Unit Verification/Commitment Instances -/

instance : VerificationModel Unit where
  -- Unit verification model: trivial cryptography.
  Hash := Unit
  hash := fun _ => ()
  hashTagged := fun _ _ => ()
  decEqH := by infer_instance
  SigningKey := Unit
  VerifyKey := Unit
  Signature := Unit
  sign := fun _ _ => ()
  verifySignature := fun _ _ _ => true
  verifyKeyOf := fun _ => ()
  CommitmentKey := Unit
  Commitment := Unit
  CommitmentProof := Unit
  Nonce := Unit
  NullifierKey := Unit
  Nullifier := Unit
  commit := fun _ _ _ => ()
  nullify := fun _ _ => ()
  verifyCommitment := fun _ _ _ => true
  decEqC := by infer_instance
  decEqN := by infer_instance
  defaultCommitmentKey := ()
  defaultNullifierKey := ()
  defaultNonce := ()

/-! ## Unit Authenticated-State Instances -/

instance : AuthTree Unit where
  -- Unit authenticated tree: all proofs validate.
  Root := Unit
  Leaf := Unit
  Path := Unit
  verifyPath := fun _ _ _ => true

instance : AccumulatedSet Unit where
  -- Unit accumulated set: membership is vacuous.
  Key := Unit
  State := Unit
  ProofMember := Unit
  ProofNonMember := Unit
  empty := ()
  keyOfHash := fun _ => ()
  insert := fun st _ => st
  verifyMember := fun _ _ _ => true
  verifyNonMember := fun _ _ _ => true

/-! ## Composed instances -/

private def sumSites (ι₁ ι₂ : Type u) [IdentityModel ι₁] [IdentityModel ι₂] :
    (Sum (IdentityModel.ParticipantId ι₁) (IdentityModel.ParticipantId ι₂) → List (Sum (IdentityModel.SiteId ι₁) (IdentityModel.SiteId ι₂))) :=
  -- Lift sites into the sum identity model.
  fun
    | Sum.inl p => (IdentityModel.sites (ι:=ι₁) p).map Sum.inl
    | Sum.inr p => (IdentityModel.sites (ι:=ι₂) p).map Sum.inr

private def sumSiteName (ι₁ ι₂ : Type u) [IdentityModel ι₁] [IdentityModel ι₂] :
    (Sum (IdentityModel.SiteId ι₁) (IdentityModel.SiteId ι₂) → Site) :=
  -- Lift site names into the sum identity model.
  fun
    | Sum.inl s => IdentityModel.siteName (ι:=ι₁) s
    | Sum.inr s => IdentityModel.siteName (ι:=ι₂) s

private def sumSiteOf (ι₁ ι₂ : Type u) [IdentityModel ι₁] [IdentityModel ι₂] :
    Site → Option (Sum (IdentityModel.SiteId ι₁) (IdentityModel.SiteId ι₂)) :=
  -- Prefer the left model when both interpret a site name.
  fun site =>
    match IdentityModel.siteOf (ι:=ι₁) site with
    | some s => some (Sum.inl s)
    | none => (IdentityModel.siteOf (ι:=ι₂) site).map Sum.inr

private def sumSiteCapabilities (ι₁ ι₂ : Type u) [IdentityModel ι₁] [IdentityModel ι₂] :
    (Sum (IdentityModel.SiteId ι₁) (IdentityModel.SiteId ι₂) → SiteCapabilities) :=
  -- Lift site capabilities into the sum identity model.
  fun
    | Sum.inl s => IdentityModel.siteCapabilities (ι:=ι₁) s
    | Sum.inr s => IdentityModel.siteCapabilities (ι:=ι₂) s

private def sumReliableEdges (ι₁ ι₂ : Type u) [IdentityModel ι₁] [IdentityModel ι₂] :
    List (Sum (IdentityModel.SiteId ι₁) (IdentityModel.SiteId ι₂) ×
          Sum (IdentityModel.SiteId ι₁) (IdentityModel.SiteId ι₂)) :=
  -- Lift reliable edges into the sum identity model.
  (IdentityModel.reliableEdges (ι:=ι₁)).map (fun p => (Sum.inl p.1, Sum.inl p.2)) ++
  (IdentityModel.reliableEdges (ι:=ι₂)).map (fun p => (Sum.inr p.1, Sum.inr p.2))

private def sumDecEqP (ι₁ ι₂ : Type u) [IdentityModel ι₁] [IdentityModel ι₂] :
    DecidableEq (Sum (IdentityModel.ParticipantId ι₁) (IdentityModel.ParticipantId ι₂)) := by
  -- Build decidable equality for summed participants.
  classical
  let _ : DecidableEq (IdentityModel.ParticipantId ι₁) := IdentityModel.decEqP (ι:=ι₁)
  let _ : DecidableEq (IdentityModel.ParticipantId ι₂) := IdentityModel.decEqP (ι:=ι₂)
  exact instDecidableEqSum

private def sumDecEqS (ι₁ ι₂ : Type u) [IdentityModel ι₁] [IdentityModel ι₂] :
    DecidableEq (Sum (IdentityModel.SiteId ι₁) (IdentityModel.SiteId ι₂)) := by
  -- Build decidable equality for summed sites.
  classical
  let _ : DecidableEq (IdentityModel.SiteId ι₁) := IdentityModel.decEqS (ι:=ι₁)
  let _ : DecidableEq (IdentityModel.SiteId ι₂) := IdentityModel.decEqS (ι:=ι₂)
  exact instDecidableEqSum

instance instIdentityModelSum (ι₁ ι₂ : Type u)
    [IdentityModel ι₁] [IdentityModel ι₂] : IdentityModel (Sum ι₁ ι₂) where
  -- Sum identity model: dispatch on the chosen side.
  ParticipantId := Sum (IdentityModel.ParticipantId ι₁) (IdentityModel.ParticipantId ι₂)
  SiteId := Sum (IdentityModel.SiteId ι₁) (IdentityModel.SiteId ι₂)
  sites := sumSites ι₁ ι₂
  siteName := sumSiteName ι₁ ι₂
  siteOf := sumSiteOf ι₁ ι₂
  siteCapabilities := sumSiteCapabilities ι₁ ι₂
  reliableEdges := sumReliableEdges ι₁ ι₂
  decEqP := sumDecEqP ι₁ ι₂
  decEqS := sumDecEqS ι₁ ι₂

instance instEffectRuntimeSum (ε₁ ε₂ : Type u) [EffectRuntime ε₁] [EffectRuntime ε₂] :
    EffectRuntime (Sum ε₁ ε₂) where
  -- Sum effects dispatch to the corresponding component model.
  EffectAction := Sum (EffectRuntime.EffectAction ε₁) (EffectRuntime.EffectAction ε₂)
  EffectCtx := EffectRuntime.EffectCtx ε₁ × EffectRuntime.EffectCtx ε₂
  exec := fun a ctx =>
    match a, ctx with
    | Sum.inl a1, (c1, c2) => (EffectRuntime.exec a1 c1, c2)
    | Sum.inr a2, (c1, c2) => (c1, EffectRuntime.exec a2 c2)

instance instEffectSpecSum (ε₁ ε₂ : Type u)
    [EffectRuntime ε₁] [EffectRuntime ε₂] [EffectSpec ε₁] [EffectSpec ε₂] :
    EffectSpec (Sum ε₁ ε₂) where
  -- Sum typing dispatches to the corresponding effect spec.
  handlerType := fun a =>
    match a with
    | Sum.inl a1 => EffectSpec.handlerType a1
    | Sum.inr a2 => EffectSpec.handlerType a2

instance instEffectRuntimeProd (ε₁ ε₂ : Type u) [EffectRuntime ε₁] [EffectRuntime ε₂] :
    EffectRuntime (ε₁ × ε₂) where
  -- Product effects run both components.
  EffectAction := EffectRuntime.EffectAction ε₁ × EffectRuntime.EffectAction ε₂
  EffectCtx := EffectRuntime.EffectCtx ε₁ × EffectRuntime.EffectCtx ε₂
  exec := fun a ctx =>
    match a, ctx with
    | (a1, a2), (c1, c2) => (EffectRuntime.exec a1 c1, EffectRuntime.exec a2 c2)

instance instEffectSpecProd (ε₁ ε₂ : Type u)
    [EffectRuntime ε₁] [EffectRuntime ε₂] [EffectSpec ε₁] [EffectSpec ε₂] :
    EffectSpec (ε₁ × ε₂) where
  -- V1 product handlers are conservatively typed as terminal.
  handlerType := fun _ => LocalType.end_

instance instGuardLayerProd (γ₁ γ₂ : Type u) [GuardLayer γ₁] [GuardLayer γ₂] :
    GuardLayer (γ₁ × γ₂) where
  -- Product layer combines identifiers to keep layers distinct.
  layerId := fun g => combineLayerId (GuardLayer.layerId g.1) (GuardLayer.layerId g.2)
  Resource := GuardLayer.Resource γ₁ × GuardLayer.Resource γ₂
  Evidence := GuardLayer.Evidence γ₁ × GuardLayer.Evidence γ₂
  open_ := fun r =>
    match GuardLayer.open_ r.1, GuardLayer.open_ r.2 with
    | some e1, some e2 => some (e1, e2)
    | _, _ => none
  close := fun r e =>
    (GuardLayer.close r.1 e.1, GuardLayer.close r.2 e.2)
  encodeEvidence := fun e =>
    -- Encode pair evidence as a value product.
    Value.prod (GuardLayer.encodeEvidence e.1) (GuardLayer.encodeEvidence e.2)
  decodeEvidence := fun v =>
    -- Decode a value product into pair evidence.
    match v with
    | .prod v1 v2 =>
        match GuardLayer.decodeEvidence v1, GuardLayer.decodeEvidence v2 with
        | some e1, some e2 => some (e1, e2)
        | _, _ => none
    | _ => none
  decEq := by
    -- Use product equality derived from component layers.
    classical
    infer_instance

instance instPersistenceModelProd (π₁ π₂ : Type u)
    [PersistenceModel π₁] [PersistenceModel π₂] : PersistenceModel (π₁ × π₂) where
  -- Product persistence model: apply and derive component-wise.
  PState := PersistenceModel.PState π₁ × PersistenceModel.PState π₂
  Delta := PersistenceModel.Delta π₁ × PersistenceModel.Delta π₂
  SessionState := PersistenceModel.SessionState π₁ × PersistenceModel.SessionState π₂
  apply := fun st δ =>
    (PersistenceModel.apply st.1 δ.1, PersistenceModel.apply st.2 δ.2)
  derive := fun st sid =>
    match PersistenceModel.derive st.1 sid, PersistenceModel.derive st.2 sid with
    | some s1, some s2 => some (s1, s2)
    | _, _ => none
  empty := (PersistenceModel.empty, PersistenceModel.empty)
  openDelta := fun sid =>
    (PersistenceModel.openDelta sid, PersistenceModel.openDelta sid)
  closeDelta := fun sid =>
    (PersistenceModel.closeDelta sid, PersistenceModel.closeDelta sid)

/-! ## Bridge classes -/

class IdentityGuardBridge (ι : Type u) (γ : Type u) [IdentityModel ι] [GuardLayer γ] where
  -- Map identities into guard resources.
  bridge : IdentityModel.ParticipantId ι → GuardLayer.Resource γ

class EffectGuardBridge (ε : Type u) (γ : Type u) [EffectRuntime ε] [GuardLayer γ] where
  -- Map effect actions into guard resources.
  bridge : EffectRuntime.EffectAction ε → GuardLayer.Resource γ

class PersistenceEffectBridge (π : Type u) (ε : Type u) [PersistenceModel π] [EffectRuntime ε] where
  -- Map effects into persistence deltas.
  bridge : EffectRuntime.EffectAction ε → PersistenceModel.Delta π

class IdentityPersistenceBridge (ι : Type u) (π : Type u) [IdentityModel ι] [PersistenceModel π] where
  -- Map identities into persistent state.
  bridge : IdentityModel.ParticipantId ι → PersistenceModel.PState π

class IdentityVerificationBridge (ι : Type u) (ν : Type u)
    [IdentityModel ι] [VerificationModel ν] where
  -- Map identities into verification keys.
  bridge : IdentityModel.ParticipantId ι → VerificationModel.VerifyKey ν

/-! ## Bridge composition -/

instance instIdentityGuardBridgeSum (ι₁ ι₂ γ : Type u)
    [IdentityModel ι₁] [IdentityModel ι₂] [GuardLayer γ]
    [IdentityGuardBridge ι₁ γ] [IdentityGuardBridge ι₂ γ] :
    IdentityGuardBridge (Sum ι₁ ι₂) γ where
  -- Lift identity-to-guard bridges over identity sums.
  bridge := fun
    | Sum.inl p => IdentityGuardBridge.bridge (ι:=ι₁) p
    | Sum.inr p => IdentityGuardBridge.bridge (ι:=ι₂) p

instance instEffectGuardBridgeSum (ε₁ ε₂ γ : Type u)
    [EffectRuntime ε₁] [EffectRuntime ε₂] [GuardLayer γ]
    [EffectGuardBridge ε₁ γ] [EffectGuardBridge ε₂ γ] :
    EffectGuardBridge (Sum ε₁ ε₂) γ where
  -- Lift effect-to-guard bridges over effect sums.
  bridge := fun
    | Sum.inl a => EffectGuardBridge.bridge (ε:=ε₁) a
    | Sum.inr a => EffectGuardBridge.bridge (ε:=ε₂) a

instance instPersistenceEffectBridgeSum (π ε₁ ε₂ : Type u)
    [PersistenceModel π] [EffectRuntime ε₁] [EffectRuntime ε₂]
    [PersistenceEffectBridge π ε₁] [PersistenceEffectBridge π ε₂] :
    PersistenceEffectBridge π (Sum ε₁ ε₂) where
  -- Lift effect-to-persistence bridges over effect sums.
  bridge := fun
    | Sum.inl a => PersistenceEffectBridge.bridge (ε:=ε₁) a
    | Sum.inr a => PersistenceEffectBridge.bridge (ε:=ε₂) a

instance instIdentityPersistenceBridgeSum (ι₁ ι₂ π : Type u)
    [IdentityModel ι₁] [IdentityModel ι₂] [PersistenceModel π]
    [IdentityPersistenceBridge ι₁ π] [IdentityPersistenceBridge ι₂ π] :
    IdentityPersistenceBridge (Sum ι₁ ι₂) π where
  -- Lift identity-to-persistence bridges over identity sums.
  bridge := fun
    | Sum.inl p => IdentityPersistenceBridge.bridge (ι:=ι₁) p
    | Sum.inr p => IdentityPersistenceBridge.bridge (ι:=ι₂) p

instance instIdentityVerificationBridgeSum (ι₁ ι₂ ν : Type u)
    [IdentityModel ι₁] [IdentityModel ι₂] [VerificationModel ν]
    [IdentityVerificationBridge ι₁ ν] [IdentityVerificationBridge ι₂ ν] :
    IdentityVerificationBridge (Sum ι₁ ι₂) ν where
  -- Lift identity-to-verification bridges over identity sums.
  bridge := fun
    | Sum.inl p => IdentityVerificationBridge.bridge (ι:=ι₁) p
    | Sum.inr p => IdentityVerificationBridge.bridge (ι:=ι₂) p


/- Proof-level composition claims and witnesses live in:
`Runtime.Proofs.VM.DomainComposition`.
-/
