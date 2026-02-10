import Runtime.VM.Model.Config
import Runtime.VM.Composition.DomainComposition
import Runtime.Resources.BufferRA

/-!
# Unit Model

Minimal computable instances for the VM domain interfaces.
-/

/-
The Problem. Testing the VM requires concrete implementations of all domain
interfaces, but full implementations are complex. We need minimal computable
instances that satisfy the interface contracts without introducing complexity.

Solution Structure. Defines marker types (`UnitIdentity`, `UnitGuard`, etc.) with
trivial typeclass instances. Each instance provides no-op implementations: single
site per participant, empty guard layer, no persistence, no effects, no verification.
These enable running the VM in tests without domain-specific behavior.
-/

set_option autoImplicit false

/-! ## Unit model instances -/

structure UnitIdentity where
  -- Marker type for unit identity instances.
  unit : Unit := ()

inductive UnitGuard : Type
  -- Empty guard type for computable tests.

structure UnitPersist where
  -- Marker type for unit persistence instances.
  unit : Unit := ()

inductive UnitEffect : Type
  -- Empty effect type for computable tests.

structure UnitVerify where
  -- Marker type for unit verification instances.
  unit : Unit := ()

instance : IdentityModel UnitIdentity where
  -- Simple identity model: one site per participant.
  ParticipantId := Nat
  SiteId := Nat
  sites := fun p => [p]
  siteName := fun s => toString s
  siteOf := fun _ => none
  siteCapabilities := fun _ => default
  reliableEdges := []
  decEqP := by infer_instance
  decEqS := by infer_instance

instance : GuardLayer UnitGuard where
  -- Empty guard layer avoids identifiers.
  layerId := fun g => nomatch g
  Resource := Unit
  Evidence := Unit
  open_ := fun _ => some ()
  close := fun _ _ => ()
  encodeEvidence := fun _ => Value.unit
  decodeEvidence := fun v =>
    match v with
    | .unit => some ()
    | _ => none
  decEq := by
    intro a
    cases a

instance : PersistenceModel UnitPersist where
  -- Unit persistence model with no-op updates.
  PState := Unit
  Delta := Unit
  SessionState := Unit
  apply := fun _ _ => ()
  derive := fun _ _ => some ()
  empty := ()
  openDelta := fun _ => ()
  closeDelta := fun _ => ()

instance : EffectRuntime UnitEffect where
  -- Unit effect model for computable tests.
  EffectAction := Unit
  EffectCtx := Unit
  exec := fun _ _ => ()

instance : EffectSpec UnitEffect where
  -- Unit effect typing is terminal.
  handlerType := fun _ => LocalType.end_

instance : Inhabited (EffectRuntime.EffectAction UnitEffect) := ⟨()⟩
instance : Inhabited (EffectRuntime.EffectCtx UnitEffect) := ⟨()⟩

instance : VerificationModel UnitVerify where
  -- Unit verification model with unit-valued primitives.
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

instance : AuthTree UnitVerify where
  -- Trivial authenticated tree interface for tests.
  Root := Unit
  Leaf := Unit
  Path := Unit
  verifyPath := fun _ _ _ => true

instance : AccumulatedSet UnitVerify where
  -- Unit accumulated set for computable tests.
  Key := Unit
  State := Unit
  ProofMember := Unit
  ProofNonMember := Unit
  empty := ()
  keyOfHash := fun _ => ()
  insert := fun st _ => st
  verifyMember := fun _ _ _ => true
  verifyNonMember := fun _ _ _ => true

instance : IdentityGuardBridge UnitIdentity UnitGuard where
  -- Map participants into unit guard resources.
  bridge := fun _ => ()

instance : EffectGuardBridge UnitEffect UnitGuard where
  -- Map effects into unit guard resources.
  bridge := fun _ => ()

instance : PersistenceEffectBridge UnitPersist UnitEffect where
  -- Map effects into unit persistence deltas.
  bridge := fun _ => ()

instance : IdentityPersistenceBridge UnitIdentity UnitPersist where
  -- Map participants into unit persistent state.
  bridge := fun _ => ()

instance : IdentityVerificationBridge UnitIdentity UnitVerify where
  -- Map participants into unit verification keys.
  bridge := fun _ => ()

/-! ## Unit configuration -/

def unitGuardChain : GuardChain UnitGuard :=
  { layers := [], active := fun _ => false }

def unitCostModel : CostModel UnitGuard UnitEffect :=
  { stepCost := fun _ => 1
  , minCost := 1
  , defaultBudget := 50
  , hMinCost := by intro _ _; exact Nat.le_refl 1
  , hMinPos := by exact Nat.le_refl 1 }

def unitBufferConfig : BufferConfig :=
  { mode := .fifo, initialCapacity := 16, policy := .block }

def unitFlowPolicy : FlowPolicy :=
  { allowed := fun _ _ => true }

def unitConfig : VMConfig UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify :=
  { bufferConfig := fun _ => unitBufferConfig
  , schedPolicy := .roundRobin
  , violationPolicy := { allow := fun _ => false }
  , flowPolicy := unitFlowPolicy
  , spatialOk := fun _ => true
  , transportOk := fun _ _ => true
  , complianceProof := fun _ => ((), ())
  , maxCoroutines := 8
  , maxSessions := 4
  , guardChain := unitGuardChain
  , guardChainWf := by
      simp [GuardChain.wf, GuardChain.layerIds, unitGuardChain]
  , roleSigningKey := fun _ => ()
  , costModel := unitCostModel
  , speculationEnabled := false }
