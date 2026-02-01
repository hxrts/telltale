import Runtime.VM.Program
import Runtime.VM.Exec
import Runtime.VM.ExecHelpers
import Runtime.VM.Config
import Runtime.Resources.BufferRA
import Runtime.Monitor.Monitor

/-
The Problem. Provide a concrete, runnable VM example that exercises
session opening, send/recv, and offer/choose in a single coroutine.

Solution Structure. Define a tiny two-role protocol, instantiate a
computable test model, and assemble a minimal VM state for tests.
-/

set_option autoImplicit false

/-! ## Test model instances -/

structure TestIdentity where
  -- Marker type for test identity instances.
  unit : Unit := ()

inductive TestGuard : Type
  -- Empty guard type for computable tests.

structure TestPersist where
  -- Marker type for test persistence instances.
  unit : Unit := ()

inductive TestEffect : Type
  -- Empty effect type for computable tests.

structure TestVerify where
  -- Marker type for test verification instances.
  unit : Unit := ()

instance : IdentityModel TestIdentity where
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

instance : GuardLayer TestGuard where
  -- Empty guard layer avoids noncomputable identifiers.
  layerId := fun g => nomatch g
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
  decEq := by
    -- Empty type has decidable equality.
    intro a
    cases a

instance : PersistenceModel TestPersist where
  -- Unit persistence model with no-op updates.
  PState := Unit
  Delta := Unit
  SessionState := Unit
  apply := fun _ _ => ()
  derive := fun _ _ => some ()
  empty := ()
  openDelta := fun _ => ()
  closeDelta := fun _ => ()

instance : EffectModel TestEffect where
  -- Empty effect model avoids noncomputable iProp constants.
  EffectAction := Empty
  EffectCtx := Unit
  exec := fun a _ => nomatch a
  handlerType := fun a => nomatch a

instance : VerificationModel TestVerify where
  -- Test verification model with unit-valued primitives.
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

instance : AuthTree TestVerify where
  -- Trivial authenticated tree interface for tests.
  Root := Unit
  Leaf := Unit
  Path := Unit
  verifyPath := fun _ _ _ => true

instance : AccumulatedSet TestVerify where
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

instance : IdentityGuardBridge TestIdentity TestGuard where
  -- Map participants into unit guard resources.
  bridge := fun _ => ()

instance : EffectGuardBridge TestEffect TestGuard where
  -- Map effects into unit guard resources.
  bridge := fun _ => ()

instance : PersistenceEffectBridge TestPersist TestEffect where
  -- Map effects into unit persistence deltas.
  bridge := fun _ => ()

instance : IdentityPersistenceBridge TestIdentity TestPersist where
  -- Map participants into unit persistent state.
  bridge := fun _ => ()

instance : IdentityVerificationBridge TestIdentity TestVerify where
  -- Map participants into unit verification keys.
  bridge := fun _ => ()

/-! ## Test configuration -/

def testGuardChain : GuardChain TestGuard :=
  -- Empty guard chain for tests.
  { layers := [], active := fun _ => false }

def testCostModel : CostModel TestGuard TestEffect :=
  -- Constant-cost model for tests.
  { stepCost := fun _ => 1
  , minCost := 1
  , defaultBudget := 50
  , hMinCost := by intro _ _; exact Nat.le_refl 1
  , hMinPos := by exact Nat.le_refl 1 }

def testBufferConfig : BufferConfig :=
  -- Default FIFO buffers with blocking backpressure.
  { mode := .fifo, initialCapacity := 16, policy := .block }

def testFlowPolicy : FlowPolicy :=
  -- Allow all knowledge flows in tests.
  { allowed := fun _ _ => true }

def testConfig : VMConfig TestIdentity TestGuard TestPersist TestEffect TestVerify :=
  -- Minimal VM config for the example program.
  { bufferConfig := fun _ => testBufferConfig
  , schedPolicy := .roundRobin
  , violationPolicy := { allow := fun _ => false }
  , flowPolicy := testFlowPolicy
  , spatialOk := fun _ => true
  , transportOk := fun _ _ => true
  , complianceProof := fun _ => ((), ())
  , maxCoroutines := 8
  , maxSessions := 4
  , guardChain := testGuardChain
  , guardChainWf := by
      -- Empty guard chain is trivially well-formed.
      simp [GuardChain.wf, GuardChain.layerIds, testGuardChain]
  , roleSigningKey := fun _ => ()
  , costModel := testCostModel
  , speculationEnabled := false }

/-! ## Example protocol types -/

def aliceType : LocalType :=
  -- Alice sends a nat and then offers a single label.
  LocalType.send "Bob" .nat
    (LocalType.select "Bob" [("ok", LocalType.end_)])

def bobType : LocalType :=
  -- Bob receives a nat and then branches on a single label.
  LocalType.recv "Alice" .nat
    (LocalType.branch "Alice" [("ok", LocalType.end_)])

def exampleRoles : RoleSet :=
  -- Two-role session for the example.
  ["Alice", "Bob"]

def exampleLocalTypes : List (Role × LocalType) :=
  -- Local types for Alice and Bob in role order.
  [("Alice", aliceType), ("Bob", bobType)]

def exampleHandlers (sid : SessionId) : List (Edge × HandlerId) :=
  -- Bind all session edges to a single handler id for V1.
  [({ sid := sid, sender := "Alice", receiver := "Alice" }, 0),
    ({ sid := sid, sender := "Alice", receiver := "Bob" }, 0),
    ({ sid := sid, sender := "Bob", receiver := "Alice" }, 0),
    ({ sid := sid, sender := "Bob", receiver := "Bob" }, 0)]

def exampleDsts : List (Role × Reg) :=
  -- Destination registers for the opened endpoints.
  [("Alice", 0), ("Bob", 1)]

/-! ## Example program -/

def exampleCode : List (Instr TestGuard TestEffect) :=
  -- Bytecode for a single coroutine running both endpoints.
  [ Instr.open exampleRoles exampleLocalTypes (exampleHandlers 0) exampleDsts
  , Instr.loadImm 2 (.nat 7)
  , Instr.send 0 2
  , Instr.recv 1 3
  , Instr.offer 0 "ok"
  , Instr.choose 1 [("ok", 6)]
  , Instr.halt
  ]

def exampleProgram : Program TestGuard TestEffect :=
  -- Package the bytecode with metadata and entry points.
  { code := exampleCode.toArray
  , entryPoints := exampleRoles.map (fun r => (r, 0))
  , localTypes := exampleLocalTypes
  , handlerTypes := []
  , metadata := { name := "example", version := 1, sourceHash := 0 } }

/-! ## Example VM state -/

def exampleArena : Arena :=
  -- Empty arena with zero capacity for the example.
  { slots := #[], nextFree := 0, capacity := 0, inv := by exact Nat.le_refl 0 }

def exampleToken : ProgressToken :=
  -- Progress token for Bob's receive endpoint in session 0.
  { sid := 0, endpoint := { sid := 0, role := "Bob" } }

def exampleCoro : CoroutineState TestGuard TestEffect :=
  -- Single ready coroutine with a fresh register file.
  { id := 0
  , pc := 0
  , regs := Array.replicate 6 .unit
  , status := .ready
  , effectCtx := ()
  , ownedEndpoints := []
  , progressTokens := [exampleToken]
  , knowledgeSet := []
  , costBudget := testConfig.costModel.defaultBudget
  , specState := none }

def exampleSched : SchedState TestGuard :=
  -- Minimal scheduler state with the single coroutine ready.
  { policy := testConfig.schedPolicy
  , readyQueue := [0]
  , blockedSet := []
  , timeslice := 1
  , stepCount := 0 }

def exampleMonitor : SessionMonitor TestGuard :=
  -- Permissive monitor for the example VM run.
  { step := fun sk => some sk }

def exampleState : VMState TestIdentity TestGuard TestPersist TestEffect TestVerify :=
  -- Assemble the initial VM state for the example program.
  { config := testConfig
  , code := exampleProgram
  , programs := #[]
  , coroutines := #[exampleCoro]
  , buffers := []
  , persistent := ()
  , nextCoroId := 1
  , nextSessionId := 0
  , arena := exampleArena
  , sessions := []
  , resourceStates := []
  , guardResources := []
  , sched := exampleSched
  , monitor := exampleMonitor
  , obsTrace := []
  , crashedSites := []
  , partitionedEdges := []
  , mask := ()
  , ghostSessions := ()
  , progressSupply := () }
