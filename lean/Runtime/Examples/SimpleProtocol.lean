import Runtime.VM.Model.Program
import Runtime.VM.Semantics.Exec
import Runtime.VM.Semantics.ExecHelpers
import Runtime.VM.Model.UnitModel
import Runtime.VM.Runtime.Monitor

/-
The Problem. Provide a concrete, runnable VM example that exercises
session opening, send/receive, and offer/choose in a single coroutine.

Solution Structure. Define a tiny two-role protocol, instantiate a
computable test model, and assemble a minimal VM state for tests.
-/

set_option autoImplicit false

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

def exampleCode : List (Instr UnitGuard UnitEffect) :=
  -- Bytecode for a single coroutine running both endpoints.
  [ Instr.open exampleRoles exampleLocalTypes (exampleHandlers 0) exampleDsts
  , Instr.set 2 (.nat 7)
  , Instr.send 0 2
  , Instr.receive 1 3
  , Instr.offer 0 "ok"
  , Instr.choose 1 [("ok", 6)]
  , Instr.halt
  ]

def exampleProgram : Program UnitGuard UnitEffect :=
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

def exampleCoro : CoroutineState UnitGuard UnitEffect :=
  -- Single ready coroutine with a fresh register file.
  { id := 0
  , programId := 0
  , pc := 0
  , regs := Array.replicate 6 .unit
  , status := .ready
  , effectCtx := ()
  , ownedEndpoints := []
  , progressTokens := [exampleToken]
  , knowledgeSet := []
  , costBudget := unitConfig.costModel.defaultBudget
  , specState := none }

def exampleSched : SchedState UnitGuard :=
  -- Minimal scheduler state with the single coroutine ready.
  { policy := unitConfig.schedPolicy
  , readyQueue := [0]
  , blockedSet := {}
  , timeslice := 1
  , stepCount := 0 }

def exampleMonitor : SessionMonitor UnitGuard :=
  -- Permissive monitor for the example VM run.
  { step := fun sk => some sk }

def exampleState : VMState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify :=
  -- Assemble the initial VM state for the example program.
  { config := unitConfig
  , code := exampleProgram
  , programs := #[exampleProgram]
  , coroutines := #[exampleCoro]
  , buffers := []
  , persistent := ()
  , nextCoroId := 1
  , nextSessionId := 0
  , arena := exampleArena
  , sessions := []
  , resourceStates := {}
  , guardResources := []
  , sched := exampleSched
  , monitor := exampleMonitor
  , obsTrace := []
  , clock := 0
  , crashedSites := []
  , partitionedEdges := []
  , mask := ()
  , ghostSessions := ()
  , progressSupply := () }
