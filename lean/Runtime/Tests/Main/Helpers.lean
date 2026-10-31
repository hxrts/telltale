
import Runtime.Examples.SimpleProtocol
import Runtime.ProtocolMachine.Runtime.Runner
import Runtime.ProtocolMachine.Runtime.ThreadedRunner
import Runtime.ProtocolMachine.Semantics.ExecSpeculation
import Runtime.ProtocolMachine.Semantics.ExecOwnership
import Runtime.ProtocolMachine.Runtime.Loader
import Runtime.ProtocolMachine.Runtime.Failure
import Runtime.Adequacy.EnvelopeCore
import Runtime.Proofs.Contracts.RuntimeContracts
import Runtime.Proofs.Examples.ComposedProofPack
import Runtime.Proofs.TheoremPack.API
import SessionTypes.LocalTypeR

/-! # Runtime tests: shared helpers

Trace tagging, empty protocol machine state, sample images, and scheduler/speculation
fixtures shared by the `runtime_tests` executable (`Runtime.Tests.Main`).
-/

set_option autoImplicit false
set_option maxRecDepth 4096

open SessionTypes.LocalTypeR
open SessionTypes.GlobalType

/-- Tag observable events for comparison (UnitEffect only). -/
def obsTag : ObsEvent UnitEffect → String
  | .sent _ _ _ _ => "sent"
  | .received _ _ _ _ => "received"
  | .offered _ _ => "offered"
  | .chose _ _ => "chose"
  | .acquired _ _ => "acquired"
  | .released _ _ => "released"
  | .invoked _ _ => "invoked"
  | .opened _ _ => "opened"
  | .closed _ => "closed"
  | .epochAdvanced _ _ => "epoch"
  | .transferred _ _ _ => "transferred"
  | .forked _ _ => "forked"
  | .joined _ => "joined"
  | .aborted _ => "aborted"
  | .sessionTerminal _ _ => "session_terminal"
  | .tagged _ => "tagged"
  | .checked _ _ => "checked"
  | .failureBranchEntered _ _ _ => "failure_branch_entered"
  | .timeoutIssued _ _ _ => "timeout_issued"
  | .cancellationRequested _ _ _ _ => "cancellation_requested"
  | .cancelled _ _ _ => "cancelled"

/-- Extract tags from a filtered trace (UnitEffect only). -/
def traceTags (trace : List (TickedObsEvent UnitEffect)) : List String :=
  trace.map (fun ev => obsTag ev.event)

/-- Minimal empty protocol machine state for loading choreographies. -/
def emptyState : ProtocolMachineState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify :=
  { config := unitConfig
  , code := exampleProgram
  , programs := #[]
  , coroutines := #[]
  , buffers := []
  , persistent := ()
  , nextCoroId := 0
  , nextSessionId := 0
  , arena := exampleArena
  , sessions := []
  , resourceStates := {}
  , guardResources := []
  , sched := { policy := unitConfig.schedPolicy, readyQueue := [], blockedSet := {}, timeslice := 1, stepCount := 0 }
  , monitor := exampleMonitor
  , obsTrace := []
  , clock := 0
  , crashedSites := []
  , partitionedEdges := []
  , mask := ()
  , ghostSessions := default
  , progressSupply := () }

def withCommReplayMode
    (st : ProtocolMachineState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify)
    (mode : CommunicationReplayMode) :
    ProtocolMachineState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify :=
  { st with config := { st.config with communicationReplayMode := mode } }

def sampleCommIdentity (seqNo : Nat) : CommunicationIdentity :=
  { sid := 0
  , sender := "A"
  , receiver := "B"
  , stepKind := .receive
  , label := "recv"
  , payloadDigest := communicationIdentityPayloadDigest (.nat 7)
  , seqNo := seqNo }

/-- Simple two-party LocalTypeR image. -/
def twoPartyImage : CodeImage UnitGuard UnitEffect :=
  let lbl : SessionTypes.GlobalType.Label := { name := "msg" }
  let ltA : LocalTypeR := .send "B" [(lbl, none, .end)]
  let ltB : LocalTypeR := .recv "A" [(lbl, none, .end)]
  CodeImage.fromLocalTypes [ ("A", ltA), ("B", ltB) ] .end

/-- Test helper: assert a boolean. -/
def expect (ok : Bool) (msg : String) : IO Unit :=
/- ## Structured Block 2 -/
  if ok then pure () else throw (IO.userError msg)

def mkReadyCoro (id : CoroutineId) (tokens : List ProgressToken := []) :
    CoroutineState UnitGuard UnitEffect :=
  { id := id
  , programId := 0
  , pc := 0
  , regs := Array.replicate 8 .unit
  , status := .ready
  , effectCtx := default
  , ownedEndpoints := []
  , progressTokens := tokens
  , knowledgeSet := []
  , costBudget := unitConfig.costModel.defaultBudget
  , specState := none }

def withSpecConfig
    (st : ProtocolMachineState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify)
    (enabled : Bool) (maxDepth : Nat) :
    ProtocolMachineState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify :=
  { st with
      config := { st.config with speculationEnabled := enabled, maxSpeculationDepth := maxDepth } }

def mkForkOperandCoro (id : CoroutineId) (ghostSid : Nat)
    (spec : Option SpeculationState := none) :
    CoroutineState UnitGuard UnitEffect :=
  let regs : RegFile := #[.nat ghostSid, .unit, .unit, .unit, .unit, .unit, .unit, .unit]
  { mkReadyCoro id with regs := regs, specState := spec }

def isSpecFault (res : ExecResult UnitGuard UnitEffect) : Bool :=
  match res.status with
  | .faulted (.specFault _) => true
  | _ => false

def hasTransferFaultMsg (res : ExecResult UnitGuard UnitEffect) (msg : String) : Bool :=
  match res.status with
  | .faulted (.transferFault m) => m = msg
  | _ => false

def schedulerTestState (policy : SchedPolicy) (allTokens : Bool := false) :
    ProtocolMachineState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify :=
  let token : ProgressToken := { sid := 0, endpoint := { sid := 0, role := "B" } }
  let tokensFor := fun (cid : CoroutineId) =>
    if allTokens || cid = 3 then [token] else []
  let coros : Array (CoroutineState UnitGuard UnitEffect) :=
    #[ mkReadyCoro 0 (tokensFor 0)
     , mkReadyCoro 1 (tokensFor 1)
     , mkReadyCoro 2 (tokensFor 2)
     , mkReadyCoro 3 (tokensFor 3) ]
  let laneMap : LaneOfMap :=
    ((({} : LaneOfMap).insert 0 0).insert 1 1).insert 2 0 |>.insert 3 1
  let sched0 : SchedState UnitGuard :=
    { policy := policy
    , readyQueue := [0, 1, 2, 3]
    , blockedSet := {}
    , laneOf := laneMap
    , timeslice := 1
    , stepCount := 0 }
  { emptyState with
      coroutines := coros
      nextCoroId := coros.size
      sched := syncLaneViews sched0 }

def collectSchedulePicks (fuel : Nat)
    (st : ProtocolMachineState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify)
    (acc : List CoroutineId := []) : List CoroutineId :=
  match fuel with
  | 0 => acc.reverse
  | fuel' + 1 =>
      match schedule st with
      | none => acc.reverse
      | some (cid, st') =>
          let sched' := updateAfterStep st'.sched cid .continue
          collectSchedulePicks fuel' { st' with sched := sched' } (cid :: acc)

theorem sched_round_one_eq_sched_round_one
    (st : ProtocolMachineState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify) :
    schedRoundOne st = schedRound 1 st := by
  simp [schedRound]
