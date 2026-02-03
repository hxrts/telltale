import Runtime.Examples.SimpleProtocol
import Runtime.VM.RunScheduled
import Runtime.VM.LoadChoreography
import SessionTypes.LocalTypeR
import SessionTypes.GlobalType

/-
Executable Lean tests for the scheduled VM runner.
-/

set_option autoImplicit false

open SessionTypes.LocalTypeR
open SessionTypes.GlobalType

/-- Tag observable events for comparison (UnitEffect only). -/
def obsTag : ObsEvent UnitEffect → String
  | .sent _ _ _ => "sent"
  | .received _ _ _ => "received"
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
  | .tagged _ => "tagged"
  | .checked _ _ => "checked"

/-- Extract tags from a filtered trace (UnitEffect only). -/
def traceTags (trace : List (TickedObsEvent UnitEffect)) : List String :=
  trace.map (fun ev => obsTag ev.event)

/-- Minimal empty VM state for loading choreographies. -/
def emptyState : VMState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify :=
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
  , resourceStates := []
  , guardResources := []
  , sched := { policy := unitConfig.schedPolicy, readyQueue := [], blockedSet := [], timeslice := 1, stepCount := 0 }
  , monitor := exampleMonitor
  , obsTrace := []
  , clock := 0
  , crashedSites := []
  , partitionedEdges := []
  , mask := ()
  , ghostSessions := ()
  , progressSupply := () }

/-- Simple two-party LocalTypeR image. -/
def twoPartyImage : CodeImage UnitGuard UnitEffect :=
  let lbl : SessionTypes.GlobalType.Label := { name := "msg" }
  let ltA : LocalTypeR := .send "B" [(lbl, none, .end)]
  let ltB : LocalTypeR := .recv "A" [(lbl, none, .end)]
  CodeImage.fromLocalTypes [ ("A", ltA), ("B", ltB) ] .end

/-- Test helper: assert a boolean. -/
def expect (ok : Bool) (msg : String) : IO Unit :=
  if ok then pure () else throw (IO.userError msg)

/-- Main test entry point. -/
def main : IO Unit := do
  -- Test 1: N=1, single protocol.
  let (st1, _) := loadChoreography emptyState twoPartyImage
  let st1' := runScheduled 50 1 st1
  expect (allTerminal st1') "N=1: not all done"

  -- Test 2: N=∞ (use large N), single protocol.
  let (st2, _) := loadChoreography emptyState twoPartyImage
  let st2' := runScheduled 50 100 st2
  expect (allTerminal st2') "N=∞: not all done"

  -- Test 3: N=1 and N=∞, multi-session, per-session traces match.
  let (st3, sid1) := loadChoreography emptyState twoPartyImage
  let (st4, sid2) := loadChoreography st3 twoPartyImage
  let seq := runScheduled 100 1 st4
  let par := runScheduled 100 100 st4
  let seqTrace := Runtime.VM.normalizeTrace seq.obsTrace
  let parTrace := Runtime.VM.normalizeTrace par.obsTrace
  let seq1 := traceTags (filterBySid sid1 seqTrace)
  let par1 := traceTags (filterBySid sid1 parTrace)
  expect (decide (seq1 = par1)) "session 1 traces differ"
  let seq2 := traceTags (filterBySid sid2 seqTrace)
  let par2 := traceTags (filterBySid sid2 parTrace)
  expect (decide (seq2 = par2)) "session 2 traces differ"
