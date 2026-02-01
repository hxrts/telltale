import Runtime.Examples.SimpleProtocol
import Runtime.VM.Exec
import Runtime.VM.Exec.Helpers

/-
The Problem. Provide an executable Lean test that runs the example VM
program and checks the resulting trace and session typing.

Solution Structure. Step the VM for a fixed number of instructions,
then assert expected register values, local types, and trace length.
-/

set_option autoImplicit false

/-! ## VM test runner -/

def runSteps (n : Nat)
    (st : VMState TestIdentity TestGuard TestPersist TestEffect TestVerify) :
    VMState TestIdentity TestGuard TestPersist TestEffect TestVerify :=
  -- Execute n single-instruction steps on coroutine 0.
  match n with
  | 0 => st
  | n' + 1 =>
      let (st', _) := execInstr st 0
      runSteps n' st'

def expect (ok : Bool) (msg : String) : IO Unit :=
  -- Fail fast when a test condition is false.
  if ok then pure () else throw (IO.userError msg)

/-! ## Main test entry point -/

def main : IO Unit := do
  -- Run the example program for 7 instructions.
  let st' := runSteps 7 exampleState
  let coroOk :=
    match st'.coroutines[0]? with
    | none => false
    | some c => decide (c.regs[3]? = some (.nat 7))
  let epA : Endpoint := { sid := 0, role := "Alice" }
  let epB : Endpoint := { sid := 0, role := "Bob" }
  let typeAOk :=
    match SessionStore.lookupType st'.sessions epA with
    | some .end_ => true
    | _ => false
  let typeBOk :=
    match SessionStore.lookupType st'.sessions epB with
    | some .end_ => true
    | _ => false
  let traceOk := decide (st'.obsTrace.length = 5)
  expect coroOk "recv did not write the expected value"
  expect typeAOk "Alice endpoint did not reach end_"
  expect typeBOk "Bob endpoint did not reach end_"
  expect traceOk "unexpected observable trace length"
