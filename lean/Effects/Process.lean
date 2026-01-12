/-
Copyright (c) 2025 Rumpsteak Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Effects.Basic
import Effects.Types
import Effects.Values
import Effects.Environments

/-!
# Process Language

This module defines the minimal process language for async session effects:
- `skip`: terminated process
- `seq P Q`: sequential composition
- `par P Q`: parallel composition
- `send k x`: send value at x over channel k
- `recv k x`: receive into variable x from channel k
- `newChan kL kR T`: create a fresh channel with endpoints kL and kR
- `assign x v`: assign value v to variable x

Also defines the runtime configuration combining:
- Next available channel ID
- Variable store
- Message buffers
- Current process
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-- Process terms for the minimal async session calculus. -/
inductive Process where
  /-- Terminated process. -/
  | skip : Process
  /-- Sequential composition: run P then Q. -/
  | seq : Process → Process → Process
  /-- Parallel composition: run P and Q concurrently. -/
  | par : Process → Process → Process
  /-- Send the value at variable x over channel variable k. -/
  | send : Var → Var → Process
  /-- Receive a value from channel variable k into variable x. -/
  | recv : Var → Var → Process
  /-- Create a new channel with left endpoint kL and right endpoint kR.
      The channel has session type T at the left endpoint. -/
  | newChan : Var → Var → SType → Process
  /-- Assign value v to variable x. -/
  | assign : Var → Value → Process
  deriving Repr, DecidableEq

namespace Process

/-- Check if a process is terminated. -/
def isSkip : Process → Bool
  | .skip => true
  | _ => false

/-- Check if a process can make progress (is not skip). -/
def canStep : Process → Bool
  | .skip => false
  | _ => true

end Process

/-- Runtime configuration for process execution. -/
structure Config where
  /-- Next available channel ID for allocation. -/
  nextId : ChanId
  /-- Variable store mapping names to values. -/
  store : Store
  /-- Message buffers for each endpoint. -/
  bufs : Buffers
  /-- Current process being executed. -/
  proc : Process
  deriving Repr, DecidableEq

namespace Config

/-- Create an initial configuration for a process. -/
def init (P : Process) : Config :=
  { nextId := 0
    store := []
    bufs := []
    proc := P }

/-- Check if the configuration has terminated. -/
def isDone (C : Config) : Bool := C.proc.isSkip

/-- Update just the process in a configuration. -/
def withProc (C : Config) (P : Process) : Config :=
  { C with proc := P }

/-- Update just the store in a configuration. -/
def withStore (C : Config) (st : Store) : Config :=
  { C with store := st }

/-- Update just the buffers in a configuration. -/
def withBufs (C : Config) (B : Buffers) : Config :=
  { C with bufs := B }

end Config

end
