import Protocol.Semantics

/-! # MPST Simulation

This module provides executable simulation for MPST protocols. -/

/-
The Problem. We need an executable step function for testing and debugging
protocols. The semantics is relational, so we need a decidable version
that attempts to find a valid step.

Solution Structure. We define:
1. `stepDecide`: attempt one step, returning `some C'` or `none`
2. `runSteps`: execute multiple steps until stuck or limit
3. `traceSteps`: execute and collect the full trace
Non-determinism in parallel composition is resolved by left-first.
-/

/-!
## Overview

The `stepDecide` function implements a decidable step function that
attempts to execute one step of a configuration. This enables:
- Testing protocol implementations
- Debugging protocol behavior
- Exploring protocol traces

## Key Functions

- `stepDecide`: Attempt one step, returning `some C'` or `none`
- `runSteps`: Execute multiple steps until stuck or limit
- `traceSteps`: Execute and collect the trace

## Limitations

The simulation is non-deterministic for parallel composition.
The current implementation picks the left branch first.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

/-! ## Decidable Step Function -/

/-- Attempt to execute a base step.

Returns `some C'` if the step succeeds, `none` if blocked or stuck.

Note: For parallel composition, we try left first, then right.
This makes the simulation deterministic but may not explore all interleavings.
-/
def stepBaseDecide (C : Config) : Option Config :=
  match C.proc with
  | .skip => none  -- Already terminated

  | .send k x =>
    match lookupStr C.store k with
    | some (.chan e) =>
      match lookupStr C.store x with
      | some v =>
        -- Read target role and type from G at runtime
        -- In well-typed configs, this would come from the type lookup
        match lookupG C.G e with
        | some (.send target T L) =>
          some (sendStep C e { sid := e.sid, sender := e.role, receiver := target } v T L)
        | _ => none
      | _ => none
    | _ => none

  | .recv k x =>
    match lookupStr C.store k with
    | some (.chan e) =>
      -- Get source role from type
      match lookupG C.G e with
      | some (.recv source _ L) =>
          match lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } with
          | v :: _ =>
            some (recvStep C e { sid := e.sid, sender := source, receiver := e.role } x v L)
          | [] => none  -- Buffer empty, blocked
        | _ => none
    | _ => none

  | .select k ℓ =>
    match lookupStr C.store k with
    | some (.chan e) =>
      match lookupG C.G e with
      | some (.select target branches) =>
        match branches.find? (fun b => b.1 == ℓ) with
        | some (_, L) =>
          some (sendStep C e { sid := e.sid, sender := e.role, receiver := target } (.string ℓ) .string L)
        | none => none
      | _ => none
    | _ => none

  | .branch k bs =>
    match lookupStr C.store k with
    | some (.chan e) =>
      match lookupG C.G e with
      | some (.branch source typeBranches) =>
        match lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } with
        | .string ℓ :: _ =>
          match bs.find? (fun b => b.1 == ℓ), typeBranches.find? (fun b => b.1 == ℓ) with
          | some (_, P), some (_, L) =>
            match dequeueBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } with
            | some (bufs', _) =>
              let edge : Edge := { sid := e.sid, sender := source, receiver := e.role }
              some { C with proc := P, bufs := bufs', G := updateG C.G e L, D := updateD C.D edge (lookupD C.D edge).tail }
            | none => none
          | _, _ => none  -- Label not found in branches
        | _ => none  -- Buffer empty or not a string
      | _ => none  -- No matching type in G
    | _ => none

  | .newSession roles f P =>
    some { (newSessionStep C roles f) with proc := P }

  | .assign x v =>
    some { C with
      proc := .skip
      store := updateStr C.store x v }

  | .seq P Q =>
    match P with
    | .skip => some { C with proc := Q }  -- seq skip Q → Q
    | _ => none  -- Would need recursive step in P

  | .par nS nG P Q =>
    match P with
    | .skip => some { C with proc := Q }  -- par skip Q → Q
    | _ =>
      match Q with
      | .skip => some { C with proc := P }  -- par P skip → P
      | _ => none  -- Would need recursive step

/-- Coarse size measure for well-founded recursion on processes. -/
private def procSize : Process → Nat
  | .skip => 0
  | .seq P Q => procSize P + procSize Q + 1
  | .par _ _ P Q => procSize P + procSize Q + 1
  | .send _ _ => 0
  | .recv _ _ => 0
  | .select _ _ => 0
  | .branch _ _ => 1
  | .newSession _ _ _ => 1
  | .assign _ _ => 0

private lemma procSize_lt_seq_left (P Q : Process) : procSize P < procSize (.seq P Q) := by
  have hpos : 0 < procSize Q + 1 := Nat.succ_pos _
  have h := Nat.lt_add_of_pos_right (n := procSize P) hpos
  simp [procSize, Nat.add_assoc]

private lemma procSize_lt_par_left (nS nG : Nat) (P Q : Process) :
    procSize P < procSize (.par nS nG P Q) := by
  have hpos : 0 < procSize Q + 1 := Nat.succ_pos _
  have h := Nat.lt_add_of_pos_right (n := procSize P) hpos
  simp [procSize, Nat.add_assoc]

private lemma procSize_lt_par_right (nS nG : Nat) (P Q : Process) :
    procSize Q < procSize (.par nS nG P Q) := by
  have hpos : 0 < procSize P + 1 := Nat.succ_pos _
  have h := Nat.lt_add_of_pos_left (n := procSize Q) hpos
  simpa [procSize, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- Attempt a full step with contextual closure.

For seq and par, we recursively try to step the subprocesses.
-/
private def stepDecideAux (proc : Process) (C : Config) : Option Config :=
  match proc with
  | .skip => none

  | .seq P Q =>
    if P = .skip then
      some { C with proc := Q }
    else
      match stepDecideAux P { C with proc := P } with
      | some C' => some { C' with proc := .seq C'.proc Q }
      | none => none

  | .par nS nG P Q =>
    if P = .skip then
      some { C with proc := Q }
    else if Q = .skip then
      some { C with proc := P }
    else
      -- Try left first
      match stepDecideAux P { C with proc := P } with
      | some C' => some { C' with proc := .par nS nG C'.proc Q }
      | none =>
        -- Try right
        match stepDecideAux Q { C with proc := Q } with
        | some C' => some { C' with proc := .par nS nG P C'.proc }
        | none => none

  | _ => stepBaseDecide C

termination_by
  procSize proc
decreasing_by
  all_goals
    first
      | simpa using procSize_lt_seq_left _ _
      | simpa using procSize_lt_par_left _ _ _ _
      | simpa using procSize_lt_par_right _ _ _ _

def stepDecide (C : Config) : Option Config :=
  stepDecideAux C.proc C

/-! ## Multi-Step Execution -/

/-- Run up to n steps, returning the final configuration.

Stops early if:
- The process terminates (becomes skip)
- The configuration is stuck (stepDecide returns none)
-/
def runSteps (C : Config) (n : Nat) : Config :=
  if n = 0 then C
  else if C.proc = .skip then C
  else
    match stepDecide C with
    | some C' => runSteps C' (n - 1)
    | none => C  -- Stuck
termination_by n

/-- Run steps and collect the trace.

Returns a list of configurations from initial to final.
-/
def traceSteps (C : Config) (n : Nat) : List Config :=
  if n = 0 then [C]
  else if C.proc = .skip then [C]
  else
    match stepDecide C with
    | some C' => C :: traceSteps C' (n - 1)
    | none => [C]
termination_by n

/-- Check if a configuration can step. -/
def canStep (C : Config) : Bool :=
  (stepDecide C).isSome

/-- Check if a configuration is terminated. -/
def isTerminated (C : Config) : Bool :=
  C.proc == .skip

/-- Check if a configuration is stuck (not terminated but can't step). -/
def isStuck (C : Config) : Bool :=
  !isTerminated C && !canStep C


end
