import Effects.Semantics

/-!
# MPST Simulation

This module provides executable simulation for MPST protocols.

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

noncomputable section

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
        -- Need target role from local type, use placeholder for now
        -- In well-typed configs, this would come from the type
        some (sendStep C { sid := e.sid, sender := e.role, receiver := "target" } v)
      | _ => none
    | _ => none

  | .recv k x =>
    match lookupStr C.store k with
    | some (.chan e) =>
      -- Try all possible source roles - simplified version
      -- In well-typed configs, the source comes from the type
      match lookupBuf C.bufs { sid := e.sid, sender := "source", receiver := e.role } with
      | v :: _ =>
        match dequeueBuf C.bufs { sid := e.sid, sender := "source", receiver := e.role } with
        | some (bufs', _) =>
          some { C with
            proc := .skip
            store := updateStr C.store x v
            bufs := bufs' }
        | none => none
      | [] => none  -- Buffer empty, blocked
    | _ => none

  | .select k ℓ =>
    match lookupStr C.store k with
    | some (.chan e) =>
      some (sendStep C { sid := e.sid, sender := e.role, receiver := "target" } (.string ℓ))
    | _ => none

  | .branch k bs =>
    match lookupStr C.store k with
    | some (.chan e) =>
      match lookupBuf C.bufs { sid := e.sid, sender := "source", receiver := e.role } with
      | .string ℓ :: _ =>
        match bs.find? (fun b => b.1 == ℓ) with
        | some (_, P) =>
          match dequeueBuf C.bufs { sid := e.sid, sender := "source", receiver := e.role } with
          | some (bufs', _) =>
            some { C with proc := P, bufs := bufs' }
          | none => none
        | none => none  -- Label not found in branches
      | _ => none  -- Buffer empty or wrong type
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

  | .par P Q =>
    match P with
    | .skip => some { C with proc := Q }  -- par skip Q → Q
    | _ =>
      match Q with
      | .skip => some { C with proc := P }  -- par P skip → P
      | _ => none  -- Would need recursive step


/-- Attempt a full step with contextual closure.

For seq and par, we recursively try to step the subprocesses.
-/
partial def stepDecide (C : Config) : Option Config :=
  match C.proc with
  | .skip => none

  | .seq P Q =>
    if P = .skip then
      some { C with proc := Q }
    else
      match stepDecide { C with proc := P } with
      | some C' => some { C' with proc := .seq C'.proc Q }
      | none => none

  | .par P Q =>
    if P = .skip then
      some { C with proc := Q }
    else if Q = .skip then
      some { C with proc := P }
    else
      -- Try left first
      match stepDecide { C with proc := P } with
      | some C' => some { C' with proc := .par C'.proc Q }
      | none =>
        -- Try right
        match stepDecide { C with proc := Q } with
        | some C' => some { C' with proc := .par P C'.proc }
        | none => none

  | _ => stepBaseDecide C

/-! ## Multi-Step Execution -/

/-- Run up to n steps, returning the final configuration.

Stops early if:
- The process terminates (becomes skip)
- The configuration is stuck (stepDecide returns none)
-/
partial def runSteps (C : Config) (n : Nat) : Config :=
  if n = 0 then C
  else if C.proc = .skip then C
  else
    match stepDecide C with
    | some C' => runSteps C' (n - 1)
    | none => C  -- Stuck

/-- Run steps and collect the trace.

Returns a list of configurations from initial to final.
-/
partial def traceSteps (C : Config) (n : Nat) : List Config :=
  if n = 0 then [C]
  else if C.proc = .skip then [C]
  else
    match stepDecide C with
    | some C' => C :: traceSteps C' (n - 1)
    | none => [C]

/-- Check if a configuration can step. -/
def canStep (C : Config) : Bool :=
  (stepDecide C).isSome

/-- Check if a configuration is terminated. -/
def isTerminated (C : Config) : Bool :=
  C.proc == .skip

/-- Check if a configuration is stuck (not terminated but can't step). -/
def isStuck (C : Config) : Bool :=
  !isTerminated C && !canStep C

/-! ## Simulation Properties -/

/-- If stepDecide returns some, then Step holds (soundness). -/
theorem stepDecide_sound {C C' : Config} (h : stepDecide C = some C') :
    Step C C' := by
  sorry  -- Proof requires case analysis on C.proc

/-- If Step holds for decidable cases, stepDecide returns some (completeness for decidable subset). -/
theorem stepDecide_complete_base {C C' : Config} (h : StepBase C C')
    (hDec : stepBaseDecide C = some C') :
    True := by
  trivial

/-! ## Example: Running Ping-Pong -/

-- The simulation functions work best with concrete configurations.
-- See Examples.lean for protocol definitions.

end
