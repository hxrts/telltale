/-
Copyright (c) 2025 Rumpsteak Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Effects.Process
import Effects.Typing
import Effects.Freshness

/-!
# Operational Semantics

This module defines the small-step operational semantics for async session effects:
- `StepBase`: primitive head steps (send, recv, newChan, assign, structural)
- `Step`: contextual closure for seq and par (evaluation contexts)

The semantics is an interleaving semantics for parallel composition:
either branch can step, maintaining true concurrency at the operational level.

Key features:
- Send enqueues the value in the dual endpoint's buffer (async)
- Recv dequeues from the endpoint's own buffer (blocking if empty)
- newChan allocates a fresh channel pair
- Parallel processes step independently (interleaving)
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Base Steps (Head Reductions) -/

/-- Primitive head steps for processes. -/
inductive StepBase : Config → Config → Prop where

  /-- Sequential composition: skip ; Q → Q -/
  | seq2 {C : Config} {Q : Process} :
      StepBase { C with proc := Process.seq Process.skip Q }
                { C with proc := Q }

  /-- Parallel composition: skip || Q → Q -/
  | par_skip_left {C : Config} {Q : Process} :
      StepBase { C with proc := Process.par Process.skip Q }
                { C with proc := Q }

  /-- Parallel composition: P || skip → P -/
  | par_skip_right {C : Config} {P : Process} :
      StepBase { C with proc := Process.par P Process.skip }
                { C with proc := P }

  /-- Assignment: x := v → skip (with store update).
      Requires AssignSafe to preserve SupplyInv. -/
  | assign {C : Config} {x : Var} {v : Value} :
      AssignSafe C v →
      StepBase { C with proc := Process.assign x v }
                { C with proc := Process.skip,
                         store := updateStr C.store x v }

  /-- Channel creation: newChan(kL, kR, T) → skip.
      Allocates fresh endpoints at nextId, bumps nextId. -/
  | newChan {C : Config} {kL kR : Var} {T : SType} :
      let n := C.nextId
      StepBase { C with proc := Process.newChan kL kR T }
                { C with proc := Process.skip,
                         nextId := n + 1,
                         store := updateStr (updateStr C.store kL (Value.chan (n, Polarity.L)))
                                            kR (Value.chan (n, Polarity.R)),
                         bufs := updateBuf (updateBuf C.bufs (n, Polarity.L) [])
                                           (n, Polarity.R) [] }

  /-- Send: send k x → skip (enqueue value at dual endpoint). -/
  | send {C : Config} {k x : Var} {e : Endpoint} {v : Value} {q : Buffer} :
      lookupStr C.store k = some (Value.chan e) →
      lookupStr C.store x = some v →
      q = lookupBuf C.bufs e.dual →
      StepBase { C with proc := Process.send k x }
                { C with proc := Process.skip,
                         bufs := updateBuf C.bufs e.dual (q ++ [v]) }

  /-- Receive: recv k x → skip (dequeue from own endpoint).
      Only steps if the buffer is non-empty. -/
  | recv {C : Config} {k x : Var} {e : Endpoint} {v : Value} {vs : Buffer} :
      lookupStr C.store k = some (Value.chan e) →
      lookupBuf C.bufs e = v :: vs →
      StepBase { C with proc := Process.recv k x }
                { C with proc := Process.skip,
                         store := updateStr C.store x v,
                         bufs := updateBuf C.bufs e vs }

/-! ## Contextual Closure (Evaluation Contexts) -/

/-- Full step relation: base steps plus contextual closure for seq/par. -/
inductive Step : Config → Config → Prop where

  /-- A base step is a step. -/
  | base {C C' : Config} :
      StepBase C C' →
      Step C C'

  /-- Step under left side of sequential composition. -/
  | seq_left {C C' : Config} {P P' Q : Process} :
      Step C C' →
      C.proc = P →
      C'.proc = P' →
      Step { C with proc := Process.seq P Q }
           { C' with proc := Process.seq P' Q }

  /-- Step under left side of parallel composition. -/
  | par_left {C C' : Config} {P P' Q : Process} :
      Step C C' →
      C.proc = P →
      C'.proc = P' →
      Step { C with proc := Process.par P Q }
           { C' with proc := Process.par P' Q }

  /-- Step under right side of parallel composition. -/
  | par_right {C C' : Config} {P Q Q' : Process} :
      Step C C' →
      C.proc = Q →
      C'.proc = Q' →
      Step { C with proc := Process.par P Q }
           { C' with proc := Process.par P Q' }

namespace Step

/-- Step is deterministic modulo the choice of which parallel branch to step.
    (The actual step in each branch is deterministic.) -/
theorem deterministic_base {C C₁ C₂ : Config}
    (h₁ : StepBase C C₁) (h₂ : StepBase C C₂) : C₁ = C₂ := by
  cases h₁ <;> cases h₂ <;> try rfl
  all_goals simp_all

/-- Reflexive-transitive closure of Step. -/
inductive Star : Config → Config → Prop where
  | refl {C : Config} : Star C C
  | step {C C' C'' : Config} : Step C C' → Star C' C'' → Star C C''

/-- A configuration is stuck if it cannot step. -/
def Stuck (C : Config) : Prop := ¬∃ C', Step C C'

/-- A configuration terminates if it reaches skip with no more work. -/
def Terminates (C : Config) : Prop := C.proc = Process.skip

end Step

/-! ## Send/Recv Helper Functions -/

/-- Compute the configuration after a send step (for use in proofs). -/
def sendStep (C : Config) (e : Endpoint) (v : Value) : Config :=
  let q := lookupBuf C.bufs e.dual
  { C with
    proc := Process.skip
    bufs := updateBuf C.bufs e.dual (q ++ [v]) }

/-- Compute the configuration after a recv step (for use in proofs). -/
def recvStep (C : Config) (e : Endpoint) (x : Var) (v : Value) (vs : Buffer) : Config :=
  { C with
    proc := Process.skip
    store := updateStr C.store x v
    bufs := updateBuf C.bufs e vs }

end
