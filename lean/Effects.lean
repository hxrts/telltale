/-
Copyright (c) 2025 Rumpsteak Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Effects.Basic
import Effects.Types
import Effects.Values
import Effects.Assoc
import Effects.Environments
import Effects.Process
import Effects.Typing
import Effects.Coherence
import Effects.Split
import Effects.ProcessTyping
import Effects.Freshness
import Effects.Semantics
import Effects.Preservation

/-!
# Session Types with Async Effects

This library formalizes a type system for asynchronous session types with
buffered communication. The key features are:

## Core Concepts

- **Session Types** (`SType`): Describe communication protocols as sequences of
  send/receive actions. Duality ensures matching communication partners.

- **Endpoints** (`Endpoint`): Each channel has two endpoints (L/R) with dual
  session types. Messages are buffered at endpoints.

- **Async Buffers**: Send operations enqueue messages at the dual endpoint's
  buffer. Receive operations dequeue from the local buffer.

## Type System

- **Value Typing** (`HasTypeVal`): Types runtime values including channel
  endpoints, which carry their session type.

- **Buffer Typing** (`BufferTyping`): Message queues are typed by lists of
  value types, ensuring received messages have expected types.

- **Coherence** (`Coherent`): The key invariant for async communication.
  After consuming "in-flight" messages (tracked in DEnv), session types
  at dual endpoints remain duals of each other.

- **Process Typing** (`HasTypeProcN`): Types processes with explicit name
  supply for fresh channel allocation. Tracks how environments evolve.

## Operational Semantics

- **Base Steps** (`StepBase`): Primitive operations including send (enqueue),
  recv (dequeue), newChan (allocate), and assignment.

- **Contextual Closure** (`Step`): Extends base steps to work under
  sequential and parallel composition (interleaving semantics).

## Metatheory

- **Preservation**: Well-typed configurations step to well-typed configurations.
  The proof maintains all invariants: store typing, buffer typing, coherence,
  and the freshness/name supply invariant.

- **Progress** (partial): Well-typed configurations either terminate, can step,
  or are blocked on an empty receive buffer (no deadlock from type errors).

## Module Structure

- `Basic`: Polarity, endpoints, duality
- `Types`: Session types and value types
- `Values`: Runtime values
- `Assoc`: Association list utilities
- `Environments`: Stores, buffers, typing environments
- `Process`: Process language AST
- `Typing`: Value/buffer typing, coherence definition, store typing
- `Coherence`: Coherence preservation proofs (send/recv)
- `Split`: Linear context splitting for parallel composition
- `ProcessTyping`: Process typing judgment
- `Freshness`: Name supply invariant
- `Semantics`: Operational semantics
- `Preservation`: Subject reduction theorem

## References

This formalization is based on the async session types literature:
- Gay & Hole, "Subtyping for Session Types in the Pi Calculus" (2005)
- Deniélou & Yoshida, "Dynamic Multirole Session Types" (2011)
- Scalas & Yoshida, "Less is More" (2019)

The coherence invariant with type-level queue traces follows approaches
similar to those in:
- Lindley & Morris, "A Semantics for Propositions as Sessions" (2015)
-/
