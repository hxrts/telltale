/-
Copyright (c) 2025 Telltale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Effects.Basic
import Effects.LocalType
import Effects.Values
import Effects.Environments
import Effects.Coherence
import Effects.Process
import Effects.Typing
import Effects.Semantics
import Effects.Preservation
import Effects.DeadlockFreedom
import Effects.Monitor
import Effects.Spatial
import Effects.Determinism
import Effects.Deployment
import Effects.Examples
import Effects.Simulation
import Effects.Decidability

/-!
# Session Types with Async Effects

This library formalizes a type system for asynchronous multiparty session types
with buffered communication. The key features are:

## Core Concepts

- **Local Types** (`LocalType`): Describe communication protocols as sequences of
  send/receive actions directed at specific roles.

- **Endpoints** (`Endpoint`): `SessionId × Role` pairs identifying participants.
  Messages are buffered per directed edge (sender → receiver).

- **Async Buffers**: Send operations enqueue messages at the edge buffer.
  Receive operations dequeue from the matching edge buffer.

## Type System

- **Value Typing** (`HasTypeVal`): Types runtime values including endpoint
  channels, which carry their session type.

- **Buffer Typing** (`BuffersTyped`): Message queues per edge are typed by
  lists of value types, ensuring received messages have expected types.

- **Coherence** (`Coherent`): The key invariant for async communication.
  For each directed edge, the sender's and receiver's local types are
  consistent with the in-flight message trace.

- **Process Typing** (`HasTypeProcN`): Types processes with session tracking.
  Tracks how environments evolve.

## Operational Semantics

- **Base Steps** (`StepBase`): Primitive operations including send (enqueue),
  recv (dequeue), newSession (allocate), and assignment.

- **Contextual Closure** (`Step`): Extends base steps to work under
  sequential and parallel composition (interleaving semantics).

## Metatheory

- **Preservation**: Well-typed configurations step to well-typed configurations.
  The proof maintains all invariants: store typing, buffer typing, coherence,
  and session freshness.

- **Progress** (partial): Well-typed configurations either terminate, can step,
  or are blocked on an empty receive buffer (no deadlock from type errors).

## Module Structure

- `Basic`: Session IDs, roles, endpoints, directed edges
- `LocalType`: Local types with role-directed actions
- `Values`: Runtime values with endpoint channels
- `Environments`: Stores, buffers (per-edge), type environments
- `Coherence`: Multiparty coherence invariant and preservation
- `Process`: MPST process language
- `Typing`: Value/buffer typing, store typing
- `Semantics`: Async operational semantics
- `Preservation`: Subject reduction theorem
- `DeadlockFreedom`: Progress guarantees with guardedness
- `Monitor`: Proof-carrying runtime with linear tokens
- `Spatial`: Spatial requirements and topology satisfaction
- `Determinism`: Unique branch labels and diamond property
- `Deployment`: Deployed protocol bundles and linking
- `Examples`: Concrete protocol examples (Ping-Pong, Two-Buyer)
- `Simulation`: Executable step function and trace utilities
- `Decidability`: Decidable instances and boolean checkers

## References

This formalization is based on the async session types literature:
- Gay & Hole, "Subtyping for Session Types in the Pi Calculus" (2005)
- Deniélou & Yoshida, "Dynamic Multirole Session Types" (2011)
- Scalas & Yoshida, "Less is More" (2019)

The coherence invariant with type-level queue traces follows approaches
similar to those in:
- Lindley & Morris, "A Semantics for Propositions as Sessions" (2015)
-/
