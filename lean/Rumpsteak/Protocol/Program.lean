import Rumpsteak.Protocol.Core

/-! # Rumpsteak.Protocol.Program

Effect-based program representation for verification.

## Overview

This module encodes the effect sequences exported by the Rust choreography
compiler. Programs consist of a role identifier and a sequence of effects
(send/recv operations). The runner compares these against projected local types.

## Expose

The following definitions form the semantic interface for proofs:

- `Effect`: Send or receive operation with partner and label
- `Program`: Role identifier paired with effect sequence
- `effectToLocalAction`: Convert an effect to a local action for comparison
- `localTypeOf`: Build a local type from a program's effects
- `matchesLocalType`: Check if program effects match a projected local type

Internal helpers like `isEmpty`, `effectLabels`, and `appendEffect` are
implementation details.

## Main Definitions

- `Effect` - Inductive type for send/recv operations
- `Program` - Structure pairing role with effects
- `effectToLocalAction` - Effect to LocalAction conversion
- `localTypeOf` - Program to LocalType conversion
-/

namespace Rumpsteak.Protocol.Program

open Rumpsteak.Protocol.Core

/-- An effect represents a single communication operation in a program.
    Effects are produced by the Rust choreography compiler's code generator. -/
inductive Effect
  /-- Send a message with the given label to the partner role. -/
  | send (partner : String) (label : String)
  /-- Receive a message with the given label from the partner role. -/
  | recv (partner : String) (label : String)
deriving Inhabited, Repr, DecidableEq, BEq

/-- A program bundles a role identifier with its sequence of effects.
    This represents the exported output from the Rust compiler for verification. -/
structure Program where
  /-- The role this program is for. -/
  role : String
  /-- The sequence of communication effects. -/
  effects : List Effect
deriving Inhabited, Repr, BEq

/-- Convert an effect to a local action for comparison with projections.
    The mapping is direct: send→send, recv→recv, preserving partner and label. -/
def effectToLocalAction : Effect → LocalAction
  | .send partner label => { kind := LocalKind.send, partner, label }
  | .recv partner label => { kind := LocalKind.recv, partner, label }

/-- Build a local type from a program's effect sequence.
    Each effect is converted to the corresponding local action. -/
def localTypeOf (program : Program) : LocalType :=
  { actions := program.effects.map effectToLocalAction }

/-- Check if a program's effects exactly match a local type.
    Used for verifying that generated programs conform to projections. -/
def matchesLocalType (program : Program) (lt : LocalType) : Bool :=
  localTypeOf program == lt

/-- Check if a program has no effects. -/
def isEmpty (program : Program) : Bool :=
  program.effects.isEmpty

/-- Extract all labels from a program's effects for quick comparison. -/
def effectLabels (program : Program) : List String :=
  program.effects.map fun effect =>
    match effect with
    | .send _ label => label
    | .recv _ label => label

/-- Append an effect to a program (for dynamic program construction). -/
def appendEffect (program : Program) (effect : Effect) : Program :=
  { program with effects := program.effects ++ [effect] }

end Rumpsteak.Protocol.Program
