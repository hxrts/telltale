/-! # Rumpsteak.Protocol.Semantics.Process

Process expressions for operational semantics.

## Overview

This module defines process expressions that represent the runtime behavior
of session-typed programs. Processes can send/receive messages, make choices,
recurse, and run in parallel.

Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)

## Expose

The following definitions form the semantic interface for proofs:

- `Process`: Inductive type for process expressions
- `Process.freeVars`: Extract free process variables
- `Process.substitute`: Substitute a process for a variable

## Main Definitions

- `Process` - Inductive type for process syntax
- `Value` - Runtime values
- Substitution and free variable operations
-/

import Rumpsteak.Protocol.GlobalType

namespace Rumpsteak.Protocol.Semantics.Process

open Rumpsteak.Protocol.GlobalType (Sort Label)

/-- Runtime values that can be sent in messages. -/
inductive Value where
  /-- Unit value -/
  | unit : Value
  /-- Natural number -/
  | nat : Nat → Value
  /-- Boolean -/
  | bool : Bool → Value
  /-- String -/
  | string : String → Value
  /-- Pair of values -/
  | pair : Value → Value → Value
deriving Repr, DecidableEq, BEq, Inhabited

/-- Process expressions.

    Syntax:
    - `inaction`: Terminated process (0)
    - `send role label value P`: Send value with label to role, continue as P
    - `recv role branches`: Receive from role, branch on label
    - `cond b P Q`: If-then-else
    - `rec X P`: Recursive process μX.P
    - `var X`: Process variable
    - `par P Q`: Parallel composition P | Q

    Processes represent the runtime behavior of session-typed programs. -/
inductive Process where
  /-- Terminated process -/
  | inaction : Process
  /-- Send a message: role!label⟨v⟩.P -/
  | send : String → Label → Value → Process → Process
  /-- Receive with branching: role?{lᵢ.Pᵢ} -/
  | recv : String → List (Label × Process) → Process
  /-- Conditional: if b then P else Q -/
  | cond : Bool → Process → Process → Process
  /-- Recursive process: μX.P -/
  | rec : String → Process → Process
  /-- Process variable: X -/
  | var : String → Process
  /-- Parallel composition: P | Q -/
  | par : Process → Process → Process
deriving Repr, Inhabited

/-- Extract free process variables from a process. -/
def Process.freeVars : Process → List String
  | .inaction => []
  | .send _ _ _ p => p.freeVars
  | .recv _ branches => branches.bind fun (_, p) => p.freeVars
  | .cond _ p q => p.freeVars ++ q.freeVars
  | .rec x p => p.freeVars.filter (· != x)
  | .var x => [x]
  | .par p q => p.freeVars ++ q.freeVars

/-- Substitute a process for a variable. -/
def Process.substitute (proc : Process) (varName : String) (replacement : Process) : Process :=
  match proc with
  | .inaction => .inaction
  | .send role label value p =>
    .send role label value (p.substitute varName replacement)
  | .recv role branches =>
    .recv role (branches.map fun (l, p) => (l, p.substitute varName replacement))
  | .cond b p q =>
    .cond b (p.substitute varName replacement) (q.substitute varName replacement)
  | .rec x p =>
    if x == varName then
      .rec x p  -- Variable is shadowed
    else
      .rec x (p.substitute varName replacement)
  | .var x =>
    if x == varName then replacement else .var x
  | .par p q =>
    .par (p.substitute varName replacement) (q.substitute varName replacement)

/-- Unfold one level of recursion: μX.P ↦ P[μX.P/X] -/
def Process.unfold : Process → Process
  | p@(.rec x body) => body.substitute x p
  | p => p

/-- Check if a process is closed (no free variables). -/
def Process.isClosed (p : Process) : Bool :=
  p.freeVars.isEmpty

/-- Check if a process has terminated. -/
def Process.isTerminated : Process → Bool
  | .inaction => true
  | .par p q => p.isTerminated && q.isTerminated
  | _ => false

/-- Count the size of a process (for termination arguments). -/
def Process.size : Process → Nat
  | .inaction => 1
  | .send _ _ _ p => 1 + p.size
  | .recv _ branches => 1 + branches.foldl (fun acc (_, p) => acc + p.size) 0
  | .cond _ p q => 1 + p.size + q.size
  | .rec _ p => 1 + p.size
  | .var _ => 1
  | .par p q => 1 + p.size + q.size

/-- A role process pairs a role name with its process. -/
structure RoleProcess where
  /-- The role name -/
  role : String
  /-- The process implementing this role -/
  process : Process
deriving Repr, Inhabited

/-- Check if all role processes have terminated. -/
def allTerminated (rps : List RoleProcess) : Bool :=
  rps.all fun rp => rp.process.isTerminated

end Rumpsteak.Protocol.Semantics.Process
