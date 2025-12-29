/-! # Rumpsteak.Protocol.Semantics.Reduction

Reduction semantics for multiparty sessions.

## Overview

This module defines the single-step reduction relation for configurations.
Reduction rules capture how processes execute by sending/receiving messages
through queues.

Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)

## Reduction Rules

- [Send]: A send process enqueues a message
- [Recv]: A receive process dequeues and branches on the label
- [Cond]: Conditional evaluates to one branch
- [Rec]: Recursive process unfolds

## Expose

The following definitions form the semantic interface for proofs:

- `Reduces`: Inductive relation for single-step reduction
- `step`: Decidable single-step function
- `run`: Multi-step execution with fuel

## Main Definitions

- `Reduces` - Inductive reduction relation
- `step` - Decidable step function
- `ReduceResult` - Result type for step function
-/

import Rumpsteak.Protocol.Semantics.Process
import Rumpsteak.Protocol.Semantics.Configuration

namespace Rumpsteak.Protocol.Semantics.Reduction

open Rumpsteak.Protocol.GlobalType (Label)
open Rumpsteak.Protocol.Semantics.Process
open Rumpsteak.Protocol.Semantics.Configuration

/-- Result of a reduction step. -/
inductive ReduceResult where
  /-- Successful reduction -/
  | ok : Configuration → ReduceResult
  /-- No reduction possible (stuck or done) -/
  | stuck : ReduceResult
  /-- Error during reduction -/
  | error : String → ReduceResult
deriving Repr, Inhabited

/-- Try to reduce a send action for a role.
    Enqueues the message and updates the process. -/
def reduceSend (c : Configuration) (senderRole : String)
    (receiverRole : String) (label : Label) (value : Value) (cont : Process)
    : ReduceResult :=
  let ch := { sender := senderRole, receiver := receiverRole }
  let msg := { sender := senderRole, label := label, value := value }
  let c' := c.enqueue ch msg
  let c'' := c'.setProcess senderRole cont
  .ok c''

/-- Try to reduce a receive action for a role.
    Dequeues a message and selects the matching branch. -/
def reduceRecv (c : Configuration) (receiverRole : String)
    (senderRole : String) (branches : List (Label × Process))
    : ReduceResult :=
  let ch := { sender := senderRole, receiver := receiverRole }
  match c.dequeue ch with
  | none => .stuck  -- No message available
  | some (msg, c') =>
    -- Find matching branch
    match branches.find? (fun (l, _) => l.name == msg.label.name) with
    | none => .error s!"No branch for label {msg.label.name}"
    | some (_, cont) =>
      let c'' := c'.setProcess receiverRole cont
      .ok c''

/-- Try to reduce a conditional for a role. -/
def reduceCond (c : Configuration) (role : String)
    (cond : Bool) (thenBranch : Process) (elseBranch : Process)
    : ReduceResult :=
  let cont := if cond then thenBranch else elseBranch
  let c' := c.setProcess role cont
  .ok c'

/-- Try to reduce a recursive process for a role. -/
def reduceRec (c : Configuration) (role : String)
    (x : String) (body : Process)
    : ReduceResult :=
  let unfolded := body.substitute x (Process.rec x body)
  let c' := c.setProcess role unfolded
  .ok c'

/-- Try to step a single process for a role.
    Returns the new configuration if a step is possible. -/
def stepProcess (c : Configuration) (rp : RoleProcess) : ReduceResult :=
  match rp.process with
  | .inaction => .stuck
  | .var _ => .stuck  -- Free variable, stuck
  | .send receiver label value cont =>
    reduceSend c rp.role receiver label value cont
  | .recv sender branches =>
    reduceRecv c rp.role sender branches
  | .cond b p q =>
    reduceCond c rp.role b p q
  | .rec x body =>
    reduceRec c rp.role x body
  | .par _ _ => .stuck  -- Parallel handled at configuration level

/-- Try to make one step in the configuration.
    Tries each process in order until one can step. -/
def step (c : Configuration) : ReduceResult :=
  let rec tryProcess : List RoleProcess → ReduceResult
    | [] => .stuck
    | rp :: rest =>
      match stepProcess c rp with
      | .ok c' => .ok c'
      | .stuck => tryProcess rest
      | .error e => .error e
  tryProcess c.processes

/-- Run the configuration for up to `fuel` steps. -/
def run (c : Configuration) (fuel : Nat) : Configuration × Nat :=
  if fuel == 0 then (c, 0)
  else match step c with
  | .ok c' =>
    let (final, stepsRemaining) := run c' (fuel - 1)
    (final, stepsRemaining)
  | .stuck => (c, fuel)
  | .error _ => (c, fuel)

/-- Check if the configuration can make progress. -/
def canStep (c : Configuration) : Bool :=
  match step c with
  | .ok _ => true
  | _ => false

/-- Inductive reduction relation for formal proofs.

    This is the propositional version of the reduction semantics. -/
inductive Reduces : Configuration → Configuration → Prop where
  /-- Send rule: enqueue message -/
  | send :
    ∀ (c : Configuration) (role receiver : String)
      (label : Label) (value : Value) (cont : Process),
    c.getProcess role = some (.send receiver label value cont) →
    Reduces c (reduceSendConfig c role receiver label value cont)

  /-- Receive rule: dequeue and branch -/
  | recv :
    ∀ (c : Configuration) (role sender : String)
      (branches : List (Label × Process)) (msg : Message) (cont : Process),
    c.getProcess role = some (.recv sender branches) →
    c.dequeue { sender := sender, receiver := role } = some (msg, _) →
    branches.find? (fun (l, _) => l.name == msg.label.name) = some (_, cont) →
    Reduces c (receiveConfig c role cont)

  /-- Conditional rule -/
  | cond :
    ∀ (c : Configuration) (role : String)
      (b : Bool) (p q : Process),
    c.getProcess role = some (.cond b p q) →
    Reduces c (c.setProcess role (if b then p else q))

  /-- Recursion rule: unfold -/
  | rec :
    ∀ (c : Configuration) (role x : String) (body : Process),
    c.getProcess role = some (.rec x body) →
    Reduces c (c.setProcess role (body.substitute x (.rec x body)))
where
  /-- Helper for send reduction -/
  reduceSendConfig (c : Configuration) (role receiver : String)
      (label : Label) (value : Value) (cont : Process) : Configuration :=
    let ch := { sender := role, receiver := receiver }
    let msg := { sender := role, label := label, value := value }
    (c.enqueue ch msg).setProcess role cont

  /-- Helper for receive reduction -/
  receiveConfig (c : Configuration) (role : String) (cont : Process) : Configuration :=
    c.setProcess role cont

/-- Multi-step reduction (reflexive-transitive closure). -/
inductive ReducesStar : Configuration → Configuration → Prop where
  | refl : ∀ c, ReducesStar c c
  | step : ∀ c1 c2 c3, Reduces c1 c2 → ReducesStar c2 c3 → ReducesStar c1 c3

/-- A configuration is stuck if it cannot reduce but is not done. -/
def isStuck (c : Configuration) : Prop :=
  ¬ c.isDone ∧ ∀ c', ¬ Reduces c c'

end Rumpsteak.Protocol.Semantics.Reduction
