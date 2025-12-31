import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.Semantics.Process

/-! # Rumpsteak.Protocol.Semantics.Configuration

Configurations for multiparty session operational semantics.

## Overview

A configuration consists of parallel processes and message queues.
Queues are indexed by (sender, receiver) pairs and implement FIFO ordering.

Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)

## Expose

The following definitions form the semantic interface for proofs:

- `Message`: A message in transit with sender, label, and value
- `Queue`: FIFO queue of messages
- `Configuration`: Parallel processes plus message queues
- `Configuration.isDone`: Check if configuration has terminated
- `Configuration.queuesEmpty`: Check if all queues are empty

## Main Definitions

- `Message` - Structure for in-flight messages
- `Queue` - Type alias for message lists
- `Configuration` - Main configuration structure
-/

namespace Rumpsteak.Protocol.Semantics.Configuration

open Rumpsteak.Protocol.GlobalType (Label)
open Rumpsteak.Protocol.Semantics.Process

/-- A message in transit between two roles. -/
structure Message where
  /-- The sender role -/
  sender : String
  /-- The message label -/
  label : Label
  /-- The message payload -/
  value : Value
deriving Repr, DecidableEq, BEq, Inhabited

/-- A queue of messages between two roles.
    Messages are ordered FIFO (first in, first out). -/
abbrev Queue := List Message

/-- A channel identifies a directed communication path. -/
structure Channel where
  /-- The sender role -/
  sender : String
  /-- The receiver role -/
  receiver : String
deriving Repr, DecidableEq, BEq, Inhabited

/-- Configuration: parallel processes plus message queues.

    A configuration represents the complete runtime state of a
    multiparty session, including:
    - A process for each participating role
    - FIFO message queues for each directed channel -/
structure Configuration where
  /-- Processes for each role -/
  processes : List RoleProcess
  /-- Message queues indexed by channel -/
  queues : List (Channel × Queue)
deriving Repr, Inhabited

/-- Create an empty configuration with given roles and empty queues. -/
def Configuration.empty (roles : List String) : Configuration :=
  let procs := roles.map fun r => { role := r, process := Process.inaction }
  let channels := roles.flatMap fun s =>
    roles.filterMap fun r =>
      if s != r then some { sender := s, receiver := r } else none
  let queues := channels.map fun ch => (ch, [])
  { processes := procs, queues := queues }

/-- Get the process for a specific role. -/
def Configuration.getProcess (c : Configuration) (role : String) : Option Process :=
  c.processes.find? (fun rp => rp.role == role) |>.map (·.process)

/-- Update the process for a specific role. -/
def Configuration.setProcess (c : Configuration) (role : String) (proc : Process) : Configuration :=
  { c with processes := c.processes.map fun rp =>
      if rp.role == role then { rp with process := proc } else rp }

/-- Get the queue for a specific channel. -/
def Configuration.getQueue (c : Configuration) (ch : Channel) : Queue :=
  c.queues.find? (fun (ch', _) => ch' == ch) |>.map (·.2) |>.getD []

/-- Update the queue for a specific channel. -/
def Configuration.setQueue (c : Configuration) (ch : Channel) (q : Queue) : Configuration :=
  { c with queues := c.queues.map fun (ch', q') =>
      if ch' == ch then (ch', q) else (ch', q') }

/-- Enqueue a message on a channel (add to end). -/
def Configuration.enqueue (c : Configuration) (ch : Channel) (msg : Message) : Configuration :=
  let q := c.getQueue ch
  c.setQueue ch (q ++ [msg])

/-- Dequeue a message from a channel (remove from front). -/
def Configuration.dequeue (c : Configuration) (ch : Channel) : Option (Message × Configuration) :=
  let q := c.getQueue ch
  match q with
  | [] => none
  | msg :: rest => some (msg, c.setQueue ch rest)

/-- Check if configuration has terminated (all processes done, queues empty). -/
def Configuration.isDone (c : Configuration) : Bool :=
  c.processes.all (fun rp => rp.process.isTerminated) &&
  c.queues.all (fun (_, q) => q.isEmpty)

/-- Check if all queues are empty. -/
def Configuration.queuesEmpty (c : Configuration) : Bool :=
  c.queues.all (fun (_, q) => q.isEmpty)

/-- Count total messages in all queues. -/
def Configuration.totalMessages (c : Configuration) : Nat :=
  c.queues.foldl (fun acc (_, q) => acc + q.length) 0

/-- Get all non-empty queues. -/
def Configuration.nonEmptyQueues (c : Configuration) : List (Channel × Queue) :=
  c.queues.filter (fun (_, q) => !q.isEmpty)

/-- Get all roles that can currently make progress. -/
def Configuration.activeRoles (c : Configuration) : List String :=
  c.processes.filterMap fun rp =>
    match rp.process with
    | .inaction => none
    | .var _ => none
    | _ => some rp.role

/-! ## Lemmas for setProcess -/

/-- Helper: find? preserves under map when the element is unchanged. -/
private theorem find?_map_unchanged {α : Type _} (l : List α) (p : α → Bool) (f : α → α)
    (hf : ∀ a, p a = true → f a = a)
    (hfp : ∀ a, p (f a) = p a)
    : (l.map f).find? p = l.find? p := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.find?_cons, hfp]
    split
    · -- p x = true
      rename_i hp
      rw [hf x hp]
    · -- p x = false
      exact ih

/-- setProcess preserves the process for other roles. -/
theorem Configuration.setProcess_preserves_other
    (c : Configuration) (role otherRole : String) (proc : Process)
    (hne : role ≠ otherRole)
    : (c.setProcess role proc).getProcess otherRole = c.getProcess otherRole := by
  unfold setProcess getProcess
  congr 1
  apply find?_map_unchanged
  · intro rp hp
    simp only [beq_iff_eq] at hp
    have : rp.role ≠ role := by rw [hp]; exact hne.symm
    simp only [beq_eq_false_iff_ne.mpr this, Bool.false_eq_true, ↓reduceIte]
  · intro rp
    cases h : rp.role == role
    · rfl
    · rfl

/-- Helper for setProcess_sets_role. -/
private theorem setProcess_sets_role_aux (l : List RoleProcess) (role : String) (proc : Process)
    (hexists : (l.find? (fun rp => rp.role == role)).map (·.process) ≠ none)
    : ((l.map fun rp => if rp.role == role then { rp with process := proc } else rp).find?
        (fun rp => rp.role == role)).map (·.process) = some proc := by
  induction l with
  | nil => simp only [List.find?_nil, Option.map_none, ne_eq, not_true_eq_false] at hexists
  | cons rp rest ih =>
    simp only [List.map_cons, List.find?_cons]
    cases hrp : rp.role == role with
    | true => simp only [hrp, ↓reduceIte, Option.map_some]
    | false =>
      simp only [hrp, Bool.false_eq_true, ↓reduceIte]
      apply ih
      simp only [List.find?_cons, hrp] at hexists
      exact hexists

/-- setProcess sets the process for the target role. -/
theorem Configuration.setProcess_sets_role
    (c : Configuration) (role : String) (proc : Process)
    (hexists : c.getProcess role ≠ none)
    : (c.setProcess role proc).getProcess role = some proc := by
  unfold setProcess getProcess at *
  exact setProcess_sets_role_aux c.processes role proc hexists

/-- After setProcess, the processes list has the same length. -/
theorem Configuration.setProcess_length
    (c : Configuration) (role : String) (proc : Process)
    : (c.setProcess role proc).processes.length = c.processes.length := by
  unfold setProcess
  simp only [List.length_map]

/-- setProcess preserves membership for other roles. -/
theorem Configuration.setProcess_mem_other
    (c : Configuration) (role : String) (proc : Process)
    (rp : RoleProcess) (hrp : rp ∈ c.processes) (hne : rp.role ≠ role)
    : rp ∈ (c.setProcess role proc).processes := by
  unfold setProcess
  simp only [List.mem_map]
  refine ⟨rp, hrp, ?_⟩
  have h : (rp.role == role) = false := beq_eq_false_iff_ne.mpr hne
  simp only [h, Bool.false_eq_true, ↓reduceIte]

/-- setProcess preserves queues. -/
theorem Configuration.setProcess_queues
    (c : Configuration) (role : String) (proc : Process)
    : (c.setProcess role proc).queues = c.queues := by
  unfold setProcess
  rfl

/-- enqueue preserves processes. -/
theorem Configuration.enqueue_processes
    (c : Configuration) (ch : Channel) (msg : Message)
    : (c.enqueue ch msg).processes = c.processes := by
  unfold enqueue setQueue
  rfl

end Rumpsteak.Protocol.Semantics.Configuration
