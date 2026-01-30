import SessionTypes.GlobalType

/-! # Semantics.Environment

Environment configuration for MPST execution.

This module defines the runtime environment state including message queues,
pending timeouts, and environment actions (delivery, timeout events).

## Design Principles

- Message queues are FIFO per sender-receiver pair
- Timeouts are per-role pending events (no global clock)
- Environment actions are nondeterministic choices
- No observable effect without a step (silent denial)

## Expose

The following definitions form the semantic interface for proofs:

- `MsgQueue` - Per-channel message queue
- `EnvConfig` - Environment configuration state
- `EnvAction` - Environment action (deliver, timeout, drop)
- `EnvConfigStep` - Environment transition relation
- `FairEnv` - Fairness predicate for liveness
-/

namespace Semantics.Environment

open SessionTypes.GlobalType (Label)

/-! ## Message Queues

Messages are queued per sender-receiver pair. Each queue is FIFO.
-/

/-- A role name in the protocol. -/
abbrev RoleName := String

/-- A message in transit: label with optional payload type. -/
structure Message where
  label : Label
  deriving Inhabited, Repr, DecidableEq, BEq

/-- Per-channel message queue (FIFO). -/
abbrev MsgQueue := List Message

/-- Channel identifier: ordered pair of sender and receiver. -/
structure Channel where
  sender : RoleName
  receiver : RoleName
  deriving Inhabited, Repr, DecidableEq, Hashable

/-- BEq instance derived from DecidableEq. -/
instance : BEq Channel := ⟨fun a b => decide (a = b)⟩

/-- LawfulBEq instance for Channel. -/
instance : LawfulBEq Channel where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

namespace Channel

/-- Create a channel from sender to receiver. -/
def mk' (s r : RoleName) : Channel := ⟨s, r⟩

/-- Reverse channel direction. -/
def reverse (ch : Channel) : Channel := ⟨ch.receiver, ch.sender⟩

end Channel

/-! ## Environment Configuration

The environment tracks:
- Message queues per channel
- Pending timeout events per role
- Delivery status (for fairness tracking)
-/

/-- Timeout event pending for a role. -/
structure PendingTimeout where
  role : RoleName
  label : Label
  deriving Inhabited, Repr, DecidableEq, BEq

/-- Environment configuration state.

This captures the runtime state outside of protocol logic:
- `queues`: messages in transit between role pairs
- `pendingTimeouts`: timeout events that may fire
- `deliveryCount`: for fairness tracking (messages eventually delivered)
-/
structure EnvConfig where
  /-- Message queues indexed by channel. -/
  queues : Channel → MsgQueue
  /-- Pending timeout events. -/
  pendingTimeouts : List PendingTimeout
  /-- Delivery counter for fairness (monotonically increasing). -/
  deliveryCount : Nat := 0
  deriving Inhabited

namespace EnvConfig

/-- Empty environment with no messages or timeouts. -/
def empty : EnvConfig where
  queues := fun _ => []
  pendingTimeouts := []

/-- Get the queue for a specific channel. -/
def getQueue (env : EnvConfig) (ch : Channel) : MsgQueue :=
  env.queues ch

/-- Check if a channel has pending messages. -/
def hasMessages (env : EnvConfig) (ch : Channel) : Bool :=
  !(env.queues ch).isEmpty

/-- Enqueue a message on a channel. -/
def enqueue (env : EnvConfig) (ch : Channel) (msg : Message) : EnvConfig :=
  { env with queues := fun c => if c == ch then env.queues ch ++ [msg] else env.queues c }

/-- Dequeue the first message from a channel (if any). -/
def dequeue (env : EnvConfig) (ch : Channel) : Option (Message × EnvConfig) :=
  match env.queues ch with
  | [] => none
  | msg :: rest =>
      some (msg, { env with
        queues := fun c => if c == ch then rest else env.queues c
        deliveryCount := env.deliveryCount + 1
      })

/-- Add a pending timeout. -/
def addTimeout (env : EnvConfig) (role : RoleName) (label : Label) : EnvConfig :=
  { env with pendingTimeouts := ⟨role, label⟩ :: env.pendingTimeouts }

/-- Remove a pending timeout (if it exists). -/
def removeTimeout (env : EnvConfig) (role : RoleName) (label : Label) : EnvConfig :=
  { env with pendingTimeouts := env.pendingTimeouts.filter (fun t => !(t.role == role && t.label == label)) }

/-- Check if a timeout is pending. -/
def hasTimeout (env : EnvConfig) (role : RoleName) (label : Label) : Bool :=
  env.pendingTimeouts.any (fun t => t.role == role && t.label == label)

/-- Total number of messages in all queues. -/
def totalMessages (env : EnvConfig) (channels : List Channel) : Nat :=
  channels.foldl (fun acc ch => acc + (env.queues ch).length) 0

end EnvConfig

/-! ## Environment Actions

Environment actions represent nondeterministic choices made by the runtime:
- Message delivery (dequeue and deliver to receiver)
- Timeout firing (signal timeout to a role)
- Message drop (for unreliable channels, if modeled)
-/

/-- Environment action: a nondeterministic event from the runtime. -/
inductive EnvAction where
  /-- Deliver a message from sender to receiver. -/
  | deliver : Channel → Message → EnvAction
  /-- Fire a timeout event for a role. -/
  | timeout : RoleName → Label → EnvAction
  /-- Drop a message (unreliable channel). -/
  | drop : Channel → Message → EnvAction
  deriving Inhabited, Repr, DecidableEq, BEq

namespace EnvAction

/-- Check if action is a delivery. -/
def isDeliver : EnvAction → Bool
  | deliver _ _ => true
  | _ => false

/-- Check if action is a timeout. -/
def isTimeout : EnvAction → Bool
  | timeout _ _ => true
  | _ => false

/-- Get the channel for delivery/drop actions. -/
def channel? : EnvAction → Option Channel
  | deliver ch _ => some ch
  | drop ch _ => some ch
  | _ => none

end EnvAction

/-! ## Environment Step Relation

The environment can transition based on actions. This is separate from
protocol steps—the environment provides the nondeterminism.
-/

/-- Environment step: action transforms environment state.

This relation captures what the environment can do:
- Deliver: dequeue message and mark delivered
- Timeout: fire pending timeout and remove from pending
- Drop: remove message without delivery (unreliable)
-/
inductive EnvConfigStep : EnvConfig → EnvAction → EnvConfig → Prop where
  /-- Deliver the head message from a channel. -/
  | deliver (env : EnvConfig) (ch : Channel) (msg : Message) (env' : EnvConfig) :
      env.queues ch = msg :: rest →
      env' = { env with
        queues := fun c => if c == ch then rest else env.queues c
        deliveryCount := env.deliveryCount + 1 } →
      EnvConfigStep env (.deliver ch msg) env'

  /-- Fire a pending timeout. -/
  | timeout (env : EnvConfig) (role : RoleName) (label : Label) (env' : EnvConfig) :
      env.hasTimeout role label = true →
      env' = env.removeTimeout role label →
      EnvConfigStep env (.timeout role label) env'

  /-- Drop a message from a channel (unreliable transport). -/
  | drop (env : EnvConfig) (ch : Channel) (msg : Message) (env' : EnvConfig) :
      env.queues ch = msg :: rest →
      env' = { env with queues := fun c => if c == ch then rest else env.queues c } →
      EnvConfigStep env (.drop ch msg) env'

/-! ## Fairness

Fairness ensures eventual delivery: if a message is enqueued and the receiver
is ready, it will eventually be delivered. This is a property of traces,
not individual steps.
-/

/-- A trace is a sequence of environment configurations. -/
abbrev EnvTrace := List EnvConfig

/-- Get element at index with default. -/
private def EnvTrace.getAt (tr : EnvTrace) (i : Nat) : Option EnvConfig :=
  if h : i < tr.length then some (tr[i]'h) else none

/-- Fairness predicate: messages are eventually delivered.

A trace is fair if:
1. Every enqueued message is eventually delivered (weak fairness)
2. Pending timeouts eventually fire if the role is waiting (weak fairness)

This is specified coinductively in practice, but we define the property here.
-/
def FairEnv (trace : EnvTrace) : Prop :=
  -- For now, a simple approximation: delivery count increases unboundedly
  -- or all queues eventually empty
  ∀ i, i < trace.length →
    ∃ j, j > i ∧ j < trace.length ∧
      (match trace.getAt j, trace.getAt i with
        | some envJ, some envI => envJ.deliveryCount > envI.deliveryCount
        | _, _ => False) ∨
      (match trace.getAt j with
        | some env => env.pendingTimeouts.isEmpty
        | none => False)

/-- Strong fairness: every infinitely often enabled action is taken infinitely often. -/
def StrongFairEnv (trace : EnvTrace) : Prop :=
  -- Placeholder for strong fairness
  FairEnv trace

/-! ## Queue Invariants

Properties of message queues for reasoning about protocol execution.
-/

/-- All queues are empty. -/
def EnvConfig.allQueuesEmpty (env : EnvConfig) (channels : List Channel) : Prop :=
  ∀ ch, ch ∈ channels → env.queues ch = []

/-- No pending timeouts. -/
def EnvConfig.noTimeouts (env : EnvConfig) : Prop :=
  env.pendingTimeouts = []

/-- Quiescent environment: no messages, no timeouts. -/
def EnvConfig.quiescent (env : EnvConfig) (channels : List Channel) : Prop :=
  env.allQueuesEmpty channels ∧ env.noTimeouts

/-- Enqueue preserves other channels. -/
theorem enqueue_other (env : EnvConfig) (ch ch' : Channel) (msg : Message)
    (hne : ch ≠ ch') :
    (env.enqueue ch msg).queues ch' = env.queues ch' := by
  simp only [EnvConfig.enqueue]
  split
  · next heq => exact absurd (beq_iff_eq.mp heq) hne.symm
  · rfl

/-- Dequeue reduces queue length by one. -/
theorem dequeue_length (env : EnvConfig) (ch : Channel) (msg : Message) (env' : EnvConfig)
    (hdeq : env.dequeue ch = some (msg, env')) :
    (env'.queues ch).length + 1 = (env.queues ch).length := by
  unfold EnvConfig.dequeue at hdeq
  cases hq : env.queues ch with
  | nil => simp [hq] at hdeq
  | cons m rest =>
      simp [hq] at hdeq
      obtain ⟨hmsg, henv'⟩ := hdeq
      subst henv' hmsg
      simp only [↓reduceIte, List.length_cons]

end Semantics.Environment
