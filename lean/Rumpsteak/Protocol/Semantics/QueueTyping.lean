import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.ProjectionR
import Rumpsteak.Protocol.Semantics.Typing

/-! # Rumpsteak.Protocol.Semantics.QueueTyping

Async queue typing scaffolding for subject reduction.

This module defines queue-type environments and basic consistency predicates.
It mirrors the shape of the Coq development (see `subject_reduction/README.md`
and `subject_reduction/theories/Process/Congruence.v`).
-/

namespace Rumpsteak.Protocol.Semantics.QueueTyping

open Rumpsteak.Protocol.GlobalType
open Rumpsteak.Protocol.ProjectionR
open Rumpsteak.Protocol.Semantics.Configuration
open Rumpsteak.Protocol.Semantics.Typing

/-- A queue type is the list of labels in FIFO order. -/
abbrev QueueType := List Label

/-- Queue type environment indexed by channel. -/
abbrev QueueTypeEnv := List (Channel × QueueType)

/-- Extract the queue type from a runtime queue. -/
def queueTypeOfQueue (q : Queue) : QueueType :=
  q.map (fun msg => msg.label)

/-- Extract a queue-type environment from a configuration. -/
def queueTypeEnvOfConfig (c : Configuration) : QueueTypeEnv :=
  c.queues.map (fun (ch, q) => (ch, queueTypeOfQueue q))

/-! ## Queue environment updates -/

/-- Update a queue-type environment at a channel. -/
def queueTypeEnv_setQueue (qenv : QueueTypeEnv) (ch : Channel) (qt : QueueType) : QueueTypeEnv :=
  qenv.map (fun (ch', qt') => if ch' == ch then (ch', qt) else (ch', qt'))

/-- Enqueue into a queue-type environment, setting the channel to the new labels. -/
def queueTypeEnv_enqueue (qenv : QueueTypeEnv) (ch : Channel) (qt : QueueType) : QueueTypeEnv :=
  queueTypeEnv_setQueue qenv ch qt

/-- Dequeue from a queue-type environment, setting the channel to the residual labels. -/
def queueTypeEnv_dequeue (qenv : QueueTypeEnv) (ch : Channel) (rest : QueueType) : QueueTypeEnv :=
  queueTypeEnv_setQueue qenv ch rest

inductive QueueEnvRed : QueueTypeEnv → QueueTypeEnv → Prop where
  | enqueue (qenv : QueueTypeEnv) (ch : Channel) (qt : QueueType) :
      QueueEnvRed qenv (queueTypeEnv_enqueue qenv ch qt)
  | dequeue (qenv : QueueTypeEnv) (ch : Channel) (rest : QueueType) :
      QueueEnvRed qenv (queueTypeEnv_dequeue qenv ch rest)

theorem queueTypeEnvOfConfig_setQueue (c : Configuration) (ch : Channel) (q : Queue) :
    queueTypeEnvOfConfig (c.setQueue ch q) =
      queueTypeEnv_setQueue (queueTypeEnvOfConfig c) ch (queueTypeOfQueue q) := by
  cases c with
  | mk procs queues =>
    -- unfold on the concrete list of queues
    unfold queueTypeEnvOfConfig queueTypeEnv_setQueue Configuration.setQueue
    -- now prove by induction on queues
    induction queues with
    | nil =>
      simp
    | cons pair rest ih =>
      cases pair with
      | mk ch' q' =>
        by_cases h : ch' = ch
        · subst h
          simp
          intro a b hmem
          by_cases hch : a = ch' <;> simp [hch]
        · simp [h, beq_iff_eq]
          intro a b hmem
          by_cases hch : a = ch <;> simp [hch]

theorem queueTypeEnvOfConfig_enqueue (c : Configuration) (ch : Channel) (msg : Message) :
    queueTypeEnvOfConfig (c.enqueue ch msg) =
      queueTypeEnv_enqueue (queueTypeEnvOfConfig c) ch
        (queueTypeOfQueue (c.getQueue ch ++ [msg])) := by
  unfold Configuration.enqueue
  -- enqueue uses setQueue with q ++ [msg]
  have :=
    queueTypeEnvOfConfig_setQueue c ch (c.getQueue ch ++ [msg])
  simpa [queueTypeEnv_enqueue, queueTypeEnv_setQueue, queueTypeOfQueue] using this

theorem queueTypeEnvOfConfig_dequeue (c c' : Configuration) (ch : Channel) (msg : Message)
    (hdeq : c.dequeue ch = some (msg, c')) :
    ∃ rest,
      c.getQueue ch = msg :: rest ∧
      queueTypeEnvOfConfig c' =
        queueTypeEnv_dequeue (queueTypeEnvOfConfig c) ch (queueTypeOfQueue rest) := by
  unfold Configuration.dequeue at hdeq
  cases hq : c.getQueue ch with
  | nil =>
    simp [hq] at hdeq
  | cons msg' rest =>
    simp [hq] at hdeq
    cases hdeq with
    | intro hmsg hc' =>
      cases hmsg
      cases hc'
      refine ⟨rest, ?_, ?_⟩
      · simp [hq]
      have := queueTypeEnvOfConfig_setQueue c ch rest
      simpa [queueTypeEnv_dequeue] using this

/-- A queue is well-typed against its queue type. -/
def QueueWellTyped (q : Queue) (qt : QueueType) : Prop :=
  List.Forall₂ (fun msg lbl =>
    msg.label = lbl) q qt

theorem QueueWellTyped_of_queueTypeOfQueue (q : Queue) :
    QueueWellTyped q (queueTypeOfQueue q) := by
  induction q with
  | nil => simp [QueueWellTyped, queueTypeOfQueue]
  | cons msg rest ih =>
    simp [QueueWellTyped, queueTypeOfQueue, ih]

theorem QueueWellTyped_enqueue {q : Queue} {qt : QueueType} {msg : Message}
    (h : QueueWellTyped q qt) :
    QueueWellTyped (q ++ [msg]) (qt ++ [msg.label]) := by
  induction h with
  | nil => simp [QueueWellTyped]
  | cons hhead hrest ih =>
    exact List.Forall₂.cons hhead (by simpa using ih)

theorem QueueWellTyped_dequeue {msg : Message} {q : Queue} {lbl : Label} {qt : QueueType}
    (h : QueueWellTyped (msg :: q) (lbl :: qt)) :
    QueueWellTyped q qt := by
  cases h with
  | cons _ hrest => simpa using hrest

/-- A configuration's queues are well-typed against a queue-type environment. -/
def QueueEnvWellTyped (c : Configuration) (qenv : QueueTypeEnv) : Prop :=
  List.Forall₂ (fun (cq : Channel × Queue) (qt : Channel × QueueType) =>
    cq.1 = qt.1 ∧ QueueWellTyped cq.2 qt.2) c.queues qenv

theorem QueueEnvWellTyped_setQueue (c : Configuration) (qenv : QueueTypeEnv)
    (ch : Channel) (q : Queue) (qtNew : QueueType)
    (h : QueueEnvWellTyped c qenv) (hqt : QueueWellTyped q qtNew) :
    QueueEnvWellTyped (c.setQueue ch q) (queueTypeEnv_setQueue qenv ch qtNew) := by
  -- This second proof uses explicit list recursion to avoid `simp` ambiguity.
  cases c with
  | mk procs queues =>
    unfold Configuration.setQueue queueTypeEnv_setQueue QueueEnvWellTyped at *
    -- recurse on the queue list, carrying the Forall₂ proof
    induction queues generalizing qenv with
    | nil =>
      cases qenv with
      | nil => simp at h ⊢
      | cons _ _ => cases h
    | cons cq rest ih =>
      cases qenv with
      | nil => cases h
      | cons qt restq =>
        cases h with
        | cons hhead htail =>
          rcases hhead with ⟨hch_eq, hqt_head⟩
          apply List.Forall₂.cons
          · cases hch : cq.1 == ch with
            | true =>
              have hch' : (qt.1 == ch) = true := by
                simpa [hch_eq] using hch
              refine ⟨?_, ?_⟩
              · calc
                  (if cq.1 == ch then (cq.1, q) else (cq.1, cq.2)).1
                      = cq.1 := by simp [hch]
                  _ = qt.1 := by simpa using hch_eq
                  _ = (if qt.1 == ch then (qt.1, qtNew) else (qt.1, qt.2)).1 := by
                        simp [hch']
              · simpa [hch, hch'] using hqt
            | false =>
              have hch' : (qt.1 == ch) = false := by
                simpa [hch_eq] using hch
              refine ⟨?_, ?_⟩
              · calc
                  (if cq.1 == ch then (cq.1, q) else (cq.1, cq.2)).1
                      = cq.1 := by simp [hch]
                  _ = qt.1 := by simpa using hch_eq
                  _ = (if qt.1 == ch then (qt.1, qtNew) else (qt.1, qt.2)).1 := by
                        simp [hch']
              · simpa [hch, hch'] using hqt_head
          · exact ih restq htail

theorem QueueEnvWellTyped_enqueue (c : Configuration) (qenv : QueueTypeEnv)
    (ch : Channel) (msg : Message)
    (h : QueueEnvWellTyped c qenv) :
    QueueEnvWellTyped (c.enqueue ch msg)
      (queueTypeEnv_enqueue qenv ch (queueTypeOfQueue (c.getQueue ch ++ [msg]))) := by
  -- enqueue is setQueue with q ++ [msg]
  unfold Configuration.enqueue
  refine QueueEnvWellTyped_setQueue c qenv ch (c.getQueue ch ++ [msg])
    (queueTypeOfQueue (c.getQueue ch ++ [msg])) h ?_
  exact QueueWellTyped_of_queueTypeOfQueue _

theorem QueueEnvWellTyped_dequeue (c c' : Configuration) (qenv : QueueTypeEnv)
    (ch : Channel) (msg : Message)
    (h : QueueEnvWellTyped c qenv)
    (hdeq : c.dequeue ch = some (msg, c')) :
    ∃ rest,
      c.getQueue ch = msg :: rest ∧
      QueueEnvWellTyped c' (queueTypeEnv_dequeue qenv ch (queueTypeOfQueue rest)) := by
  -- unfold dequeue to get the residual queue
  unfold Configuration.dequeue at hdeq
  cases hq : c.getQueue ch with
  | nil =>
    simp [hq] at hdeq
  | cons msg' rest =>
    simp [hq] at hdeq
    cases hdeq with
    | intro hmsg hc' =>
      cases hmsg
      cases hc'
      refine ⟨rest, ?_, ?_⟩
      · simp [hq]
      · exact QueueEnvWellTyped_setQueue c qenv ch rest (queueTypeOfQueue rest) h
          (QueueWellTyped_of_queueTypeOfQueue rest)

/-- Consume a sequence of labels on a channel (if possible). -/
def consumeLabels (g : GlobalType) (ch : Channel) : List Label → Option GlobalType
  | [] => some g
  | l :: ls =>
      match g.consume ch.sender ch.receiver l with
      | none => none
      | some g' => consumeLabels g' ch ls

/-- Queue env consistency with the global type (existence of a consumption path). -/
def QueueEnvConsistent (g : GlobalType) (qenv : QueueTypeEnv) : Prop :=
  ∀ ch labels, (ch, labels) ∈ qenv →
    ∃ g', consumeLabels g ch labels = some g'

axiom QueueEnvConsistent_enqueue (g : GlobalType) (qenv : QueueTypeEnv)
    (ch : Channel) (qt : QueueType)
    (hcons : QueueEnvConsistent g qenv) :
    QueueEnvConsistent g (queueTypeEnv_enqueue qenv ch qt)

axiom QueueEnvConsistent_dequeue (g : GlobalType) (qenv : QueueTypeEnv)
    (ch : Channel) (qt : QueueType)
    (hcons : QueueEnvConsistent g qenv) :
    QueueEnvConsistent g (queueTypeEnv_dequeue qenv ch qt)

/-- Queue-aware configuration typing (queue env + per-role typing). -/
def ConfigWellTypedQueue (g : GlobalType) (c : Configuration) : Prop :=
  c.hasUniqueRoles ∧
  ∃ qenv,
    QueueEnvWellTyped c qenv ∧
    QueueEnvConsistent g qenv ∧
    ∀ rp ∈ c.processes, ∃ g' lt,
      GlobalTypeStepStar g g' ∧
      projectR g' rp.role = .ok lt ∧
      WellTyped [] rp.process lt

end Rumpsteak.Protocol.Semantics.QueueTyping
