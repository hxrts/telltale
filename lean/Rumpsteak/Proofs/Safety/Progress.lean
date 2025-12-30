/-! # Rumpsteak.Proofs.Safety.Progress

Progress theorem for multiparty sessions.

## Overview

Progress states that well-typed configurations can always make progress:
they are either done (all processes terminated, queues empty) or can take
a reduction step. This guarantees deadlock freedom.

Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)

## Claims

- `Progress`: If ⊢ M : G and M ≠ done, then ∃ M'. M → M'
- `DeadlockFreedom`: Well-typed configurations never get stuck

## Main Results

- `progress`: Main theorem
-/

import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.LocalTypeR
import Rumpsteak.Protocol.ProjectionR
import Rumpsteak.Protocol.Semantics.Process
import Rumpsteak.Protocol.Semantics.Configuration
import Rumpsteak.Protocol.Semantics.Reduction
import Rumpsteak.Protocol.Semantics.Typing

namespace Rumpsteak.Proofs.Safety.Progress

open Rumpsteak.Protocol.GlobalType
open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.ProjectionR
open Rumpsteak.Protocol.Semantics.Process
open Rumpsteak.Protocol.Semantics.Configuration
open Rumpsteak.Protocol.Semantics.Reduction
open Rumpsteak.Protocol.Semantics.Typing

/-! ## Claims -/

/-- Progress: well-typed, non-terminated configurations can reduce.

    Theorem 2 (Yoshida & Gheri):
    If a configuration M is well-typed against global type G,
    and M is not done, then there exists M' such that M → M'.

    Formal: ∀ G M, ⊢ M : G → ¬ M.isDone → ∃ M'. M → M' -/
def Progress : Prop :=
  ∀ (g : GlobalType) (c : Configuration),
    ConfigWellTyped g c → ¬ c.isDone → ∃ c', Reduces c c'

/-- Deadlock Freedom: well-typed configurations never get stuck.

    A stuck configuration is one that is not done but cannot reduce.
    This claim says well-typed configurations are never stuck.

    Formal: ∀ G M, ⊢ M : G → ¬ isStuck M -/
def DeadlockFreedom : Prop :=
  ∀ (g : GlobalType) (c : Configuration),
    ConfigWellTyped g c → ¬ isStuck c

/-- Canonical Forms: well-typed processes have expected structure. -/
def CanonicalSend : Prop :=
  ∀ (Γ : TypingContext) (p : Process) (receiver : String) (label : Label) (t : LocalTypeR),
    WellTyped Γ p (.send receiver [(label, t)]) →
    ∃ (value : Value) (cont : Process), p = .send receiver label value cont

def CanonicalRecv : Prop :=
  ∀ (Γ : TypingContext) (p : Process) (sender : String) (types : List (Label × LocalTypeR)),
    WellTyped Γ p (.recv sender types) →
    ∃ (branches : List (Label × Process)), p = .recv sender branches

/-- Claims bundle for progress properties. -/
structure Claims where
  /-- Main progress theorem -/
  progress : Progress
  /-- Deadlock freedom -/
  deadlockFreedom : DeadlockFreedom
  /-- Canonical form for send -/
  canonicalSend : CanonicalSend
  /-- Canonical form for recv -/
  canonicalRecv : CanonicalRecv

/-! ## Proofs -/

/-- Canonical form for send types. -/
theorem canonical_send : CanonicalSend := by
  intro Γ p receiver label t h
  cases h with
  | send h_cont =>
    rename_i value cont _
    exact ⟨value, cont, rfl⟩

/-- Canonical form for receive types. -/
theorem canonical_recv : CanonicalRecv := by
  intro Γ p sender types h
  cases h with
  | recv hlen hall hlabel =>
    rename_i branches
    exact ⟨branches, rfl⟩

/-- Deadlock freedom follows from progress. -/
theorem deadlock_freedom_from_progress (h : Progress) : DeadlockFreedom := by
  intro g c hwt hstuck
  unfold isStuck at hstuck
  obtain ⟨hnotdone, hnoreduce⟩ := hstuck
  have ⟨c', hred⟩ := h g c hwt hnotdone
  exact hnoreduce c' hred

/-- Helper: If not all processes are terminated, there's an active role. -/
theorem exists_active_process (c : Configuration)
    (hproc : ¬ c.processes.all (fun rp => rp.process.isTerminated))
    : ∃ rp, rp ∈ c.processes ∧ ¬ rp.process.isTerminated := by
  simp only [List.all_eq_true, Bool.not_eq_true'] at hproc
  push_neg at hproc
  obtain ⟨rp, hrp, hterm⟩ := hproc
  exact ⟨rp, hrp, Bool.not_eq_true _ ▸ hterm⟩

/-- Helper: A send process can always reduce (enqueue is always possible). -/
theorem send_can_reduce (c : Configuration) (role receiver : String)
    (label : Label) (value : Value) (cont : Process)
    (hrp : c.getProcess role = some (.send receiver label value cont))
    : ∃ c', Reduces c c' := by
  use Reduces.reduceSendConfig c role receiver label value cont
  exact Reduces.send c role receiver label value cont hrp

/-- Helper: A conditional process can always reduce. -/
theorem cond_can_reduce (c : Configuration) (role : String)
    (b : Bool) (p q : Process)
    (hrp : c.getProcess role = some (.cond b p q))
    : ∃ c', Reduces c c' := by
  use c.setProcess role (if b then p else q)
  exact Reduces.cond c role b p q hrp

/-- Helper: A recursive process can always reduce (unfold). -/
theorem rec_can_reduce (c : Configuration) (role x : String) (body : Process)
    (hrp : c.getProcess role = some (.rec x body))
    : ∃ c', Reduces c c' := by
  use c.setProcess role (body.substitute x (.rec x body))
  exact Reduces.rec c role x body hrp

/-- Progress theorem.

    Proof outline (Theorem 2, Yoshida & Gheri):
    1. If M is not done, either some process is not terminated or queues not empty
    2. Case analysis on the non-terminated process:
       - send: can always enqueue
       - recv: by well-typedness, matching message exists or sender will send
       - cond: can always evaluate
       - rec: can always unfold
    3. The key insight for recv is that the global type ensures
       matching send/recv pairs -/
theorem progress : Progress := by
  intro g c hwt hnotdone
  -- Configuration is not done means: not all terminated OR queues not empty
  unfold Configuration.isDone at hnotdone
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff] at hnotdone
  cases hnotdone with
  | inl hproc =>
    -- Some process is not terminated
    obtain ⟨rp, hrp, hactive⟩ := exists_active_process c hproc
    -- Case analysis on the process
    cases hproc_form : rp.process with
    | inaction =>
      -- Contradiction: inaction is terminated
      unfold Process.isTerminated at hactive
      simp only [hproc_form] at hactive
      exact absurd rfl hactive
    | var x =>
      -- Free variable: shouldn't occur in well-typed configs
      -- Well-typed processes in empty context are closed
      unfold ConfigWellTyped RoleProcessWellTyped at hwt
      simp only [List.all_eq_true, decide_eq_true_eq] at hwt
      have hwt_rp := hwt rp hrp
      cases hproj : projectR g rp.role with
      | ok lt =>
        simp only [hproj, hproc_form] at hwt_rp
        -- A variable can't be typed by any local type in empty context
        cases hwt_rp with
        | var hlookup =>
          unfold TypingContext.lookup at hlookup
          simp at hlookup
      | error _ =>
        simp only [hproj] at hwt_rp
    | send receiver label value cont =>
      have hget : c.getProcess rp.role = some (.send receiver label value cont) := by
        unfold Configuration.getProcess
        simp only [Option.map_eq_some_iff]
        exact ⟨rp, hrp, hproc_form⟩
      exact send_can_reduce c rp.role receiver label value cont hget
    | recv sender branches =>
      -- TODO: Receive case - the hardest part of the progress proof
      --
      -- Strategy outline (following Yoshida & Gheri Theorem 2):
      -- 1. By well-typedness, the receiver's type is ?sender{lᵢ.Tᵢ}
      -- 2. The global type has a matching comm(sender, receiver, {lᵢ.Gᵢ})
      -- 3. Case split on sender's process state:
      --    a. If sender has matching send: can reduce via [Send]+[Recv]
      --    b. If sender is blocked on recv: apply IH to show sender can progress
      --    c. If sender is terminated: contradiction (global type says comm pending)
      -- 4. Key insight: the global type G ensures a send/recv pair exists
      --
      -- Required lemmas:
      -- - `global_type_comm_exists`: If p : ?q{...}, global has comm(q,p,...)
      -- - `sender_has_matching_send`: Well-typed sender with !p{l.T} is send process
      -- - `queue_has_message_or_sender_will_send`: Either message in queue or
      --   sender process is send (by well-formedness of the global type)
      sorry
    | cond b p q =>
      have hget : c.getProcess rp.role = some (.cond b p q) := by
        unfold Configuration.getProcess
        simp only [Option.map_eq_some_iff]
        exact ⟨rp, hrp, hproc_form⟩
      exact cond_can_reduce c rp.role b p q hget
    | rec x body =>
      have hget : c.getProcess rp.role = some (.rec x body) := by
        unfold Configuration.getProcess
        simp only [Option.map_eq_some_iff]
        exact ⟨rp, hrp, hproc_form⟩
      exact rec_can_reduce c rp.role x body hget
    | par p q =>
      -- TODO: Parallel at process level
      --
      -- This case should be ruled out by the typing judgment.
      -- Our WellTyped relation doesn't have a case for Process.par,
      -- so a well-typed process in empty context cannot be a par.
      --
      -- Required: Show WellTyped [] (.par p q) lt is uninhabited
      -- by cases on the WellTyped constructors (none match par).
      sorry
  | inr hqueue =>
    -- TODO: Orphan messages case - prove this is impossible for well-typed configs
    --
    -- If all processes are terminated but queues are non-empty, we have
    -- "orphan messages" - sent messages that will never be received.
    --
    -- Strategy:
    -- 1. By well-typedness, each process type matches its projected local type
    -- 2. Global type well-formedness ensures balanced send/recv
    -- 3. If process p sent message m to q, then:
    --    - p's local type had a send action
    --    - q's local type has a matching recv action
    --    - Since q is terminated (type end), it must have consumed the recv
    -- 4. Therefore, the message must have been received - contradiction
    --
    -- Required lemmas:
    -- - `terminated_has_end_type`: isTerminated p → WellTyped Γ p .end
    -- - `send_recv_balance`: Well-formed global types have matching sends/recvs
    -- - `queue_empty_when_all_terminated`: Well-typed + all terminated → queues empty
    sorry

/-! ## Partial Claims Bundle -/

/-- Partial claims with proven lemmas. -/
def partialClaims : CanonicalSend ∧ CanonicalRecv :=
  ⟨canonical_send, canonical_recv⟩

end Rumpsteak.Proofs.Safety.Progress
