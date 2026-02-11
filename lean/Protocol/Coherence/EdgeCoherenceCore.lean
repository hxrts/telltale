import Protocol.Coherence.Consume

/-! # Protocol.Coherence.EdgeCoherence

Coherence lemmas and invariants for session-environment evolution.
-/

/-!
# MPST Coherence

This module defines the coherence invariant for multiparty session types.
-/

/-
The Problem. In MPST, multiple roles communicate via directed edges with asynchronous
buffers. We need an invariant that captures "all edges are in sync" without requiring
global re-derivation from a common ancestor type.

Solution Structure. We define edge-local coherence via the Consume function:
1. `Consume`: models how a local type evolves as buffered messages arrive
2. `EdgeCoherent`: per-edge check that sender/receiver types align with buffer
3. `Coherent`: all active edges are edge-coherent
4. 3-way case split for preservation: updated edge, related edge, unrelated edge
-/

/-!
In binary session types, coherence states that after consuming in-flight messages,
dual endpoints have dual types. In MPST, this generalizes to:

**For each directed edge (p → q) in session s:**
1. The sender's local type G[s,p] is consistent with what was sent on D[s,p,q]
2. The receiver's local type G[s,q] is consistent with what must be received on D[s,p,q]
3. The communication patterns match: sends to q align with branches from p

## Consume Function

The `Consume` function models how a local type evolves as buffered messages arrive.
For role p's view:
- `Consume L [] = some L` (no messages → unchanged)
- `Consume (recv q T L) (T :: ts) = Consume L ts` (receive consumes a message)
- `Consume (branch q bs) _ = ...` (branch must handle incoming label)

## Coherence Invariant

`Coherent G D` states that for every session and every **active** directed edge:
- Sender's continuation after sending matches what's in the queue
- Receiver's continuation after consuming matches sender's intent

## Proof Technique: Edge Case Analysis

The key preservation proofs (`Coherent_send_preserved`, `Coherent_recv_preserved`)
proceed by case analysis on which edge we're checking coherence for:

1. **e = updated edge**: The sender's/receiver's local type changed, trace changed
2. **e involves modified endpoint**: The other endpoint of e was modified
3. **e unrelated**: Neither endpoint was modified, environments unchanged at e

This 3-way case split is the core proof technique for coherence preservation.
Adapted from binary session types where the split is: a = e, a = e.dual, a unrelated.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Edge-wise Coherence -/

/-- Coherence for a single directed edge.
    States that the sender's output on the edge matches what the receiver expects. -/
def EdgeCoherent (G : GEnv) (D : DEnv) (e : Edge) : Prop :=
  let senderEp := { sid := e.sid, role := e.sender : Endpoint }
  let receiverEp := { sid := e.sid, role := e.receiver : Endpoint }
  let trace := lookupD D e
  ∀ Lrecv,
    lookupG G receiverEp = some Lrecv →
    ∃ Lsender,
      lookupG G senderEp = some Lsender ∧
      -- After consuming what sender has sent (tracked in D[sender,receiver])
      -- from receiver's perspective, receiver can handle it
      (Consume e.sender Lrecv trace).isSome

/-! ### Active Edges -/

/-- An edge is active if both sender and receiver endpoints exist in G. -/
def ActiveEdge (G : GEnv) (e : Edge) : Prop :=
  (lookupG G { sid := e.sid, role := e.sender }).isSome ∧
  (lookupG G { sid := e.sid, role := e.receiver }).isSome

/-- Full coherence: edge-coherent for all **active** edges. -/
def Coherent (G : GEnv) (D : DEnv) : Prop :=
  ∀ e, ActiveEdge G e → EdgeCoherent G D e

/-! ### Small Helpers -/

/-- ActiveEdge from concrete sender/receiver lookups. -/
theorem ActiveEdge_of_endpoints {G : GEnv} {e : Edge} {Lsender Lrecv : LocalType}
    (hGsender : lookupG G { sid := e.sid, role := e.sender } = some Lsender)
    (hGrecv : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv) :
    ActiveEdge G e := by
  simp [ActiveEdge, hGsender, hGrecv]

/-- If an edge is active after updating one endpoint, it was already active before. -/
theorem ActiveEdge_updateG_inv {G : GEnv} {e : Edge} {ep : Endpoint} {L : LocalType} :
    ActiveEdge (updateG G ep L) e →
    (lookupG G ep).isSome →
    ActiveEdge G e := by
  intro hActive hEp
  rcases hActive with ⟨hSender, hRecv⟩
  have hSender' : (lookupG G { sid := e.sid, role := e.sender }).isSome := by
    rcases (Option.isSome_iff_exists).1 hSender with ⟨Ls, hLs⟩
    by_cases hEq : ({ sid := e.sid, role := e.sender } : Endpoint) = ep
    · simpa [hEq] using hEp
    · have hNe : ep ≠ { sid := e.sid, role := e.sender } := by
        exact Ne.symm hEq
      have hLs' : lookupG G { sid := e.sid, role := e.sender } = some Ls := by
        simpa [lookupG_update_neq _ _ _ _ hNe] using hLs
      exact (Option.isSome_iff_exists).2 ⟨Ls, hLs'⟩
  have hRecv' : (lookupG G { sid := e.sid, role := e.receiver }).isSome := by
    rcases (Option.isSome_iff_exists).1 hRecv with ⟨Lr, hLr⟩
    by_cases hEq : ({ sid := e.sid, role := e.receiver } : Endpoint) = ep
    · simpa [hEq] using hEp
    · have hNe : ep ≠ { sid := e.sid, role := e.receiver } := by
        exact Ne.symm hEq
      have hLr' : lookupG G { sid := e.sid, role := e.receiver } = some Lr := by
        simpa [lookupG_update_neq _ _ _ _ hNe] using hLr
      exact (Option.isSome_iff_exists).2 ⟨Lr, hLr'⟩
  exact ⟨hSender', hRecv'⟩

/-- Extract EdgeCoherent from Coherent given sender/receiver lookups. -/
theorem Coherent_edge_of_endpoints {G : GEnv} {D : DEnv} {e : Edge}
    {Lsender Lrecv : LocalType}
    (hCoh : Coherent G D)
    (hGsender : lookupG G { sid := e.sid, role := e.sender } = some Lsender)
    (hGrecv : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv) :
    EdgeCoherent G D e := by
  exact hCoh e (ActiveEdge_of_endpoints hGsender hGrecv)

/-- Coherent gives EdgeCoherent for any active edge. -/
theorem Coherent_edge_any {G : GEnv} {D : DEnv} (hCoh : Coherent G D) {e : Edge}
    (hActive : ActiveEdge G e) :
    EdgeCoherent G D e := by
  exact hCoh e hActive

/-- Extract EdgeCoherent content from Coherent given receiver lookup and active edge.
    Returns sender exists and consume succeeds. -/
theorem Coherent_edge_of_receiver {G : GEnv} {D : DEnv} {e : Edge} {Lrecv : LocalType}
    (hCoh : Coherent G D)
    (hGrecv : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv)
    (hActive : ActiveEdge G e := by simp [ActiveEdge, hGrecv, *]) :
    ∃ Lsender,
      lookupG G { sid := e.sid, role := e.sender } = some Lsender ∧
      (Consume e.sender Lrecv (lookupD D e)).isSome := by
  exact hCoh e hActive Lrecv hGrecv

/-- Extract the consume condition from `EdgeCoherent` given a receiver lookup. -/
theorem EdgeCoherent_consume_of_receiver {G : GEnv} {D : DEnv} {e : Edge} {Lrecv : LocalType}
    (hCoh : EdgeCoherent G D e)
    (hGrecv : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv) :
    (Consume e.sender Lrecv (lookupD D e)).isSome := by
  rcases hCoh Lrecv hGrecv with ⟨_, _, hConsume⟩
  exact hConsume

/-- Extract the sender lookup guaranteed by `EdgeCoherent` given a receiver lookup. -/
theorem EdgeCoherent_sender_of_receiver {G : GEnv} {D : DEnv} {e : Edge} {Lrecv : LocalType}
    (hCoh : EdgeCoherent G D e)
    (hGrecv : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv) :
    ∃ Lsender, lookupG G { sid := e.sid, role := e.sender } = some Lsender := by
  rcases hCoh Lrecv hGrecv with ⟨Lsender, hGsender, _⟩
  exact ⟨Lsender, hGsender⟩


/-! ## Key Lemmas: EdgeCoherent Forces Empty Trace

These lemmas show that EdgeCoherent constrains trace structure:
1. For non-recv/branch receiver types (send, select, etc.), trace must be empty
2. For recv/branch with different sender, trace must be empty
-/

/-- If receiver type is send (or other non-recv/branch), trace must be empty.
    This is because Consume for .send only succeeds on empty trace. -/
theorem trace_empty_when_send_receiver
    {G : GEnv} {D : DEnv} {e : Edge}
    {r : Role} {T : ValType} {L : LocalType}
    (hCoh : EdgeCoherent G D e)
    (hSend : lookupG G ⟨e.sid, e.receiver⟩ = some (.send r T L)) :
    lookupD D e = [] := by
  simp only [EdgeCoherent] at hCoh
  obtain ⟨Ls, hLsender, hIsSome⟩ := hCoh (.send r T L) hSend
  have h : (Consume e.sender (.send r T L) (lookupD D e)).isSome := hIsSome
  cases hTrace : lookupD D e with
  | nil => rfl
  | cons t ts =>
    rw [hTrace] at h
    simp only [Consume, consumeOne, Option.isSome] at h
    exact Bool.noConfusion h

/-- Similar lemma for select receiver type. -/
theorem trace_empty_when_select_receiver
    {G : GEnv} {D : DEnv} {e : Edge}
    {r : Role} {bs : List (String × LocalType)}
    (hCoh : EdgeCoherent G D e)
    (hSelect : lookupG G ⟨e.sid, e.receiver⟩ = some (.select r bs)) :
    lookupD D e = [] := by
  simp only [EdgeCoherent] at hCoh
  obtain ⟨Ls, hLsender, hIsSome⟩ := hCoh (.select r bs) hSelect
  cases hTrace : lookupD D e with
  | nil => rfl
  | cons t ts =>
    rw [hTrace] at hIsSome
    simp only [Consume, consumeOne, Option.isSome] at hIsSome
    exact Bool.noConfusion hIsSome

/-! ## Key Lemma: Different Sender Forces Empty Trace

When the receiver's type expects messages from sender A, but we're examining
the edge from sender B (B ≠ A), EdgeCoherent forces the trace from B to be empty.
This is because Consume only succeeds on non-empty trace when sender matches.

This lemma is the key to solving "continuation recv/branch from different sender" cases. -/

/-- If receiver expects recv from r, but edge has different sender, trace must be empty.
    This is the creative shortcut that resolves the "different sender" sorries. -/
theorem trace_empty_when_recv_other_sender
    {G : GEnv} {D : DEnv} {e : Edge}
    {r : Role} {T : ValType} {L : LocalType}
    (hCoh : EdgeCoherent G D e)
    (hRecv : lookupG G ⟨e.sid, e.receiver⟩ = some (.recv r T L))
    (hNe : e.sender ≠ r) :
    lookupD D e = [] := by
  -- EdgeCoherent gives us a sender witness and that (Consume e.sender (.recv r T L) trace).isSome.
  simp only [EdgeCoherent] at hCoh
  obtain ⟨Ls, hLsender, hIsSome⟩ := hCoh (.recv r T L) hRecv
  -- hIsSome : (Consume e.sender (.recv r T L) (lookupD D e)).isSome
  -- From Consume_other_empty, if trace is non-empty, Consume returns none
  cases hTrace : lookupD D e with
  | nil => rfl
  | cons t ts =>
    -- Consume e.sender (.recv r T L) (t :: ts) returns none because e.sender ≠ r
    rw [hTrace] at hIsSome
    simp only [Consume, consumeOne] at hIsSome
    have hNeq : (e.sender == r) = false := beq_eq_false_iff_ne.mpr hNe
    simp only [hNeq, Bool.false_and, Option.isSome] at hIsSome
    exact Bool.noConfusion hIsSome

/-- Similar lemma for branch: if receiver expects branch from r, but edge has different sender, trace is empty. -/
theorem trace_empty_when_branch_other_sender
    {G : GEnv} {D : DEnv} {e : Edge}
    {r : Role} {bs : List (String × LocalType)}
    (hCoh : EdgeCoherent G D e)
    (hBranch : lookupG G ⟨e.sid, e.receiver⟩ = some (.branch r bs))
    (hNe : e.sender ≠ r) :
    lookupD D e = [] := by
  simp only [EdgeCoherent] at hCoh
  obtain ⟨Ls, hLsender, hIsSome⟩ := hCoh (.branch r bs) hBranch
  cases hTrace : lookupD D e with
  | nil => rfl
  | cons t ts =>
    rw [hTrace] at hIsSome
    simp only [Consume, consumeOne] at hIsSome
    have hNeq : (e.sender == r) = false := beq_eq_false_iff_ne.mpr hNe
    -- For branch, consumeOne checks if t is .string and r == from_
    cases t with
    | string =>
      have hFalse : False := by
        simpa [Consume, consumeOne, hNeq] using hIsSome
      exact hFalse.elim
    | _ =>
      -- If head is not string, consumeOne returns none anyway
      have hFalse : False := by
        simpa [Consume, consumeOne] using hIsSome
      exact hFalse.elim

/-! ## Head Coherent (Progress Refinement)

HeadCoherent is a refinement of Coherent that ensures the buffer head
matches the expected receive type. This is needed for progress because
plain Coherent only says the receiver can *eventually* consume all messages,
not that the *immediate* buffer head matches.

Reference: `work/effects/008.lean:380-391` -/

/-- Buffer head type matches expected receive type at receiver.

When the receiver expects `recv _ T _`, the buffer head (if any) must have type T.
When the receiver expects `branch`, the buffer head (if any) must be a string label.

This property is needed for progress: it ensures that when we have a non-empty
buffer, we can actually take a recv/branch step. -/
def HeadCoherent (G : GEnv) (D : DEnv) : Prop :=
  ∀ (e : Edge), ActiveEdge G e →
    let receiverEp : Endpoint := ⟨e.sid, e.receiver⟩
    match lookupG G receiverEp with
    | some (.recv _ T _) =>
      match lookupD D e with
      | [] => True  -- Empty buffer is fine (blocked)
      | T' :: _ => T = T'  -- Head must match expected type
    | some (.branch _ _) =>
      match lookupD D e with
      | [] => True
      | T' :: _ => T' = .string  -- Branch expects string label
    | _ => True

/-- Role-completeness for GEnv: if a local type mentions a peer role,
    that peer endpoint exists in G for the same session. -/
def RoleComplete (G : GEnv) : Prop :=
  ∀ e L, lookupG G e = some L →
    match LocalType.targetRole? L with
    | some r => ∃ L', lookupG G ⟨e.sid, r⟩ = some L'
    | none => True

/-- Role-completeness specialized to recv types. -/
theorem RoleComplete_recv
    {G : GEnv} {e : Endpoint} {r : Role} {T : ValType} {L : LocalType}
    (hComplete : RoleComplete G)
    (hG : lookupG G e = some (.recv r T L)) :
    ∃ L', lookupG G ⟨e.sid, r⟩ = some L' := by
  -- For recv, targetRole? = some r, so RoleComplete gives the witness directly.
  simpa [RoleComplete, LocalType.targetRole?] using hComplete e (.recv r T L) hG

/-- Role-completeness specialized to branch types. -/
theorem RoleComplete_branch
    {G : GEnv} {e : Endpoint} {r : Role} {bs : List (Label × LocalType)}
    (hComplete : RoleComplete G)
    (hG : lookupG G e = some (.branch r bs)) :
    ∃ L', lookupG G ⟨e.sid, r⟩ = some L' := by
  -- For branch, targetRole? = some r, so RoleComplete gives the witness directly.
  simpa [RoleComplete, LocalType.targetRole?] using hComplete e (.branch r bs) hG

/-- ValidLabels ensures received branch labels are valid.

When the receiver is at a branch type and the buffer contains a string label,
that label must be one of the valid branch options.

Reference: `work/effects/008.lean:392-397` -/
def ValidLabels (G : GEnv) (_D : DEnv) (bufs : Buffers) : Prop :=
  ∀ (e : Edge) (source : Role) (bs : List (Label × LocalType)),
    ActiveEdge G e →
    lookupG G ⟨e.sid, e.receiver⟩ = some (.branch source bs) →
    match lookupBuf bufs e with
    | (.string l) :: _ => (bs.find? (fun b => b.1 == l)).isSome
    | _ => True

/-! ## Receiver Readiness (Progress Support)

SendReady encodes the additional invariant needed for progress/preservation with
asynchronous buffers: after consuming the current trace on the edge, the receiver
can accept the next message of type T from the sender. This is exactly the
`hRecvReady` hypothesis required by `TypedStep.send`.
-/

/-- Receiver readiness for a send: after consuming the current trace on the edge,
    the receiver can consume one more message of type T from the sender. -/
def SendReady (G : GEnv) (D : DEnv) : Prop :=
  ∀ e q T L,
    lookupG G e = some (.send q T L) →
    ∀ Lrecv, lookupG G { sid := e.sid, role := q } = some Lrecv →
      ∃ L', Consume e.role Lrecv (lookupD D { sid := e.sid, sender := e.role, receiver := q }) = some L' ∧
            (Consume e.role L' [T]).isSome

/-- Receiver readiness for a select: after consuming the current trace on the edge,
    the receiver can consume a label (encoded as .string) from the selector. -/
def SelectReady (G : GEnv) (D : DEnv) : Prop :=
  ∀ e q bs ℓ L,
    lookupG G e = some (.select q bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    ∀ Lrecv, lookupG G { sid := e.sid, role := q } = some Lrecv →
      ∃ L', Consume e.role Lrecv (lookupD D { sid := e.sid, sender := e.role, receiver := q }) = some L' ∧
            (Consume e.role L' [.string]).isSome


end
