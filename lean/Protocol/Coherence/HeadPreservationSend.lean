import Protocol.Coherence.HeadPreservationRecv
import Protocol.Coherence.EdgeCoherence

/-! # Protocol.Coherence.HeadPreservationSend

Coherence lemmas and invariants for session-environment evolution.
-/


/-! # MPST Coherence: Send Head Preservation

This module proves head preservation for send (value transmission) steps.
-/

/-
The Problem. When a role sends a value, the trace grows with the value type.
We must show that edge coherence is preserved: the receiver can still consume
the extended trace using its recv type.

Solution Structure. We prove head preservation by:
1. Showing the sent type matches the receiver's expected recv type
2. Proving Consume succeeds on the extended trace via `Consume_append`
3. Handling the 3-way edge case split (updated, related, unrelated)
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

`Coherent G D` states that for every session and every directed edge:
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

/-! ## HeadCoherent Preservation Lemmas -/

/-- Helper: Consume on a self-recv head succeeds iff the tail does. -/
private theorem Consume_tail_of_self_recv
    {from_ : Role} {T : ValType} {L : LocalType} {ts : List ValType} :
    (Consume from_ (.recv from_ T L) (T :: ts)).isSome →
    (Consume from_ L ts).isSome := by
  -- Reduce Consume on a matching recv head to Consume on the tail.
  intro hConsume
  simpa [Consume, consumeOne, beq_self_eq_true, Bool.true_and] using hConsume

/-- Helper: If Consume succeeds on a recv head, the head type matches. -/
private theorem Consume_head_eq_of_recv
    {from_ r : Role} {T : ValType} {L : LocalType} {t : ValType} {ts : List ValType} :
    (Consume from_ (.recv r T L) (t :: ts)).isSome → t = T := by
  -- Extract a witness and apply the recv-head matching lemma.
  intro hConsume
  rcases (Option.isSome_iff_exists).1 hConsume with ⟨L', hEq⟩
  exact (Consume_recv_head_match (from_:=from_) (r:=r) (T:=T) (L:=L) (t:=t) (ts:=ts) hEq).2

/-- Helper: Consume on a branch with a non-empty trace is impossible. -/
private theorem Consume_branch_nonempty_isSome_false
    {from_ r : Role} {bs : List (String × LocalType)} {t : ValType} {ts : List ValType} :
    (Consume from_ (.branch r bs) (t :: ts)).isSome → False := by
  -- Turn isSome into an equality and use the existing contradiction lemma.
  intro hConsume
  rcases (Option.isSome_iff_exists).1 hConsume with ⟨L', hEq⟩
  exact Consume_branch_nonempty_false (from_:=from_) (r:=r) (bs:=bs) (t:=t) (ts:=ts) (L':=L') hEq

/-- HeadCoherent is preserved when sending.
    Send action appends to trace END, so the HEAD is unchanged.
    The sender's G entry changes, but receiver's G entry is unchanged
    (unless sender = receiver, which is handled separately).
    Reference: `work/effects/004.lean` proof structure -/
theorem HeadCoherent_send_preserved
    (G : GEnv) (D : DEnv) (senderEp : Endpoint) (receiverRole : Role) (T : ValType) (L : LocalType)
    (hHead : HeadCoherent G D)
    (hCoh : Coherent G D)
    (hG : lookupG G senderEp = some (.send receiverRole T L))
    -- When trace is empty and receiver expects recv/branch from sender, T must match
    (hRecvReady : ∀ Lrecv, lookupG G { sid := senderEp.sid, role := receiverRole } = some Lrecv →
      ∃ L', Consume senderEp.role Lrecv (lookupD D { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }) = some L' ∧
            (Consume senderEp.role L' [T]).isSome) :
    let sendEdge := { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole : Edge }
    HeadCoherent (updateG G senderEp L) (updateD D sendEdge (lookupD D sendEdge ++ [T])) := by
  intro sendEdge e hActive  -- The edge we check HeadCoherent for
  simp only [HeadCoherent] at hHead ⊢
  have hActiveOrig : ActiveEdge G e :=
    ActiveEdge_updateG_inv (G:=G) (e:=e) (ep:=senderEp) (L:=L) hActive (by simp [hG])
  -- Case split: is e the send edge or not?
  by_cases heq : e = sendEdge
  · -- Case 1: e = sendEdge - type and trace both change
    subst heq
    -- Self-send case: receiver = sender, handled by subst and lookup lemmas.
    by_cases hRecvIsSender : receiverRole = senderEp.role
    · -- Self-send: receiver = sender, type at senderEp changes to L
      subst hRecvIsSender
      -- sendEdge = { sid := senderEp.sid, sender := senderEp.role, receiver := senderEp.role }
      -- Receiver endpoint = senderEp, so receiver type in updated G is L
      have hRecvEp : { sid := sendEdge.sid, role := sendEdge.receiver : Endpoint } = senderEp := rfl
      simp only [hRecvEp, lookupG_update_eq, lookupD_update_eq]
      -- Case on continuation type L
      cases L with
      | end_ => exact True.intro
      | send _ _ _ => exact True.intro
      | select _ _ => exact True.intro
      | var _ => exact True.intro
      | mu _ => exact True.intro
      | recv r T' L' =>
        -- Self-send case: original type is .send, hRecvReady requires Consume on it
        have ⟨L'', hConsumeOrig, hConsumeSingle⟩ := hRecvReady (.send senderEp.role T (.recv r T' L')) hG
        -- Case on original trace
        cases hOrigTrace : lookupD D sendEdge with
        | nil =>
          -- Empty trace: Consume on .send returns the .send type
          rw [hOrigTrace] at hConsumeOrig
          simp only [Consume] at hConsumeOrig
          -- hConsumeOrig : some (.send ...) = some L'', so L'' = .send ...
          have hL''eq : L'' = .send senderEp.role T (.recv r T' L') := Option.some.inj hConsumeOrig.symm
          rw [hL''eq] at hConsumeSingle
          -- Consume on .send type with [T] fails
          simp only [Consume, consumeOne, Option.isSome] at hConsumeSingle
          exact Bool.noConfusion hConsumeSingle
        | cons t ts =>
          -- Non-empty trace: Consume on .send fails
          rw [hOrigTrace] at hConsumeOrig
          simp only [Consume, consumeOne] at hConsumeOrig
          exact Option.noConfusion hConsumeOrig
      | branch r bs =>
        -- Same as recv case - hRecvReady requires Consume on SEND which fails
        have ⟨L'', hConsumeOrig, hConsumeSingle⟩ := hRecvReady (.send senderEp.role T (.branch r bs)) hG
        cases hOrigTrace : lookupD D sendEdge with
        | nil =>
          rw [hOrigTrace] at hConsumeOrig
          simp only [Consume] at hConsumeOrig
          have hL''eq : L'' = .send senderEp.role T (.branch r bs) := Option.some.inj hConsumeOrig.symm
          rw [hL''eq] at hConsumeSingle
          simp only [Consume, consumeOne, Option.isSome] at hConsumeSingle
          exact Bool.noConfusion hConsumeSingle
        | cons t ts =>
          rw [hOrigTrace] at hConsumeOrig
          simp only [Consume, consumeOne] at hConsumeOrig
          exact Option.noConfusion hConsumeOrig
    · -- Normal case: receiver ≠ sender
      have hRecvNeq : senderEp ≠ { sid := senderEp.sid, role := receiverRole } := by
        intro h
        have : senderEp.role = receiverRole := congrArg Endpoint.role h
        exact hRecvIsSender this.symm
      -- Receiver's type unchanged
      rw [lookupG_update_neq _ _ _ _ hRecvNeq]
      -- Trace was ts, now ts ++ [T]
      simp only [lookupD_update_eq]
      -- Case on receiver's type in original G
      cases hRecvType : lookupG G { sid := senderEp.sid, role := receiverRole } with
      | none => trivial
      | some Lr =>
        -- Original HeadCoherent at sendEdge (sender and receiver exist)
        have hActiveOrig : ActiveEdge G sendEdge :=
          ActiveEdge_of_endpoints (G:=G) (e:=sendEdge) hG hRecvType
        have hOrigHead := hHead sendEdge hActiveOrig
        cases Lr with
        | end_ => trivial
        | send _ _ _ => trivial
        | select _ _ => trivial
        | var _ => trivial
        | mu _ => trivial
        | recv r T' L' =>
          -- Original: if trace non-empty, head = T'
          -- After: trace ++ [T], head unchanged (unless trace was empty)
          cases hTrace : lookupD D sendEdge with
          | nil =>
            simp only [List.nil_append]
            -- Empty trace → single element [T], new head is T
            -- Use hRecvReady to get T' = T
            have ⟨L'', hConsumeOrig, hConsumeSingle⟩ := hRecvReady (.recv r T' L') hRecvType
            -- With empty trace, Consume returns the type unchanged
            -- Note: sendEdge = { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }
            rw [hTrace] at hConsumeOrig
            simp only [Consume] at hConsumeOrig
            -- hConsumeOrig : some (.recv r T' L') = some L''
            have hL''eq : L'' = .recv r T' L' := Option.some.inj hConsumeOrig.symm
            rw [hL''eq] at hConsumeSingle
            -- hConsumeSingle : (Consume senderEp.role (recv r T' L') [T]).isSome
            -- For this to succeed, senderEp.role == r AND T == T'
            simp only [Consume, consumeOne, Option.isSome] at hConsumeSingle
            by_cases hSenderMatch : senderEp.role == r
            · simp only [hSenderMatch, Bool.true_and] at hConsumeSingle
              by_cases hTypeMatch : T == T'
              · exact (eq_of_beq hTypeMatch).symm
              · simp only [hTypeMatch] at hConsumeSingle
                exact Bool.noConfusion hConsumeSingle
            · simp only [hSenderMatch, Bool.false_and] at hConsumeSingle
              exact Bool.noConfusion hConsumeSingle
          | cons t ts =>
            simp only [List.cons_append]
            -- Trace head unchanged: t :: (ts ++ [T]) still has head t
            -- hOrigHead specialized to sendEdge with recv type gives T' = t
            have hOrigAtEdge := hOrigHead
            -- sendEdge = { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }
            -- so { sid := sendEdge.sid, role := sendEdge.receiver } = { sid := senderEp.sid, role := receiverRole }
            have hEpEq : { sid := sendEdge.sid, role := sendEdge.receiver : Endpoint } = { sid := senderEp.sid, role := receiverRole } := rfl
            simp only [hEpEq, hRecvType, hTrace] at hOrigAtEdge
            exact hOrigAtEdge
        | branch source bs =>
          cases hTrace : lookupD D sendEdge with
          | nil =>
            simp only [List.nil_append]
            -- Empty trace → single element [T], new head is T
            -- Use hRecvReady to get T = .string
            have ⟨L'', hConsumeOrig, hConsumeSingle⟩ := hRecvReady (.branch source bs) hRecvType
            -- With empty trace, Consume returns the type unchanged
            rw [hTrace] at hConsumeOrig
            simp only [Consume] at hConsumeOrig
            -- hConsumeOrig : some (.branch source bs) = some L''
            have hL''eq : L'' = .branch source bs := Option.some.inj hConsumeOrig.symm
            rw [hL''eq] at hConsumeSingle
            -- Consume on branch type always fails because consumeOne doesn't handle branch
            -- consumeOne returns none for all non-recv types, so Consume returns none
            simp only [Consume, consumeOne, Option.isSome] at hConsumeSingle
            exact Bool.noConfusion hConsumeSingle
          | cons t ts =>
            simp only [List.cons_append]
            -- Trace head unchanged: t :: (ts ++ [T]) still has head t
            -- hOrigHead specialized to sendEdge with branch type gives t = .string
            have hOrigAtEdge := hOrigHead
            have hEpEq : { sid := sendEdge.sid, role := sendEdge.receiver : Endpoint } = { sid := senderEp.sid, role := receiverRole } := rfl
            simp only [hEpEq, hRecvType, hTrace] at hOrigAtEdge
            exact hOrigAtEdge
  · -- Case 2: e ≠ sendEdge
    -- Check if receiver endpoint changed (is it senderEp?)
    by_cases hRecvMatch : { sid := e.sid, role := e.receiver : Endpoint } = senderEp
    · -- Receiver endpoint is senderEp, type changed from SEND to L
      subst hRecvMatch
      rw [lookupG_update_eq]
      have hNeSymm : sendEdge ≠ e := Ne.symm heq
      rw [lookupD_update_neq _ _ _ _ hNeSymm]
      -- L replaces .send at senderEp, check HeadCoherent for L
      cases hL : L with
      | end_ => trivial
      | send _ _ _ => trivial
      | select _ _ => trivial
      | var _ => trivial
      | mu _ => trivial
      | recv r T' L' =>
        -- HeadCoherent for recv: check if trace head matches T'
        -- Key insight: Original G[senderEp] = .send, so by trace_empty_when_send_receiver, D[e] = []
        -- After update, D'[e] = D[e] = [] (since e ≠ sendEdge), so HeadCoherent is trivially True
        have hEdgeCoh : EdgeCoherent G D e := Coherent_edge_any hCoh hActiveOrig
        -- e.receiver = senderEp.role, and G[senderEp] = .send receiverRole T L
        have hRecvType' : lookupG G ⟨e.sid, e.receiver⟩ = some (.send receiverRole T L) := by
          simp only [hG]  -- e.receiver = senderEp.role after subst
        have hTraceEmpty := trace_empty_when_send_receiver hEdgeCoh hRecvType'
        rw [hTraceEmpty]
        trivial
      | branch source bs' =>
        -- HeadCoherent for branch: same reasoning - original D[e] = [] because sender type is .send
        have hEdgeCoh : EdgeCoherent G D e := Coherent_edge_any hCoh hActiveOrig
        have hRecvType' : lookupG G ⟨e.sid, e.receiver⟩ = some (.send receiverRole T L) := by
          simp only [hG]
        have hTraceEmpty := trace_empty_when_send_receiver hEdgeCoh hRecvType'
        rw [hTraceEmpty]
        trivial
    · -- Receiver endpoint unchanged
      have hRecvNoMatch : senderEp ≠ { sid := e.sid, role := e.receiver } := fun h => hRecvMatch h.symm
      rw [lookupG_update_neq _ _ _ _ hRecvNoMatch]
      -- Trace at e unchanged
      have hNeSymm : sendEdge ≠ e := Ne.symm heq
      rw [lookupD_update_neq _ _ _ _ hNeSymm]
      -- Original HeadCoherent at e
      exact hHead e hActiveOrig


end
