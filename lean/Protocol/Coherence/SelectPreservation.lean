import Protocol.Coherence.StoreTyping

/-! # MPST Coherence: Select Preservation

This module proves coherence preservation for select (internal choice) steps.
-/

/-
The Problem. When a role makes an internal choice, both its local type and the
trace change. We must show edge coherence is preserved for all affected edges.

Solution Structure. We prove select preservation via:
1. Head preservation: receiver's branch type accepts the new label
2. Continuation coherence: remaining protocol stays coherent
3. 3-way edge case analysis for unaffected edges
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

/-! ## Core Development -/

theorem Coherent_select_preserved
    (G : GEnv) (D : DEnv) (selectorEp : Endpoint) (targetRole : Role)
    (bs : List (String × LocalType)) (ℓ : String) (L : LocalType)
    (hCoh : Coherent G D)
    (hG : lookupG G selectorEp = some (.select targetRole bs))
    (_hFind : bs.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    -- CRITICAL: The target must be ready to accept the label
    (hTargetReady : ∀ Ltarget, lookupG G { sid := selectorEp.sid, role := targetRole } = some Ltarget →
      ∃ L', Consume selectorEp.role Ltarget (lookupD D { sid := selectorEp.sid, sender := selectorEp.role, receiver := targetRole }) = some L' ∧
            (Consume selectorEp.role L' [.string]).isSome) :
    let selectEdge := { sid := selectorEp.sid, sender := selectorEp.role, receiver := targetRole : Edge }
    Coherent (updateG G selectorEp L) (updateD D selectEdge (lookupD D selectEdge ++ [.string])) := by
  -- Similar structure to Coherent_send_preserved, with .string for labels
  intro selectEdge e hActive
  have hActiveOrig : ActiveEdge G e :=
    ActiveEdge_updateG_inv (G:=G) (e:=e) (ep:=selectorEp) (L:=L) hActive (by simp [hG])
  by_cases heq : e = selectEdge
  · -- Case 1: e = selectEdge
    subst heq
    simp only [EdgeCoherent]
    intro Lrecv hGrecv
    have hSenderLookup : lookupG (updateG G selectorEp L) { sid := selectorEp.sid, role := selectorEp.role } = some L := by
      convert lookupG_update_eq G selectorEp L
    refine ⟨L, hSenderLookup, ?_⟩
    by_cases hTargetIsSender : targetRole = selectorEp.role
    · -- Self-select: target = selector
      subst hTargetIsSender
      have hRecvLookup : lookupG (updateG G selectorEp L) { sid := selectorEp.sid, role := selectorEp.role } = some L := by
        simpa using hSenderLookup
      have hEq : Lrecv = L := by
        have : some L = some Lrecv := by
          simpa [hRecvLookup, selectEdge] using hGrecv
        exact (Option.some.inj this).symm
      simp only [lookupD_update_eq]
      -- hTargetReady with SELECT type is unsatisfiable (Consume on SELECT fails)
      obtain ⟨L', hL', hL'T⟩ := hTargetReady (.select selectorEp.role bs) hG
      cases hTrace : lookupD D { sid := selectorEp.sid, sender := selectorEp.role, receiver := selectorEp.role } with
      | nil =>
        rw [hTrace] at hL'
        simp only [Consume] at hL'
        simp only [Option.some.injEq] at hL'
        subst hL'
        simp only [Consume, consumeOne, Option.isSome] at hL'T
        exact Bool.noConfusion hL'T
      | cons t ts =>
        rw [hTrace] at hL'
        simp only [Consume, consumeOne] at hL'
        exact Option.noConfusion hL'
    · -- Normal case: target ≠ selector
      have hTargetNeq : selectorEp ≠ { sid := selectorEp.sid, role := targetRole } := by
        intro h
        have : selectorEp.role = targetRole := congrArg Endpoint.role h
        exact hTargetIsSender this.symm
      have hGrecv' : lookupG G { sid := selectorEp.sid, role := targetRole } = some Lrecv := by
        simpa [lookupG_update_neq _ _ _ _ hTargetNeq, selectEdge] using hGrecv
      simp only [lookupD_update_eq]
      obtain ⟨L', hL', hL'T⟩ := hTargetReady Lrecv hGrecv'
      rw [Consume_append _ _ _ _ hL']
      exact hL'T
  · -- Case 2: e ≠ selectEdge - use irrelevance lemmas
    have hNeSymm : selectEdge ≠ e := Ne.symm heq
    by_cases hSenderMatch : { sid := e.sid, role := e.sender : Endpoint } = selectorEp
    · -- Sender endpoint is selectorEp
      by_cases hRecvMatch : { sid := e.sid, role := e.receiver : Endpoint } = selectorEp
      · -- Self-loop case
        have hSid1 : e.sid = selectorEp.sid := congrArg Endpoint.sid hSenderMatch
        have hRole1 : e.sender = selectorEp.role := congrArg Endpoint.role hSenderMatch
        have hSid2 : e.sid = selectorEp.sid := congrArg Endpoint.sid hRecvMatch
        have hRole2 : e.receiver = selectorEp.role := congrArg Endpoint.role hRecvMatch
        simp only [EdgeCoherent]
        intro Lrecv hGrecv
        have hLookupS : lookupG (updateG G selectorEp L) { sid := e.sid, role := e.sender } = some L := by
          conv => lhs; rw [hSid1, hRole1]
          exact lookupG_update_eq G selectorEp L
        have hLookupR : lookupG (updateG G selectorEp L) { sid := e.sid, role := e.receiver } = some L := by
          conv => lhs; rw [hSid2, hRole2]
          exact lookupG_update_eq G selectorEp L
        have hEq : Lrecv = L := by
          have : some L = some Lrecv := by
            simpa [hLookupR] using hGrecv
          exact (Option.some.inj this).symm
        refine ⟨L, hLookupS, ?_⟩
        rw [lookupD_update_neq _ _ _ _ hNeSymm]
        have hOrigCoh := Coherent_edge_any hCoh hActiveOrig
        have hOrigRecvG : lookupG G { sid := e.sid, role := e.receiver } = some (.select targetRole bs) := by
          conv => lhs; rw [hSid2, hRole2]; exact hG
        have hOrig := EdgeCoherent_consume_of_receiver hOrigCoh hOrigRecvG
        cases hTrace : lookupD D e with
        | nil =>
          rw [hRole1]
          simp only [Consume, Option.isSome]
        | cons t ts =>
          rw [hRole1, hTrace] at hOrig
          simp only [Consume, consumeOne, Option.isSome] at hOrig
          exact Bool.noConfusion hOrig
      · -- Sender = selectorEp, receiver ≠ selectorEp
        have hRecvNoMatch : selectorEp ≠ { sid := e.sid, role := e.receiver } := fun h => hRecvMatch h.symm
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        simp only [EdgeCoherent]
        intro Lrecv hGrecv
        have hGrecv' : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv := by
          simpa [lookupG_update_neq _ _ _ _ hRecvNoMatch] using hGrecv
        have hOrigCoh := Coherent_edge_any hCoh hActiveOrig
        have hConsume := EdgeCoherent_consume_of_receiver hOrigCoh hGrecv'
        have hSid : e.sid = selectorEp.sid := congrArg Endpoint.sid hSenderMatch
        have hRole : e.sender = selectorEp.role := congrArg Endpoint.role hSenderMatch
        have hSenderLookup : lookupG (updateG G selectorEp L) { sid := e.sid, role := e.sender } = some L := by
          conv => lhs; rw [hSid, hRole]; exact lookupG_update_eq G selectorEp L
        refine ⟨L, hSenderLookup, hConsume⟩
    · -- Sender endpoint ≠ selectorEp
      have hSenderNoMatch : selectorEp ≠ { sid := e.sid, role := e.sender } := fun h => hSenderMatch h.symm
      by_cases hRecvMatch : { sid := e.sid, role := e.receiver : Endpoint } = selectorEp
      · -- Receiver = selectorEp, sender ≠ selectorEp
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        simp only [EdgeCoherent]
        intro Lrecv hGrecv
        have hSid : e.sid = selectorEp.sid := congrArg Endpoint.sid hRecvMatch
        have hRole : e.receiver = selectorEp.role := congrArg Endpoint.role hRecvMatch
        have hRecvLookup : lookupG (updateG G selectorEp L) { sid := e.sid, role := e.receiver } = some L := by
          conv => lhs; rw [hSid, hRole]; exact lookupG_update_eq G selectorEp L
        have hEq : Lrecv = L := by
          have : some L = some Lrecv := by
            simpa [hRecvLookup] using hGrecv
          exact (Option.some.inj this).symm
        have hOrigCoh := Coherent_edge_any hCoh hActiveOrig
        have hOrigRecv : lookupG G { sid := e.sid, role := e.receiver } = some (.select targetRole bs) := by
          conv => lhs; rw [hSid, hRole]; exact hG
        have hOrig := EdgeCoherent_consume_of_receiver hOrigCoh hOrigRecv
        rcases EdgeCoherent_sender_of_receiver hOrigCoh hOrigRecv with ⟨Lsender, hGsender⟩
        have hGsender' : lookupG (updateG G selectorEp L) { sid := e.sid, role := e.sender } = some Lsender := by
          simpa [lookupG_update_neq _ _ _ _ hSenderNoMatch] using hGsender
        refine ⟨Lsender, hGsender', ?_⟩
        cases hTrace : lookupD D e with
        | nil => simp only [Consume, Option.isSome]
        | cons t ts =>
          rw [hTrace] at hOrig
          simp only [Consume, consumeOne, Option.isSome] at hOrig
          exact Bool.noConfusion hOrig
      · -- Neither endpoint is selectorEp
        have hRecvNoMatch : selectorEp ≠ { sid := e.sid, role := e.receiver } := fun h => hRecvMatch h.symm
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        exact EdgeCoherent_updateG_irrelevant _ _ _ _ _ hSenderNoMatch hRecvNoMatch (Coherent_edge_any hCoh hActiveOrig)

/-- Coherent is preserved when branching (receiving a label).
    Branch removes .string from trace HEAD, advances brancher type.
    Similar structure to Coherent_recv_preserved. -/
theorem Coherent_branch_preserved
    (G : GEnv) (D : DEnv) (brancherEp : Endpoint) (senderRole : Role)
    (bs : List (String × LocalType)) (ℓ : String) (L : LocalType)
    (hCoh : Coherent G D)
    (hG : lookupG G brancherEp = some (.branch senderRole bs))
    (_hFind : bs.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    (hTrace : (lookupD D { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role }).head? = some .string) :
    let branchEdge := { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role : Edge }
    Coherent (updateG G brancherEp L) (updateD D branchEdge (lookupD D branchEdge).tail) := by
  -- Similar structure to Coherent_recv_preserved, adapted for branch/select
  intro branchEdge e hActive
  have hActiveOrig : ActiveEdge G e :=
    ActiveEdge_updateG_inv (G:=G) (e:=e) (ep:=brancherEp) (L:=L) hActive (by simp [hG])
  by_cases heq : e = branchEdge
  · -- Case 1: e = branchEdge
    subst heq
    simp only [EdgeCoherent]
    intro Lrecv hGrecv
    have hRecvLookup : lookupG (updateG G brancherEp L) { sid := brancherEp.sid, role := brancherEp.role } = some L := by
      convert lookupG_update_eq G brancherEp L
    by_cases hSenderIsRecv : senderRole = brancherEp.role
    · -- Self-branch: sender = receiver
      subst hSenderIsRecv
      have hEq : Lrecv = L := by
        have : some L = some Lrecv := by
          simpa [hRecvLookup, branchEdge] using hGrecv
        exact (Option.some.inj this).symm
      have hSenderLookup : lookupG (updateG G brancherEp L) { sid := brancherEp.sid, role := brancherEp.role } = some L := by
        simpa using hRecvLookup
      refine ⟨L, hSenderLookup, ?_⟩
      simp only [lookupD_update_eq]
      have hOrigCoh := Coherent_edge_any hCoh hActiveOrig
      cases hTraceVal : lookupD D branchEdge with
      | nil =>
        rw [hTraceVal] at hTrace
        simp only [List.head?] at hTrace
        exact Option.noConfusion hTrace
      | cons t rest =>
        rw [hTraceVal] at hTrace
        simp only [List.head?, Option.some.injEq] at hTrace
        subst hTrace
        -- Original coherence with branch type
        -- consumeOne doesn't handle branch, so this case is vacuously handled
        -- by showing original coherence required empty trace or contradiction
        have hOrig := EdgeCoherent_consume_of_receiver hOrigCoh hG
        rw [hTraceVal] at hOrig
        simp only [Consume, consumeOne, Option.isSome] at hOrig
        exact Bool.noConfusion hOrig
    · -- Normal case: sender ≠ receiver
      have hSenderNeq : brancherEp ≠ { sid := brancherEp.sid, role := senderRole } := by
        intro h
        have : brancherEp.role = senderRole := congrArg Endpoint.role h
        exact hSenderIsRecv this.symm
      have hEq : Lrecv = L := by
        have : some L = some Lrecv := by
          simpa [hRecvLookup, branchEdge] using hGrecv
        exact (Option.some.inj this).symm
      simp only [lookupD_update_eq]
      have hOrigCoh := Coherent_edge_any hCoh hActiveOrig
      rcases EdgeCoherent_sender_of_receiver hOrigCoh hG with ⟨Lsender, hGsender⟩
      have hSenderLookup : lookupG (updateG G brancherEp L) { sid := brancherEp.sid, role := senderRole } = some Lsender := by
        simpa [lookupG_update_neq _ _ _ _ hSenderNeq] using hGsender
      refine ⟨Lsender, hSenderLookup, ?_⟩
      cases hTraceVal : lookupD D branchEdge with
      | nil =>
        rw [hTraceVal] at hTrace
        simp only [List.head?] at hTrace
        exact Option.noConfusion hTrace
      | cons t rest =>
        rw [hTraceVal] at hTrace
        simp only [List.head?, Option.some.injEq] at hTrace
        subst hTrace
        have hOrig := EdgeCoherent_consume_of_receiver hOrigCoh hG
        rw [hTraceVal] at hOrig
        simp only [Consume, consumeOne, Option.isSome] at hOrig
        -- consumeOne on branch type returns none, so Consume fails on non-empty trace
        exact Bool.noConfusion hOrig
  · -- Case 2: e ≠ branchEdge
    have hNeSymm : branchEdge ≠ e := Ne.symm heq
    by_cases hSenderMatch : { sid := e.sid, role := e.sender : Endpoint } = brancherEp
    · -- Sender endpoint is brancherEp
      by_cases hRecvMatch : { sid := e.sid, role := e.receiver : Endpoint } = brancherEp
      · -- Self-loop case
        have hSid1 : e.sid = brancherEp.sid := congrArg Endpoint.sid hSenderMatch
        have hRole1 : e.sender = brancherEp.role := congrArg Endpoint.role hSenderMatch
        have hSid2 : e.sid = brancherEp.sid := congrArg Endpoint.sid hRecvMatch
        have hRole2 : e.receiver = brancherEp.role := congrArg Endpoint.role hRecvMatch
        simp only [EdgeCoherent]
        intro Lrecv hGrecv
        have hLookupS : lookupG (updateG G brancherEp L) { sid := e.sid, role := e.sender } = some L := by
          conv => lhs; rw [hSid1, hRole1]
          exact lookupG_update_eq G brancherEp L
        have hLookupR : lookupG (updateG G brancherEp L) { sid := e.sid, role := e.receiver } = some L := by
          conv => lhs; rw [hSid2, hRole2]
          exact lookupG_update_eq G brancherEp L
        have hEq : Lrecv = L := by
          have : some L = some Lrecv := by
            simpa [hLookupR] using hGrecv
          exact (Option.some.inj this).symm
        refine ⟨L, hLookupS, ?_⟩
        rw [lookupD_update_neq _ _ _ _ hNeSymm]
        have hOrigCoh := Coherent_edge_any hCoh hActiveOrig
        have hOrigRecvG : lookupG G { sid := e.sid, role := e.receiver } = some (.branch senderRole bs) := by
          conv => lhs; rw [hSid2, hRole2]; exact hG
        have hOrig := EdgeCoherent_consume_of_receiver hOrigCoh hOrigRecvG
        cases hTraceE : lookupD D e with
        | nil =>
          rw [hRole1]
          simp only [Consume, Option.isSome]
        | cons t ts =>
          rw [hRole1, hTraceE] at hOrig
          simp only [Consume, consumeOne, Option.isSome] at hOrig
          exact Bool.noConfusion hOrig
      · -- Sender = brancherEp, receiver ≠ brancherEp
        have hRecvNoMatch : brancherEp ≠ { sid := e.sid, role := e.receiver } := fun h => hRecvMatch h.symm
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        simp only [EdgeCoherent]
        intro Lrecv hGrecv
        have hGrecv' : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv := by
          simpa [lookupG_update_neq _ _ _ _ hRecvNoMatch] using hGrecv
        have hOrigCoh := Coherent_edge_any hCoh hActiveOrig
        have hConsume := EdgeCoherent_consume_of_receiver hOrigCoh hGrecv'
        have hSid : e.sid = brancherEp.sid := congrArg Endpoint.sid hSenderMatch
        have hRole : e.sender = brancherEp.role := congrArg Endpoint.role hSenderMatch
        have hSenderLookup : lookupG (updateG G brancherEp L) { sid := e.sid, role := e.sender } = some L := by
          conv => lhs; rw [hSid, hRole]; exact lookupG_update_eq G brancherEp L
        refine ⟨L, hSenderLookup, hConsume⟩
    · -- Sender endpoint ≠ brancherEp
      have hSenderNoMatch : brancherEp ≠ { sid := e.sid, role := e.sender } := fun h => hSenderMatch h.symm
      by_cases hRecvMatch : { sid := e.sid, role := e.receiver : Endpoint } = brancherEp
      · -- Receiver = brancherEp, sender ≠ brancherEp
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        simp only [EdgeCoherent]
        intro Lrecv hGrecv
        have hSid : e.sid = brancherEp.sid := congrArg Endpoint.sid hRecvMatch
        have hRole : e.receiver = brancherEp.role := congrArg Endpoint.role hRecvMatch
        have hRecvLookup : lookupG (updateG G brancherEp L) { sid := e.sid, role := e.receiver } = some L := by
          conv => lhs; rw [hSid, hRole]; exact lookupG_update_eq G brancherEp L
        have hEq : Lrecv = L := by
          have : some L = some Lrecv := by
            simpa [hRecvLookup] using hGrecv
          exact (Option.some.inj this).symm
        have hOrigCoh := Coherent_edge_any hCoh hActiveOrig
        have hOrigRecv : lookupG G { sid := e.sid, role := e.receiver } = some (.branch senderRole bs) := by
          conv => lhs; rw [hSid, hRole]; exact hG
        have hOrig := EdgeCoherent_consume_of_receiver hOrigCoh hOrigRecv
        rcases EdgeCoherent_sender_of_receiver hOrigCoh hOrigRecv with ⟨Lsender, hGsender⟩
        have hGsender' : lookupG (updateG G brancherEp L) { sid := e.sid, role := e.sender } = some Lsender := by
          simpa [lookupG_update_neq _ _ _ _ hSenderNoMatch] using hGsender
        refine ⟨Lsender, hGsender', ?_⟩
        cases hTraceE : lookupD D e with
        | nil => simp only [Consume, Option.isSome]
        | cons t ts =>
          rw [hTraceE] at hOrig
          simp only [Consume, consumeOne, Option.isSome] at hOrig
          exact Bool.noConfusion hOrig
      · -- Neither endpoint is brancherEp
        have hRecvNoMatch : brancherEp ≠ { sid := e.sid, role := e.receiver } := fun h => hRecvMatch h.symm
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        exact EdgeCoherent_updateG_irrelevant _ _ _ _ _ hSenderNoMatch hRecvNoMatch (Coherent_edge_any hCoh hActiveOrig)


end
