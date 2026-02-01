import Protocol.Coherence.EdgeCoherence

/-!
# MPST Coherence

This module defines the coherence invariant for multiparty session types.

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

noncomputable section

theorem HeadCoherent_select_preserved
    (G : GEnv) (D : DEnv) (selectorEp : Endpoint) (targetRole : Role)
    (bs : List (String × LocalType)) (ℓ : String) (L : LocalType)
    (hHead : HeadCoherent G D)
    (hCoh : Coherent G D)
    (hG : lookupG G selectorEp = some (.select targetRole bs))
    (hFind : bs.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    -- When trace is empty and receiver expects recv/branch from sender, .string must match
    (hRecvReady : ∀ Lrecv, lookupG G { sid := selectorEp.sid, role := targetRole } = some Lrecv →
      ∃ L', Consume selectorEp.role Lrecv (lookupD D { sid := selectorEp.sid, sender := selectorEp.role, receiver := targetRole }) = some L' ∧
            (Consume selectorEp.role L' [.string]).isSome) :
    let selectEdge := { sid := selectorEp.sid, sender := selectorEp.role, receiver := targetRole : Edge }
    HeadCoherent (updateG G selectorEp L) (updateD D selectEdge (lookupD D selectEdge ++ [.string])) := by
  -- Same structure as HeadCoherent_send_preserved: appending to END doesn't change HEAD
  intro selectEdge e
  simp only [HeadCoherent] at hHead ⊢
  by_cases heq : e = selectEdge
  · -- e = selectEdge: trace gets .string appended at END
    subst heq
    -- Self-select case is unusual
    by_cases hTargetIsSelector : targetRole = selectorEp.role
    · -- Self-select: receiver = selector, type at selectorEp changes to L
      subst hTargetIsSelector
      -- selectEdge = { sid := selectorEp.sid, sender := selectorEp.role, receiver := selectorEp.role }
      -- Receiver endpoint = selectorEp, so receiver type in updated G is L
      have hRecvEp : { sid := selectEdge.sid, role := selectEdge.receiver : Endpoint } = selectorEp := rfl
      simp only [hRecvEp, lookupG_update_eq, lookupD_update_eq]
      -- Case on continuation type L
      cases L with
      | end_ => exact True.intro
      | send _ _ _ => exact True.intro
      | select _ _ => exact True.intro
      | var _ => exact True.intro
      | mu _ => exact True.intro
      | recv r T' L' =>
        -- Self-select case: original type is .select, hRecvReady requires Consume on it
        have ⟨L'', hConsumeOrig, hConsumeSingle⟩ := hRecvReady (.select selectorEp.role bs) hG
        -- Case on original trace
        cases hOrigTrace : lookupD D selectEdge with
        | nil =>
          -- Empty trace: Consume on .select returns the .select type
          rw [hOrigTrace] at hConsumeOrig
          simp only [Consume] at hConsumeOrig
          -- hConsumeOrig : some (.select ...) = some L'', so L'' = .select ...
          have hL''eq : L'' = .select selectorEp.role bs := Option.some.inj hConsumeOrig.symm
          rw [hL''eq] at hConsumeSingle
          -- Consume on .select type with [.string] fails
          simp only [Consume, consumeOne, Option.isSome] at hConsumeSingle
          exact Bool.noConfusion hConsumeSingle
        | cons t ts =>
          -- Non-empty trace: Consume on .select fails
          rw [hOrigTrace] at hConsumeOrig
          simp only [Consume, consumeOne] at hConsumeOrig
          exact Option.noConfusion hConsumeOrig
      | branch r bs' =>
        -- Same as recv case - hRecvReady requires Consume on SELECT which fails
        have ⟨L'', hConsumeOrig, hConsumeSingle⟩ := hRecvReady (.select selectorEp.role bs) hG
        cases hOrigTrace : lookupD D selectEdge with
        | nil =>
          rw [hOrigTrace] at hConsumeOrig
          simp only [Consume] at hConsumeOrig
          have hL''eq : L'' = .select selectorEp.role bs := Option.some.inj hConsumeOrig.symm
          rw [hL''eq] at hConsumeSingle
          simp only [Consume, consumeOne, Option.isSome] at hConsumeSingle
          exact Bool.noConfusion hConsumeSingle
        | cons t ts =>
          rw [hOrigTrace] at hConsumeOrig
          simp only [Consume, consumeOne] at hConsumeOrig
          exact Option.noConfusion hConsumeOrig
    · -- Normal case: target ≠ selector
      have hTargetNeq : selectorEp ≠ { sid := selectorEp.sid, role := targetRole } := by
        intro h
        have : selectorEp.role = targetRole := congrArg Endpoint.role h
        exact hTargetIsSelector this.symm
      -- Target's type unchanged
      rw [lookupG_update_neq _ _ _ _ hTargetNeq]
      simp only [lookupD_update_eq]
      have hOrigHead := hHead selectEdge
      -- Case on target's type in original G
      cases hTargetType : lookupG G { sid := selectorEp.sid, role := targetRole } with
      | none => trivial
      | some Lt =>
        cases Lt with
        | end_ => trivial
        | send _ _ _ => trivial
        | select _ _ => trivial
        | var _ => trivial
        | mu _ => trivial
        | recv r T' L' =>
          cases hTrace : lookupD D selectEdge with
          | nil =>
            simp only [List.nil_append]
            -- Empty trace: use hRecvReady to derive .string = T'
            have ⟨L'', hConsumeOrig, hConsumeSingle⟩ := hRecvReady (.recv r T' L') hTargetType
            rw [hTrace] at hConsumeOrig
            simp only [Consume] at hConsumeOrig
            have hL''eq : L'' = .recv r T' L' := Option.some.inj hConsumeOrig.symm
            rw [hL''eq] at hConsumeSingle
            -- Consume selectorEp.role (.recv r T' L') [.string] must be isSome
            -- This requires selectorEp.role == r and .string == T'
            simp only [Consume, consumeOne, Option.isSome] at hConsumeSingle
            -- Case on whether sender matches
            by_cases hSenderMatch : selectorEp.role == r
            · simp only [hSenderMatch, Bool.true_and] at hConsumeSingle
              -- Now we need .string == T' to hold
              by_cases hTypeMatch : ValType.string == T'
              · -- T' = .string, so HeadCoherent is trivially satisfied
                have hTeq : T' = ValType.string := (eq_of_beq hTypeMatch).symm
                simp only [hTeq]
              · simp only [hTypeMatch] at hConsumeSingle
                exact Bool.noConfusion hConsumeSingle
            · simp only [hSenderMatch, Bool.false_and] at hConsumeSingle
              exact Bool.noConfusion hConsumeSingle
          | cons t ts =>
            simp only [List.cons_append]
            have hEpEq : { sid := selectEdge.sid, role := selectEdge.receiver : Endpoint } = { sid := selectorEp.sid, role := targetRole } := rfl
            simp only [hEpEq, hTargetType, hTrace] at hOrigHead
            exact hOrigHead
        | branch source bs' =>
          cases hTrace : lookupD D selectEdge with
          | nil =>
            simp only [List.nil_append]
            -- Empty trace → single element [.string], head is .string
            -- branch expects .string, so this is trivially satisfied (rfl or trivial)
          | cons t ts =>
            simp only [List.cons_append]
            have hEpEq : { sid := selectEdge.sid, role := selectEdge.receiver : Endpoint } = { sid := selectorEp.sid, role := targetRole } := rfl
            simp only [hEpEq, hTargetType, hTrace] at hOrigHead
            exact hOrigHead
  · -- e ≠ selectEdge: unchanged
    have hNeSymm : selectEdge ≠ e := Ne.symm heq
    rw [lookupD_update_neq _ _ _ _ hNeSymm]
    -- G update at selectorEp; check if it affects receiver lookup
    by_cases hRecvMatch : selectorEp = { sid := e.sid, role := e.receiver }
    · -- selectorEp is the receiver for edge e
      subst hRecvMatch
      rw [lookupG_update_eq]
      -- L replaces .select at selectorEp, check HeadCoherent for L
      cases hL : L with
      | end_ => trivial
      | send _ _ _ => trivial
      | select _ _ => trivial
      | var _ => trivial
      | mu _ => trivial
      | recv r T' L' =>
        -- HeadCoherent for recv: check if trace head matches T'
        -- Key insight: Original G[selectorEp] = .select, so by trace_empty_when_select_receiver, D[e] = []
        have hEdgeCoh : EdgeCoherent G D e := hCoh e
        have hSelectType' : lookupG G ⟨e.sid, e.receiver⟩ = some (.select targetRole bs) := by
          simp only [hG]
        have hTraceEmpty := trace_empty_when_select_receiver hEdgeCoh hSelectType'
        rw [hTraceEmpty]
        trivial
      | branch source bs' =>
        -- HeadCoherent for branch: same reasoning
        have hEdgeCoh : EdgeCoherent G D e := hCoh e
        have hSelectType' : lookupG G ⟨e.sid, e.receiver⟩ = some (.select targetRole bs) := by
          simp only [hG]
        have hTraceEmpty := trace_empty_when_select_receiver hEdgeCoh hSelectType'
        rw [hTraceEmpty]
        trivial
    · -- selectorEp is not the receiver
      have hRecvNoMatch : selectorEp ≠ { sid := e.sid, role := e.receiver } := hRecvMatch
      rw [lookupG_update_neq _ _ _ _ hRecvNoMatch]
      exact hHead e

/-- HeadCoherent is preserved when branching (receiving a label).
    Branch removes trace HEAD and advances receiver type to selected branch. -/
theorem HeadCoherent_branch_preserved
    (G : GEnv) (D : DEnv) (brancherEp : Endpoint) (senderRole : Role)
    (bs : List (String × LocalType)) (ℓ : String) (L : LocalType)
    (hHead : HeadCoherent G D)
    (hCoh : Coherent G D)
    (hG : lookupG G brancherEp = some (.branch senderRole bs))
    (_hFind : bs.find? (fun b => b.1 == ℓ) = some (ℓ, L))  -- Not needed for head coherence.
    (hTrace : (lookupD D { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role }).head? = some .string) :
    let branchEdge := { sid := brancherEp.sid, sender := senderRole, receiver := brancherEp.role : Edge }
    HeadCoherent (updateG G brancherEp L) (updateD D branchEdge (lookupD D branchEdge).tail) := by
  -- Same structure as HeadCoherent_recv_preserved: removes HEAD, advances type
  intro branchEdge e
  simp only [HeadCoherent] at hHead ⊢
  by_cases heq : e = branchEdge
  · -- Case 1: e = branchEdge - type and trace both change
    subst heq
    -- Self-branch case is unusual
    by_cases hSenderIsBrancher : senderRole = brancherEp.role
    · -- Self-branch: sender = receiver, Coherent forces empty trace; hTrace contradicts.
      subst hSenderIsBrancher
      have hEdgeCoh : EdgeCoherent G D branchEdge := hCoh branchEdge
      have hConsume :
          (Consume brancherEp.role (.branch brancherEp.role bs) (lookupD D branchEdge)).isSome :=
        by
          obtain ⟨Ls, _hSender, hConsume⟩ := hEdgeCoh (.branch brancherEp.role bs) hG
          exact hConsume
      cases hTraceVal : lookupD D branchEdge with
      | nil =>
          -- Empty trace contradicts head? = some .string.
          rw [hTraceVal] at hTrace
          have hFalse : False := by
            simpa [List.head?] using hTrace
          exact hFalse.elim
      | cons t ts =>
          -- Consume on a branch with non-empty trace is impossible.
          have hConsume' :
              (Consume brancherEp.role (.branch brancherEp.role bs) (t :: ts)).isSome := by
            simpa [hTraceVal] using hConsume
          rcases (Option.isSome_iff_exists).1 hConsume' with ⟨L', hEq⟩
          exact (Consume_branch_nonempty_false
            (from_:=brancherEp.role) (r:=brancherEp.role) (bs:=bs) (t:=t) (ts:=ts) (L':=L') hEq).elim
    · -- Normal case: sender ≠ brancher
      have hSenderNeq : brancherEp ≠ { sid := brancherEp.sid, role := senderRole } := by
        intro h; exact hSenderIsBrancher (congrArg Endpoint.role h).symm
      -- Brancher lookup gives L (the selected continuation)
      have hBranchLookup : lookupG (updateG G brancherEp L) { sid := brancherEp.sid, role := brancherEp.role } = some L := by
        convert lookupG_update_eq G brancherEp L
      rw [hBranchLookup, lookupD_update_eq]
      -- Get trace structure from hTrace
      cases hTraceVal : lookupD D branchEdge with
      | nil =>
        rw [hTraceVal] at hTrace
        simp only [List.head?] at hTrace
        exact Option.noConfusion hTrace
      | cons t ts =>
        rw [hTraceVal] at hTrace
        simp only [List.head?, Option.some.injEq] at hTrace
        subst hTrace
        simp only [List.tail_cons]
        -- L is continuation after branch, check structure
        cases hL : L with
        | end_ => trivial
        | send _ _ _ => trivial
        | select _ _ => trivial
        | var _ => trivial
        | mu _ => trivial
        | recv r T' L' =>
          -- Coherent contradicts a non-empty tail after a branch label.
          cases ts with
          | nil => trivial
          | cons t' ts' =>
            have hEdgeCoh : EdgeCoherent G D branchEdge := hCoh branchEdge
            have hConsume :
                (Consume senderRole (.branch senderRole bs) (.string :: t' :: ts')).isSome := by
              obtain ⟨Ls, _hSender, hConsume⟩ := hEdgeCoh (.branch senderRole bs) hG
              simpa [hTraceVal] using hConsume
            rcases (Option.isSome_iff_exists).1 hConsume with ⟨L', hEq⟩
            exact (Consume_branch_nonempty_false
              (from_:=senderRole) (r:=senderRole) (bs:=bs) (t:=.string) (ts:=t' :: ts')
              (L':=L') hEq).elim
        | branch source bs' =>
          cases ts with
          | nil => trivial
          | cons t' ts' =>
            have hEdgeCoh : EdgeCoherent G D branchEdge := hCoh branchEdge
            have hConsume :
                (Consume senderRole (.branch senderRole bs) (.string :: t' :: ts')).isSome := by
              obtain ⟨Ls, _hSender, hConsume⟩ := hEdgeCoh (.branch senderRole bs) hG
              simpa [hTraceVal] using hConsume
            rcases (Option.isSome_iff_exists).1 hConsume with ⟨L', hEq⟩
            exact (Consume_branch_nonempty_false
              (from_:=senderRole) (r:=senderRole) (bs:=bs) (t:=.string) (ts:=t' :: ts')
              (L':=L') hEq).elim
  · -- Case 2: e ≠ branchEdge - unchanged
    have hNeSymm : branchEdge ≠ e := Ne.symm heq
    rw [lookupD_update_neq _ _ _ _ hNeSymm]
    by_cases hRecvMatch : brancherEp = { sid := e.sid, role := e.receiver }
    · -- brancherEp is the receiver for edge e
      subst hRecvMatch
      rw [lookupG_update_eq]
      -- L replaces .branch at brancherEp, check HeadCoherent for L
      cases hL : L with
      | end_ => trivial
      | send _ _ _ => trivial
      | select _ _ => trivial
      | var _ => trivial
      | mu _ => trivial
      | recv r T' L' =>
        -- HeadCoherent for recv: check if trace head matches T'
        -- Key insight: Original G[brancherEp] = .branch senderRole bs
        -- e.sender ≠ senderRole (since e ≠ branchEdge but e.receiver = brancherEp.role)
        -- By trace_empty_when_branch_other_sender: D[e] = []
        have hEdgeCoh : EdgeCoherent G D e := hCoh e
        have hBranchType' : lookupG G ⟨e.sid, e.receiver⟩ = some (.branch senderRole bs) := by
          simp only [hG]
        have hSenderNe : e.sender ≠ senderRole := by
          intro hEq
          apply heq
          have hEdgeEq : e = branchEdge := by
            have hSidEq : e.sid = branchEdge.sid := rfl
            have hSenderEq : e.sender = branchEdge.sender := hEq
            have hRecvEq : e.receiver = branchEdge.receiver := rfl
            calc e = ⟨e.sid, e.sender, e.receiver⟩ := by rfl
              _ = ⟨branchEdge.sid, branchEdge.sender, branchEdge.receiver⟩ := by
                  simp only [hSidEq, hSenderEq, hRecvEq]
              _ = branchEdge := by rfl
          exact hEdgeEq
        have hTraceEmpty := trace_empty_when_branch_other_sender hEdgeCoh hBranchType' hSenderNe
        rw [hTraceEmpty]
        trivial
      | branch source bs' =>
        -- Same reasoning
        have hEdgeCoh : EdgeCoherent G D e := hCoh e
        have hBranchType' : lookupG G ⟨e.sid, e.receiver⟩ = some (.branch senderRole bs) := by
          simp only [hG]
        have hSenderNe : e.sender ≠ senderRole := by
          intro hEq
          apply heq
          have hEdgeEq : e = branchEdge := by
            have hSidEq : e.sid = branchEdge.sid := rfl
            have hSenderEq : e.sender = branchEdge.sender := hEq
            have hRecvEq : e.receiver = branchEdge.receiver := rfl
            calc e = ⟨e.sid, e.sender, e.receiver⟩ := by rfl
              _ = ⟨branchEdge.sid, branchEdge.sender, branchEdge.receiver⟩ := by
                  simp only [hSidEq, hSenderEq, hRecvEq]
              _ = branchEdge := by rfl
          exact hEdgeEq
        have hTraceEmpty := trace_empty_when_branch_other_sender hEdgeCoh hBranchType' hSenderNe
        rw [hTraceEmpty]
        trivial
    · -- brancherEp is not the receiver
      have hRecvNoMatch : brancherEp ≠ { sid := e.sid, role := e.receiver } := hRecvMatch
      rw [lookupG_update_neq _ _ _ _ hRecvNoMatch]
      exact hHead e


end
