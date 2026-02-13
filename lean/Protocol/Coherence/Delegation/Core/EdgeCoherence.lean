import Protocol.Coherence.Delegation.Core.Base

/-! # Protocol.Coherence.Delegation.Core.EdgeCoherence

Edge-coherence lemmas following delegation redirection.
-/

/-
The Problem. After establishing delegation-step primitives, we need dedicated
edge-coherence lemmas for unrelated and other-session edges.

Solution Structure. Proves the remaining edge-coherence transport lemmas.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

-- Unrelated-Edge Coherence

theorem delegate_unrelated_edge_coherent
    (G G' : GEnv) (D D' : DEnv) (s : SessionId)
    (A B : Role) (e : Edge)
    (hSid : e.sid = s)
    (hSenderA : e.sender ≠ A)
    (hSenderB : e.sender ≠ B)
    (hReceiverA : e.receiver ≠ A)
    (hReceiverB : e.receiver ≠ B)
    (hCohOld : EdgeCoherent G D e)
    (hDeleg : DelegationStep G G' D D' s A B) :
    EdgeCoherent G' D' e := by
  intro Lrecv hGrecv
  have hGrecv' : lookupG G' ⟨s, e.receiver⟩ = some Lrecv := by
    simpa [hSid] using hGrecv
  -- Receiver lookup in G' comes from renaming the old receiver type.
  have hOther := hDeleg.other_roles_G ⟨s, e.receiver⟩ rfl hReceiverA hReceiverB
  have hMap : (lookupG G ⟨s, e.receiver⟩).map (renameLocalTypeRole s A B) = some Lrecv := by
    simpa [hOther] using hGrecv'
  cases hLookup : lookupG G ⟨s, e.receiver⟩ with
  | none =>
      simp [hLookup] at hMap
  | some Lrecv0 =>
      have hEq : renameLocalTypeRole s A B Lrecv0 = Lrecv := by
        have : some (renameLocalTypeRole s A B Lrecv0) = some Lrecv := by
          simpa [hLookup] using hMap
        exact Option.some.inj this
      -- Original coherence on e.
      have hLookup' : lookupG G ⟨e.sid, e.receiver⟩ = some Lrecv0 := by
        simpa [hSid] using hLookup
      have hCohOld' := hCohOld Lrecv0 hLookup'
      rcases hCohOld' with ⟨Lsender0, hGsender0, hConsumeOld⟩
      -- Sender lookup in G' is the renamed sender type.
      have hSenderOther := hDeleg.other_roles_G ⟨s, e.sender⟩ rfl hSenderA hSenderB
      have hSenderLookup : lookupG G' ⟨s, e.sender⟩ =
          some (renameLocalTypeRole s A B Lsender0) := by
        have hGsender0' : lookupG G ⟨s, e.sender⟩ = some Lsender0 := by
          simpa [hSid] using hGsender0
        simpa [hSenderOther, hGsender0']
      have hSenderLookup' : lookupG G' ⟨e.sid, e.sender⟩ =
          some (renameLocalTypeRole s A B Lsender0) := by
        simpa [hSid] using hSenderLookup
      -- Unrelated-edge coherence: trace/consume transport.
      have hRedir : IsRedirectedEdge e e s A B := by
        have hEq' := redirectEdge_no_A e s A B hSid hSenderA hReceiverA
        simp [IsRedirectedEdge, hEq']
      have hTrace :
          lookupD D' e = (lookupD D e).map (renameValTypeRole s A B) := by
        exact hDeleg.trace_preserved _ _ hRedir
      -- Consume success is preserved under renaming for unrelated sender.
      have hConsumeRen :
          (Consume e.sender (renameLocalTypeRole s A B Lrecv0)
            ((lookupD D e).map (renameValTypeRole s A B))).isSome := by
        cases hCons : Consume e.sender Lrecv0 (lookupD D e) with
        | none =>
            have : False := by
              simpa [hCons] using hConsumeOld
            exact (False.elim this)
        | some L' =>
            have hRen :=
              Consume_rename_unrelated (s:=s) (A:=A) (B:=B) (from_:=e.sender)
                (L:=Lrecv0) (ts:=lookupD D e) (L':=L') hSenderA hSenderB hCons
            simp [hRen]
      refine ⟨renameLocalTypeRole s A B Lsender0, hSenderLookup', ?_⟩
      simpa [hEq, hTrace] using hConsumeRen

-- Other-Session Edge Coherence

/-- Edges in other sessions are unchanged by delegation. -/
theorem delegate_other_session_edge_coherent
    (G G' : GEnv) (D D' : DEnv) (s : SessionId)
    (A B : Role) (e : Edge)
    (hSid : e.sid ≠ s)
    (hCohOld : EdgeCoherent G D e)
    (hDeleg : DelegationStep G G' D D' s A B) :
    EdgeCoherent G' D' e := by
  intro Lrecv hGrecv
  have hOtherRecv := hDeleg.other_sessions_G ⟨e.sid, e.receiver⟩ hSid
  have hRecv : lookupG G ⟨e.sid, e.receiver⟩ = some Lrecv := by
    simpa [hOtherRecv] using hGrecv
  have hCohOld' := hCohOld Lrecv hRecv
  rcases hCohOld' with ⟨Lsender, hGsender, hConsume⟩
  have hOtherSender := hDeleg.other_sessions_G ⟨e.sid, e.sender⟩ hSid
  have hSender : lookupG G' ⟨e.sid, e.sender⟩ = some Lsender := by
    simpa [hOtherSender] using hGsender
  have hTrace : lookupD D' e = lookupD D e := by
    simpa using hDeleg.other_sessions_D e hSid
  refine ⟨Lsender, hSender, ?_⟩
  simpa [hTrace] using hConsume



end
