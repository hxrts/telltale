import Protocol.Coherence.Delegation.Core

/-! # Protocol.Coherence.Delegation.Preservation

Delegation-preservation helper and main theorems.
-/

/-
The Problem. After defining delegation semantics, we need case analysis lemmas
and the coherence-preservation theorem.

Solution Structure. Proves helper lemmas then the main preservation theorem and
session-renaming equivariance support.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Delegation Preservation Helpers

These private lemmas factor out the case analysis used in the main theorem.
Each handles a specific configuration of sender/receiver relationship to A and B. -/

/-- Reconstruct an edge from its field equalities. -/
lemma edge_eq_of {e : Edge} {sid : SessionId} {sender receiver : Role}
    (hSid : e.sid = sid) (hSender : e.sender = sender) (hReceiver : e.receiver = receiver) :
    e = ⟨sid, sender, receiver⟩ := by
  cases e with
  | mk sid' sender' receiver' =>
      simp at hSid hSender hReceiver
      subst hSid
      subst hSender
      subst hReceiver
      rfl

/-- If role r (distinct from A and B) has an endpoint in G', it had one in G.
    Used to recover pre-delegation types for the coherence witnesses. -/
lemma old_lookup_of_new_role
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (hDeleg : DelegationStep G G' D D' s A B) :
    ∀ r, r ≠ A → r ≠ B →
      (lookupG G' ⟨s, r⟩).isSome → ∃ L, lookupG G ⟨s, r⟩ = some L := by
  intro r hRA hRB hSome
  rcases (Option.isSome_iff_exists).1 hSome with ⟨L', hLookup'⟩
  have hOther := hDeleg.other_roles_G ⟨s, r⟩ rfl hRA hRB
  have hMap : (lookupG G ⟨s, r⟩).map (renameLocalTypeRole s A B) = some L' := by
    simpa [hOther] using hLookup'
  cases hOld : lookupG G ⟨s, r⟩ with
  | none =>
      have : False := by
        simpa [hOld] using hMap
      exact (False.elim this)
  | some L0 =>
      exact ⟨L0, by simpa [hOld]⟩

/-! ## Helper Case: Redirected Self-Edge `(B,B)` -/

/-- Case: self-edge (B,B). Corresponds to old self-edge (A,A).
    Both sender and receiver underwent A→B renaming. -/
lemma coherent_case_senderB_receiverB
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role} {e : Edge}
    (hCoh : Coherent G D)
    (hDeleg : DelegationStep G G' D D' s A B)
    (hSid : e.sid = s) (hSenderB : e.sender = B) (hReceiverB : e.receiver = B) :
    EdgeCoherent G' D' e := by
  have hActiveOld : ActiveEdge G ⟨s, A, A⟩ :=
    ActiveEdge_of_endpoints (e:=⟨s, A, A⟩) hDeleg.A_lookup hDeleg.A_lookup
  have hCohOld : EdgeCoherent G D ⟨s, A, A⟩ :=
    Coherent_edge_any hCoh hActiveOld
  have hEdge :=
    delegate_redirected_edge_coherent_self (G:=G) (G':=G') (D:=D) (D':=D')
      (s:=s) (A:=A) (B:=B) hCohOld hDeleg
  have hEq : e = ⟨s, B, B⟩ := edge_eq_of (e:=e) hSid hSenderB hReceiverB
  simpa [hEq] using hEdge

/-! ## Helper Case: Redirected Sender `(B,C)` -/

/-- Case: edge (B,C) where C ≠ B. Corresponds to old edge (A,C).
    Sender A became B; receiver C unchanged but type renamed. -/
lemma coherent_case_senderB_receiverNeB
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role} {e : Edge}
    (hCoh : Coherent G D)
    (hDeleg : DelegationStep G G' D D' s A B)
    (hOldOfNew : ∀ r, r ≠ A → r ≠ B →
      (lookupG G' ⟨s, r⟩).isSome → ∃ L, lookupG G ⟨s, r⟩ = some L)
    (hSid : e.sid = s) (hSenderB : e.sender = B) (hReceiverB : e.receiver ≠ B)
    (hActive : ActiveEdge G' e) :
    EdgeCoherent G' D' e := by
  cases e with
  | mk sid sender receiver =>
      have hSid' : sid = s := by simpa using hSid
      have hSenderB' : sender = B := by simpa using hSenderB
      have hReceiverB' : receiver ≠ B := by simpa using hReceiverB
      have hReceiverNeA : receiver ≠ A := by
        intro hEq
        have : (lookupG G' ⟨s, A⟩).isSome := by
          simpa [hSid', hEq] using hActive.2
        simpa [hDeleg.A_removed] using this
      have hRecvSome' : (lookupG G' ⟨s, receiver⟩).isSome := by
        simpa [hSid'] using hActive.2
      have ⟨Lrecv0, hGrecv0⟩ := hOldOfNew receiver hReceiverNeA hReceiverB' hRecvSome'
      have hActiveOld : ActiveEdge G ⟨s, A, receiver⟩ :=
        ActiveEdge_of_endpoints (e:=⟨s, A, receiver⟩) hDeleg.A_lookup hGrecv0
      have hCohOld : EdgeCoherent G D ⟨s, A, receiver⟩ :=
        Coherent_edge_any hCoh hActiveOld
	      have hEdge :=
	        delegate_redirected_edge_coherent (G:=G) (G':=G') (D:=D) (D':=D')
	          (s:=s) (A:=A) (B:=B) (C:=receiver)
	          (Ne.symm hReceiverNeA) (Ne.symm hReceiverB') hCohOld hDeleg
	      simpa [hSid', hSenderB'] using hEdge

/-! ## Helper Case: Redirected Receiver `(C,B)` -/

/-- Case: edge (C,B) where C ≠ B. Corresponds to old edge (C,A).
    Receiver A became B; sender C unchanged but type renamed. -/
lemma coherent_case_senderNeB_receiverB
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role} {e : Edge}
    (hCoh : Coherent G D)
    (hDeleg : DelegationStep G G' D D' s A B)
    (hOldOfNew : ∀ r, r ≠ A → r ≠ B →
      (lookupG G' ⟨s, r⟩).isSome → ∃ L, lookupG G ⟨s, r⟩ = some L)
    (hSid : e.sid = s) (hSenderB : e.sender ≠ B) (hReceiverB : e.receiver = B)
    (hActive : ActiveEdge G' e) :
    EdgeCoherent G' D' e := by
  cases e with
  | mk sid sender receiver =>
      have hSid' : sid = s := by simpa using hSid
      have hSenderB' : sender ≠ B := by simpa using hSenderB
      have hReceiverB' : receiver = B := by simpa using hReceiverB
      have hSenderNeA : sender ≠ A := by
        intro hEq
        have : (lookupG G' ⟨s, A⟩).isSome := by
          simpa [hSid', hEq] using hActive.1
        simpa [hDeleg.A_removed] using this
      have hSenderSome' : (lookupG G' ⟨s, sender⟩).isSome := by
        simpa [hSid'] using hActive.1
      have ⟨Lsender0, hGsender0⟩ := hOldOfNew sender hSenderNeA hSenderB' hSenderSome'
      have hActiveOld : ActiveEdge G ⟨s, sender, A⟩ :=
        ActiveEdge_of_endpoints (e:=⟨s, sender, A⟩) hGsender0 hDeleg.A_lookup
      have hCohOld : EdgeCoherent G D ⟨s, sender, A⟩ :=
        Coherent_edge_any hCoh hActiveOld
	      have hEdge :=
	        delegate_redirected_edge_coherent_receiver (G:=G) (G':=G') (D:=D) (D':=D')
	          (s:=s) (A:=A) (B:=B) (C:=sender)
	          hSenderNeA hSenderB' hCohOld hDeleg
	      simpa [hSid', hReceiverB'] using hEdge

/-! ## Helper Case: Unrelated Session Edge `(C,D)` -/

/-- Case: edge (C,D) where neither C nor D is A or B.
    Edge is unchanged but types/traces undergo A→B renaming. -/
lemma coherent_case_unrelated
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role} {e : Edge}
    (hCoh : Coherent G D)
    (hDeleg : DelegationStep G G' D D' s A B)
    (hOldOfNew : ∀ r, r ≠ A → r ≠ B →
      (lookupG G' ⟨s, r⟩).isSome → ∃ L, lookupG G ⟨s, r⟩ = some L)
    (hSid : e.sid = s)
    (hSenderB : e.sender ≠ B) (hReceiverB : e.receiver ≠ B)
    (hSenderNeA : e.sender ≠ A) (hReceiverNeA : e.receiver ≠ A)
    (hActive : ActiveEdge G' e) :
    EdgeCoherent G' D' e := by
  have hSenderSome' : (lookupG G' ⟨s, e.sender⟩).isSome := by
    simpa [hSid] using hActive.1
  have hRecvSome' : (lookupG G' ⟨s, e.receiver⟩).isSome := by
    simpa [hSid] using hActive.2
  have ⟨Lsender0, hGsender0⟩ := hOldOfNew e.sender hSenderNeA hSenderB hSenderSome'
  have ⟨Lrecv0, hGrecv0⟩ := hOldOfNew e.receiver hReceiverNeA hReceiverB hRecvSome'
  have hGsender0' : lookupG G ⟨e.sid, e.sender⟩ = some Lsender0 := by
    simpa [hSid] using hGsender0
  have hGrecv0' : lookupG G ⟨e.sid, e.receiver⟩ = some Lrecv0 := by
    simpa [hSid] using hGrecv0
  have hActiveOld : ActiveEdge G e :=
    ActiveEdge_of_endpoints (e:=e) hGsender0' hGrecv0'
  have hCohOld : EdgeCoherent G D e := Coherent_edge_any hCoh hActiveOld
  exact delegate_unrelated_edge_coherent (G:=G) (G':=G') (D:=D) (D':=D')
    (s:=s) (A:=A) (B:=B) (e:=e) hSid hSenderNeA hSenderB hReceiverNeA hReceiverB hCohOld hDeleg

/-! ## Helper Case: Other Session Edge -/

/-- Case: edge in a different session. Unchanged by delegation. -/
lemma coherent_case_other_session
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role} {e : Edge}
    (hCoh : Coherent G D)
    (hDeleg : DelegationStep G G' D D' s A B)
    (hSid : e.sid ≠ s)
    (hActive : ActiveEdge G' e) :
    EdgeCoherent G' D' e := by
  rcases (Option.isSome_iff_exists).1 hActive.1 with ⟨Lsender, hGsender'⟩
  rcases (Option.isSome_iff_exists).1 hActive.2 with ⟨Lrecv, hGrecv'⟩
  have hOtherSender := hDeleg.other_sessions_G ⟨e.sid, e.sender⟩ hSid
  have hOtherRecv := hDeleg.other_sessions_G ⟨e.sid, e.receiver⟩ hSid
  have hGsender : lookupG G ⟨e.sid, e.sender⟩ = some Lsender := by
    simpa [hOtherSender] using hGsender'
  have hGrecv : lookupG G ⟨e.sid, e.receiver⟩ = some Lrecv := by
    simpa [hOtherRecv] using hGrecv'
  have hActiveOld : ActiveEdge G e :=
    ActiveEdge_of_endpoints (e:=e) hGsender hGrecv
  have hCohOld : EdgeCoherent G D e := Coherent_edge_any hCoh hActiveOld
  exact delegate_other_session_edge_coherent (G:=G) (G':=G') (D:=D) (D':=D')
    (s:=s) (A:=A) (B:=B) (e:=e) hSid hCohOld hDeleg

/-! ## Main Theorem -/

/-- **Delegation preserves coherence.**

    If we have coherence before a delegation step (A delegates endpoint in session s to B),
    then we have coherence after.

    **Proof strategy** (four-way case split on edge e in session s):

    1. **Self-edge (B,B)**: Old edge was (A,A). Use `delegate_redirected_edge_coherent_self`.

    2. **Sender is B, receiver C ≠ B**: Old edge was (A,C). The sender A became B;
       receiver C unchanged but its type renamed. Use `delegate_redirected_edge_coherent`.

    3. **Receiver is B, sender C ≠ B**: Old edge was (C,A). The receiver A became B;
       sender C unchanged but its type renamed. Use `delegate_redirected_edge_coherent_receiver`.

    4. **Neither endpoint is A or B**: Edge unchanged but types/traces renamed.
       Use `delegate_unrelated_edge_coherent`.

    Edges in other sessions are unchanged (case 5). -/
theorem delegation_preserves_coherent :
  ∀ G G' D D' s A B,
    Coherent G D →
    DelegationStep G G' D D' s A B →
    Coherent G' D' := by
  intro G G' D D' s A B hCoh hDeleg e hActive
  -- Top-level split: is edge e in the delegated session s?
  by_cases hSid : e.sid = s
  · -- Case: Edge in session s. Further split on sender/receiver relationship to B.
    have hOldOfNew := old_lookup_of_new_role (G:=G) (G':=G') (D:=D) (D':=D')
      (s:=s) (A:=A) (B:=B) hDeleg
    by_cases hSenderB : e.sender = B
    · by_cases hReceiverB : e.receiver = B
      · -- Case 1: Self-edge (B,B) — corresponds to old (A,A)
        exact coherent_case_senderB_receiverB (G:=G) (G':=G') (D:=D) (D':=D')
          (s:=s) (A:=A) (B:=B) (e:=e) hCoh hDeleg hSid hSenderB hReceiverB
      · -- Case 2: Edge (B,C) where C ≠ B — corresponds to old (A,C)
        exact coherent_case_senderB_receiverNeB (G:=G) (G':=G') (D:=D) (D':=D')
          (s:=s) (A:=A) (B:=B) (e:=e) hCoh hDeleg hOldOfNew hSid hSenderB hReceiverB hActive
    · by_cases hReceiverB : e.receiver = B
      · -- Case 3: Edge (C,B) where C ≠ B — corresponds to old (C,A)
        exact coherent_case_senderNeB_receiverB (G:=G) (G':=G') (D:=D) (D':=D')
          (s:=s) (A:=A) (B:=B) (e:=e) hCoh hDeleg hOldOfNew hSid hSenderB hReceiverB hActive
      · -- Case 4: Neither endpoint is B. Show neither is A (would contradict ActiveEdge).
        have hSenderNeA : e.sender ≠ A := by
          intro hEq
          have : (lookupG G' ⟨s, A⟩).isSome := by
            simpa [hSid, hEq] using hActive.1
          simpa [hDeleg.A_removed] using this
        have hReceiverNeA : e.receiver ≠ A := by
          intro hEq
          have : (lookupG G' ⟨s, A⟩).isSome := by
            simpa [hSid, hEq] using hActive.2
          simpa [hDeleg.A_removed] using this
        -- Edge unchanged but types/traces renamed
        exact coherent_case_unrelated (G:=G) (G':=G') (D:=D) (D':=D')
          (s:=s) (A:=A) (B:=B) (e:=e)
          hCoh hDeleg hOldOfNew hSid hSenderB hReceiverB hSenderNeA hReceiverNeA hActive
  · -- Case 5: Edge in different session — unchanged by delegation
    exact coherent_case_other_session (G:=G) (G':=G') (D:=D) (D':=D')
      (s:=s) (A:=A) (B:=B) (e:=e) hCoh hDeleg hSid hActive

/-- Delegation-specific wrapper for the unified preservation framework:
    delegation steps preserve `Coherent`. -/
theorem delegation_preserves_coherent_unified
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (hCoh : Coherent G D)
    (hDeleg : DelegationStep G G' D D' s A B) :
    Coherent G' D' :=
  delegation_preserves_coherent G G' D D' s A B hCoh hDeleg

/-! ## Session Renaming Equivariance -/

/-- DelegationWF is preserved under session renaming. -/
theorem DelegationWF_respects_renaming (ρ : SessionRenaming)
    {G : GEnv} {s : SessionId} {A B : Role}
    (hWF : DelegationWF G s A B) :
    DelegationWF (renameGEnv ρ G) (ρ.f s) A B where
  A_in_session := by
    -- Show endpoint equality: ⟨ρ.f s, A⟩ = renameEndpoint ρ ⟨s, A⟩
    have hep : (⟨ρ.f s, A⟩ : Endpoint) = renameEndpoint ρ ⟨s, A⟩ := by simp [renameEndpoint]
    rw [hep, lookupG_rename]
    simp only [Option.isSome_map]
    exact hWF.A_in_session
  B_not_in_session := by
    -- Show endpoint equality: ⟨ρ.f s, B⟩ = renameEndpoint ρ ⟨s, B⟩
    have hep : (⟨ρ.f s, B⟩ : Endpoint) = renameEndpoint ρ ⟨s, B⟩ := by simp [renameEndpoint]
    rw [hep, lookupG_rename]
    simp only [Option.isNone_map]
    exact hWF.B_not_in_session
  A_ne_B := hWF.A_ne_B

/-! ## Session-Renaming Equivariance: Redirected Edges -/

/-- IsRedirectedEdge is preserved under session renaming. -/
theorem IsRedirectedEdge_respects_renaming (ρ : SessionRenaming)
    {e e' : Edge} {s : SessionId} {A B : Role}
    (hRedir : IsRedirectedEdge e e' s A B) :
    IsRedirectedEdge (renameEdge ρ e) (renameEdge ρ e') (ρ.f s) A B := by
  -- IsRedirectedEdge is just: e' = redirectEdge e s A B
  simp only [IsRedirectedEdge] at hRedir ⊢
  -- Need to show: renameEdge ρ e' = redirectEdge (renameEdge ρ e) (ρ.f s) A B
  simp only [hRedir, renameEdge, redirectEdge]
  by_cases hSid : e.sid = s
  · -- e.sid = s: both redirects apply
    simp only [hSid, beq_self_eq_true, ↓reduceIte]
  · -- e.sid ≠ s: neither redirect applies
    have hSidRen : ρ.f e.sid ≠ ρ.f s := fun h => hSid (ρ.inj e.sid s h)
    have hBeq : (e.sid == s) = false := beq_eq_false_iff_ne.mpr hSid
    have hBeqRen : (ρ.f e.sid == ρ.f s) = false := beq_eq_false_iff_ne.mpr hSidRen
    simp only [hBeq, hBeqRen, Bool.false_eq_true, ↓reduceIte]

/-! ## Session-Renaming Equivariance: Preimage Helpers -/

/-- Helper: construct edge preimage when we know the session ID maps. -/
theorem edge_preimage_of_sid_eq (ρ : SessionRenaming) (e : Edge) (s : SessionId)
    (hSid : e.sid = ρ.f s) :
    e = renameEdge ρ { sid := s, sender := e.sender, receiver := e.receiver } := by
  simp only [renameEdge]
  cases e with
  | mk sid sender receiver =>
    simp only [Edge.mk.injEq, and_self, and_true]
    simp only at hSid
    exact hSid

/-- Helper: if e.sid ≠ ρ.f s and e has a preimage e₀, then e₀.sid ≠ s. -/
theorem preimage_sid_ne (ρ : SessionRenaming) (e e₀ : Edge) (s : SessionId)
    (hNeSid : e.sid ≠ ρ.f s) (hEeq : e = renameEdge ρ e₀) :
    e₀.sid ≠ s := by
  intro heq
  have hContra : e.sid = ρ.f s := by
    simp only [hEeq, renameEdge, heq]
  exact hNeSid hContra

/-- Helper: analogous preimage lemma for endpoints. -/
theorem endpoint_preimage_sid_ne (ρ : SessionRenaming) (ep ep' : Endpoint) (s : SessionId)
    (hNeSid : ep.sid ≠ ρ.f s) (hEpEq : ep = renameEndpoint ρ ep') :
    ep'.sid ≠ s := by
  intro heq
  have hContra : ep.sid = ρ.f s := by
    simp only [hEpEq, renameEndpoint, heq]
  exact hNeSid hContra


end
