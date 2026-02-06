import Protocol.Coherence.EdgeCoherence
import Protocol.Environments.RoleRenaming

/-! # Delegation Preservation

Proves that delegation steps preserve the coherence invariant. This bridges
Protocol-level metatheory to VM-level instruction execution.

## Main Results

- `DelegationStep`: Specification of a delegation step (A → B in session s)
- `delegation_preserves_coherent`: Coherence preserved across delegation

## Proof Strategy

Three-way edge case analysis after delegation from A to B in session s:
1. **Redirected edges** `(A,C)→(B,C)` or `(C,A)→(C,B)`: Use role-renaming lemmas
2. **Self-edge** `(A,A)→(B,B)`: Combine sender and receiver renaming
3. **Other-session edges**: Unchanged by session isolation
4. **Unrelated edges**: Neither endpoint is A or B, apply renaming to types/traces
-/

/-
The Problem. Delegation transfers an endpoint from role A to role B in session s.
This changes the typing environment (GEnv) and delivery environment (DEnv):
- A's endpoint is removed from GEnv
- B's endpoint is added with A's old type (with A→B renaming in roles)
- Other participants' types have A→B renaming
- Edges are redirected: (A,C)→(B,C) and (C,A)→(C,B)
- Edge traces are preserved under redirection

The difficulty is that coherence depends on Consume succeeding for each edge,
and Consume checks that the receiver's type matches the trace. After delegation,
both types and traces undergo role renaming, so we must prove that Consume
commutes with role renaming.

Solution Structure. The proof decomposes into four helper theorems:
1. `Consume_delegate`: Consume commutes with A→B renaming when sender is A
2. `Consume_rename_unrelated`: Consume commutes with renaming for unrelated sender
3. `delegate_redirected_edge_coherent`: Redirected edges remain coherent
4. `delegate_unrelated_edge_coherent`: Edges not involving A/B remain coherent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

noncomputable section

/-! ## Well-Formedness Conditions -/

/-- Well-formedness conditions for delegation from A to B in session s. -/
structure DelegationWF (G : GEnv) (s : SessionId) (A B : Role) : Prop where
  /-- A is in session s (has an endpoint) -/
  A_in_session : (lookupG G ⟨s, A⟩).isSome
  /-- B is not already in session s (simple delegation case) -/
  B_not_in_session : (lookupG G ⟨s, B⟩).isNone
  /-- A and B are distinct roles -/
  A_ne_B : A ≠ B

/-! ## Edge Redirection -/

/-- Redirect an edge from A to B in session s.
    - If sender is A, becomes B
    - If receiver is A, becomes B
    - Edges in other sessions unchanged -/
def redirectEdge (e : Edge) (s : SessionId) (A B : Role) : Edge :=
  if e.sid == s then
    { sid := s,
      sender := if e.sender == A then B else e.sender,
      receiver := if e.receiver == A then B else e.receiver }
  else e

/-- An edge e' is the redirection of edge e. -/
def IsRedirectedEdge (e e' : Edge) (s : SessionId) (A B : Role) : Prop :=
  e' = redirectEdge e s A B

theorem redirectEdge_other_session (e : Edge) (s : SessionId) (A B : Role)
    (hSid : e.sid ≠ s) : redirectEdge e s A B = e := by
  simp [redirectEdge, hSid]

theorem redirectEdge_no_A (e : Edge) (s : SessionId) (A B : Role)
    (hSid : e.sid = s) (hSender : e.sender ≠ A) (hReceiver : e.receiver ≠ A) :
    redirectEdge e s A B = e := by
  have hS : (e.sender == A) = false := beq_eq_false_iff_ne.mpr hSender
  have hR : (e.receiver == A) = false := beq_eq_false_iff_ne.mpr hReceiver
  cases e with
  | mk sid sender receiver =>
      have hSid' : sid = s := by
        simpa using hSid
      subst hSid'
      simp [redirectEdge, hS, hR]

theorem IsRedirectedEdge_sender (s : SessionId) (A B C : Role) (hCA : C ≠ A) :
    IsRedirectedEdge ⟨s, A, C⟩ ⟨s, B, C⟩ s A B := by
  have hC : (C == A) = false := beq_eq_false_iff_ne.mpr hCA
  simp [IsRedirectedEdge, redirectEdge, hC]

theorem IsRedirectedEdge_receiver (s : SessionId) (A B C : Role) (hCA : C ≠ A) :
    IsRedirectedEdge ⟨s, C, A⟩ ⟨s, C, B⟩ s A B := by
  have hC : (C == A) = false := beq_eq_false_iff_ne.mpr hCA
  simp [IsRedirectedEdge, redirectEdge, hC]

/-! ## Delegation Step Relation -/

/-- A delegation step transfers an endpoint from role A to role B in session s.

    This is defined as a predicate specifying what the post-delegation environments
    must satisfy, rather than computing them explicitly.

    **GEnv conditions:**
    - A's endpoint for session s is removed
    - B's endpoint for session s is added with A's old type, renamed (A → B)
    - Other endpoints in session s have A → B renaming in their types
    - Endpoints in other sessions are unchanged

    **DEnv conditions:**
    - Edges are redirected: (A,C,s) → (B,C,s) and (C,A,s) → (C,B,s)
    - Traces are preserved under redirection
    - Edges in other sessions are unchanged

    The simple case assumes B is not already in session s. The general case
    (B already participates) requires type merging via Consume_mono (task 3.6). -/
structure DelegationStep (G G' : GEnv) (D D' : DEnv) (s : SessionId) (A B : Role) where
  /-- Well-formedness: A in session, B not in session, A ≠ B -/
  wf : DelegationWF G s A B

  /-- A's original local type in session s. -/
  A_type : LocalType

  /-- A's endpoint lookup before delegation. -/
  A_lookup : lookupG G ⟨s, A⟩ = some A_type

  /-- A is removed from session s -/
  A_removed : lookupG G' ⟨s, A⟩ = none

  /-- B gains an endpoint in session s -/
  B_added : lookupG G' ⟨s, B⟩ = some (renameLocalTypeRole s A B A_type)

  /-- Other roles in session s get their local types renamed (A → B). -/
  other_roles_G :
    ∀ ep, ep.sid = s → ep.role ≠ A → ep.role ≠ B →
      lookupG G' ep = (lookupG G ep).map (renameLocalTypeRole s A B)

  /-- Endpoints outside session s are unchanged -/
  other_sessions_G : ∀ ep, ep.sid ≠ s → lookupG G' ep = lookupG G ep

  /-- Redirected edges have their traces renamed (A → B) from their pre-images. -/
  trace_preserved : ∀ e e',
    IsRedirectedEdge e e' s A B →
    lookupD D' e' = (lookupD D e).map (renameValTypeRole s A B)

  /-- Edges in other sessions are unchanged -/
  other_sessions_D : ∀ e, e.sid ≠ s → lookupD D' e = lookupD D e

/-! ## Role-Renaming for Consume (Delegation) -/

/-- If a consume step succeeds from A, it also succeeds after renaming A → B. -/
theorem consumeOne_delegate (s : SessionId) (A B : Role) (T : ValType) (L L' : LocalType)
    (h : consumeOne A T L = some L') :
    consumeOne B (renameValTypeRole s A B T) (renameLocalTypeRole s A B L) =
      some (renameLocalTypeRole s A B L') := by
  cases L with
  | recv r T' Lr =>
      by_cases hCond : A == r && T == T'
      · have hL : L' = Lr := by
          have : some Lr = some L' := by
            simpa [consumeOne, hCond] using h
          exact (Option.some.inj this).symm
        have hBoth := Bool.and_eq_true_iff.mp hCond
        have hRoleEq : A = r := eq_of_beq hBoth.1
        have hTypeEq : T = T' := eq_of_beq hBoth.2
        simp [consumeOne, renameLocalTypeRole, renameRole, hRoleEq, hTypeEq, hL]
      · have : False := by
          simpa [consumeOne, hCond] using h
        exact (False.elim this)
  | send r T' Lr =>
      cases h
  | select r bs =>
      cases h
  | branch r bs =>
      cases h
  | end_ =>
      cases h
  | var n =>
      cases h
  | mu Lr =>
      cases h

/-- Delegation renaming preserves Consume success (A → B). -/
theorem Consume_delegate (s : SessionId) (A B : Role) (L : LocalType) (ts : List ValType) (L' : LocalType)
    (h : Consume A L ts = some L') :
    Consume B (renameLocalTypeRole s A B L) (ts.map (renameValTypeRole s A B)) =
      some (renameLocalTypeRole s A B L') := by
  induction ts generalizing L L' with
  | nil =>
      simp [Consume] at h
      simp [Consume, h]
  | cons t ts ih =>
      simp [Consume] at h
      cases hOne : consumeOne A t L with
      | none =>
          have : False := by
            simpa [hOne] using h
          exact (False.elim this)
      | some L1 =>
          have hTail : Consume A L1 ts = some L' := by
            simpa [hOne] using h
          have hRen := consumeOne_delegate (s:=s) (A:=A) (B:=B) (T:=t) (L:=L) (L':=L1) hOne
          have hTailRen := ih (L:=L1) (L':=L') hTail
          simp [Consume, hRen, hTailRen]

/-! ## Role-Renaming for Unrelated Senders -/

/-- If a consume step succeeds from `from_` and `from_` is unrelated to A/B,
    it also succeeds after renaming A → B. -/
theorem consumeOne_rename_unrelated (s : SessionId) (A B : Role) (from_ : Role)
    (T : ValType) (L L' : LocalType)
    (hFromA : from_ ≠ A) (hFromB : from_ ≠ B)
    (h : consumeOne from_ T L = some L') :
    consumeOne from_ (renameValTypeRole s A B T) (renameLocalTypeRole s A B L) =
      some (renameLocalTypeRole s A B L') := by
  cases L with
  | recv r T' Lr =>
      have hCond : (from_ == r && T == T') = true := by
        by_cases hCond : from_ == r && T == T'
        · exact hCond
        · have : False := by
            simpa [consumeOne, hCond] using h
          exact (False.elim this)
      have hL : L' = Lr := by
        have : some Lr = some L' := by
          simpa [consumeOne, hCond] using h
        exact (Option.some.inj this).symm
      have hBoth := Bool.and_eq_true_iff.mp hCond
      have hRoleEq : from_ = r := eq_of_beq hBoth.1
      have hTypeEq : T = T' := eq_of_beq hBoth.2
      have hRoleNeA : r ≠ A := by
        intro hEq
        apply hFromA
        exact hRoleEq.trans hEq
      have hRoleNeB : r ≠ B := by
        intro hEq
        apply hFromB
        exact hRoleEq.trans hEq
      have hRoleRen : renameRole A B r = r := by
        simp [renameRole, beq_eq_false_iff_ne.mpr hRoleNeA]
      have hBeqRole : (from_ == renameRole A B r) = true := by
        simp [hRoleEq, hRoleRen]
      have hBeqType : (renameValTypeRole s A B T == renameValTypeRole s A B T') = true := by
        simp [hTypeEq]
      simp [consumeOne, renameLocalTypeRole, renameValTypeRole, hBeqRole, hBeqType, hL]
  | send r T' Lr =>
      cases h
  | select r bs =>
      cases h
  | branch r bs =>
      cases h
  | end_ =>
      cases h
  | var n =>
      cases h
  | mu Lr =>
      cases h

/-- Renaming preserves Consume success for an unrelated sender. -/
theorem Consume_rename_unrelated (s : SessionId) (A B : Role) (from_ : Role)
    (L : LocalType) (ts : List ValType) (L' : LocalType)
    (hFromA : from_ ≠ A) (hFromB : from_ ≠ B)
    (h : Consume from_ L ts = some L') :
    Consume from_ (renameLocalTypeRole s A B L) (ts.map (renameValTypeRole s A B)) =
      some (renameLocalTypeRole s A B L') := by
  induction ts generalizing L L' with
  | nil =>
      simp [Consume] at h
      simp [Consume, h]
  | cons t ts ih =>
      simp [Consume] at h
      cases hOne : consumeOne from_ t L with
      | none =>
          have : False := by
            simpa [hOne] using h
          exact (False.elim this)
      | some L1 =>
          have hTail : Consume from_ L1 ts = some L' := by
            simpa [hOne] using h
          have hRen := consumeOne_rename_unrelated (s:=s) (A:=A) (B:=B) (from_:=from_)
            (T:=t) (L:=L) (L':=L1) hFromA hFromB hOne
          have hTailRen := ih (L:=L1) (L':=L') hTail
          simp [Consume, hRen, hTailRen]

/-! ## Redirected Edge Coherence -/

/-- Redirected edges preserve coherence under role renaming. -/
theorem delegate_redirected_edge_coherent
    (G G' : GEnv) (D D' : DEnv) (s : SessionId)
    (A B C : Role)
    (hAC : A ≠ C) (hBC : B ≠ C)
    (hCohOld : EdgeCoherent G D ⟨s, A, C⟩)
    (hDeleg : DelegationStep G G' D D' s A B) :
    EdgeCoherent G' D' ⟨s, B, C⟩ := by
  intro Lrecv hGrecv
  -- Receiver lookup in G' comes from renaming the old receiver type.
  have hOther := hDeleg.other_roles_G ⟨s, C⟩ rfl (Ne.symm hAC) (Ne.symm hBC)
  have hMap : (lookupG G ⟨s, C⟩).map (renameLocalTypeRole s A B) = some Lrecv := by
    simpa [hOther] using hGrecv
  cases hLookup : lookupG G ⟨s, C⟩ with
  | none =>
      simp [hLookup] at hMap
  | some Lrecv0 =>
      have hEq : renameLocalTypeRole s A B Lrecv0 = Lrecv := by
        have : some (renameLocalTypeRole s A B Lrecv0) = some Lrecv := by
          simpa [hLookup] using hMap
        exact Option.some.inj this
      -- Original coherence on (A,C).
      have hCohOld' := hCohOld Lrecv0 hLookup
      rcases hCohOld' with ⟨Lsender0, hGsender0, hConsumeOld⟩
      -- Redirected trace.
      have hRedir : IsRedirectedEdge ⟨s, A, C⟩ ⟨s, B, C⟩ s A B := by
        exact IsRedirectedEdge_sender s A B C (Ne.symm hAC)
      have hTrace :
          lookupD D' ⟨s, B, C⟩ = (lookupD D ⟨s, A, C⟩).map (renameValTypeRole s A B) := by
        exact hDeleg.trace_preserved _ _ hRedir
      -- Consume is preserved under role renaming.
      have hConsumeRen :
          (Consume B (renameLocalTypeRole s A B Lrecv0)
            ((lookupD D ⟨s, A, C⟩).map (renameValTypeRole s A B))).isSome := by
        cases hCons : Consume A Lrecv0 (lookupD D ⟨s, A, C⟩) with
        | none =>
            have : False := by
              simpa [hCons] using hConsumeOld
            exact (False.elim this)
        | some L' =>
            have hRen :=
              Consume_delegate (s:=s) (A:=A) (B:=B) (L:=Lrecv0)
                (ts:=lookupD D ⟨s, A, C⟩) (L':=L') hCons
            simp [hRen]
      refine ⟨renameLocalTypeRole s A B hDeleg.A_type, hDeleg.B_added, ?_⟩
      simpa [hEq, hTrace] using hConsumeRen

/-- Redirected edges (receiver A → B) preserve coherence under role renaming. -/
theorem delegate_redirected_edge_coherent_receiver
    (G G' : GEnv) (D D' : DEnv) (s : SessionId)
    (A B C : Role)
    (hCA : C ≠ A) (hCB : C ≠ B)
    (hCohOld : EdgeCoherent G D ⟨s, C, A⟩)
    (hDeleg : DelegationStep G G' D D' s A B) :
    EdgeCoherent G' D' ⟨s, C, B⟩ := by
  intro Lrecv hGrecv
  -- Receiver lookup is B_added.
  have hRecvEq : Lrecv = renameLocalTypeRole s A B hDeleg.A_type := by
    have : some (renameLocalTypeRole s A B hDeleg.A_type) = some Lrecv := by
      simpa [hDeleg.B_added] using hGrecv
    exact (Option.some.inj this).symm
  -- Original coherence at (C,A).
  have hCohOld' := hCohOld hDeleg.A_type hDeleg.A_lookup
  rcases hCohOld' with ⟨Lsender0, hGsender0, hConsumeOld⟩
  -- Sender lookup in G' for C.
  have hOther := hDeleg.other_roles_G ⟨s, C⟩ rfl hCA hCB
  have hSenderLookup : lookupG G' ⟨s, C⟩ = some (renameLocalTypeRole s A B Lsender0) := by
    simpa [hOther, hGsender0]
  -- Redirected trace for (C,A) → (C,B).
  have hRedir : IsRedirectedEdge ⟨s, C, A⟩ ⟨s, C, B⟩ s A B := by
    exact IsRedirectedEdge_receiver s A B C hCA
  have hTrace :
      lookupD D' ⟨s, C, B⟩ = (lookupD D ⟨s, C, A⟩).map (renameValTypeRole s A B) := by
    exact hDeleg.trace_preserved _ _ hRedir
  -- Consume success preserved since sender C is unrelated to A/B.
  have hConsumeRen :
      (Consume C (renameLocalTypeRole s A B hDeleg.A_type)
        ((lookupD D ⟨s, C, A⟩).map (renameValTypeRole s A B))).isSome := by
    cases hCons : Consume C hDeleg.A_type (lookupD D ⟨s, C, A⟩) with
    | none =>
        have : False := by
          simpa [hCons] using hConsumeOld
        exact (False.elim this)
    | some L' =>
        have hRen := Consume_rename_unrelated (s:=s) (A:=A) (B:=B) (from_:=C)
          (L:=hDeleg.A_type) (ts:=lookupD D ⟨s, C, A⟩) (L':=L') hCA hCB hCons
        simp [hRen]
  refine ⟨renameLocalTypeRole s A B Lsender0, hSenderLookup, ?_⟩
  simpa [hRecvEq, hTrace] using hConsumeRen

/-- Redirected self-edge `(A,A)` preserves coherence under delegation. -/
theorem delegate_redirected_edge_coherent_self
    (G G' : GEnv) (D D' : DEnv) (s : SessionId)
    (A B : Role)
    (hCohOld : EdgeCoherent G D ⟨s, A, A⟩)
    (hDeleg : DelegationStep G G' D D' s A B) :
    EdgeCoherent G' D' ⟨s, B, B⟩ := by
  intro Lrecv hGrecv
  -- Receiver lookup is B_added.
  have hRecvEq : Lrecv = renameLocalTypeRole s A B hDeleg.A_type := by
    have : some (renameLocalTypeRole s A B hDeleg.A_type) = some Lrecv := by
      simpa [hDeleg.B_added] using hGrecv
    exact (Option.some.inj this).symm
  -- Consume condition on the original self-edge.
  have hConsumeOld :
      (Consume A hDeleg.A_type (lookupD D ⟨s, A, A⟩)).isSome := by
    exact EdgeCoherent_consume_of_receiver hCohOld hDeleg.A_lookup
  -- Redirected trace for (A,A) → (B,B).
  have hRedir : IsRedirectedEdge ⟨s, A, A⟩ ⟨s, B, B⟩ s A B := by
    simp [IsRedirectedEdge, redirectEdge]
  have hTrace :
      lookupD D' ⟨s, B, B⟩ = (lookupD D ⟨s, A, A⟩).map (renameValTypeRole s A B) := by
    exact hDeleg.trace_preserved _ _ hRedir
  -- Consume success preserved under renaming.
  have hConsumeRen :
      (Consume B (renameLocalTypeRole s A B hDeleg.A_type)
        ((lookupD D ⟨s, A, A⟩).map (renameValTypeRole s A B))).isSome := by
    cases hCons : Consume A hDeleg.A_type (lookupD D ⟨s, A, A⟩) with
    | none =>
        have : False := by
          simpa [hCons] using hConsumeOld
        exact (False.elim this)
    | some L' =>
        have hRen :=
          Consume_delegate (s:=s) (A:=A) (B:=B) (L:=hDeleg.A_type)
            (ts:=lookupD D ⟨s, A, A⟩) (L':=L') hCons
        simp [hRen]
  refine ⟨renameLocalTypeRole s A B hDeleg.A_type, hDeleg.B_added, ?_⟩
  simpa [hRecvEq, hTrace] using hConsumeRen

/-! ## Unrelated Edge Coherence -/

/-- Edges in the delegated session that do **not** mention A or B as receiver
    remain coherent under role renaming. -/
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
      -- Trace is preserved under renaming (edge unchanged).
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

/-! ## Other-Session Edge Coherence -/

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

/-! ## Delegation Preservation Helpers

These private lemmas factor out the case analysis used in the main theorem.
Each handles a specific configuration of sender/receiver relationship to A and B. -/

/-- Reconstruct an edge from its field equalities. -/
private lemma edge_eq_of {e : Edge} {sid : SessionId} {sender receiver : Role}
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
private lemma old_lookup_of_new_role
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

/-- Case: self-edge (B,B). Corresponds to old self-edge (A,A).
    Both sender and receiver underwent A→B renaming. -/
private lemma coherent_case_senderB_receiverB
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

/-- Case: edge (B,C) where C ≠ B. Corresponds to old edge (A,C).
    Sender A became B; receiver C unchanged but type renamed. -/
private lemma coherent_case_senderB_receiverNeB
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

/-- Case: edge (C,B) where C ≠ B. Corresponds to old edge (C,A).
    Receiver A became B; sender C unchanged but type renamed. -/
private lemma coherent_case_senderNeB_receiverB
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

/-- Case: edge (C,D) where neither C nor D is A or B.
    Edge is unchanged but types/traces undergo A→B renaming. -/
private lemma coherent_case_unrelated
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

/-- Case: edge in a different session. Unchanged by delegation. -/
private lemma coherent_case_other_session
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

end
