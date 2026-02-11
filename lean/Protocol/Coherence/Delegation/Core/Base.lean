import Protocol.Coherence.EdgeCoherence
import Protocol.Environments.RoleRenaming

/-! # Delegation Preservation

Proves that delegation steps preserve the coherence invariant. This bridges
Protocol-level metatheory to VM-level instruction execution.

## Main Results

- `DelegationStep`: Specification of a delegation step (A → B in session s)
- `delegation_preserves_coherent`: Coherence preserved across delegation

## Proof Strategy

Four-way edge case analysis after delegation from A to B in session s:
1. **Edges created by delegation** `(B,C)` or `(C,B)` (with C ≠ B): Redirected from old `(A,C)`/`(C,A)`
2. **Self-edge** `(A,A)→(B,B)`: Combine sender and receiver renaming
3. **Unrelated edges**: Neither endpoint is A or B, apply renaming to types/traces
4. **Other-session edges**: Unchanged by session isolation
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
set_option linter.unnecessarySimpa false

open scoped Classical

section

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

  /-- In session `s`, edges incident to the removed role `A` are emptied. -/
  A_incident_empty :
    ∀ e, e.sid = s → (e.sender = A ∨ e.receiver = A) → lookupD D' e = []

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
      simp [consumeOne, renameLocalTypeRole, hBeqRole, hBeqType, hL]
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

end
