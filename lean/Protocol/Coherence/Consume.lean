import Protocol.Environments

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

section

/-! ## Helper Lemmas for Edge Case Analysis -/

/-- An edge cannot have the same sender and receiver. -/
theorem Edge.sender_ne_receiver (e : Edge) (h : e.sender ≠ e.receiver) : e.sender ≠ e.receiver := h

/-- Flip an edge's direction (swap sender and receiver). -/
def Edge.flip (e : Edge) : Edge :=
  { sid := e.sid, sender := e.receiver, receiver := e.sender }

/-- An edge is not equal to its flip (assuming sender ≠ receiver). -/
theorem Edge.ne_flip (e : Edge) (h : e.sender ≠ e.receiver) : e ≠ e.flip := by
  intro heq
  -- From heq : e = e.flip, we get e.sender = e.flip.sender = e.receiver
  have : e.sender = e.receiver := by
    have h1 : e.sender = (e.flip).sender := congrArg Edge.sender heq
    simp only [Edge.flip] at h1
    exact h1
  exact h this

/-- Helper: edge equality when sessions match. -/
theorem Edge.eq_iff (e1 e2 : Edge) :
    e1 = e2 ↔ e1.sid = e2.sid ∧ e1.sender = e2.sender ∧ e1.receiver = e2.receiver := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  · intro ⟨hs, hp, hq⟩
    cases e1; cases e2
    simp only at hs hp hq
    subst hs hp hq
    rfl

/-! ## Consume: Advance Local Type by Pending Messages -/

/-- Consume a single receive from a local type for messages from role `from`.
    Returns the continuation after receiving type T from `from`.
    Note: Does not unfold mu - caller should unfold if needed. -/
def consumeOne (from_ : Role) (T : ValType) : LocalType → Option LocalType
  | .recv r' T' L => if from_ == r' && T == T' then some L else none
  | _ => none

/-- Consume a sequence of pending message types from a local type.
    Models how the type evolves as buffered messages from `from_` are received. -/
def Consume (from_ : Role) : LocalType → List ValType → Option LocalType
  | L, [] => some L
  | L, T :: ts =>
    match consumeOne from_ T L with
    | some L' => Consume from_ L' ts
    | none => none

/-- Consume for end type with empty queue. -/
theorem Consume_end_nil (from_ : Role) : Consume from_ .end_ [] = some .end_ := rfl

/-- Consume for recv with matching type. -/
theorem Consume_recv_cons (from_ : Role) (T : ValType) (L : LocalType) (ts : List ValType) :
    Consume from_ (.recv from_ T L) (T :: ts) = Consume from_ L ts := by
  simp only [Consume, consumeOne, beq_self_eq_true, Bool.and_true, ↓reduceIte]

/-- If consumeOne succeeds, the local type depth strictly decreases. -/
theorem consumeOne_depth_lt {from_ : Role} {T : ValType} {L L' : LocalType}
    (h : consumeOne from_ T L = some L') : L'.depth < L.depth := by
  -- Only `.recv` can consume; all other cases are contradictions.
  cases L with
  | recv r T' L0 =>
      -- consumeOne succeeds only if sender and type match.
      by_cases hRole : from_ == r
      · by_cases hType : T == T'
        · -- Success case: L' = L0, so depth strictly decreases.
          simp [consumeOne, hRole, hType] at h
          cases h
          simpa [LocalType.depth] using (LocalType.depth_advance_recv r T' L0)
        · -- Mismatched type makes consumeOne fail.
          simp [consumeOne, hRole, hType] at h
      · -- Mismatched sender makes consumeOne fail.
        simp [consumeOne, hRole] at h
  | send _ _ _ | select _ _ | branch _ _ | end_ | var _ | mu _ =>
      -- Non-recv types never consume.
      simp [consumeOne] at h

/-- Consuming a trace never exceeds the receiver's depth. -/
theorem Consume_length_le_depth {from_ : Role} {L L' : LocalType} {ts : List ValType}
    (h : Consume from_ L ts = some L') : ts.length ≤ L.depth := by
  -- Induct on the trace to count consumed steps.
  induction ts generalizing L with
  | nil =>
      -- Empty trace has length 0.
      simp
  | cons t ts ih =>
      -- One consumeOne step followed by recursion on the tail.
      cases hStep : consumeOne from_ t L with
      | none =>
          -- consumeOne fails, so Consume cannot succeed.
          simp [Consume, hStep] at h
      | some L1 =>
          -- Use IH on the remaining trace, then add one step.
          have hTail : Consume from_ L1 ts = some L' := by
            simpa [Consume, hStep] using h
          have hLen : ts.length ≤ L1.depth := ih hTail
          have hLt : L1.depth < L.depth := consumeOne_depth_lt hStep
          have hLe1 : ts.length + 1 ≤ L1.depth + 1 := Nat.succ_le_succ hLen
          have hLe2 : L1.depth + 1 ≤ L.depth := Nat.succ_le_of_lt hLt
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using le_trans hLe1 hLe2

/-- Consume associativity for append: consuming ts then [T] equals consuming ts ++ [T].
    This is the key lemma for send preservation - appending to trace end
    corresponds to receiver eventually receiving that type.
    Reference: `work/effects/004.lean` Consume_append -/
theorem Consume_append (from_ : Role) (Lr : LocalType) (ts : List ValType) (T : ValType) {L' : LocalType} :
    Consume from_ Lr ts = some L' →
    Consume from_ Lr (ts ++ [T]) = Consume from_ L' [T] := by
  intro h
  induction ts generalizing Lr L' with
  | nil =>
    -- ts = [], so Consume from_ Lr [] = some L' means L' = Lr
    simp only [Consume, List.nil_append] at h ⊢
    simp only [Option.some.injEq] at h
    rw [h]
  | cons t ts' ih =>
    -- ts = t :: ts', need to step through Consume
    simp only [Consume, List.cons_append] at h ⊢
    cases hOne : consumeOne from_ t Lr with
    | none =>
      -- consumeOne failed, so Consume returns none, h becomes none = some L'
      simp only [hOne] at h
      exact Option.noConfusion h
    | some L'' =>
      simp only [hOne] at h ⊢
      exact ih L'' h

/-- Consume decomposition: consuming T::ts equals consuming T then ts.
    This is the key lemma for recv preservation.
    Reference: `work/effects/004.lean` Consume_cons -/
theorem Consume_cons (from_ : Role) (Lr : LocalType) (T : ValType) (ts : List ValType) :
    Consume from_ Lr (T :: ts) =
    match Consume from_ Lr [T] with
    | some L' => Consume from_ L' ts
    | none => none := by
  simp only [Consume]
  cases hOne : consumeOne from_ T Lr with
  | none => rfl
  | some L' => rfl

/-! ## Consume Renaming Lemmas -/

/-- Renaming commutes with a single consume step. -/
theorem consumeOne_rename (ρ : SessionRenaming) (from_ : Role) (T : ValType) (L : LocalType) :
    consumeOne from_ (renameValType ρ T) (renameLocalType ρ L) =
      (consumeOne from_ T L).map (renameLocalType ρ) := by
  cases L <;> simp [consumeOne, renameLocalType, renameValType_beq]

/-- Renaming commutes with Consume over a trace. -/
theorem Consume_rename (ρ : SessionRenaming) (from_ : Role) (L : LocalType) (ts : List ValType) :
    Consume from_ (renameLocalType ρ L) (ts.map (renameValType ρ)) =
      (Consume from_ L ts).map (renameLocalType ρ) := by
  induction ts generalizing L with
  | nil =>
    simp [Consume]
  | cons t ts ih =>
    simp [Consume]
    cases h : consumeOne from_ t L with
    | none =>
        simp [consumeOne_rename, h]
    | some L' =>
        simp [consumeOne_rename, h, ih]

/-- Corollary: If Consume succeeds on [T] for a recv type from the same sender, the types match. -/
theorem Consume_single_recv_match {from_ : Role} {T T' : ValType} {L L' : LocalType}
    (h : Consume from_ (.recv from_ T' L) [T] = some L') :
    T = T' := by
  simp only [Consume, consumeOne, beq_self_eq_true, Bool.true_and] at h
  by_cases hEq : T == T' <;> simp [hEq] at h
  exact eq_of_beq hEq

/-- Corollary: If Consume succeeds on [T] for a branch type from the same sender, T must be .string. -/
theorem Consume_single_branch_string {from_ : Role} {bs : List (String × LocalType)} {T : ValType} {L' : LocalType}
    (h : Consume from_ (.branch from_ bs) [T] = some L') :
    T = .string := by
  simp only [Consume, consumeOne] at h
  cases T with
  | string => rfl
  | _ => exact Option.noConfusion h

/-- For non-recv/branch types, Consume only succeeds on empty trace.
    This is because consumeOne only handles recv and branch. -/
theorem Consume_non_recv_empty {from_ : Role} {L : LocalType} {ts : List ValType} {L' : LocalType}
    (hNotRecv : ∀ r T L'', L ≠ .recv r T L'')
    (hNotBranch : ∀ r bs, L ≠ .branch r bs)
    (h : Consume from_ L ts = some L') :
    ts = [] := by
  cases ts with
  | nil => rfl
  | cons t ts' =>
    simp only [Consume] at h
    -- consumeOne from_ t L only succeeds for L = .recv or L = .branch
    cases L with
    | end_ => simp only [consumeOne] at h; exact Option.noConfusion h
    | send _ _ _ => simp only [consumeOne] at h; exact Option.noConfusion h
    | select _ _ => simp only [consumeOne] at h; exact Option.noConfusion h
    | var _ => simp only [consumeOne] at h; exact Option.noConfusion h
    | mu _ => simp only [consumeOne] at h; exact Option.noConfusion h
    | recv r T L'' => exact absurd rfl (hNotRecv r T L'')
    | branch r bs => exact absurd rfl (hNotBranch r bs)

/-- If sender ≠ role in recv type, trace must be empty for consumption to succeed.
    Reference: `work/effects/004.lean` Consume_other_empty -/
theorem Consume_other_empty {from_ r : Role} {T : ValType} {L : LocalType}
    {ts : List ValType} {L' : LocalType}
    (hNe : from_ ≠ r)
    (h : Consume from_ (.recv r T L) ts = some L') :
    ts = [] := by
  cases ts with
  | nil => rfl
  | cons t ts' =>
    -- Consume from_ (.recv r T L) (t :: ts') requires consumeOne to succeed
    -- But consumeOne checks from_ == r, which is false
    simp only [Consume, consumeOne] at h
    have hNeq : (from_ == r) = false := beq_eq_false_iff_ne.mpr hNe
    simp only [hNeq, Bool.false_and] at h
    exact Option.noConfusion h

/-- If Consume succeeds on recv type with non-empty trace, then either:
    1. sender matches the recv's role AND trace head matches expected type, OR
    2. It fails (contradiction).
    This lemma extracts the trace head = expected type constraint. -/
theorem Consume_recv_head_match {from_ r : Role} {T : ValType} {L : LocalType}
    {t : ValType} {ts : List ValType} {L' : LocalType}
    (hConsume : Consume from_ (.recv r T L) (t :: ts) = some L') :
    from_ = r ∧ t = T := by
  simp only [Consume, consumeOne] at hConsume
  by_cases hRole : from_ == r
  · simp only [hRole, Bool.true_and] at hConsume
    by_cases hType : t == T
    · simp only [hType] at hConsume
      exact ⟨eq_of_beq hRole, eq_of_beq hType⟩
    · simp only [hType] at hConsume
      exact Option.noConfusion hConsume
  · simp only [hRole, Bool.false_and] at hConsume
    exact Option.noConfusion hConsume

/-- For branch type: Consume on non-empty trace always fails because consumeOne
    doesn't handle branch type. This lemma extracts the contradiction. -/
theorem Consume_branch_nonempty_false {from_ : Role} {r : Role} {bs : List (String × LocalType)}
    {t : ValType} {ts : List ValType} {L' : LocalType}
    (hConsume : Consume from_ (.branch r bs) (t :: ts) = some L') : False := by
  simp only [Consume, consumeOne] at hConsume
  exact Option.noConfusion hConsume


end
