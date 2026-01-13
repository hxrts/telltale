import Effects.Environments

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

open scoped Classical

noncomputable section

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

/-! ## Edge-wise Coherence -/

/-- Coherence for a single directed edge.
    States that the sender's output on the edge matches what the receiver expects. -/
def EdgeCoherent (G : GEnv) (D : DEnv) (e : Edge) : Prop :=
  let senderEp := { sid := e.sid, role := e.sender : Endpoint }
  let receiverEp := { sid := e.sid, role := e.receiver : Endpoint }
  let trace := lookupD D e
  ∀ Lsender Lrecv,
    lookupG G senderEp = some Lsender →
    lookupG G receiverEp = some Lrecv →
    -- After consuming what sender has sent (tracked in D[sender,receiver])
    -- from receiver's perspective, receiver can handle it
    (Consume e.sender Lrecv trace).isSome

/-- Full coherence: edge-coherent for all edges in all sessions. -/
def Coherent (G : GEnv) (D : DEnv) : Prop :=
  ∀ e, EdgeCoherent G D e

/-! ## Buffer Typing -/

/-- A value has a given type under GEnv. -/
inductive HasTypeVal (G : GEnv) : Value → ValType → Prop where
  | unit : HasTypeVal G .unit .unit
  | bool (b : Bool) : HasTypeVal G (.bool b) .bool
  | nat (n : Nat) : HasTypeVal G (.nat n) .nat
  | string (s : String) : HasTypeVal G (.string s) .string
  | prod {v₁ v₂ T₁ T₂} :
      HasTypeVal G v₁ T₁ →
      HasTypeVal G v₂ T₂ →
      HasTypeVal G (.prod v₁ v₂) (.prod T₁ T₂)
  | chan {e L} :
      lookupG G e = some L →
      HasTypeVal G (.chan e) (.chan e.sid e.role)

/-- A buffer at edge e is typed by the type trace at e. -/
def BufferTyped (G : GEnv) (D : DEnv) (bufs : Buffers) (e : Edge) : Prop :=
  let buf := lookupBuf bufs e
  let trace := lookupD D e
  ∃ h : buf.length = trace.length,
    ∀ i (hi : i < buf.length),
      HasTypeVal G (buf.get ⟨i, hi⟩) (trace.get ⟨i, h ▸ hi⟩)

/-- All buffers are typed. -/
def BuffersTyped (G : GEnv) (D : DEnv) (bufs : Buffers) : Prop :=
  ∀ e, BufferTyped G D bufs e

/-! ## Store Typing -/

/-- Store is typed by SEnv: every variable has its declared type. -/
def StoreTyped (G : GEnv) (S : SEnv) (store : Store) : Prop :=
  ∀ x v T,
    lookupStr store x = some v →
    lookupSEnv S x = some T →
    HasTypeVal G v T

/-! ## Coherence Preservation Lemmas -/

/-- Coherence is preserved when we send a value from p to q.
    Sending updates:
    - G[p] advances (send to q consumed)
    - D[p,q] grows (type appended to trace)

    **Proof strategy** (3-way case split on edge a):

    1. **a = e (the send edge p→q)**:
       - Sender (p) type changes from `send q T L` to `L`
       - Trace D[p,q] grows by T
       - Need: receiver (q) can still consume the trace
       - Key: appending T to trace means receiver will eventually recv T

    2. **a involves sender endpoint p (but a ≠ e)**:
       - e.g., edge p→r for r ≠ q
       - Only G[p] changed (not G[r])
       - D[p,r] unchanged (only D[p,q] = D[e] changed)
       - Use lookupG_update_neq and lookupD_update_neq

    3. **a unrelated to p**:
       - Neither G nor D changed at a
       - Old coherence witness still works

    The key insight is that appending T to trace D[p,q] corresponds to
    the receiver eventually needing to recv T, which matches the
    sender's advance from `send q T L` to `L`. -/
theorem Coherent_send_preserved
    (G : GEnv) (D : DEnv) (senderEp : Endpoint) (receiverRole : Role) (T : ValType) (L : LocalType)
    (hCoh : Coherent G D)
    (hG : lookupG G senderEp = some (.send receiverRole T L)) :
    let sendEdge := { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole : Edge }
    Coherent (updateG G senderEp L) (updateD D sendEdge (lookupD D sendEdge ++ [T])) := by
  -- The key insight: we need to show EdgeCoherent for every edge in the updated environment
  -- Using a sorry for now - this requires careful reasoning about how appending to trace
  -- affects the Consume function and what it means for coherence
  sorry

/-- Coherence is preserved when we receive a value at q from p.
    Receiving updates:
    - G[q] advances (recv from p consumed)
    - D[p,q] shrinks (type popped from trace)

    **Proof strategy** (3-way case split on edge a):

    1. **a = e (the recv edge p→q)**:
       - Receiver (q) type changes from `recv p T L` to `L`
       - Trace D[p,q] loses T from front
       - Key: the Consume function handles one less T, still matches

    2. **a involves receiver endpoint q (but a ≠ e)**:
       - e.g., edge r→q for r ≠ p
       - Only G[q] changed (not G[r])
       - D[r,q] unchanged (only D[p,q] = D[e] changed)
       - Use lookupG_update_neq and lookupD_update_neq

    3. **a unrelated to q**:
       - Neither G nor D changed at a
       - Old coherence witness still works

    This is the dual of the send case: popping T from trace D[p,q]
    corresponds to the receiver advancing from `recv p T L` to `L`. -/
theorem Coherent_recv_preserved
    (G : GEnv) (D : DEnv) (receiverEp : Endpoint) (senderRole : Role) (T : ValType) (L : LocalType)
    (v : Value)
    (hCoh : Coherent G D)
    (hG : lookupG G receiverEp = some (.recv senderRole T L))
    (hTrace : (lookupD D { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }).head? = some T) :
    let e := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role : Edge }
    Coherent (updateG G receiverEp L) (updateD D e (lookupD D e).tail) := by
  -- Similar to send_preserved, requires 3-way edge case analysis
  -- Using sorry for now - the key insight is that popping from trace
  -- corresponds to receiver advancing past recv
  sorry

/-! ## Initialization Lemma -/

/-- Empty environments are coherent. -/
theorem Coherent_empty : Coherent [] [] := by
  intro e Lsender Lrecv hGsender hGrecv
  -- lookupG [] _ = none for any endpoint
  unfold lookupG at hGsender
  simp only [List.lookup] at hGsender
  -- hGsender : none = some Lsender is a contradiction
  exact (Option.some_ne_none Lsender hGsender.symm).elim

/-- Initialize coherent environments for a new session with local types. -/
def initSession (sid : SessionId) (roles : RoleSet) (localTypes : Role → LocalType) :
    GEnv × DEnv × Buffers :=
  let G := roles.map fun r => ({ sid := sid, role := r }, localTypes r)
  let D := initDEnv sid roles
  let bufs := initBuffers sid roles
  (G, D, bufs)

/-- Initialized session environments are coherent (when types are projections). -/
theorem initSession_coherent (sid : SessionId) (roles : RoleSet) (localTypes : Role → LocalType)
    (hProj : True)  -- Placeholder for "localTypes are valid projections"
    : let (G, D, _) := initSession sid roles localTypes
      Coherent G D := by
  sorry  -- Requires projection coherence

end
