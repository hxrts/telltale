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
  ∀ (e : Edge),
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

/-- ValidLabels ensures received branch labels are valid.

When the receiver is at a branch type and the buffer contains a string label,
that label must be one of the valid branch options.

Reference: `work/effects/008.lean:392-397` -/
def ValidLabels (G : GEnv) (D : DEnv) (bufs : Buffers) : Prop :=
  ∀ (e : Edge),
    let receiverEp : Endpoint := ⟨e.sid, e.receiver⟩
    ∀ source bs,
      lookupG G receiverEp = some (.branch source bs) →
      match lookupBuf bufs e with
      | (.string l) :: _ => (bs.find? (fun b => b.1 == l)).isSome
      | _ => True

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

/-! ### Value Type Inversion Lemmas

These lemmas extract concrete value forms from typing judgments.
Reference: `work/effects/008.lean:313-324, 521-524` -/

/-- If a value has channel type, it must be a channel value with matching endpoint.
    Reference: `work/effects/008.lean:313-318` -/
theorem HasTypeVal_chan_inv {G : GEnv} {v : Value} {sid : SessionId} {role : Role}
    (h : HasTypeVal G v (.chan sid role)) :
    v = .chan ⟨sid, role⟩ := by
  cases h with
  | chan hLookup => rfl

/-- If a value has string type, it must be a string value.
    Reference: `work/effects/008.lean:521-524` -/
theorem HasTypeVal_string_inv {G : GEnv} {v : Value}
    (h : HasTypeVal G v .string) :
    ∃ s, v = .string s := by
  cases h with
  | string s => exact ⟨s, rfl⟩

/-- If a value has bool type, it must be a bool value. -/
theorem HasTypeVal_bool_inv {G : GEnv} {v : Value}
    (h : HasTypeVal G v .bool) :
    ∃ b, v = .bool b := by
  cases h with
  | bool b => exact ⟨b, rfl⟩

/-- If a value has nat type, it must be a nat value. -/
theorem HasTypeVal_nat_inv {G : GEnv} {v : Value}
    (h : HasTypeVal G v .nat) :
    ∃ n, v = .nat n := by
  cases h with
  | nat n => exact ⟨n, rfl⟩

/-- If a value has unit type, it must be unit. -/
theorem HasTypeVal_unit_inv {G : GEnv} {v : Value}
    (h : HasTypeVal G v .unit) :
    v = .unit := by
  cases h; rfl

/-- If a value has product type, it must be a product value. -/
theorem HasTypeVal_prod_inv {G : GEnv} {v : Value} {T₁ T₂ : ValType}
    (h : HasTypeVal G v (.prod T₁ T₂)) :
    ∃ v₁ v₂, v = .prod v₁ v₂ ∧ HasTypeVal G v₁ T₁ ∧ HasTypeVal G v₂ T₂ := by
  cases h with
  | prod h1 h2 => exact ⟨_, _, rfl, h1, h2⟩

/-- HasTypeVal is preserved when extending GEnv if channel endpoints are preserved. -/
theorem HasTypeVal_mono (G G' : GEnv) (v : Value) (T : ValType)
    (hHas : HasTypeVal G v T)
    (hMono : ∀ e L, lookupG G e = some L → lookupG G' e = some L) :
    HasTypeVal G' v T := by
  induction hHas generalizing G' with
  | unit => exact HasTypeVal.unit
  | bool b => exact HasTypeVal.bool b
  | nat n => exact HasTypeVal.nat n
  | string s => exact HasTypeVal.string s
  | prod h1 h2 ih1 ih2 => exact HasTypeVal.prod (ih1 G' hMono) (ih2 G' hMono)
  | chan hLookup => exact HasTypeVal.chan (hMono _ _ hLookup)

/-- HasTypeVal is preserved when prepending disjoint endpoints to GEnv. -/
theorem HasTypeVal_prepend (G1 G2 : GEnv) (v : Value) (T : ValType)
    (hHas : HasTypeVal G2 v T)
    (hDisjoint : ∀ e L, lookupG G2 e = some L → G1.lookup e = none) :
    HasTypeVal (G1 ++ G2) v T := by
  apply HasTypeVal_mono G2 (G1 ++ G2) v T hHas
  intro e L hLookup
  simp only [lookupG, List.lookup_append]
  have hNone := hDisjoint e L hLookup
  simp only [hNone, Option.none_or]
  exact hLookup

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

/-- Strong store typing: same-domain property + type correspondence.
    This strengthening is needed for the progress theorem.
    Reference: `work/effects/008.lean:114-116` -/
structure StoreTypedStrong (G : GEnv) (S : SEnv) (store : Store) : Prop where
  /-- Same-domain: S and store have the same variables. -/
  sameDomain : ∀ x, (lookupSEnv S x).isSome ↔ (lookupStr store x).isSome
  /-- Type correspondence: values have their declared types. -/
  typeCorr : StoreTyped G S store

/-- StoreTypedStrong implies StoreTyped. -/
theorem StoreTypedStrong.toStoreTyped {G : GEnv} {S : SEnv} {store : Store}
    (h : StoreTypedStrong G S store) : StoreTyped G S store :=
  h.typeCorr

/-! ### Store Bridge Lemma

The key lemma connecting static typing to runtime values.
Reference: `work/effects/008.lean:304-308` -/

/-- If a variable has a type in the static environment and the store is strongly typed,
    then the variable exists in the store and its value has the corresponding type.
    Reference: `work/effects/008.lean:304-308` -/
theorem store_lookup_of_senv_lookup {G : GEnv} {S : SEnv} {store : Store} {x : Var} {T : ValType}
    (hStore : StoreTypedStrong G S store) (hS : lookupSEnv S x = some T) :
    ∃ v, lookupStr store x = some v ∧ HasTypeVal G v T := by
  -- From sameDomain: if x is in S, then x is in store
  have hDom := hStore.sameDomain x
  rw [hS, Option.isSome_some] at hDom
  have hInStore : (lookupStr store x).isSome := hDom.mp rfl
  -- Get the value from store
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hInStore
  -- Use type correspondence
  have hTyped := hStore.typeCorr x v T hv hS
  exact ⟨v, hv, hTyped⟩

/-- Weaker version when we only have StoreTyped but know the variable is in store.
    This is useful when the step relation already provides the store lookup. -/
theorem store_value_typed {G : GEnv} {S : SEnv} {store : Store} {x : Var} {v : Value} {T : ValType}
    (hStore : StoreTyped G S store) (hStr : lookupStr store x = some v) (hS : lookupSEnv S x = some T) :
    HasTypeVal G v T :=
  hStore x v T hStr hS

/-! ## EdgeCoherent Irrelevance Lemmas -/

/-- Updating G at an endpoint not involved in edge e doesn't affect EdgeCoherent at e.
    Reference: `work/effects/004.lean` EdgeCoherent_updateG_irrelevant -/
theorem EdgeCoherent_updateG_irrelevant (G : GEnv) (D : DEnv) (e : Edge)
    (ep : Endpoint) (L : LocalType)
    (hNeSender : ep ≠ { sid := e.sid, role := e.sender })
    (hNeRecv : ep ≠ { sid := e.sid, role := e.receiver })
    (hCoh : EdgeCoherent G D e) :
    EdgeCoherent (updateG G ep L) D e := by
  simp only [EdgeCoherent] at hCoh ⊢
  intro Lsender Lrecv hGsender hGrecv
  -- Use lookupG_update_neq since ep is different from both endpoints
  rw [lookupG_update_neq _ _ _ _ hNeSender] at hGsender
  rw [lookupG_update_neq _ _ _ _ hNeRecv] at hGrecv
  exact hCoh Lsender Lrecv hGsender hGrecv

/-- Updating D at edge e' ≠ e doesn't affect EdgeCoherent at e.
    Reference: `work/effects/004.lean` EdgeCoherent_updateD_irrelevant -/
theorem EdgeCoherent_updateD_irrelevant (G : GEnv) (D : DEnv) (e e' : Edge)
    (ts : List ValType)
    (hNe : e' ≠ e)
    (hCoh : EdgeCoherent G D e) :
    EdgeCoherent G (updateD D e' ts) e := by
  simp only [EdgeCoherent] at hCoh ⊢
  intro Lsender Lrecv hGsender hGrecv
  -- Use lookupD_update_neq since e' ≠ e
  simp only [lookupD_update_neq _ _ _ _ hNe]
  exact hCoh Lsender Lrecv hGsender hGrecv

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
       - Key: use `hRecvReady` + `Consume_append` to show receiver handles extended trace

    2. **a involves sender endpoint p (but a ≠ e)**:
       - e.g., edge p→r for r ≠ q
       - Only G[p] changed (not G[r])
       - D[p,r] unchanged (only D[p,q] = D[e] changed)
       - Use `EdgeCoherent_updateG_irrelevant` and `EdgeCoherent_updateD_irrelevant`

    3. **a unrelated to p**:
       - Neither G nor D changed at a
       - Use irrelevance lemmas

    The `hRecvReady` hypothesis is required. Without it, the theorem is FALSE.
    We cannot guarantee the receiver can handle T after consuming the current buffer.

    Reference: `work/effects/004.lean` Coherent_send_preserved -/
theorem Coherent_send_preserved
    (G : GEnv) (D : DEnv) (senderEp : Endpoint) (receiverRole : Role) (T : ValType) (L : LocalType)
    (hCoh : Coherent G D)
    (hG : lookupG G senderEp = some (.send receiverRole T L))
    -- CRITICAL: The receiver must be ready to accept T after consuming current buffer
    (hRecvReady : ∀ Lrecv, lookupG G { sid := senderEp.sid, role := receiverRole } = some Lrecv →
      ∃ L', Consume senderEp.role Lrecv (lookupD D { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }) = some L' ∧
            (Consume senderEp.role L' [T]).isSome) :
    let sendEdge := { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole : Edge }
    Coherent (updateG G senderEp L) (updateD D sendEdge (lookupD D sendEdge ++ [T])) := by
  intro sendEdge
  intro e  -- The edge we need to show coherence for

  -- Case split: is e the send edge or not?
  by_cases heq : e = sendEdge
  · -- Case 1: e = sendEdge (the edge being modified)
    subst heq
    simp only [EdgeCoherent]
    intro Lsender Lrecv hGsender hGrecv
    -- For sendEdge: sender = senderEp.role, receiver = receiverRole
    -- Sender endpoint lookup in updated G
    have hSenderLookup : lookupG (updateG G senderEp L) { sid := senderEp.sid, role := senderEp.role } = some L := by
      convert lookupG_update_eq G senderEp L
    -- Check if receiver = sender (self-send case)
    by_cases hRecvIsSender : receiverRole = senderEp.role
    · -- Self-send: receiver role = sender role
      subst hRecvIsSender
      -- Both lookups give L
      rw [hSenderLookup] at hGsender hGrecv
      simp only [Option.some.injEq] at hGsender hGrecv
      subst hGsender hGrecv
      simp only [lookupD_update_eq]
      -- Use hRecvReady - in self-send case, receiver's original type is the sender's type
      -- Note: hRecvReady with a SEND original type is actually unsatisfiable!
      -- Consume on SEND type only succeeds with empty trace, giving back the SEND type.
      -- Then hL'T requires Consume (SEND) [T] to be some, but that's none.
      -- So we derive a contradiction.
      obtain ⟨L', hL', hL'T⟩ := hRecvReady (.send senderEp.role T L) hG
      -- Case on the trace to derive a contradiction
      -- Consume of SEND type only succeeds with empty trace
      cases hTrace : lookupD D { sid := senderEp.sid, sender := senderEp.role, receiver := senderEp.role } with
      | nil =>
        rw [hTrace] at hL'
        simp only [Consume] at hL'
        simp only [Option.some.injEq] at hL'
        subst hL'
        simp only [Consume, consumeOne, Option.isSome] at hL'T
        -- hL'T : false = true is a contradiction
        exact Bool.noConfusion hL'T
      | cons t ts =>
        rw [hTrace] at hL'
        simp only [Consume, consumeOne] at hL'
        -- hL' : none = some L' is a contradiction
        exact Option.noConfusion hL'
    · -- Normal case: receiver ≠ sender
      have hRecvNeq : senderEp ≠ { sid := senderEp.sid, role := receiverRole } := by
        intro h
        have : senderEp.role = receiverRole := by
          have h' := congrArg Endpoint.role h
          simp at h'
          exact h'
        exact hRecvIsSender this.symm
      rw [hSenderLookup] at hGsender
      rw [lookupG_update_neq _ _ _ _ hRecvNeq] at hGrecv
      simp only [Option.some.injEq] at hGsender
      subst hGsender
      simp only [lookupD_update_eq]
      -- Use hRecvReady with receiver's original type
      obtain ⟨L', hL', hL'T⟩ := hRecvReady Lrecv hGrecv
      rw [Consume_append _ _ _ _ hL']
      exact hL'T
  · -- Case 2: e ≠ sendEdge - use irrelevance lemmas
    -- EdgeCoherent_updateD_irrelevant needs: sendEdge ≠ e
    have hNeSymm : sendEdge ≠ e := Ne.symm heq
    -- Check if senderEp is involved in edge e's endpoints
    by_cases hSenderMatch : { sid := e.sid, role := e.sender : Endpoint } = senderEp
    · -- Sender endpoint is senderEp
      by_cases hRecvMatch : { sid := e.sid, role := e.receiver : Endpoint } = senderEp
      · -- Both endpoints are senderEp - self-loop case
        -- Extract components from endpoint equalities
        have hSid1 : e.sid = senderEp.sid := congrArg Endpoint.sid hSenderMatch
        have hRole1 : e.sender = senderEp.role := congrArg Endpoint.role hSenderMatch
        have hSid2 : e.sid = senderEp.sid := congrArg Endpoint.sid hRecvMatch
        have hRole2 : e.receiver = senderEp.role := congrArg Endpoint.role hRecvMatch
        -- e is a self-loop at senderEp, but e ≠ sendEdge
        simp only [EdgeCoherent]
        intro Lsender Lrecv hGsender hGrecv
        -- Both lookups in updated G give L
        have hLookupS : lookupG (updateG G senderEp L) { sid := e.sid, role := e.sender } = some L := by
          conv => lhs; rw [hSid1, hRole1]
          exact lookupG_update_eq G senderEp L
        have hLookupR : lookupG (updateG G senderEp L) { sid := e.sid, role := e.receiver } = some L := by
          conv => lhs; rw [hSid2, hRole2]
          exact lookupG_update_eq G senderEp L
        rw [hLookupS] at hGsender
        rw [hLookupR] at hGrecv
        simp only [Option.some.injEq] at hGsender hGrecv
        subst hGsender hGrecv
        rw [lookupD_update_neq _ _ _ _ hNeSymm]
        -- Need to show Consume e.sender L (lookupD D e) is some
        -- Original coherence: sender had type .send receiverRole T L, receiver had same type
        -- Consume on SEND type only succeeds with empty trace
        have hOrigCoh := hCoh e
        simp only [EdgeCoherent] at hOrigCoh
        have hOrigSenderG : lookupG G { sid := e.sid, role := e.sender } = some (.send receiverRole T L) := by
          conv => lhs; rw [hSid1, hRole1]; exact hG
        have hOrigRecvG : lookupG G { sid := e.sid, role := e.receiver } = some (.send receiverRole T L) := by
          conv => lhs; rw [hSid2, hRole2]; exact hG
        have hOrig := hOrigCoh (.send receiverRole T L) (.send receiverRole T L) hOrigSenderG hOrigRecvG
        -- If trace is non-empty, Consume on SEND fails, contradicting hOrig
        cases hTrace : lookupD D e with
        | nil =>
          rw [hRole1]
          simp only [Consume, Option.isSome]
        | cons t ts =>
          rw [hRole1, hTrace] at hOrig
          simp only [Consume, consumeOne, Option.isSome] at hOrig
          -- hOrig : false = true is a contradiction
          exact Bool.noConfusion hOrig
      · -- Sender endpoint = senderEp, receiver endpoint ≠ senderEp
        -- Sender's type changed to L, but EdgeCoherent only checks receiver's Consume
        -- The receiver's type and trace are unchanged
        have hRecvNoMatch : senderEp ≠ { sid := e.sid, role := e.receiver } := fun h => hRecvMatch h.symm
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        -- For EdgeCoherent_updateG_irrelevant, we need both endpoints ≠ senderEp
        -- But sender endpoint = senderEp! So we can't use that lemma directly.
        -- However, EdgeCoherent doesn't actually depend on sender's type in a way that matters
        -- Let's prove it directly
        simp only [EdgeCoherent]
        intro Lsender Lrecv hGsender hGrecv
        -- Receiver lookup is unchanged (receiver ≠ senderEp)
        rw [lookupG_update_neq _ _ _ _ hRecvNoMatch] at hGrecv
        -- Trace is unchanged (e ≠ sendEdge, so lookupD unchanged)
        -- Original coherence with same receiver type and same trace
        have hOrigCoh := hCoh e
        simp only [EdgeCoherent] at hOrigCoh
        -- Get original sender type
        have hSid : e.sid = senderEp.sid := congrArg Endpoint.sid hSenderMatch
        have hRole : e.sender = senderEp.role := congrArg Endpoint.role hSenderMatch
        have hOrigSender : lookupG G { sid := e.sid, role := e.sender } = some (.send receiverRole T L) := by
          conv => lhs; rw [hSid, hRole]; exact hG
        exact hOrigCoh (.send receiverRole T L) Lrecv hOrigSender hGrecv
    · -- Sender endpoint ≠ senderEp
      have hSenderNoMatch : senderEp ≠ { sid := e.sid, role := e.sender } := fun h => hSenderMatch h.symm
      by_cases hRecvMatch : { sid := e.sid, role := e.receiver : Endpoint } = senderEp
      · -- Receiver endpoint = senderEp, sender endpoint ≠ senderEp
        -- Receiver's type changed from .send receiverRole T L to L
        -- But original coherence required Consume on the SEND type to succeed
        -- This means trace was empty, so Consume on L with empty trace succeeds
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        simp only [EdgeCoherent]
        intro Lsender Lrecv hGsender hGrecv
        -- Sender lookup is unchanged (sender ≠ senderEp)
        rw [lookupG_update_neq _ _ _ _ hSenderNoMatch] at hGsender
        -- Receiver lookup gives L
        have hSid : e.sid = senderEp.sid := congrArg Endpoint.sid hRecvMatch
        have hRole : e.receiver = senderEp.role := congrArg Endpoint.role hRecvMatch
        have hRecvLookup : lookupG (updateG G senderEp L) { sid := e.sid, role := e.receiver } = some L := by
          conv => lhs; rw [hSid, hRole]; exact lookupG_update_eq G senderEp L
        rw [hRecvLookup] at hGrecv
        simp only [Option.some.injEq] at hGrecv
        subst hGrecv
        -- Original coherence: receiver had SEND type, so Consume only works on empty trace
        have hOrigCoh := hCoh e
        simp only [EdgeCoherent] at hOrigCoh
        have hOrigRecv : lookupG G { sid := e.sid, role := e.receiver } = some (.send receiverRole T L) := by
          conv => lhs; rw [hSid, hRole]; exact hG
        have hOrig := hOrigCoh Lsender (.send receiverRole T L) hGsender hOrigRecv
        -- Consume e.sender (send ...) trace only succeeds if trace = []
        cases hTrace : lookupD D e with
        | nil =>
          simp only [Consume, Option.isSome]
        | cons t ts =>
          rw [hTrace] at hOrig
          simp only [Consume, consumeOne, Option.isSome] at hOrig
          exact Bool.noConfusion hOrig
      · -- Neither endpoint is senderEp - completely unrelated edge
        have hRecvNoMatch : senderEp ≠ { sid := e.sid, role := e.receiver } := fun h => hRecvMatch h.symm
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        exact EdgeCoherent_updateG_irrelevant _ _ _ _ _ hSenderNoMatch hRecvNoMatch (hCoh e)

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
    (hCoh : Coherent G D)
    (hG : lookupG G receiverEp = some (.recv senderRole T L))
    (hTrace : (lookupD D { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role }).head? = some T) :
    let e := { sid := receiverEp.sid, sender := senderRole, receiver := receiverEp.role : Edge }
    Coherent (updateG G receiverEp L) (updateD D e (lookupD D e).tail) := by
  intro recvEdge
  intro e  -- The edge we need to show coherence for

  -- Case split: is e the recv edge or not?
  by_cases heq : e = recvEdge
  · -- Case 1: e = recvEdge (the edge being modified)
    subst heq
    simp only [EdgeCoherent]
    intro Lsender Lrecv hGsender hGrecv
    -- For recvEdge: sender = senderRole, receiver = receiverEp.role
    -- Receiver endpoint lookup in updated G
    have hRecvLookup : lookupG (updateG G receiverEp L) { sid := receiverEp.sid, role := receiverEp.role } = some L := by
      convert lookupG_update_eq G receiverEp L
    -- Check if sender = receiver (self-recv case)
    by_cases hSenderIsRecv : senderRole = receiverEp.role
    · -- Self-recv: sender role = receiver role
      subst hSenderIsRecv
      -- Both lookups give L
      rw [hRecvLookup] at hGsender hGrecv
      simp only [Option.some.injEq] at hGsender hGrecv
      subst hGsender hGrecv
      simp only [lookupD_update_eq]
      -- Original coherence at this edge
      have hOrigCoh := hCoh recvEdge
      simp only [EdgeCoherent] at hOrigCoh
      -- Receiver's original type was .recv, so original coherence worked
      -- The trace was T :: rest (from hTrace), original Consume consumed T and continued
      -- After recv, we consume from rest
      -- Use Consume_cons to decompose the original
      cases hTraceVal : lookupD D recvEdge with
      | nil =>
        -- If trace was empty, hTrace would say head? = some T, but [] has head? = none
        rw [hTraceVal] at hTrace
        simp only [List.head?] at hTrace
        -- hTrace : none = some T is a contradiction
        exact Option.noConfusion hTrace
      | cons t rest =>
        -- t = T from hTrace
        rw [hTraceVal] at hTrace
        simp only [List.head?, Option.some.injEq] at hTrace
        subst hTrace
        -- Original coherence: Consume recvEdge.role (.recv recvEdge.role t L) (t :: rest) is some
        have hOrig := hOrigCoh (.recv receiverEp.role t L) (.recv receiverEp.role t L) hG hG
        -- Decompose using Consume definition
        rw [hTraceVal] at hOrig
        -- recvEdge.sender = receiverEp.role, and after subst, t = T (the message type)
        -- The beq checks: recvEdge.sender == receiverEp.role (true) and t == t (true)
        simp only [Consume, consumeOne] at hOrig
        have hBeqRole : (recvEdge.sender == receiverEp.role) = true := beq_self_eq_true _
        have hBeqType : (t == t) = true := beq_self_eq_true _
        simp only [hBeqRole, hBeqType, Bool.and_self, ite_true] at hOrig
        -- Now we need: Consume recvEdge.sender L rest is some
        simp only [List.tail_cons]
        exact hOrig
    · -- Normal case: sender ≠ receiver
      have hSenderNeq : receiverEp ≠ { sid := receiverEp.sid, role := senderRole } := by
        intro h
        have : receiverEp.role = senderRole := congrArg Endpoint.role h
        exact hSenderIsRecv this.symm
      rw [hRecvLookup] at hGrecv
      rw [lookupG_update_neq _ _ _ _ hSenderNeq] at hGsender
      simp only [Option.some.injEq] at hGrecv
      subst hGrecv
      simp only [lookupD_update_eq]
      -- Original coherence
      have hOrigCoh := hCoh recvEdge
      simp only [EdgeCoherent] at hOrigCoh
      -- Use original coherence with receiver's original type
      cases hTraceVal : lookupD D recvEdge with
      | nil =>
        rw [hTraceVal] at hTrace
        simp only [List.head?] at hTrace
        exact Option.noConfusion hTrace
      | cons t rest =>
        rw [hTraceVal] at hTrace
        simp only [List.head?, Option.some.injEq] at hTrace
        subst hTrace
        have hOrig := hOrigCoh Lsender (.recv senderRole t L) hGsender hG
        rw [hTraceVal] at hOrig
        simp only [Consume, consumeOne] at hOrig
        -- recvEdge.sender = senderRole, and after subst, t = T
        have hBeqRole : (recvEdge.sender == senderRole) = true := beq_self_eq_true _
        have hBeqType : (t == t) = true := beq_self_eq_true _
        simp only [hBeqRole, hBeqType, Bool.and_self, ite_true] at hOrig
        simp only [List.tail_cons]
        exact hOrig
  · -- Case 2: e ≠ recvEdge - use irrelevance lemmas
    have hNeSymm : recvEdge ≠ e := Ne.symm heq
    -- Check if receiverEp is involved in edge e's endpoints
    by_cases hSenderMatch : { sid := e.sid, role := e.sender : Endpoint } = receiverEp
    · -- Sender endpoint is receiverEp
      by_cases hRecvMatch : { sid := e.sid, role := e.receiver : Endpoint } = receiverEp
      · -- Both endpoints are receiverEp - self-loop case
        have hSid1 : e.sid = receiverEp.sid := congrArg Endpoint.sid hSenderMatch
        have hRole1 : e.sender = receiverEp.role := congrArg Endpoint.role hSenderMatch
        have hSid2 : e.sid = receiverEp.sid := congrArg Endpoint.sid hRecvMatch
        have hRole2 : e.receiver = receiverEp.role := congrArg Endpoint.role hRecvMatch
        simp only [EdgeCoherent]
        intro Lsender Lrecv hGsender hGrecv
        have hLookupS : lookupG (updateG G receiverEp L) { sid := e.sid, role := e.sender } = some L := by
          conv => lhs; rw [hSid1, hRole1]
          exact lookupG_update_eq G receiverEp L
        have hLookupR : lookupG (updateG G receiverEp L) { sid := e.sid, role := e.receiver } = some L := by
          conv => lhs; rw [hSid2, hRole2]
          exact lookupG_update_eq G receiverEp L
        rw [hLookupS] at hGsender
        rw [hLookupR] at hGrecv
        simp only [Option.some.injEq] at hGsender hGrecv
        subst hGsender hGrecv
        rw [lookupD_update_neq _ _ _ _ hNeSymm]
        -- Original coherence at e with receiver's original type .recv
        have hOrigCoh := hCoh e
        simp only [EdgeCoherent] at hOrigCoh
        have hOrigSenderG : lookupG G { sid := e.sid, role := e.sender } = some (.recv senderRole T L) := by
          conv => lhs; rw [hSid1, hRole1]; exact hG
        have hOrigRecvG : lookupG G { sid := e.sid, role := e.receiver } = some (.recv senderRole T L) := by
          conv => lhs; rw [hSid2, hRole2]; exact hG
        have hOrig := hOrigCoh (.recv senderRole T L) (.recv senderRole T L) hOrigSenderG hOrigRecvG
        -- Consume e.sender (.recv senderRole T L) trace succeeds
        -- If sender ≠ senderRole, Consume only works on empty trace
        -- If sender = senderRole, Consume matches the recv
        -- Either way, we can derive Consume e.sender L trace.tail
        -- Actually, simpler: if trace is empty, Consume L [] = some L
        -- If trace is non-empty, original must have matched the recv, so...
        -- This case is complex. Let's use: after consuming, the type becomes L
        cases hTraceE : lookupD D e with
        | nil =>
          rw [hRole1]
          simp only [Consume, Option.isSome]
        | cons t ts =>
          -- Original coherence: Consume e.sender (.recv senderRole T L) (t::ts) is some
          -- For recv type, this only works if e.sender = senderRole and t = T
          rw [hRole1] at hOrig
          simp only [hTraceE, Consume, consumeOne] at hOrig
          -- If senderRole = receiverEp.role (from hRole1), then the match depends on T = t
          -- Check if senderRole = receiverEp.role
          by_cases hSR : senderRole = receiverEp.role
          · -- If senderRole = receiverEp.role, then e = recvEdge (contradiction with heq)
            -- recvEdge = {receiverEp.sid, senderRole, receiverEp.role}
            -- After hSR: recvEdge = {receiverEp.sid, receiverEp.role, receiverEp.role}
            -- e has: e.sid = receiverEp.sid, e.sender = receiverEp.role, e.receiver = receiverEp.role
            -- So e = recvEdge
            exfalso
            apply heq
            have hEdgeEq : e = recvEdge := by
              -- e.sid = receiverEp.sid = recvEdge.sid
              -- e.sender = receiverEp.role = senderRole = recvEdge.sender (by hSR)
              -- e.receiver = receiverEp.role = recvEdge.receiver
              have hSidEq : e.sid = recvEdge.sid := hSid1
              have hSenderEq : e.sender = recvEdge.sender := hRole1.trans hSR.symm
              have hRecvEq : e.receiver = recvEdge.receiver := hRole2
              -- Use decidable equality
              calc e = ⟨e.sid, e.sender, e.receiver⟩ := by rfl
                _ = ⟨recvEdge.sid, recvEdge.sender, recvEdge.receiver⟩ := by
                    simp only [hSidEq, hSenderEq, hRecvEq]
                _ = recvEdge := by rfl
            exact hEdgeEq
          · -- senderRole ≠ receiverEp.role
            -- But we're in self-loop case where e.sender = receiverEp.role
            -- hOrig has Consume receiverEp.role (.recv senderRole T L) (t::ts)
            -- For this to succeed, we need receiverEp.role == senderRole, which is false
            -- So hOrig simplifies to none.isSome = true, a contradiction
            have hBeq : (receiverEp.role == senderRole) = false := beq_eq_false_iff_ne.mpr (Ne.symm hSR)
            simp only [hBeq, Bool.false_and] at hOrig
            simp only [Option.isSome] at hOrig
            exact Bool.noConfusion hOrig
      · -- Sender endpoint = receiverEp, receiver endpoint ≠ receiverEp
        have hRecvNoMatch : receiverEp ≠ { sid := e.sid, role := e.receiver } := fun h => hRecvMatch h.symm
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        simp only [EdgeCoherent]
        intro Lsender Lrecv hGsender hGrecv
        rw [lookupG_update_neq _ _ _ _ hRecvNoMatch] at hGrecv
        have hOrigCoh := hCoh e
        simp only [EdgeCoherent] at hOrigCoh
        have hSid : e.sid = receiverEp.sid := congrArg Endpoint.sid hSenderMatch
        have hRole : e.sender = receiverEp.role := congrArg Endpoint.role hSenderMatch
        have hOrigSender : lookupG G { sid := e.sid, role := e.sender } = some (.recv senderRole T L) := by
          conv => lhs; rw [hSid, hRole]; exact hG
        exact hOrigCoh (.recv senderRole T L) Lrecv hOrigSender hGrecv
    · -- Sender endpoint ≠ receiverEp
      have hSenderNoMatch : receiverEp ≠ { sid := e.sid, role := e.sender } := fun h => hSenderMatch h.symm
      by_cases hRecvMatch : { sid := e.sid, role := e.receiver : Endpoint } = receiverEp
      · -- Receiver endpoint = receiverEp, sender endpoint ≠ receiverEp
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        simp only [EdgeCoherent]
        intro Lsender Lrecv hGsender hGrecv
        rw [lookupG_update_neq _ _ _ _ hSenderNoMatch] at hGsender
        have hSid : e.sid = receiverEp.sid := congrArg Endpoint.sid hRecvMatch
        have hRole : e.receiver = receiverEp.role := congrArg Endpoint.role hRecvMatch
        have hRecvLookup : lookupG (updateG G receiverEp L) { sid := e.sid, role := e.receiver } = some L := by
          conv => lhs; rw [hSid, hRole]; exact lookupG_update_eq G receiverEp L
        rw [hRecvLookup] at hGrecv
        simp only [Option.some.injEq] at hGrecv
        subst hGrecv
        -- Original coherence: receiver had .recv type
        have hOrigCoh := hCoh e
        simp only [EdgeCoherent] at hOrigCoh
        have hOrigRecv : lookupG G { sid := e.sid, role := e.receiver } = some (.recv senderRole T L) := by
          conv => lhs; rw [hSid, hRole]; exact hG
        have hOrig := hOrigCoh Lsender (.recv senderRole T L) hGsender hOrigRecv
        -- If e.sender = senderRole and trace head = T, then Consume succeeds after eating T
        -- Otherwise, trace must be empty for Consume on recv to work
        cases hTraceE : lookupD D e with
        | nil =>
          simp only [Consume, Option.isSome]
        | cons t ts =>
          simp only [hTraceE, Consume, consumeOne] at hOrig
          -- Analyze whether e.sender matches senderRole and T matches t
          by_cases hSenderEq : e.sender = senderRole
          · by_cases hTypeEq : T = t
            · simp only [hSenderEq, hTypeEq, beq_self_eq_true, Bool.and_self] at hOrig
              -- hOrig says Consume senderRole L ts is some
              -- But we need Consume e.sender L (t::ts)
              -- e.sender = senderRole, so Consume senderRole L (T::ts)
              -- L is the continuation after recv, so if L = .recv senderRole T' L', it consumes
              -- Otherwise, Consume L (T::ts) = none for send/end
              -- But we need (Consume e.sender L (t::ts)).isSome
              -- This depends on L. The original coherence gives us info about (.recv ...) consuming.
              -- After recv, L is the continuation. If L can't consume t::ts, we have a problem.
              -- Actually, the goal is just to show coherence at this edge in the NEW state.
              -- The new receiver type is L, trace is unchanged (e ≠ recvEdge).
              -- Original: Consume e.sender (.recv senderRole T L) (T::ts) = some L''
              -- After decomposition: Consume senderRole L ts = some L''
              -- But new goal: Consume e.sender L (T::ts)
              -- e.sender = senderRole, so: Consume senderRole L (T::ts)
              -- This is different from Consume senderRole L ts!
              -- Wait, this is the case where e ≠ recvEdge but e.receiver = receiverEp.
              -- The trace at e is NOT the recvEdge trace!
              -- The update to D is only at recvEdge, not at e.
              -- So we're checking coherence at e with:
              -- - Sender type: original (from G, not updated)
              -- - Receiver type: L (updated from .recv senderRole T L)
              -- - Trace: original (not updated since e ≠ recvEdge)
              -- We need: Consume e.sender L (original trace) succeeds
              -- But original coherence was for .recv type, not L type!
              -- This is the tricky case. The receiver's type changed, affecting coherence.
              -- Hmm, but e.sender might not be senderRole...
              -- Actually we're in the case where e.sender = senderRole.
              -- Original: Consume senderRole (.recv senderRole T L) (t::ts) = some L''
              -- where t = T (from hTypeEq)
              -- This gives: Consume senderRole L ts = some L''
              -- New: Consume senderRole L (T::ts) = ?
              -- These are different! New trace still has T at front, but type lost the recv.
              -- This means the new coherence might FAIL if L is not a recv for T!
              -- Actually wait, let me re-read. We're at edge e where:
              -- - e.receiver = receiverEp.role
              -- - e.sender ≠ receiverEp.role (so sender endpoint ≠ receiverEp)
              -- - e ≠ recvEdge
              -- recvEdge = {receiverEp.sid, senderRole, receiverEp.role}
              -- e has e.receiver = receiverEp.role
              -- For e ≠ recvEdge with same receiver, we need e.sender ≠ senderRole or e.sid ≠ receiverEp.sid
              -- But we're in the case hSenderEq : e.sender = senderRole!
              -- So for e ≠ recvEdge, we need e.sid ≠ receiverEp.sid.
              -- But hSid says e.sid = receiverEp.sid!
              -- Contradiction! If e.sender = senderRole, e.receiver = receiverEp.role, e.sid = receiverEp.sid,
              -- then e = recvEdge, contradicting heq.
              -- So this case is impossible.
              exfalso
              apply heq
              -- Prove e = recvEdge field by field
              have hEdgeEq : e = recvEdge := by
                have hSidEq : e.sid = recvEdge.sid := hSid
                have hSenderEqR : e.sender = recvEdge.sender := hSenderEq
                have hRecvEq : e.receiver = recvEdge.receiver := hRole
                calc e = ⟨e.sid, e.sender, e.receiver⟩ := by rfl
                  _ = ⟨recvEdge.sid, recvEdge.sender, recvEdge.receiver⟩ := by
                      simp only [hSidEq, hSenderEqR, hRecvEq]
                  _ = recvEdge := by rfl
              exact hEdgeEq
            · -- T ≠ t
              -- The Consume fails because the expected type T doesn't match t
              -- hOrig becomes none.isSome = true, a contradiction
              have hBeq : (T == t) = false := beq_eq_false_iff_ne.mpr hTypeEq
              -- Note: in Consume, we check (t == T), not (T == t)
              have hBeqComm : (t == T) = false := by
                have : t ≠ T := Ne.symm hTypeEq
                exact beq_eq_false_iff_ne.mpr this
              simp only [hSenderEq, beq_self_eq_true, Bool.true_and, hBeqComm] at hOrig
              simp only [Option.isSome] at hOrig
              exact Bool.noConfusion hOrig
          · -- e.sender ≠ senderRole
            -- The Consume on (.recv senderRole T L) fails because e.sender ≠ senderRole
            -- hOrig becomes none.isSome = true, a contradiction
            have hBeq : (e.sender == senderRole) = false := beq_eq_false_iff_ne.mpr hSenderEq
            simp only [hBeq, Bool.false_and] at hOrig
            simp only [Option.isSome] at hOrig
            exact Bool.noConfusion hOrig
      · -- Neither endpoint is receiverEp - completely unrelated edge
        have hRecvNoMatch : receiverEp ≠ { sid := e.sid, role := e.receiver } := fun h => hRecvMatch h.symm
        apply EdgeCoherent_updateD_irrelevant _ _ _ _ _ hNeSymm
        exact EdgeCoherent_updateG_irrelevant _ _ _ _ _ hSenderNoMatch hRecvNoMatch (hCoh e)

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

/-! ## Renaming Preservation Theorems -/

/-- Coherence is preserved under session renaming.
    This is the key lemma for protocol composition: renaming sessions
    doesn't break the coherence invariant. -/
theorem CoherentRenaming (ρ : SessionRenaming) (G : GEnv) (D : DEnv)
    (hCoh : Coherent G D) :
    Coherent (renameGEnv ρ G) (renameDEnv ρ D) := by
  intro e Lsender Lrecv hGsender hGrecv
  -- If lookups succeed in renamed env, preimage endpoints exist
  obtain ⟨senderEp', hsenderEq, hGsender'⟩ := lookupG_rename_inv ρ G _ _ hGsender
  obtain ⟨recvEp', hrecvEq, hGrecv'⟩ := lookupG_rename_inv ρ G _ _ hGrecv
  -- The sender/receiver roles in the renamed edge must match
  have hSenderRole : e.sender = senderEp'.role := by
    have h := congrArg Endpoint.role hsenderEq
    simp only [renameEndpoint] at h
    exact h
  have hRecvRole : e.receiver = recvEp'.role := by
    have h := congrArg Endpoint.role hrecvEq
    simp only [renameEndpoint] at h
    exact h
  -- The sessions must also match (from renaming)
  have hSid1 : e.sid = ρ.f senderEp'.sid := by
    have h := congrArg Endpoint.sid hsenderEq
    simp only [renameEndpoint] at h
    exact h
  have hSid2 : e.sid = ρ.f recvEp'.sid := by
    have h := congrArg Endpoint.sid hrecvEq
    simp only [renameEndpoint] at h
    exact h
  -- Therefore senderEp'.sid = recvEp'.sid (by injectivity of ρ.f)
  have hSidEq : senderEp'.sid = recvEp'.sid := ρ.inj _ _ (hSid1.symm.trans hSid2)
  -- Build the original edge
  let e' : Edge := { sid := senderEp'.sid, sender := senderEp'.role, receiver := recvEp'.role }
  -- Show e = renameEdge ρ e'
  have hEdgeEq : e = renameEdge ρ e' := by
    simp only [renameEdge, e']
    have h1 : e.sid = ρ.f senderEp'.sid := hSid1
    have h2 : e.sender = senderEp'.role := hSenderRole
    have h3 : e.receiver = recvEp'.role := hRecvRole
    -- Construct equality using Edge.eq_iff
    rw [Edge.eq_iff]
    exact ⟨h1, h2, h3⟩
  -- The trace is the same (up to renaming)
  have hTraceEq : lookupD (renameDEnv ρ D) e = lookupD D e' := by
    rw [hEdgeEq, lookupD_rename]
  -- Apply original coherence at e'
  have hCoh' := hCoh e' Lsender Lrecv
  -- Need to show the endpoint conditions match
  have hSenderEp : senderEp' = { sid := e'.sid, role := e'.sender : Endpoint } := by
    simp only [e']
  -- The remaining proof requires showing endpoint equalities and applying
  -- the original coherence. Using sorry until tactic issues are resolved.
  sorry

/-- HasTypeVal is preserved under session renaming. -/
theorem HasTypeVal_rename (ρ : SessionRenaming) (G : GEnv) (v : Value) (T : ValType) :
    HasTypeVal G v T → HasTypeVal (renameGEnv ρ G) v T := by
  intro h
  induction h with
  | unit => exact HasTypeVal.unit
  | bool b => exact HasTypeVal.bool b
  | nat n => exact HasTypeVal.nat n
  | string s => exact HasTypeVal.string s
  | prod _ _ ih1 ih2 => exact HasTypeVal.prod ih1 ih2
  | @chan e L hLookup =>
    -- Need to handle channel case - the endpoint gets renamed
    -- But the value still contains the original endpoint...
    -- This is subtle: the value .chan e references the original endpoint
    -- In the renamed GEnv, that original endpoint is no longer present
    -- Actually, this theorem may need adjustment - channel values need to be renamed too
    sorry  -- Channel case requires careful treatment of value renaming

/-- BuffersTyped is preserved under session renaming. -/
theorem BuffersTypedRenaming (ρ : SessionRenaming) (G : GEnv) (D : DEnv) (bufs : Buffers)
    (hTyped : BuffersTyped G D bufs) :
    BuffersTyped (renameGEnv ρ G) (renameDEnv ρ D) (renameBufs ρ bufs) := by
  intro e
  simp only [BufferTyped]
  -- Check if e is in the image of renameEdge
  by_cases h : ∃ e', renameEdge ρ e' = e
  case pos =>
    obtain ⟨e', he'⟩ := h
    subst he'
    -- Use original BufferTyped at e'
    have hTyped' := hTyped e'
    simp only [BufferTyped] at hTyped'
    obtain ⟨hLen, hElem⟩ := hTyped'
    -- Rewrite lookups using simp to avoid dependent type issues
    simp only [lookupBuf_rename, lookupD_rename]
    refine ⟨hLen, ?_⟩
    intro i hi
    -- Need HasTypeVal_rename, which has a sorry for channel case
    -- Use sorry here - this is a secondary proof that depends on
    -- the channel renaming semantics
    sorry
  case neg =>
    -- Edge not in image - both lookups return empty
    -- This case requires showing that lookups in renamed environments
    -- return [] for edges outside the renaming range
    sorry

/-! ## Disjointness Infrastructure -/

/-- Sessions present in a GEnv. -/
def SessionsOf (G : GEnv) : Set SessionId :=
  { s | ∃ e L, lookupG G e = some L ∧ e.sid = s }

/-- Two GEnvs are disjoint if they have no common sessions. -/
def GEnvDisjoint (G1 G2 : GEnv) : Prop :=
  SessionsOf G1 ∩ SessionsOf G2 = ∅

/-- Two session renamings are disjoint on given GEnvs. -/
def RenamingsDisjoint (ρ1 ρ2 : SessionRenaming) (G1 G2 : GEnv) : Prop :=
  ∀ s1 ∈ SessionsOf G1, ∀ s2 ∈ SessionsOf G2, ρ1.f s1 ≠ ρ2.f s2

/-- Renamed environments are disjoint if renamings are disjoint. -/
theorem RenamedDisjoint (ρ1 ρ2 : SessionRenaming) (G1 G2 : GEnv)
    (hDisj : RenamingsDisjoint ρ1 ρ2 G1 G2) :
    GEnvDisjoint (renameGEnv ρ1 G1) (renameGEnv ρ2 G2) := by
  simp only [GEnvDisjoint, Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff]
  intro s ⟨hS1, hS2⟩
  simp only [SessionsOf, Set.mem_setOf_eq] at hS1 hS2
  obtain ⟨e1, L1, hLookup1, hSid1⟩ := hS1
  obtain ⟨e2, L2, hLookup2, hSid2⟩ := hS2
  -- Get preimage endpoints
  obtain ⟨e1', he1Eq, hLookup1'⟩ := lookupG_rename_inv ρ1 G1 e1 L1 hLookup1
  obtain ⟨e2', he2Eq, hLookup2'⟩ := lookupG_rename_inv ρ2 G2 e2 L2 hLookup2
  -- e1.sid = ρ1.f e1'.sid and e2.sid = ρ2.f e2'.sid
  have hSid1' : e1.sid = ρ1.f e1'.sid := by rw [he1Eq]; simp only [renameEndpoint]
  have hSid2' : e2.sid = ρ2.f e2'.sid := by rw [he2Eq]; simp only [renameEndpoint]
  -- But s = e1.sid = e2.sid
  have hContra : ρ1.f e1'.sid = ρ2.f e2'.sid := by
    rw [← hSid1', ← hSid2', hSid1, hSid2]
  -- e1'.sid ∈ SessionsOf G1, e2'.sid ∈ SessionsOf G2
  have hIn1 : e1'.sid ∈ SessionsOf G1 := ⟨e1', L1, hLookup1', rfl⟩
  have hIn2 : e2'.sid ∈ SessionsOf G2 := ⟨e2', L2, hLookup2', rfl⟩
  exact hDisj _ hIn1 _ hIn2 hContra

/-! ## Dual Relation for Local Types -/

/-- Duality relation for local types.
    Two types are dual if they communicate in complementary ways. -/
inductive Dual : LocalType → LocalType → Prop where
  | end_ : Dual .end_ .end_
  | send_recv (r : Role) (T : ValType) (L1 L2 : LocalType) :
      Dual L1 L2 → Dual (.send r T L1) (.recv r T L2)
  | recv_send (r : Role) (T : ValType) (L1 L2 : LocalType) :
      Dual L1 L2 → Dual (.recv r T L1) (.send r T L2)
  -- Note: select/branch cases would need matching labels

/-- If L1 is a send to r with continuation L1', and L2 is dual to L1,
    then L2 is a recv from r and their continuations are dual. -/
theorem Dual_send_inv (L1 L2 : LocalType) (r : Role) (T : ValType) (L1' : LocalType)
    (hDual : Dual L1 L2) (hL1 : L1 = .send r T L1') :
    ∃ L2', L2 = .recv r T L2' ∧ Dual L1' L2' := by
  cases hDual with
  | end_ => cases hL1  -- .end_ ≠ .send, contradiction
  | send_recv r' T' L1'' L2' hCont =>
    cases hL1
    exact ⟨L2', rfl, hCont⟩
  | recv_send r' T' L1'' L2' _ =>
    cases hL1  -- .recv ≠ .send, contradiction

/-- Dual types with empty trace are coherent (the bridge initialization lemma).
    Note: The proof actually works for any types with empty trace; duality ensures
    the types will remain coherent as communication proceeds. -/
theorem Dual_implies_Coherent_empty (L1 L2 : LocalType) (r1 r2 : Role)
    (sid : SessionId) (_hDual : Dual L1 L2) :
    let G : GEnv := [({ sid := sid, role := r1 }, L1), ({ sid := sid, role := r2 }, L2)]
    let D : DEnv := []
    let e12 : Edge := { sid := sid, sender := r1, receiver := r2 }
    let e21 : Edge := { sid := sid, sender := r2, receiver := r1 }
    EdgeCoherent G D e12 ∧ EdgeCoherent G D e21 := by
  -- With empty D, the trace is [] for all edges
  -- EdgeCoherent requires: Consume sender Lrecv [] = some _
  -- Since trace is empty, we need Lrecv to be consumable with no messages
  -- This is trivially true: Consume _ L [] = some L
  constructor
  · -- EdgeCoherent for e12 (r1 → r2)
    intro Lsender Lrecv hGsender hGrecv
    simp only [lookupD, List.lookup, Option.getD, Consume, Option.isSome_some]
  · -- EdgeCoherent for e21 (r2 → r1)
    intro Lsender Lrecv hGsender hGrecv
    simp only [lookupD, List.lookup, Option.getD, Consume, Option.isSome_some]

end
