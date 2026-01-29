import Effects.Coherence.Part1

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

/-! ## Edge-wise Coherence -/

/-- Coherence for a single directed edge.
    States that the sender's output on the edge matches what the receiver expects. -/
def EdgeCoherent (G : GEnv) (D : DEnv) (e : Edge) : Prop :=
  let senderEp := { sid := e.sid, role := e.sender : Endpoint }
  let receiverEp := { sid := e.sid, role := e.receiver : Endpoint }
  let trace := lookupD D e
  ∀ Lrecv,
    lookupG G receiverEp = some Lrecv →
    ∃ Lsender,
      lookupG G senderEp = some Lsender ∧
      -- After consuming what sender has sent (tracked in D[sender,receiver])
      -- from receiver's perspective, receiver can handle it
      (Consume e.sender Lrecv trace).isSome

/-- Full coherence: edge-coherent for all edges in all sessions. -/
def Coherent (G : GEnv) (D : DEnv) : Prop :=
  ∀ e, EdgeCoherent G D e

/-! ### Small Helpers -/

/-- Extract the consume condition from `EdgeCoherent` given a receiver lookup. -/
theorem EdgeCoherent_consume_of_receiver {G : GEnv} {D : DEnv} {e : Edge} {Lrecv : LocalType}
    (hCoh : EdgeCoherent G D e)
    (hGrecv : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv) :
    (Consume e.sender Lrecv (lookupD D e)).isSome := by
  rcases hCoh Lrecv hGrecv with ⟨_, _, hConsume⟩
  exact hConsume

/-- Extract the sender lookup guaranteed by `EdgeCoherent` given a receiver lookup. -/
theorem EdgeCoherent_sender_of_receiver {G : GEnv} {D : DEnv} {e : Edge} {Lrecv : LocalType}
    (hCoh : EdgeCoherent G D e)
    (hGrecv : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv) :
    ∃ Lsender, lookupG G { sid := e.sid, role := e.sender } = some Lsender := by
  rcases hCoh Lrecv hGrecv with ⟨Lsender, hGsender, _⟩
  exact ⟨Lsender, hGsender⟩


/-! ## Key Lemmas: EdgeCoherent Forces Empty Trace

These lemmas show that EdgeCoherent constrains trace structure:
1. For non-recv/branch receiver types (send, select, etc.), trace must be empty
2. For recv/branch with different sender, trace must be empty

These shortcuts resolve "different sender" sorries. -/

/-- If receiver type is send (or other non-recv/branch), trace must be empty.
    This is because Consume for .send only succeeds on empty trace. -/
theorem trace_empty_when_send_receiver
    {G : GEnv} {D : DEnv} {e : Edge}
    {r : Role} {T : ValType} {L : LocalType}
    (hCoh : EdgeCoherent G D e)
    (hSend : lookupG G ⟨e.sid, e.receiver⟩ = some (.send r T L)) :
    lookupD D e = [] := by
  simp only [EdgeCoherent] at hCoh
  obtain ⟨Ls, hLsender, hIsSome⟩ := hCoh (.send r T L) hSend
  have h : (Consume e.sender (.send r T L) (lookupD D e)).isSome := hIsSome
  cases hTrace : lookupD D e with
  | nil => rfl
  | cons t ts =>
    rw [hTrace] at h
    simp only [Consume, consumeOne, Option.isSome] at h
    exact Bool.noConfusion h

/-- Similar lemma for select receiver type. -/
theorem trace_empty_when_select_receiver
    {G : GEnv} {D : DEnv} {e : Edge}
    {r : Role} {bs : List (String × LocalType)}
    (hCoh : EdgeCoherent G D e)
    (hSelect : lookupG G ⟨e.sid, e.receiver⟩ = some (.select r bs)) :
    lookupD D e = [] := by
  simp only [EdgeCoherent] at hCoh
  obtain ⟨Ls, hLsender, hIsSome⟩ := hCoh (.select r bs) hSelect
  cases hTrace : lookupD D e with
  | nil => rfl
  | cons t ts =>
    rw [hTrace] at hIsSome
    simp only [Consume, consumeOne, Option.isSome] at hIsSome
    exact Bool.noConfusion hIsSome

/-! ## Key Lemma: Different Sender Forces Empty Trace

When the receiver's type expects messages from sender A, but we're examining
the edge from sender B (B ≠ A), EdgeCoherent forces the trace from B to be empty.
This is because Consume only succeeds on non-empty trace when sender matches.

This lemma is the key to solving "continuation recv/branch from different sender" cases. -/

/-- If receiver expects recv from r, but edge has different sender, trace must be empty.
    This is the creative shortcut that resolves the "different sender" sorries. -/
theorem trace_empty_when_recv_other_sender
    {G : GEnv} {D : DEnv} {e : Edge}
    {r : Role} {T : ValType} {L : LocalType}
    (hCoh : EdgeCoherent G D e)
    (hRecv : lookupG G ⟨e.sid, e.receiver⟩ = some (.recv r T L))
    (hNe : e.sender ≠ r) :
    lookupD D e = [] := by
  -- EdgeCoherent gives us a sender witness and that (Consume e.sender (.recv r T L) trace).isSome.
  simp only [EdgeCoherent] at hCoh
  obtain ⟨Ls, hLsender, hIsSome⟩ := hCoh (.recv r T L) hRecv
  -- hIsSome : (Consume e.sender (.recv r T L) (lookupD D e)).isSome
  -- From Consume_other_empty, if trace is non-empty, Consume returns none
  cases hTrace : lookupD D e with
  | nil => rfl
  | cons t ts =>
    -- Consume e.sender (.recv r T L) (t :: ts) returns none because e.sender ≠ r
    rw [hTrace] at hIsSome
    simp only [Consume, consumeOne] at hIsSome
    have hNeq : (e.sender == r) = false := beq_eq_false_iff_ne.mpr hNe
    simp only [hNeq, Bool.false_and, Option.isSome] at hIsSome
    exact Bool.noConfusion hIsSome

/-- Similar lemma for branch: if receiver expects branch from r, but edge has different sender, trace is empty. -/
theorem trace_empty_when_branch_other_sender
    {G : GEnv} {D : DEnv} {e : Edge}
    {r : Role} {bs : List (String × LocalType)}
    (hCoh : EdgeCoherent G D e)
    (hBranch : lookupG G ⟨e.sid, e.receiver⟩ = some (.branch r bs))
    (hNe : e.sender ≠ r) :
    lookupD D e = [] := by
  simp only [EdgeCoherent] at hCoh
  obtain ⟨Ls, hLsender, hIsSome⟩ := hCoh (.branch r bs) hBranch
  cases hTrace : lookupD D e with
  | nil => rfl
  | cons t ts =>
    rw [hTrace] at hIsSome
    simp only [Consume, consumeOne] at hIsSome
    have hNeq : (e.sender == r) = false := beq_eq_false_iff_ne.mpr hNe
    -- For branch, consumeOne checks if t is .string and r == from_
    cases t with
    | string =>
      have hFalse : False := by
        simpa [Consume, consumeOne, hNeq] using hIsSome
      exact hFalse.elim
    | _ =>
      -- If head is not string, consumeOne returns none anyway
      have hFalse : False := by
        simpa [Consume, consumeOne] using hIsSome
      exact hFalse.elim

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

/-- Role-completeness for GEnv: if a local type mentions a peer role,
    that peer endpoint exists in G for the same session. -/
def RoleComplete (G : GEnv) : Prop :=
  ∀ e L, lookupG G e = some L →
    match LocalType.targetRole? L with
    | some r => ∃ L', lookupG G ⟨e.sid, r⟩ = some L'
    | none => True

/-- Role-completeness specialized to recv types. -/
theorem RoleComplete_recv
    {G : GEnv} {e : Endpoint} {r : Role} {T : ValType} {L : LocalType}
    (hComplete : RoleComplete G)
    (hG : lookupG G e = some (.recv r T L)) :
    ∃ L', lookupG G ⟨e.sid, r⟩ = some L' := by
  -- For recv, targetRole? = some r, so RoleComplete gives the witness directly.
  simpa [RoleComplete, LocalType.targetRole?] using hComplete e (.recv r T L) hG

/-- Role-completeness specialized to branch types. -/
theorem RoleComplete_branch
    {G : GEnv} {e : Endpoint} {r : Role} {bs : List (Label × LocalType)}
    (hComplete : RoleComplete G)
    (hG : lookupG G e = some (.branch r bs)) :
    ∃ L', lookupG G ⟨e.sid, r⟩ = some L' := by
  -- For branch, targetRole? = some r, so RoleComplete gives the witness directly.
  simpa [RoleComplete, LocalType.targetRole?] using hComplete e (.branch r bs) hG

/-- ValidLabels ensures received branch labels are valid.

When the receiver is at a branch type and the buffer contains a string label,
that label must be one of the valid branch options.

Reference: `work/effects/008.lean:392-397` -/
def ValidLabels (G : GEnv) (_D : DEnv) (bufs : Buffers) : Prop :=
  ∀ (e : Edge) (source : Role) (bs : List (Label × LocalType)),
    lookupG G ⟨e.sid, e.receiver⟩ = some (.branch source bs) →
    match lookupBuf bufs e with
    | (.string l) :: _ => (bs.find? (fun b => b.1 == l)).isSome
    | _ => True

/-! ## Receiver Readiness (Progress Support)

SendReady encodes the additional invariant needed for progress/preservation with
asynchronous buffers: after consuming the current trace on the edge, the receiver
can accept the next message of type T from the sender. This is exactly the
`hRecvReady` hypothesis required by `TypedStep.send`.
-/

/-- Receiver readiness for a send: after consuming the current trace on the edge,
    the receiver can consume one more message of type T from the sender. -/
def SendReady (G : GEnv) (D : DEnv) : Prop :=
  ∀ e q T L,
    lookupG G e = some (.send q T L) →
    ∀ Lrecv, lookupG G { sid := e.sid, role := q } = some Lrecv →
      ∃ L', Consume e.role Lrecv (lookupD D { sid := e.sid, sender := e.role, receiver := q }) = some L' ∧
            (Consume e.role L' [T]).isSome

/-- Receiver readiness for a select: after consuming the current trace on the edge,
    the receiver can consume a label (encoded as .string) from the selector. -/
def SelectReady (G : GEnv) (D : DEnv) : Prop :=
  ∀ e q bs ℓ L,
    lookupG G e = some (.select q bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    ∀ Lrecv, lookupG G { sid := e.sid, role := q } = some Lrecv →
      ∃ L', Consume e.role Lrecv (lookupD D { sid := e.sid, sender := e.role, receiver := q }) = some L' ∧
            (Consume e.role L' [.string]).isSome

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

/-- HasTypeVal is deterministic: each value has exactly one type.
    This is essential for deriving trace types from buffer values. -/
theorem HasTypeVal_unique {G : GEnv} {v : Value} {T₁ T₂ : ValType}
    (h₁ : HasTypeVal G v T₁) (h₂ : HasTypeVal G v T₂) : T₁ = T₂ := by
  induction h₁ generalizing T₂ with
  | unit => cases h₂; rfl
  | bool => cases h₂; rfl
  | nat => cases h₂; rfl
  | string => cases h₂; rfl
  | prod _ _ ih₁ ih₂ =>
    cases h₂ with
    | prod h₂a h₂b => congr 1 <;> [exact ih₁ h₂a; exact ih₂ h₂b]
  | chan _ => cases h₂; rfl

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

namespace List

@[simp] theorem get_map {α β} (f : α → β) (l : List α) (i : Nat) (hi : i < l.length) :
    (l.map f).get ⟨i, by simpa [List.length_map] using hi⟩ = f (l.get ⟨i, hi⟩) := by
  induction l generalizing i with
  | nil =>
      cases hi
  | cons a tl ih =>
      cases i with
      | zero =>
          simp
      | succ i =>
          have hi' : i < tl.length := by
            simpa using hi
          simp

end List

/-- If buffer has head v with type T, then trace has head T.
    Key lemma for deriving trace head in recv case.
    Proof strategy: BufferTyped gives buf[i] : trace[i] for all i.
    At i=0, buf[0]=v has type trace[0]. Since hv says v:T, by
    HasTypeVal_unique, trace[0]=T, so trace.head? = some T. -/
theorem trace_head_from_buffer {G : GEnv} {D : DEnv} {bufs : Buffers} {e : Edge}
    {v : Value} {vs : List Value} {T : ValType}
    (hBuf : lookupBuf bufs e = v :: vs)
    (hv : HasTypeVal G v T)
    (hTyped : BufferTyped G D bufs e) :
    (lookupD D e).head? = some T := by
  -- Unpack the buffer typing proof.
  rcases hTyped with ⟨hLen, hTyping⟩
  -- Buffer is non-empty at index 0.
  have h0buf : 0 < (lookupBuf bufs e).length := by
    simp [hBuf]
  -- Trace is also non-empty by length equality.
  have h0trace : 0 < (lookupD D e).length := by
    simpa [hLen] using h0buf
  -- Typing of the head element.
  have hTyped0 := hTyping 0 h0buf
  have hTyped0' : HasTypeVal G v ((lookupD D e).get ⟨0, h0trace⟩) := by
    simpa [hBuf] using hTyped0
  -- Split on the trace to extract its head and finish by uniqueness.
  cases hTrace : lookupD D e with
  | nil =>
      -- Contradiction: trace must be non-empty.
      simp [hTrace] at h0trace
  | cons t ts =>
      have hTypeTrace0 : HasTypeVal G v t := by
        simpa [hTrace] using hTyped0'
      have hEq : T = t := HasTypeVal_unique hv hTypeTrace0
      -- head? is the first element of the trace.
      simp [hEq]


end
