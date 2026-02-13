import Protocol.Coherence.EdgeCoherence
import Protocol.Coherence.Delegation

/-! # Protocol.Coherence.SubtypeReplacementCore

Core subtype-replacement compatibility lemmas and coherence preservation.
-/

/-
The Problem. Replacing one local type with a compatible type must preserve
coherence-related invariants that depend on `Consume`.

Solution Structure.
1. Define shape/receive compatibility.
2. Prove consume monotonicity under compatibility.
3. Lift compatibility to edge/global coherence preservation.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section
/-! ## Receive Compatibility

Two local types are recv-compatible if (1) they preserve the ability to consume
any buffered trace from `from_`, and (2) their **head shape** agrees (recv/branch
roles and labels). This avoids nested-inductive constraints while remaining
strong enough for Coherence/HeadCoherent/ValidLabels preservation. -/

/-- Head-shape compatibility (no recursion). -/
def ShapeCompatible : LocalType → LocalType → Prop
  | .recv r₁ T₁ _, .recv r₂ T₂ _ => r₁ = r₂ ∧ T₁ = T₂
  | .branch r₁ bs₁, .branch r₂ bs₂ => r₁ = r₂ ∧ List.map Prod.fst bs₁ = List.map Prod.fst bs₂
  | .select r₁ bs₁, .select r₂ bs₂ => r₁ = r₂ ∧ List.map Prod.fst bs₁ = List.map Prod.fst bs₂
  | .send r₁ _ _, .send r₂ _ _ => r₁ = r₂
  | .mu _, .mu _ => True
  | .var n₁, .var n₂ => n₁ = n₂
  | .end_, .end_ => True
  | _, _ => False

/-- Recv-compatible: consume preservation + head-shape compatibility. -/
def RecvCompatible (from_ : Role) (L₁ L₂ : LocalType) : Prop :=
  (∀ ts, (Consume from_ L₁ ts).isSome → (Consume from_ L₂ ts).isSome) ∧
  ShapeCompatible L₁ L₂

/-- RecvCompatible is reflexive. -/
theorem RecvCompatible.refl (from_ : Role) (L : LocalType) : RecvCompatible from_ L L := by
  constructor
  · intro ts h; exact h
  · cases L <;> simp [ShapeCompatible]

/-! ## Consume Monotonicity

If L₁ and L₂ are recv-compatible and Consume succeeds for L₁, it also succeeds
for L₂. This follows directly from the first component of `RecvCompatible`. -/

theorem Consume_mono {from_ : Role} {L₁ L₂ : LocalType} {ts : List ValType} {L₁' : LocalType}
    (hCompat : RecvCompatible from_ L₁ L₂)
    (hConsume : Consume from_ L₁ ts = some L₁') :
    ∃ L₂', Consume from_ L₂ ts = some L₂' := by
  have hSome : (Consume from_ L₁ ts).isSome := by
    simp [hConsume]
  have hSome2 := hCompat.1 ts hSome
  rcases (Option.isSome_iff_exists).1 hSome2 with ⟨L₂', hL₂'⟩
  exact ⟨L₂', hL₂'⟩

-- Coherence Preservation Under Type Replacement

-- Edge-Level Replacement Preservation

/-- EdgeCoherent is preserved when replacing the receiver's type with a compatible type.

    If the original receiver type L₁ satisfies EdgeCoherent (Consume succeeds),
    and we replace it with L₂ where RecvCompatible from_ L₁ L₂, then
    EdgeCoherent still holds for the updated configuration. -/
theorem EdgeCoherent_type_replacement {G : GEnv} {D : DEnv} {e : Edge}
    {L₁ L₂ : LocalType}
    (hEdgeCoh : EdgeCoherent G D e)
    (hRecv : lookupG G { sid := e.sid, role := e.receiver } = some L₁)
    (hCompat : RecvCompatible e.sender L₁ L₂) :
    EdgeCoherent (updateG G { sid := e.sid, role := e.receiver } L₂) D e := by
  intro Lrecv hLookupRecv
  -- After update, lookupG gives L₂
  simp only [lookupG_updateG_eq] at hLookupRecv
  simp only [Option.some.injEq] at hLookupRecv
  subst hLookupRecv
  -- Get original EdgeCoherent result
  obtain ⟨Lsender, hLookupSender, hConsumeOk⟩ := hEdgeCoh L₁ hRecv
  -- Case split on whether sender = receiver
  by_cases hEq : e.sender = e.receiver
  · -- Sender is same endpoint as receiver; update changes sender lookup
    -- New sender lookup is L₂ (rewrite sender = receiver)
    have hLookupSender' :
        lookupG (updateG G { sid := e.sid, role := e.receiver } L₂)
          { sid := e.sid, role := e.sender } = some L₂ := by
      rw [hEq]
      exact lookupG_updateG_eq
    use L₂
    constructor
    · exact hLookupSender'
    · -- L₂ can also consume the trace
      exact hCompat.1 _ hConsumeOk
  · -- Sender lookup is unchanged
    have hSenderUnchanged :
        lookupG (updateG G { sid := e.sid, role := e.receiver } L₂)
          { sid := e.sid, role := e.sender } =
        lookupG G { sid := e.sid, role := e.sender } := by
      apply lookupG_updateG_ne
      intro hEp
      apply hEq
      simpa [Endpoint.mk.injEq] using hEp
    rw [hSenderUnchanged]
    use Lsender, hLookupSender
    -- L₂ can also consume the trace
    exact hCompat.1 _ hConsumeOk

-- Global Coherence Replacement Preservation

/-- **Coherent_type_replacement**: Coherence is preserved under compatible type replacement.

    If G, D is coherent and we replace a receiver's type with a recv-compatible type,
    the result is still coherent. -/
theorem Coherent_type_replacement {G : GEnv} {D : DEnv} {ep : Endpoint}
    {L₁ L₂ : LocalType}
    (hCoh : Coherent G D)
    (hLookup : lookupG G ep = some L₁)
    (hCompat : ∀ r : Role, RecvCompatible r L₁ L₂) :
    Coherent (updateG G ep L₂) D := by
  intro e hActive
  -- Case split: is ep the receiver of e?
  by_cases hRecv : ep = { sid := e.sid, role := e.receiver }
  · -- ep is the receiver: use EdgeCoherent_type_replacement
    subst hRecv
    have hActivePre : ActiveEdge G e := by
      -- ActiveEdge after update implies ActiveEdge before (receiver was already there)
      apply ActiveEdge_updateG_inv hActive
      simp only [hLookup, Option.isSome_some]
    apply EdgeCoherent_type_replacement (hCoh e hActivePre) hLookup (hCompat e.sender)
  · -- ep is not the receiver: edge coherence depends on receiver's Consume
    have hLookupRecv : lookupG (updateG G ep L₂) { sid := e.sid, role := e.receiver } =
        lookupG G { sid := e.sid, role := e.receiver } := by
      apply lookupG_updateG_ne
      intro hEq
      exact hRecv hEq.symm
    intro Lrecv hLookupRecv'
    rw [hLookupRecv] at hLookupRecv'
    -- Coherent_type_replacement: Sender Match vs Unrelated Split
    -- Case split on whether ep is the sender
    by_cases hSend : ep = { sid := e.sid, role := e.sender }
    · -- ep is sender: sender changes but receiver and trace unchanged
      -- EdgeCoherent only needs: receiver can Consume the trace
      have hActivePre : ActiveEdge G e := by
        constructor
        · -- Sender existed before (ep was there)
          subst hSend
          simp only [hLookup, Option.isSome_some]
        · -- Receiver unchanged
          rcases hActive with ⟨_, hRecvActive⟩
          rw [← hLookupRecv]
          exact hRecvActive
      obtain ⟨Lsender, hSenderOrig, hConsume⟩ := hCoh e hActivePre Lrecv hLookupRecv'
      -- New sender is L₂
      use L₂
      constructor
      · subst hSend; exact lookupG_updateG_eq
      · exact hConsume
    -- Coherent_type_replacement: Unrelated Endpoint Case
    · -- ep is neither sender nor receiver: both unchanged
      have hLookupSendUnch : lookupG (updateG G ep L₂) { sid := e.sid, role := e.sender } =
          lookupG G { sid := e.sid, role := e.sender } := by
        apply lookupG_updateG_ne
        intro hEq
        exact hSend hEq.symm
      have hActivePre : ActiveEdge G e := by
        constructor
        · rcases hActive with ⟨hSendAct, _⟩
          rw [← hLookupSendUnch]
          exact hSendAct
        · rcases hActive with ⟨_, hRecvActive⟩
          rw [← hLookupRecv]
          exact hRecvActive
      obtain ⟨Lsender, hSender, hConsume⟩ := hCoh e hActivePre Lrecv hLookupRecv'
      use Lsender
      constructor
      · rw [hLookupSendUnch]; exact hSender
      · exact hConsume


end
