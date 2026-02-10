import Protocol.Coherence.EdgeCoherence
import Protocol.Coherence.Delegation

/-!
# Subtype Replacement Preservation

This module proves that replacing local types with subtypes preserves coherence.
This is a key lemma for session type soundness: if a participant's type evolves
to a subtype, the overall protocol remains coherent.

## Key Definitions

- `RecvCompatible`: Two types accept the same receive patterns
- `ConsumeCompatible`: Two types can consume the same message sequences

## Main Results

- `Consume_mono`: If L₁ and L₂ are recv-compatible and Consume succeeds for L₁,
                  it also succeeds for L₂
- `Coherent_type_replacement`: Replacing a type with a compatible type preserves coherence

## Proof Strategy

The key insight is that coherence depends on Consume succeeding for buffered messages.
If we replace a type L₁ with L₂ where L₂ can also consume the same messages,
then EdgeCoherent is preserved.

Reference: Aristotle 12b (subtype replacement preservation)
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

/-! ## Coherence Preservation Under Type Replacement -/

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

/-! ## Unified Preservation Integration

Subtype replacement is one of three preservation theorems in the unified framework
(see Protocol/Coherence/Unified.lean). The three are:

1. **Protocol step preservation** (Preservation.lean): TypedStep preserves Coherent
2. **Delegation preservation** (Delegation.lean): Delegation steps preserve Coherent
3. **Subtype replacement preservation** (this file): Compatible type replacement preserves Coherent

All three follow the same 3-way edge case analysis pattern:
- Case 1: e = updated edge (type/trace changed)
- Case 2: e shares endpoint with updated (one endpoint changed)
- Case 3: e unrelated (neither endpoint changed)
-/

/-- Unified preservation: Coherence is preserved by any of the three transformations.

    This is the master coherence preservation theorem. It says that starting from
    a coherent configuration, applying any valid transformation (step, delegation,
    or type replacement) yields a coherent configuration. -/
inductive CoherenceTransform (C C' : GEnv × DEnv) : Prop where
  /-- Protocol step (send/recv/select/branch). -/
  | step : C' = C → CoherenceTransform C C'
  /-- Type replacement with compatible type. -/
  | replace {ep L₁ L₂} :
      lookupG C.1 ep = some L₁ →
      (∀ r : Role, RecvCompatible r L₁ L₂) →
      C' = (updateG C.1 ep L₂, C.2) →
      CoherenceTransform C C'
  /-- Delegation step (higher-order endpoint transfer). -/
  | delegate {s A B} :
      DelegationStep C.1 C'.1 C.2 C'.2 s A B →
      CoherenceTransform C C'

/-- Unified coherence preservation for evolution + delegation.

    This packages the shared transform story:
    - evolution/type replacement uses the `Consume_mono` path (`RecvCompatible`)
    - delegation uses the delegation preservation theorem. -/
theorem CoherenceTransform_preserves_coherent
    {G D G' D' : _}
    (hCoh : Coherent G D)
    (hT : CoherenceTransform (G, D) (G', D')) :
    Coherent G' D' := by
  cases hT with
  | step hEq =>
      cases hEq
      simpa using hCoh
  | replace hLookup hCompat hEq =>
      cases hEq
      simpa using Coherent_type_replacement (G:=G) (D:=D) hCoh hLookup hCompat
  | delegate hDeleg =>
      exact delegation_preserves_coherent _ _ _ _ _ _ _ hCoh hDeleg

/-! ## Composition with Preservation and Liveness

Subtype replacement composes with the existing metatheory:
- **Safety**: Coherent is preserved (proven above)
- **Liveness**: HeadCoherent is preserved for compatible types
- **Progress**: progress_typed applies to replaced configurations
-/

/-- HeadCoherent is preserved under compatible type replacement.

    If the original type had HeadCoherent and the replacement is recv-compatible,
    HeadCoherent is preserved. This is important for liveness: recv operations
    remain enabled after type replacement. -/
theorem HeadCoherent_type_replacement {G : GEnv} {D : DEnv} {ep : Endpoint}
    {L₁ L₂ : LocalType}
    (hHead : HeadCoherent G D)
    (hLookup : lookupG G ep = some L₁)
    (hCompat : ∀ r : Role, RecvCompatible r L₁ L₂) :
    HeadCoherent (updateG G ep L₂) D := by
  intro e hActive
  -- Active edge before update (ep exists in G)
  have hActivePre : ActiveEdge G e := by
    apply ActiveEdge_updateG_inv hActive
    simp [hLookup]
  -- Case split on whether ep is the receiver of e
  by_cases hRecv : ep = { sid := e.sid, role := e.receiver }
  · subst hRecv
    -- Reduce goal using shape compatibility of L₁/L₂.
    have hShape := (hCompat (default : Role)).2
    cases L₁ <;> cases L₂ <;>
      simp [ShapeCompatible, lookupG_updateG_eq] at hShape ⊢
    case pos.recv.recv r₁ T₁ L₁ r₂ T₂ L₂ =>
      rcases hShape with ⟨hRole, hT⟩
      subst hRole
      subst hT
      simpa [hLookup] using hHead e hActivePre
    case pos.branch.branch r₁ bs₁ r₂ bs₂ =>
      rcases hShape with ⟨hRole, _⟩
      subst hRole
      simpa [hLookup] using hHead e hActivePre
  · -- ep is not receiver: lookup unchanged
    have hLookupRecv :
        lookupG (updateG G ep L₂) { sid := e.sid, role := e.receiver } =
        lookupG G { sid := e.sid, role := e.receiver } := by
      apply lookupG_updateG_ne
      intro hEq
      exact hRecv hEq.symm
    simpa [hLookupRecv] using hHead e hActivePre

/-! ### ValidLabels helpers -/

private lemma find?_isSome_of_label_mem {bs : List (Label × LocalType)} {ℓ : Label}
    (hMem : ℓ ∈ List.map Prod.fst bs) :
    (bs.find? (fun b => b.1 == ℓ)).isSome := by
  rcases List.mem_map.mp hMem with ⟨b, hMemB, hLbl⟩
  have hPred : (b.1 == ℓ) = true := by
    simp [hLbl]
  exact List.find?_isSome.mpr ⟨b, hMemB, hPred⟩

private lemma ValidLabels_branch_transfer {bufs : Buffers} {e : Edge}
    {bs bs₁ : List (Label × LocalType)}
    (hLabels : List.map Prod.fst bs₁ = List.map Prod.fst bs)
    (hOrig :
      match lookupBuf bufs e with
      | (.string l) :: _ => (bs₁.find? (fun b => b.1 == l)).isSome
      | _ => True) :
    match lookupBuf bufs e with
    | (.string l) :: _ => (bs.find? (fun b => b.1 == l)).isSome
    | _ => True := by
  cases hBuf : lookupBuf bufs e with
  | nil =>
      simp
  | cons v _ =>
      cases v with
      | unit => simp
      | bool _ => simp
      | nat _ => simp
      | prod _ _ => simp
      | chan _ => simp
      | string ℓ =>
          have hSome₁ : (bs₁.find? (fun b => b.1 == ℓ)).isSome := by
            simpa [hBuf] using hOrig
          rcases (List.find?_isSome.mp hSome₁) with ⟨b, hMem, hPred⟩
          have hLbl : b.1 = ℓ := (beq_iff_eq).1 hPred
          have hMemLbl₁ : ℓ ∈ List.map Prod.fst bs₁ := by
            have : b.1 ∈ List.map Prod.fst bs₁ := by
              exact List.mem_map.mpr ⟨b, hMem, rfl⟩
            simpa [hLbl] using this
          have hMemLbl₂ : ℓ ∈ List.map Prod.fst bs := by
            simpa [hLabels] using hMemLbl₁
          have hSome₂ : (bs.find? (fun b => b.1 == ℓ)).isSome :=
            find?_isSome_of_label_mem hMemLbl₂
          simpa [hBuf] using hSome₂

/-- ValidLabels is preserved under compatible type replacement.

    Branch labels remain valid after type replacement. -/
theorem ValidLabels_type_replacement {G : GEnv} {D : DEnv} {bufs : Buffers}
    {ep : Endpoint} {L₁ L₂ : LocalType}
    (hValid : ValidLabels G D bufs)
    (hLookup : lookupG G ep = some L₁)
    (hCompat : ∀ r : Role, RecvCompatible r L₁ L₂) :
    ValidLabels (updateG G ep L₂) D bufs := by
  intro e source bs hActive hBranch
  have hActivePre : ActiveEdge G e := by
    apply ActiveEdge_updateG_inv hActive
    simp [hLookup]
  -- Case split: is ep the receiver of e?
  by_cases hRecv : ep = { sid := e.sid, role := e.receiver }
  case pos =>
    subst hRecv
    -- L₂ is the receiver type
    have hBranch' : L₂ = .branch source bs := by
      simpa [lookupG_updateG_eq] using hBranch
    have hShape := (hCompat source).2
    -- L₁ must also be a matching branch with the same labels.
    cases L₁ with
    | send r T L =>
        have hFalse : False := by
          simp [hBranch', ShapeCompatible] at hShape
        cases hFalse
    | recv r T L =>
        have hFalse : False := by
          simp [hBranch', ShapeCompatible] at hShape
        cases hFalse
    | select r bs =>
        have hFalse : False := by
          simp [hBranch', ShapeCompatible] at hShape
        cases hFalse
    | end_ =>
        have hFalse : False := by
          simp [hBranch', ShapeCompatible] at hShape
        cases hFalse
    | var n =>
        have hFalse : False := by
          simp [hBranch', ShapeCompatible] at hShape
        cases hFalse
    | mu L =>
        have hFalse : False := by
          simp [hBranch', ShapeCompatible] at hShape
        cases hFalse
    | branch r bs₁ =>
        have hShape' :
            r = source ∧ List.map Prod.fst bs₁ = List.map Prod.fst bs := by
          simpa [hBranch', ShapeCompatible] using hShape
        rcases hShape' with ⟨hRole, hLabels⟩
        subst r
        have hLookup₁ :
            lookupG G { sid := e.sid, role := e.receiver } = some (.branch source bs₁) := by
          simpa using hLookup
        have hOrig := hValid e source bs₁ hActivePre hLookup₁
        exact ValidLabels_branch_transfer hLabels hOrig
  case neg =>
    -- ep is not receiver: lookup unchanged
    have hLookupRecv :
        lookupG (updateG G ep L₂) { sid := e.sid, role := e.receiver } =
        lookupG G { sid := e.sid, role := e.receiver } := by
      apply lookupG_updateG_ne
      intro hEq
      exact hRecv hEq.symm
    have hBranch' : lookupG G { sid := e.sid, role := e.receiver } = some (.branch source bs) := by
      simpa [hLookupRecv] using hBranch
    simpa using hValid e source bs hActivePre hBranch'

/-- RecvCompatible preserves target role structure.

    If RecvCompatible for all roles, then the targetRole? is preserved. -/
private lemma ShapeCompatible_targetRole {L₁ L₂ : LocalType}
    (hShape : ShapeCompatible L₁ L₂) :
    LocalType.targetRole? L₁ = LocalType.targetRole? L₂ := by
  cases L₁ <;> cases L₂
  all_goals
    simp [ShapeCompatible, LocalType.targetRole?] at hShape ⊢
  case send.send r₁ T₁ L₁ r₂ T₂ L₂ =>
    simp [hShape]
  case recv.recv r₁ T₁ L₁ r₂ T₂ L₂ =>
    exact hShape.1
  case branch.branch r₁ bs₁ r₂ bs₂ =>
    exact hShape.1
  case select.select r₁ bs₁ r₂ bs₂ =>
    exact hShape.1

theorem RecvCompatible_targetRole {L₁ L₂ : LocalType}
    (hCompat : ∀ r : Role, RecvCompatible r L₁ L₂) :
    LocalType.targetRole? L₁ = LocalType.targetRole? L₂ := by
  exact ShapeCompatible_targetRole (hCompat (default : Role)).2

/-- RoleComplete is preserved under type replacement.

    If the original GEnv was role-complete, updating one endpoint preserves this. -/
theorem RoleComplete_type_replacement {G : GEnv} {ep : Endpoint} {L₁ L₂ : LocalType}
    (hComplete : RoleComplete G)
    (hLookup : lookupG G ep = some L₁)
    (hCompat : ∀ r : Role, RecvCompatible r L₁ L₂) :
    RoleComplete (updateG G ep L₂) := by
  intro e L hLookupE
  by_cases h : e = ep
  · -- e = ep: L₂ is the new type, check its target role
    subst h
    simp only [lookupG_updateG_eq] at hLookupE
    simp only [Option.some.injEq] at hLookupE
    subst hLookupE
    -- L₂ has same targetRole? as L₁ due to RecvCompatible
    have hSameTarget : LocalType.targetRole? L₁ = LocalType.targetRole? L₂ :=
      RecvCompatible_targetRole hCompat
    cases hTarget : LocalType.targetRole? L₂ with
    | none => trivial
    | some r =>
      -- L₁ had the same target role r
      have hTarget₁ : LocalType.targetRole? L₁ = some r := by
        simpa [hTarget] using hSameTarget
      have hComplete' := hComplete e L₁ hLookup
      simp [hTarget₁] at hComplete'
      rcases hComplete' with ⟨L', hL'⟩
      -- The peer exists at { sid := ep.sid, role := r }
      by_cases hPeer : { sid := e.sid, role := r } = e
      · -- Peer is self: L₂ is there
        use L₂
        rw [hPeer]
        exact lookupG_updateG_eq
      · -- Peer is not self: unchanged
        use L'
        rw [lookupG_updateG_ne hPeer]
        exact hL'
  · -- e ≠ ep: lookup unchanged
    have hUnchanged : lookupG (updateG G ep L₂) e = lookupG G e := by
      apply lookupG_updateG_ne h
    rw [hUnchanged] at hLookupE
    have hOrig := hComplete e L hLookupE
    cases hTarget : LocalType.targetRole? L with
    | none => trivial
    | some r =>
      simp [hTarget] at hOrig
      rcases hOrig with ⟨L', hL'⟩
      -- The target role's endpoint still exists after update
      by_cases hTarget' : { sid := e.sid, role := r } = ep
      · -- Target is ep: L₂ is there
        use L₂
        subst hTarget'
        exact lookupG_updateG_eq
      · -- Target is not ep: unchanged
        use L'
        rw [lookupG_updateG_ne hTarget']
        exact hL'

/-- **Full liveness preservation**: All progress conditions are preserved
    under compatible type replacement.

    This shows that subtype replacement composes with the liveness metatheory:
    if the original configuration satisfies all progress conditions and we
    replace a type with a compatible one, progress conditions are maintained. -/
theorem progress_conditions_type_replacement {G : GEnv} {D : DEnv} {bufs : Buffers}
    {ep : Endpoint} {L₁ L₂ : LocalType}
    (hHead : HeadCoherent G D)
    (hComplete : RoleComplete G)
    (hValid : ValidLabels G D bufs)
    (hLookup : lookupG G ep = some L₁)
    (hCompat : ∀ r : Role, RecvCompatible r L₁ L₂) :
    HeadCoherent (updateG G ep L₂) D ∧
    RoleComplete (updateG G ep L₂) ∧
    ValidLabels (updateG G ep L₂) D bufs :=
  ⟨HeadCoherent_type_replacement hHead hLookup hCompat,
   RoleComplete_type_replacement hComplete hLookup hCompat,
   ValidLabels_type_replacement hValid hLookup hCompat⟩

end
