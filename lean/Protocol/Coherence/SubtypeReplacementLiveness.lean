import Protocol.Coherence.SubtypeReplacementCore

/-! # Protocol.Coherence.SubtypeReplacementLiveness

Integration of subtype-replacement compatibility with unified/liveness invariants.
-/

/-
The Problem. Beyond coherence itself, subtype replacement should preserve the
combined progress-side invariants used by the unified preservation story.

Solution Structure.
1. Compose core replacement lemmas with unified transformation interfaces.
2. Prove preservation for HeadCoherent/ValidLabels/RoleComplete.
3. Bundle the full progress-condition preservation theorem.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section
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

/-! ## ValidLabels helpers -/

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

/-! ## ValidLabels Preservation Under Replacement -/

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
    /-! ## ValidLabels Replacement: Receiver-Updated Shape Analysis -/
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
  /-! ## ValidLabels Replacement: Receiver Unchanged Case -/
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

/-! ## Role Target Compatibility Helpers -/

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

/-! ## RoleComplete Preservation Under Replacement -/

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
  /-! ## RoleComplete Replacement: Non-Replaced Endpoint Case -/
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

/-! ## Progress Conditions Bundle -/

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
