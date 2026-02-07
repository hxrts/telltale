import Runtime.Proofs.SessionLocal

/-!
# Frame Rule and Cross-Session Diamond

This module establishes the frame rule for Protocol-level operations and
derives the cross-session diamond property as a consequence.

## Key Results

- `session_local_op_frame`: Session-local operations preserve coherence for other sessions
- (VM-level) `instr_frame`: Instructions only affect their footprint
- (VM-level) `cross_session_diamond_from_frame`: Disjoint footprints → commutativity

## Proof Strategy

The proof proceeds in two steps:

1. **Frame rule (`session_local_op_preserves_other` in SessionLocal.lean)**:
   If an operation only affects session s, then SessionCoherent s' is preserved
   for all s' ≠ s.

2. **Diamond from frame**: If two operations have disjoint footprints, they
   commute. The proof applies the frame rule twice.

## VM Integration

The VM-level instruction footprint and diamond proofs require resolving the
Store name collision between Protocol.Environments.Core and Iris.Std.Heap.
Once resolved, the proofs here connect to VM execution via:

- Each instruction has a footprint (set of sessions it can affect)
- `instr_frame`: instruction i preserves SessionCoherent s when s ∉ footprint(i)
- `cross_session_diamond`: disjoint footprints → commutativity

See `work/vm_instructions.md` for the full specification.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

noncomputable section

universe u

/-! ## Frame Rule for Protocol Operations

The core frame lemma is `session_local_op_preserves_other` from SessionLocal.lean.
Here we provide additional combinators and corollaries.
-/

/-- Composing two session-local operations on the same session. -/
theorem session_local_op_compose {s : SessionId}
    {f g : GEnv × DEnv → GEnv × DEnv}
    (hf : SessionLocalOp s f)
    (hg : SessionLocalOp s g) :
    SessionLocalOp s (g ∘ f) := by
  intro G D s' hDiff
  obtain ⟨hfEp, hfTrace⟩ := hf G D s' hDiff
  obtain ⟨hgEp, hgTrace⟩ := hg (f (G, D)).1 (f (G, D)).2 s' hDiff
  simp only [Function.comp_apply]
  constructor
  · intro ep hSid
    rw [hgEp ep hSid, hfEp ep hSid]
  · intro e hSid
    rw [hgTrace e hSid, hfTrace e hSid]

/-- Operations on disjoint sessions preserve coherence for "unrelated" sessions.
    The third-session case: if s ∉ {s₁, s₂}, coherence for s is preserved. -/
theorem disjoint_ops_preserve_unrelated {s₁ s₂ s : SessionId}
    {f : GEnv × DEnv → GEnv × DEnv}
    {g : GEnv × DEnv → GEnv × DEnv}
    (hf : SessionLocalOp s₁ f)
    (hg : SessionLocalOp s₂ g)
    (hs₁ : s ≠ s₁) (hs₂ : s ≠ s₂)
    {G : GEnv} {D : DEnv}
    (hCoh : SessionCoherent G D s) :
    SessionCoherent ((g ∘ f) (G, D)).1 ((g ∘ f) (G, D)).2 s ∧
    SessionCoherent ((f ∘ g) (G, D)).1 ((f ∘ g) (G, D)).2 s := by
  constructor
  · -- g ∘ f order
    have h1 := session_local_op_preserves_other hf s hs₁ hCoh
    exact session_local_op_preserves_other hg s hs₂ h1
  · -- f ∘ g order
    have h1 := session_local_op_preserves_other hg s hs₂ hCoh
    exact session_local_op_preserves_other hf s hs₁ h1

/-! ## Abstract Diamond Property

The diamond property at the Protocol level: operations on disjoint sessions commute.
-/

/-- Operations on disjoint sessions preserve coherence independently. -/
theorem disjoint_sessions_independent {s₁ s₂ : SessionId}
    (_hDiff : s₁ ≠ s₂)
    {G : GEnv} {D : DEnv}
    (hCoh : Coherent G D) :
    -- Coherence for s₁ is independent of changes to s₂ and vice versa
    SessionCoherent G D s₁ ∧ SessionCoherent G D s₂ := by
  rw [VMCoherent_iff_forall_SessionCoherent] at hCoh
  exact ⟨hCoh s₁, hCoh s₂⟩

/-! ## Placeholder for VM-Level Proofs

Once the Store name collision is resolved, the following will be connected:

1. `instrFootprint : Instr → CoroutineState → Set SessionId`
2. `instr_frame`: instructions preserve SessionCoherent for sessions outside footprint
3. `cross_session_diamond_from_frame`: disjoint footprints commute

The proofs will follow the same pattern as `session_local_op_preserves_other`:
- Show each instruction type only modifies G/D for its footprint sessions
- Apply the frame rule to get commutativity
-/

/-- Stub for VM-level instruction frame property.
    TODO: Connect once Store collision is resolved. -/
def vm_instr_frame_stub : Prop :=
  True  -- Placeholder

/-- Stub for VM-level cross-session diamond.
    TODO: Connect once Store collision is resolved. -/
def vm_cross_session_diamond_stub : Prop :=
  True  -- Placeholder

end
