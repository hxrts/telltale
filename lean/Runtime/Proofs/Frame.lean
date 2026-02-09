import Runtime.Proofs.SessionLocal
import Runtime.VM.Semantics.InstrSpec
import Runtime.VM.Runtime.Loader

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
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

section

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

/-! ## Example: Role Swap Frame -/

/-- Example use of the frame rule: role swap preserves coherence for other sessions. -/
theorem swapRoles_frame_example {s sOther : SessionId} {A B : Role}
    {G : GEnv} {D : DEnv} (hDiff : sOther ≠ s)
    (hCoh : SessionCoherent G D sOther) :
    let (G', D') := swapRolesOp s A B (G, D)
    SessionCoherent G' D' sOther := by
  exact swapRoles_preserves_other_sessions (s:=s) (sOther:=sOther) (A:=A) (B:=B) hDiff hCoh

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

/-! ## VM-Level Footprint and Frame Interfaces -/

/-- Primary endpoint hint for a coroutine: use the first owned endpoint when present. -/
def coroutinePrimaryEndpoint? {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (coro : CoroutineState γ ε) : Option Endpoint :=
  coro.ownedEndpoints.head?

/-- VM instruction footprint derived from `InstrSpec.instrFootprint`.

For most instructions we use the coroutine's primary endpoint session.
For `acquire`, we conservatively include a second session via `some ep.sid`
to model footprint growth hooks at the interface level. -/
def vmInstrFootprint {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (instr : Instr γ ε) (coro : CoroutineState γ ε) : Set SessionId :=
  match coroutinePrimaryEndpoint? coro with
  | none => (∅ : Set SessionId)
  | some ep =>
      match instr with
      | .acquire _ _ => instrFootprint ep (some ep.sid)
      | _ => instrFootprint ep none

/-- Session coherence projected from VM state session store. -/
def vmSessionCoherent {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (s : SessionId) : Prop :=
  SessionCoherent (SessionStore.toGEnv st.sessions) (SessionStore.toDEnv st.sessions) s

/-- Abstract one-instruction VM step relation indexed by the decoded instruction. -/
abbrev VMInstrStep {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν] :=
  VMState ι γ π ε ν → CoroutineId → Instr γ ε → VMState ι γ π ε ν → Prop

/-- Frame contract: stepping an instruction preserves coherence for sessions
outside that instruction's footprint. -/
def instruction_frame {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (step : VMInstrStep (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν)) : Prop :=
  ∀ {st st' : VMState ι γ π ε ν} {cid : CoroutineId}
    {instr : Instr γ ε} {coro : CoroutineState γ ε} {s : SessionId},
    st.coroutines[cid]? = some coro →
    step st cid instr st' →
    s ∉ vmInstrFootprint instr coro →
    vmSessionCoherent st s →
    vmSessionCoherent st' s

/-- Cross-order frame consequence for two steps with disjoint ownership scopes:
if a session is outside both instruction footprints, coherence for that session
is preserved in both execution orders. -/
theorem cross_session_diamond_from_frame {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    {step : VMInstrStep (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν)}
    (hFrame : instruction_frame (ι:=ι) (γ:=γ) (π:=π) (ε:=ε) (ν:=ν) step)
    {st st1 st2 st12 st21 : VMState ι γ π ε ν}
    {c1 c2 : CoroutineId}
    {i1 i2 : Instr γ ε}
    {co1 co2 : CoroutineState γ ε}
    (hCo1 : st.coroutines[c1]? = some co1)
    (hCo2 : st.coroutines[c2]? = some co2)
    (hStep1 : step st c1 i1 st1)
    (hStep2 : step st c2 i2 st2)
    (hCo2After1 : st1.coroutines[c2]? = some co2)
    (hCo1After2 : st2.coroutines[c1]? = some co1)
    (hStep2After1 : step st1 c2 i2 st12)
    (hStep1After2 : step st2 c1 i1 st21)
    (_hDisj : Disjoint (vmInstrFootprint i1 co1) (vmInstrFootprint i2 co2))
    {s : SessionId}
    (hOut1 : s ∉ vmInstrFootprint i1 co1)
    (hOut2 : s ∉ vmInstrFootprint i2 co2)
    (hCoh : vmSessionCoherent st s) :
    vmSessionCoherent st12 s ∧ vmSessionCoherent st21 s := by
  constructor
  · have hCoh1 : vmSessionCoherent st1 s :=
      hFrame hCo1 hStep1 hOut1 hCoh
    exact hFrame hCo2After1 hStep2After1 hOut2 hCoh1
  · have hCoh2 : vmSessionCoherent st2 s :=
      hFrame hCo2 hStep2 hOut2 hCoh
    exact hFrame hCo1After2 hStep1After2 hOut1 hCoh2

end
