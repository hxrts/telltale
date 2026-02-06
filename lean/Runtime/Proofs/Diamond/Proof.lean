import Runtime.Proofs.Diamond.Lemmas
import Runtime.Proofs.Frame
import Runtime.VM.LoadChoreography

/-!
# Cross-Session Diamond: Main Proof

Proves that executing two coroutines on disjoint sessions in either order yields
VM states that are equivalent modulo trace ordering (`VMStateEqModTrace`).

## Proof Strategy (Frame-Based)

The proof uses the frame rule from `Runtime.Proofs.Frame`:

1. **Session-local operations** only affect their footprint (native + delegated sessions)
2. **Disjoint footprints** imply that operations commute:
   - `session_local_op_preserves_other`: operations preserve coherence for other sessions
   - `disjoint_ops_preserve_unrelated`: third sessions are unaffected by either operation

This replaces the previous instruction-group approach (Groups A/B/C with 21 cases)
with a uniform reasoning principle.

## Remaining Work

The VM-level connection requires:
1. Computing instruction footprints from `CoroutineState.ownedEndpoints`
2. Showing each instruction is session-local (affects only its footprint)
3. Applying the frame rule to get commutativity

See `Runtime.Proofs.SessionLocal` and `Runtime.Proofs.Frame` for the Protocol-level
infrastructure.
-/

set_option autoImplicit false

universe u

noncomputable section

/-! ## Definitions -/

/-- Heuristic session lookup for a coroutine. Returns the session id of the
    first owned endpoint, or 0 if the coroutine has no endpoints or is missing. -/
def sessionOf {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (cid : CoroutineId) : SessionId :=
  match st.coroutines[cid]? with
  | none => 0
  | some c =>
      match c.ownedEndpoints with
      | [] => 0
      | ep :: _ => ep.sid

/-- Cross-session diamond property: executing two coroutines on disjoint
    sessions in either order reaches equivalent VM states (modulo trace ordering).
    This is the VM-level analogue of `session_isolation`. -/
def cross_session_diamond {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (_hwf : WFVMState st)
    (c1 c2 : CoroutineId) (_hne : c1 ≠ c2)
    (_hdisj : SessionDisjoint st (sessionOf st c1) (sessionOf st c2)) : Prop :=
  let (st_c1, _) := execInstr st c1
  let (st_c1_c2, _) := execInstr st_c1 c2
  let (st_c2, _) := execInstr st c2
  let (st_c2_c1, _) := execInstr st_c2 c1
  VMStateEqModTrace st_c1_c2 st_c2_c1

/-! ## execInstr Characterization Lemmas -/

/-- When a coroutine is not found, `execInstr` returns the state unchanged. -/
theorem execInstr_not_found {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId)
    (h : st.coroutines[c]? = none) :
    (execInstr st c).1 = st := by
  unfold execInstr
  simp [h]

/-- When a coroutine is done, `execAtPC` returns the state unchanged. -/
theorem execAtPC_done {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (coro : CoroutineState γ ε)
    (hd : coro.status = .done) :
    (execAtPC st c coro).1 = st := by
  unfold execAtPC
  simp [hd]

/-- When a coroutine is faulted, `execAtPC` returns the state unchanged. -/
theorem execAtPC_faulted {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (c : CoroutineId) (coro : CoroutineState γ ε)
    (err : Fault γ) (hf : coro.status = .faulted err) :
    (execAtPC st c coro).1 = st := by
  unfold execAtPC
  simp [hf]

/-! ## Frame-Based Diamond Theorem

The main theorem uses the frame rule: instructions with disjoint footprints commute.

**Key insight**: Instead of analyzing 21 instructions individually, we:
1. Show each instruction only affects its footprint sessions
2. Apply `session_local_op_preserves_other` for disjoint sessions
3. Derive commutativity from disjoint footprints

The Protocol-level infrastructure is in:
- `Runtime.Proofs.SessionLocal`: `SessionCoherent`, `SessionLocalOp`, frame rule
- `Runtime.Proofs.Frame`: composition lemmas, abstract diamond
-/

/-- Main diamond theorem using frame-based reasoning.

The proof strategy:
1. For operations on disjoint sessions, neither affects the other's session state
2. `updateCoro_comm` handles coroutine array writes
3. Trace events permute (order doesn't matter for observational equivalence)

The frame rule (`session_local_op_preserves_other`) gives us the key property:
if c1 operates on session s1 and c2 operates on session s2 with s1 ≠ s2,
then each operation preserves the coherence needed by the other. -/
theorem cross_session_diamond_holds {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (hwf : WFVMState st)
    (c1 c2 : CoroutineId) (hne : c1 ≠ c2)
    (hdisj : SessionDisjoint st (sessionOf st c1) (sessionOf st c2)) :
    cross_session_diamond st hwf c1 c2 hne hdisj := by
  unfold cross_session_diamond
  simp only []
  -- The proof follows from:
  -- 1. execInstr_preserves_* lemmas (programs, config, monitor unchanged)
  -- 2. updateCoro_comm (distinct coroutine indices commute)
  -- 3. SessionDisjoint ensures buffer/session modifications don't overlap
  -- 4. Trace permutation (obsTrace is a multiset, order doesn't matter)
  --
  -- With the frame-based approach, this reduces to:
  -- - Show each instruction is session-local (affects only its footprint)
  -- - Apply frame rule for disjoint footprints
  --
  -- TODO: Connect VM instruction execution to Protocol-level SessionLocalOp
  -- via instrFootprint : Instr → CoroutineState → Set SessionId
  sorry

end
