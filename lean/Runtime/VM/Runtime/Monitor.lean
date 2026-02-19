import Runtime.VM.Model.Core
import IrisExtractionInstance

/-
The Problem. The runtime needs a unified monitor that tracks session
kinds uniformly, allowing typing and invariants to be checked at a
single interface.

Solution Structure. Define a lightweight monitor interface parametric
over session kinds. Failure semantics live in a separate module to avoid
cyclic dependencies on VM state.
-/

/-! # Task 23: Unified Monitor

Monitor consistency across session kinds
from iris_runtime_2.md §14.

## Definitions

## Unified Monitor
- `SessionKind` — protocol, guard, handler, ghost
- `WellTypedInstr` — unified typing judgment
- `SessionMonitor` — monitor state tracking all session kinds
- `monitor_sound`, `unified_monitor_preserves`
- `cross_kind_interop`

Failure model definitions live in `Runtime.VM.Runtime.Failure`.

Dependencies: Task 19, Shim.Invariants.
-/

set_option autoImplicit false

universe u

/-! ## Core Monitor Model -/

inductive SessionKind (γ : Type u) where
  -- The source kind of a monitored session action.
  | protocol (sid : SessionId)
  | guard (chainId : GuardChainId) (layer : γ)
  | handler (hsid : HandlerId)
  | ghost (gsid : GhostSessionId)

def SessionKind.sid? {γ : Type u} : SessionKind γ → Option SessionId :=
  -- Extract a protocol session id when present.
  fun
  | .protocol sid => some sid
  | _ => none

inductive WellTypedInstr {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] [EffectSpec ε] :
    Instr γ ε → SessionKind γ → LocalType → LocalType → Prop where
  | wt_send (sid : SessionId) (chan val : Reg) (r : Role)
      (T : ValType) (L' : LocalType) :
      -- Sending advances a send type to its continuation.
      WellTypedInstr (.send chan val) (.protocol sid) (.send r T L') L'
  | wt_receive (sid : SessionId) (chan dst : Reg) (r : Role)
      (T : ValType) (L' : LocalType) :
      -- Receiving advances a recv type to its continuation.
      WellTypedInstr (.receive chan dst) (.protocol sid) (.recv r T L') L'
  | wt_offer (sid : SessionId) (chan : Reg) (r : Role)
      (choices : List (Label × LocalType)) (lbl : Label) (L' : LocalType) :
      -- Offer advances along the selected branch.
      (lbl, L') ∈ choices →
      WellTypedInstr (.offer chan lbl) (.protocol sid) (.select r choices) L'
  | wt_choose (sid : SessionId) (chan : Reg) (r : Role)
      (choices : List (Label × LocalType)) (table : List (Label × PC)) :
      -- Choose is well-typed when table labels are covered by branches.
      (∀ lbl pc, (lbl, pc) ∈ table → ∃ L', (lbl, L') ∈ choices) →
      WellTypedInstr (.choose chan table) (.protocol sid) (.branch r choices) (.branch r choices)
  | wt_acquire (chainId : GuardChainId) (layer : γ) (dst : Reg) (L : LocalType) :
      -- Guard acquisition preserves the guard-session local type in V1.
      WellTypedInstr (.acquire layer dst) (.guard chainId layer) L L
  | wt_release (chainId : GuardChainId) (layer : γ) (ev : Reg) (L : LocalType) :
      -- Guard release preserves the guard-session local type in V1.
      WellTypedInstr (.release layer ev) (.guard chainId layer) L L
  | wt_invoke (action : EffectRuntime.EffectAction ε) (hsid : HandlerId) :
      -- Handler session typing for invoke steps.
      WellTypedInstr (.invoke action) (.handler hsid) (EffectSpec.handlerType action) .end_
  | wt_open (sid : SessionId) (roles : RoleSet) (types : List (Role × LocalType))
      (handlers : List (Edge × HandlerId)) (dsts : List (Role × Reg)) :
      -- Opening is well-typed at the boundary of a fresh session.
      WellTypedInstr (.open roles types handlers dsts) (.protocol sid) .end_ .end_
  | wt_close (sid : SessionId) (session : Reg) :
      -- Closing is well-typed at end.
      WellTypedInstr (.close session) (.protocol sid) .end_ .end_
  | wt_fork (gsid : GhostSessionId) (sidReg : Reg) (L : LocalType) :
      -- Fork preserves the ghost-session type in V1.
      WellTypedInstr (.fork sidReg) (.ghost gsid) L L
  | wt_join (gsid : GhostSessionId) (L : LocalType) :
      -- Join preserves the ghost-session type in V1.
      WellTypedInstr .join (.ghost gsid) L L
  | wt_abort (gsid : GhostSessionId) (L : LocalType) :
      -- Abort preserves the ghost-session type in V1.
      WellTypedInstr .abort (.ghost gsid) L L
  | wt_noop (i : Instr γ ε) (sk : SessionKind γ) (L : LocalType) :
      -- Non-session instructions preserve local types.
      WellTypedInstr i sk L L

/-! ## Monitor State and Recording -/

structure MonitorJudgment where
  -- Endpoint checked by the monitor.
  endpoint : Endpoint
  -- Instruction tag for this check.
  instrTag : String
  -- Tick at which the check occurred.
  tick : Nat
  deriving Repr, DecidableEq

structure SessionMonitor (γ : Type u) where
  -- Monitor transition per session kind.
  step : SessionKind γ → Option (SessionKind γ)
  -- Most recent successful monitor judgment.
  lastJudgment : Option MonitorJudgment := none
  -- Most recent monitor rejection message.
  lastRejection : Option String := none

def SessionMonitor.record {γ : Type u} (m : SessionMonitor γ)
    (endpoint : Endpoint) (instrTag : String) (tick : Nat) : SessionMonitor γ :=
  { m with
      lastJudgment := some { endpoint := endpoint, instrTag := instrTag, tick := tick }
      lastRejection := none }

def SessionMonitor.reject {γ : Type u} (m : SessionMonitor γ) (msg : String) :
    SessionMonitor γ :=
  { m with lastRejection := some msg }

/-! ## Monitor Modes and Session Interaction Filter -/

/-- Monitor precheck mode aligned with Rust VM config. -/
inductive MonitorMode where
  -- Disable monitor precheck.
  | off
  -- Run session-type precheck before instruction stepping.
  | sessionTypePrecheck
  deriving Repr, DecidableEq

/-- Check whether an instruction is pure control flow (no session interaction). -/
def instrNeedsSession {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (i : Instr γ ε) : Bool :=
  match i with
  | .set _ _ | .move _ _ | .jump _ | .spawn _ _ | .yield | .halt => false
  | _ => true

private def distinctLabels : List Label → Bool
  | [] => true
  | l :: ls => !ls.contains l && distinctLabels ls

/-! ## Monitor Admission Checks -/

def monitorAllows {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (_m : SessionMonitor γ) (_i : Instr γ ε) : Bool :=
  match _i with
  | .choose _ table =>
    -- Choose table must have distinct labels for unambiguous dispatch.
    distinctLabels (table.map Prod.fst)
  | .open roles _ _ dsts =>
    -- Role set and destination register list must align.
    roles.length == dsts.length
  | _ => true

/-! ## Monitor Meta-Properties -/

def monitor_sound {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (m : SessionMonitor γ) : Prop :=
  -- Pure control flow instructions are always accepted by the monitor.
  ∀ (i : Instr γ ε), instrNeedsSession i = false → monitorAllows m i = true

def unified_monitor_preserves {γ : Type u} (m : SessionMonitor γ) : Prop :=
  -- Monitor steps preserve protocol session ids when present.
  ∀ sk sk', m.step sk = some sk' → SessionKind.sid? sk' = SessionKind.sid? sk

def cross_kind_interop {γ : Type u} (m : SessionMonitor γ) : Prop :=
  -- Distinct session kinds step independently of protocol ids.
  ∀ sk1 sk2, sk1 ≠ sk2 →
    SessionKind.sid? sk1 = none ∨ SessionKind.sid? sk2 = none ∨ SessionKind.sid? sk1 ≠ SessionKind.sid? sk2 →
    (m.step sk1).isSome → (m.step sk2).isSome

/-! ## Canonical Contract Lemmas -/

/-- Any monitor satisfies `monitor_sound` because pure control-flow instructions
    are always accepted by `monitorAllows`. -/
theorem monitor_sound_any {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (m : SessionMonitor γ) :
    monitor_sound (γ:=γ) (ε:=ε) m := by
  intro i hNoSession
  cases i <;> simp [instrNeedsSession, monitorAllows] at hNoSession ⊢

/-- The identity-step monitor preserves protocol session ids. -/
theorem unified_monitor_preserves_identity {γ : Type u} :
    unified_monitor_preserves ({ step := fun sk : SessionKind γ => some sk } : SessionMonitor γ) := by
  intro sk sk' hStep
  simpa using congrArg SessionKind.sid? (Option.some.inj hStep).symm
