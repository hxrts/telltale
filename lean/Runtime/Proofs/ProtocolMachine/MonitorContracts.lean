import Runtime.ProtocolMachine.Runtime.Monitor

set_option autoImplicit false

/-! # Runtime.Proofs.ProtocolMachine.MonitorContracts

Proof-facing monitor contract predicates. These live outside the protocol-machine
runtime tree so the runtime implementation remains proof-free.
-/

universe u

def monitor_sound {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (m : SessionMonitor γ) : Prop :=
  ∀ (i : Instr γ ε), instrNeedsSession i = false → monitorAllows m i = true

def unified_monitor_preserves {γ : Type u} (m : SessionMonitor γ) : Prop :=
  ∀ sk sk', m.step sk = some sk' → SessionKind.sid? sk' = SessionKind.sid? sk

def cross_kind_interop {γ : Type u} (m : SessionMonitor γ) : Prop :=
  ∀ sk1 sk2, sk1 ≠ sk2 →
    SessionKind.sid? sk1 = none ∨ SessionKind.sid? sk2 = none ∨ SessionKind.sid? sk1 ≠ SessionKind.sid? sk2 →
    (m.step sk1).isSome → (m.step sk2).isSome
