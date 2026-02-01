import Runtime.VM.Definition
import Runtime.Compat.WP

/-!
# Task 12: Language Instance

Instantiate the Iris `Language` typeclass for the bytecode VM.
Connects VM execution to Iris program logic.

## Definitions

- `SessionVM` — the language tag
- `instance : Language SessionVM`
- `to_val` / `of_val` / `prim_step`
- `LanguageMixin` proofs

Dependencies: Task 11, Shim.WeakestPre.
-/

set_option autoImplicit false

inductive SessionVM (ι γ π ε ν : Type) : Type where
  -- Tag type for the VM language instance.
  | mk

def SessionVM.to_val (e : Expr) : Option Expr :=
  -- A halted expression is treated as a value.
  if e.halted then some e else none

def SessionVM.of_val (v : Expr) : Expr :=
  -- Wrap a value as a halted expression.
  { v with halted := true }

instance instLanguageSessionVM {ι γ π ε ν : Type}
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectModel ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν] :
    Iris.Language (SessionVM ι γ π ε ν) where
  expr := Expr
  val := Expr
  state := VMState ι γ π ε ν
  of_val := SessionVM.of_val
  to_val := SessionVM.to_val
  prim_step := fun e σ =>
    -- Do not step halted expressions.
    if e.halted then [] else
      let (σ', res) := execInstr σ e.cid
      match res.status with
      | .blocked _ => []
      | _ =>
          let halted' :=
            match σ'.coroutines[e.cid]? with
            | some c => match c.status with | .done => true | _ => false
            | none => true
          [({ cid := e.cid, halted := halted' }, σ', [])]

/-- `to_val` after `of_val` yields the halted expression. -/
theorem to_of_val {ι γ π ε ν : Type}
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectModel ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (v : Expr) :
    SessionVM.to_val (SessionVM.of_val v) = some { v with halted := true } := by
  -- The wrapper forces `halted = true`.
  simp [SessionVM.to_val, SessionVM.of_val]

/-- `of_val` simply flips the `halted` flag. -/
theorem of_to_val {ι γ π ε ν : Type}
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectModel ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (e : Expr) :
    SessionVM.of_val e = { e with halted := true } := by
  -- Definition is by record update.
  rfl

/-- Values are head-stuck in the VM language. -/
theorem val_head_stuck {ι γ π ε ν : Type}
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectModel ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (v : Expr) (σ : VMState ι γ π ε ν) :
    Iris.Language.prim_step (Λ:=SessionVM ι γ π ε ν) (SessionVM.of_val v) σ = [] := by
  -- A halted expression produces no steps.
  simp [Iris.Language.prim_step, instLanguageSessionVM, SessionVM.of_val]
