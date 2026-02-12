import Runtime.VM.API
import IrisExtractionInstance


/-! # Task 12: Language Instance

Instantiate the Iris `Language` typeclass for the bytecode VM.
Connects VM execution to Iris program logic.

## Definitions

- `SessionVM` — the language tag
- `instance : Language SessionVM`
- `to_val` / `of_val` / `prim_step`
- `LanguageMixin` proofs

Dependencies: Task 11, Shim.WeakestPre.
-/

/-
The Problem. Iris reasoning requires a concrete `Language` instance for the VM
so weakest-precondition rules can talk about VM expressions, values, and steps.

Solution Structure. Define value conversions (`to_val`/`of_val`), encode VM
small-step behavior as `prim_step`, then package the laws in the language mixin.
-/

set_option autoImplicit false

/-! ## Core Language Carrier -/

inductive SessionVM (ι γ π ε ν : Type) : Type where
  -- Tag type for the VM language instance.
  | mk

/-! ## Value Conversion -/

/-- Values are halted expressions. -/
abbrev SessionVMVal := { e : Expr // e.halted = true }

def SessionVM.to_val (e : Expr) : Option SessionVMVal :=
  -- A halted expression is treated as a value.
  if h : e.halted then some ⟨e, h⟩ else none

def SessionVM.of_val (v : SessionVMVal) : Expr :=
  -- Unwrap a halted expression.
  v.1

/-! ## Primitive Step Relation -/

def SessionVM.prim_step {ι γ π ε ν : Type}
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectRuntime ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (e : Expr) (σ : VMState ι γ π ε ν) (κ : List Unit)
    (e' : Expr) (σ' : VMState ι γ π ε ν) (efs : List Expr) : Prop :=
  κ = [] ∧
  e.halted = false ∧
  let (σ1, res) := execInstr σ e.cid
  match res.status with
  | .blocked _ => False
  | _ =>
      let halted' :=
        match σ1.coroutines[e.cid]? with
        | some c => match c.status with | .done => true | _ => false
        | none => true
      e' = { cid := e.cid, halted := halted' } ∧ σ' = σ1 ∧ efs = []

/-! ## Iris Language Instance -/

def instLanguageSessionVM {ι γ π ε ν : Type}
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectRuntime ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν] :
    Iris.ProgramLogic.Language where
  expr := Expr
  val := SessionVMVal
  state := VMState ι γ π ε ν
  observation := Unit
  of_val := SessionVM.of_val
  to_val := SessionVM.to_val
  prim_step := SessionVM.prim_step
  mixin :=
    { to_of_val := by
        intro v
        cases v with
        | mk v hv =>
            simp [SessionVM.to_val, SessionVM.of_val, hv]
      of_to_val := by
        intro e v h
        by_cases hhalted : e.halted
        · simp [SessionVM.to_val, hhalted] at h
          cases h
          rfl
        · simp [SessionVM.to_val, hhalted] at h
      val_stuck := by
        intro e σ κ e' σ' efs hstep
        rcases hstep with ⟨_, hhalted, _⟩
        simp [SessionVM.to_val, hhalted] }

/-! ## Conversion Lemmas -/

/-- `to_val` after `of_val` yields the halted expression. -/
theorem to_of_val {ι γ π ε ν : Type}
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectRuntime ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (v : SessionVMVal) :
    SessionVM.to_val (SessionVM.of_val v) = some v := by
  cases v with
  | mk v hv =>
      simp [SessionVM.to_val, SessionVM.of_val, hv]

/-- `of_val` simply flips the `halted` flag. -/
theorem of_to_val {ι γ π ε ν : Type}
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectRuntime ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (e : Expr) (v : SessionVMVal) :
    SessionVM.to_val e = some v → SessionVM.of_val v = e := by
  intro h
  by_cases hhalted : e.halted
  · simp [SessionVM.to_val, hhalted] at h
    cases h
    rfl
  · simp [SessionVM.to_val, hhalted] at h
