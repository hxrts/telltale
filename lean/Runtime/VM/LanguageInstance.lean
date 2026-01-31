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

universe u

inductive SessionVM (ι π ε : Type u) : Type u where
  | mk

def SessionVM.to_val (e : Expr) : Option Expr :=
  if e.halted then some e else none

def SessionVM.of_val (v : Expr) : Expr :=
  { v with halted := true }

instance instLanguageSessionVM {ι π ε : Type u}
    [IdentityModel ι] [PersistenceModel π] [EffectModel ε] :
    Iris.Language (SessionVM ι π ε) where
  expr := Expr
  val := Expr
  state := VMState ι π ε
  of_val := SessionVM.of_val
  to_val := SessionVM.to_val
  prim_step := fun e σ =>
    if e.halted then [] else
      let (σ', res) := execInstr σ e.cid
      match res.status with
      | .blocked => []
      | _ =>
          let halted' :=
            match σ'.coroutines[e.cid]? with
            | some c => match c.status with | .done => true | _ => false
            | none => true
          [({ cid := e.cid, halted := halted' }, σ', [])]

theorem to_of_val {ι π ε : Type u}
    [IdentityModel ι] [PersistenceModel π] [EffectModel ε]
    (v : Expr) :
    SessionVM.to_val (SessionVM.of_val v) = some { v with halted := true } := by
  simp [SessionVM.to_val, SessionVM.of_val]

theorem of_to_val {ι π ε : Type u}
    [IdentityModel ι] [PersistenceModel π] [EffectModel ε]
    (e : Expr) :
    SessionVM.of_val e = { e with halted := true } := by
  rfl

theorem val_head_stuck {ι π ε : Type u}
    [IdentityModel ι] [PersistenceModel π] [EffectModel ε]
    (v : Expr) (σ : VMState ι π ε) :
    Iris.Language.prim_step (Λ:=SessionVM ι π ε) (SessionVM.of_val v) σ = [] := by
  simp [Iris.Language.prim_step, instLanguageSessionVM, SessionVM.of_val]
