import Runtime.VM.CompileLocalTypeR

/-!
# CompileLocalTypeR Correctness Stubs

Statements only (no proofs yet).
-/

set_option autoImplicit false

universe u

open SessionTypes.LocalTypeR

private theorem ensureTerminal_nonempty {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (code : List (Instr γ ε)) : (ensureTerminal (γ:=γ) (ε:=ε) code).length > 0 := by
  cases code with
  | nil =>
      simp [ensureTerminal]
  | cons head tail =>
      cases h : (List.getLast? (head :: tail)) with
      | none =>
          simp [ensureTerminal, h]
      | some val =>
          cases val <;> simp [ensureTerminal, h]

private theorem ensureTerminal_last_halt_or_jmp {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (code : List (Instr γ ε)) :
    let code' := ensureTerminal (γ:=γ) (ε:=ε) code
    code'.getLast? = some .halt ∨ ∃ pc, code'.getLast? = some (.jmp pc) := by
  cases h : code.getLast? <;> simp [h, ensureTerminal]
  case some instr =>
    cases instr <;> simp [h]

theorem compile_nonempty {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    [Inhabited (EffectModel.EffectAction ε)]
    (lt : LocalTypeR) (_h : lt ≠ .end) :
    (compileLocalTypeR (γ:=γ) (ε:=ε) lt).length > 0 := by
  classical
  simpa [compileLocalTypeR] using
    (ensureTerminal_nonempty (γ:=γ) (ε:=ε)
      (code := (compileInner (γ:=γ) (ε:=ε) (default : EffectModel.EffectAction ε) lt [] []).1))

theorem compile_ends_halt_or_jmp {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    [Inhabited (EffectModel.EffectAction ε)]
    (lt : LocalTypeR) :
    let code := compileLocalTypeR (γ:=γ) (ε:=ε) lt
    code.getLast? = some .halt ∨ ∃ pc, code.getLast? = some (.jmp pc) := by
  classical
  simpa [compileLocalTypeR] using
    (ensureTerminal_last_halt_or_jmp (γ:=γ) (ε:=ε)
      (code := (compileInner (γ:=γ) (ε:=ε) (default : EffectModel.EffectAction ε) lt [] []).1))
