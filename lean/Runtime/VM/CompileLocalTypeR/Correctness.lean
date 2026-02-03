import Runtime.VM.CompileLocalTypeR

/-!
# CompileLocalTypeR Correctness Stubs

Statements only (no proofs yet).
-/

set_option autoImplicit false

universe u

open SessionTypes.LocalTypeR

axiom compile_nonempty {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    [Inhabited (EffectModel.EffectAction ε)]
    (lt : LocalTypeR) (h : lt ≠ .end) :
    (compileLocalTypeR (γ:=γ) (ε:=ε) lt).length > 0

axiom compile_ends_halt_or_jmp {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    [Inhabited (EffectModel.EffectAction ε)]
    (lt : LocalTypeR) :
    let code := compileLocalTypeR (γ:=γ) (ε:=ε) lt
    code.getLast? = some .halt ∨ ∃ pc, code.getLast? = some (.jmp pc)
