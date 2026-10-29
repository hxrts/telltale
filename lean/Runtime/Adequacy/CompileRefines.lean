import Runtime.ProtocolMachine.Model.CompileLocalTypeR

/-! # Runtime.Adequacy.CompileRefines

Compiler refinement for `compileLocalTypeR`: on the linear (single-branch,
non-recursive) fragment of `LocalTypeR`, the compiled bytecode is exactly the
instruction sequence prescribed by the local type's actions — each
value-carrying send becomes `send 0 1; invoke`, each label-only send becomes
`offer 0 lbl; invoke`, each value-carrying receive becomes `receive 0 1; invoke`,
and `end` becomes `halt`.

Scope: multi-branch choice (`choose` tables), `mu`/`var` loops, and the
multi-role image layout of `CodeImage.fromLocalTypes` (relocation, entry points)
are not covered here.
-/

/-
The Problem. The previous `compile_refines` ignored its process and guard
chain and was witnessed by a one-instruction `halt` program, saying nothing
about the compiler.

Solution Structure. Specify the expected code with an inductive relation
`LinearImpl`, prove `compileInner` appends exactly that code, and lift to
`compileLocalTypeR` through `ensureTerminal`.
-/

set_option autoImplicit false

universe u

open SessionTypes.LocalTypeR

section

variable {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]

/-- `LinearImpl d t is`: on the linear fragment, `is` is the bytecode that
implements local type `t` action by action (with handler action `d`). -/
inductive LinearImpl (d : EffectRuntime.EffectAction ε) :
    LocalTypeR → List (Instr γ ε) → Prop
  /-- `end` is implemented by `halt`. -/
  | done : LinearImpl d .end [Instr.halt]
  /-- A value send is `send 0 1; invoke d` then the continuation. -/
  | send {p : String} {lbl : SessionTypes.GlobalType.Label} {T : SessionTypes.ValType} {cont : LocalTypeR}
      {is : List (Instr γ ε)} :
      LinearImpl d cont is →
      LinearImpl d (.send p [(lbl, some T, cont)]) (Instr.send 0 1 :: Instr.invoke d :: is)
  /-- A label-only send is `offer 0 lbl; invoke d` then the continuation. -/
  | offer {p : String} {lbl : SessionTypes.GlobalType.Label} {cont : LocalTypeR} {is : List (Instr γ ε)} :
      LinearImpl d cont is →
      LinearImpl d (.send p [(lbl, none, cont)]) (Instr.offer 0 lbl.name :: Instr.invoke d :: is)
  /-- A value receive is `receive 0 1; invoke d` then the continuation. -/
  | recv {p : String} {lbl : SessionTypes.GlobalType.Label} {T : SessionTypes.ValType} {cont : LocalTypeR}
      {is : List (Instr γ ε)} :
      LinearImpl d cont is →
      LinearImpl d (.recv p [(lbl, some T, cont)]) (Instr.receive 0 1 :: Instr.invoke d :: is)

variable [Inhabited (EffectRuntime.EffectAction ε)]

/-- `compileInner` appends exactly the specified code on the linear fragment. -/
theorem compileInner_linear {d : EffectRuntime.EffectAction ε} {t : LocalTypeR}
    {is : List (Instr γ ε)} (h : LinearImpl d t is) :
    ∀ (code : List (Instr γ ε)) (lt : List (String × PC)),
      (compileInner d t code lt).1 = code ++ is := by
  induction h with
  | done => intro code lt; rw [compileInner]
  | send _ ih => intro code lt; rw [compileInner]; simp [ih]
  | offer _ ih => intro code lt; rw [compileInner]; simp [ih]
  | recv _ ih => intro code lt; rw [compileInner]; simp [ih]

omit [Inhabited (EffectRuntime.EffectAction ε)] in
/-- Linear implementations are some prefix followed by `halt`. -/
theorem LinearImpl.eq_snoc_halt {d : EffectRuntime.EffectAction ε} {t : LocalTypeR}
    {is : List (Instr γ ε)} (h : LinearImpl d t is) : ∃ pre, is = pre ++ [Instr.halt] := by
  induction h with
  | done => exact ⟨[], rfl⟩
  | send _ ih => obtain ⟨pre, rfl⟩ := ih; exact ⟨_ :: _ :: pre, rfl⟩
  | offer _ ih => obtain ⟨pre, rfl⟩ := ih; exact ⟨_ :: _ :: pre, rfl⟩
  | recv _ ih => obtain ⟨pre, rfl⟩ := ih; exact ⟨_ :: _ :: pre, rfl⟩

omit [Inhabited (EffectRuntime.EffectAction ε)] in
/-- Linear implementations end in `halt`. -/
theorem LinearImpl.getLast_halt {d : EffectRuntime.EffectAction ε} {t : LocalTypeR}
    {is : List (Instr γ ε)} (h : LinearImpl d t is) : is.getLast? = some Instr.halt := by
  obtain ⟨pre, rfl⟩ := h.eq_snoc_halt
  simp

/-- **compile_refines.** On the linear fragment, `compileLocalTypeR t` is exactly
the action-by-action implementation of `t`. -/
theorem compile_refines {t : LocalTypeR} {is : List (Instr γ ε)}
    (h : LinearImpl (γ:=γ) default t is) : compileLocalTypeR (γ:=γ) (ε:=ε) t = is := by
  unfold compileLocalTypeR
  simp only
  rw [compileInner_linear h, List.nil_append]
  unfold ensureTerminal
  rw [h.getLast_halt]

end
