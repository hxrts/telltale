import Runtime.Adequacy.CompileRefinesSpec
import Runtime.Adequacy.CompileRefinesInvariants

/-! # Runtime.Adequacy.CompileRefines

Compiler refinement for `compileLocalTypeR`: for **every** `LocalTypeR` the
compiled bytecode is a block satisfying the specification relation `Impl`
(`CompileRefinesSpec.lean`), which fixes the emitted instruction sequence for
`end`, single-branch send/receive (value or label-only, both `send`/`receive`
as in the Rust compiler), multi-branch send (first-label `offer`), multi-branch
receive (`choose` table over consecutively placed branch blocks), `mu`
(binder PC recorded) and `var` (`jump` to the binder PC, or `halt`).

Main results:
* `compileInner_spec` / `compileRecvBranchesAux_spec`: the compiler appends
  exactly a block related by `Impl` / `ImplBranches` (strong induction on the
  type, mirroring the compiler's own recursion);
* `compile_refines`: `compileLocalTypeR t` satisfies `Impl default 0 [] t`,
  with no linearity premise, and `ensureTerminal` is the identity on it;
* `compile_refines_pc_invariant`: in the compiled block every `jump` targets a
  recorded `mu` binder PC inside the block and every `choose` entry points
  inside the block;
* `compile_refines_linear`: the previous single-branch, non-recursive
  statement, kept as a corollary for existing users.

The multi-role image layout of `CodeImage.fromLocalTypes` is covered in
`CompileRefinesImage.lean`.
-/

/-
The Problem. The previous `compile_refines` only covered the linear fragment
(`LinearImpl`), saying nothing about `choose` tables or loops.

Solution Structure. `Impl` is a clause-by-clause transcription of the
compiler; `compileInner_spec` is proved by the same well-founded recursion on
`sizeOf` that defines the compiler, so each case is `rw [compileInner]` plus
rewriting with the recursive results.
-/

set_option autoImplicit false

universe u

open SessionTypes.LocalTypeR

section

variable {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
  [Inhabited (EffectRuntime.EffectAction ε)]

/-! ## The compiler meets its specification -/

mutual
  /-- `compileInner d t code env` appends a block satisfying `Impl d code.length env t`. -/
  theorem compileInner_spec (d : EffectRuntime.EffectAction ε) (t : LocalTypeR)
      (code : List (Instr γ ε)) (env : List (String × PC)) :
      ∃ (is : List (Instr γ ε)) (env' : List (String × PC)),
        Impl d code.length env t is env' ∧
          compileInner d t code env = (code ++ is, env') :=
    match t with
    | .end => ⟨[.halt], env, .done, by rw [compileInner]⟩
    | .send p branches =>
      match branches with
      | [] => ⟨[.halt], env, .sendNil, by rw [compileInner]⟩
      | (lbl, vt, cont) :: [] =>
        have ⟨is, env', h, e⟩ := compileInner_spec d cont (code ++ [.send 0 1, .invoke d]) env
        ⟨.send 0 1 :: .invoke d :: is, env', .send (by simpa using h),
          by rw [compileInner]; simpa using e⟩
      | (lbl₁, vt₁, cont₁) :: b₂ :: rest =>
        have ⟨is, env', h, e⟩ := compileInner_spec d cont₁ (code ++ [.offer 0 lbl₁.name]) env
        ⟨.offer 0 lbl₁.name :: is, env', .offerMulti (by simpa using h),
          by rw [compileInner] <;> first | simpa using e | simp⟩
    | .recv p branches =>
      match branches with
      | [] => ⟨[.halt], env, .recvNil, by rw [compileInner]⟩
      | (lbl, vt, cont) :: [] =>
        have ⟨is, env', h, e⟩ :=
          compileInner_spec d cont (code ++ [.receive 0 1, .invoke d]) env
        ⟨.receive 0 1 :: .invoke d :: is, env', .recv (by simpa using h),
          by rw [compileInner]; simpa using e⟩
      | (lbl₁, vt₁, cont₁) :: (lbl₂, vt₂, cont₂) :: rest =>
        have ⟨is₁, env₁, h₁, e₁⟩ := compileInner_spec d cont₁ (code ++ [(Instr.choose 0 [] : Instr γ ε)]) env
        have ⟨is₂, env₂, h₂, e₂⟩ :=
          compileInner_spec d cont₂ (code ++ [(Instr.choose 0 [] : Instr γ ε)] ++ is₁) env₁
        have ⟨isR, table, env₃, hR, eR⟩ :=
          compileRecvBranchesAux_spec d rest (code ++ [(Instr.choose 0 [] : Instr γ ε)] ++ is₁ ++ is₂)
            [(lbl₁.name, (code ++ [(Instr.choose 0 [] : Instr γ ε)]).length),
              (lbl₂.name, (code ++ [(Instr.choose 0 [] : Instr γ ε)] ++ is₁).length)] env₂
        ⟨.choose 0 ((lbl₁.name, code.length + 1) :: (lbl₂.name, code.length + 1 + is₁.length)
            :: table) :: (is₁ ++ is₂ ++ isR), env₃,
          .chooseMany (by simpa using h₁)
            (by rw [show code.length + 1 + is₁.length = code.length + (is₁.length + 1) by omega]
                simpa using h₂)
            (by rw [show code.length + 1 + is₁.length + is₂.length =
                  code.length + (is₁.length + is₂.length + 1) by omega]
                simpa using hR), by
            rw [compileInner]
            simp only [e₁, e₂]
            simp only [List.append_assoc, List.cons_append,
              List.nil_append, List.length_append, List.length_cons, List.length_nil] at eR ⊢
            simp only [eR, listSet_append_cons]
            rw [show code.length + (0 + 1) = code.length + 1 by omega,
              show code.length + (is₁.length + 1) = code.length + 1 + is₁.length by omega]⟩
    | .mu v body =>
      have ⟨is, env', h, e⟩ := compileInner_spec d body code ((v, code.length) :: env)
      ⟨is, env', .mu h, by rw [compileInner]; exact e⟩
    | .var v =>
      match hf : env.find? (fun p => p.fst == v) with
      | some (w, target) =>
        ⟨[.jump target], env, .varBound hf, by rw [compileInner]; simp [hf]⟩
      | none => ⟨[.halt], env, .varFree hf, by rw [compileInner]; simp [hf]⟩
  termination_by sizeOf t
  decreasing_by
    all_goals
      simp
      try omega

  /-- `compileRecvBranchesAux d bs code tbl env` appends consecutively placed
  branch blocks and extends the table in order. -/
  theorem compileRecvBranchesAux_spec (d : EffectRuntime.EffectAction ε) (bs : List BranchR)
      (code : List (Instr γ ε)) (tbl env : List (String × PC)) :
      ∃ (is : List (Instr γ ε)) (table env' : List (String × PC)),
        ImplBranches d code.length env bs is table env' ∧
          compileRecvBranchesAux d bs code tbl env = (code ++ is, tbl ++ table, env') :=
    match bs with
    | [] => ⟨[], [], env, .nil, by rw [compileRecvBranchesAux]; simp⟩
    | (lbl, vt, cont) :: rest =>
      have ⟨is, env₁, h, e⟩ := compileInner_spec d cont code env
      have ⟨isR, table, env₂, hR, eR⟩ :=
        compileRecvBranchesAux_spec d rest (code ++ is) (tbl ++ [(lbl.name, code.length)]) env₁
      ⟨is ++ isR, (lbl.name, code.length) :: table, env₂, .cons h (by simpa using hR), by
        rw [compileRecvBranchesAux]
        simp only [e]
        simpa using eR⟩
  termination_by sizeOf bs
  decreasing_by
    all_goals
      simp
      try omega
end

/-! ## Refinement of the public entry point -/

/-- `ensureTerminal` is the identity on blocks ending in `halt` or `jump`. -/
theorem ensureTerminal_of_terminal {is : List (Instr γ ε)} (h : TerminalBlock is) :
    ensureTerminal is = is := by
  rcases h with h | ⟨k, h⟩ <;> simp [ensureTerminal, h]

/-- **compile_refines.** For every local type `t`, `compileLocalTypeR t` is a
block satisfying the specification `Impl default 0 [] t` (no linearity
premise), and `ensureTerminal` does not alter it. -/
theorem compile_refines (t : LocalTypeR) :
    ∃ (env' : List (String × PC)),
      Impl (γ:=γ) (default : EffectRuntime.EffectAction ε) 0 [] t
        (compileLocalTypeR (γ:=γ) (ε:=ε) t) env' ∧
      ensureTerminal (compileLocalTypeR (γ:=γ) (ε:=ε) t) = compileLocalTypeR (γ:=γ) (ε:=ε) t := by
  obtain ⟨is, env', h, e⟩ := compileInner_spec (γ:=γ) (ε:=ε) default t [] []
  have hc : compileLocalTypeR (γ:=γ) (ε:=ε) t = is := by
    unfold compileLocalTypeR
    simp only
    rw [e, List.nil_append, ensureTerminal_of_terminal h.terminal]
  rw [hc]
  exact ⟨env', by simpa using h, ensureTerminal_of_terminal h.terminal⟩

/-- **Program-counter invariant of compiled code.** Every `jump` in
`compileLocalTypeR t` targets the PC recorded for some `mu` binder, and that PC
as well as every `choose` table entry lies inside the compiled block. -/
theorem compile_refines_pc_invariant (t : LocalTypeR) :
    let is := compileLocalTypeR (γ:=γ) (ε:=ε) t
    (∀ k, Instr.jump k ∈ is → is.length > k) ∧
    (∀ chan table, Instr.choose chan table ∈ is → ∀ e ∈ table, is.length > e.2) := by
  obtain ⟨env', h, _⟩ := compile_refines (γ:=γ) (ε:=ε) t
  exact ⟨fun k hk => by simpa using (h.jump_lt hk).2,
    fun chan table ht e he => by simpa using (h.choose_bounded chan table ht e he).2⟩

/-! ## The linear fragment, as a corollary -/

/-- `LinearImpl d t is`: on the linear (single-branch, non-recursive) fragment,
`is` is the bytecode that implements local type `t` action by action. -/
inductive LinearImpl (d : EffectRuntime.EffectAction ε) :
    LocalTypeR → List (Instr γ ε) → Prop
  /-- `end` is implemented by `halt`. -/
  | done : LinearImpl d .end [Instr.halt]
  /-- A send (value or label-only) is `send 0 1; invoke d` then the continuation. -/
  | send {p : String} {lbl : SessionTypes.GlobalType.Label} {vt : Option SessionTypes.ValType}
      {cont : LocalTypeR} {is : List (Instr γ ε)} :
      LinearImpl d cont is →
      LinearImpl d (.send p [(lbl, vt, cont)]) (Instr.send 0 1 :: Instr.invoke d :: is)
  /-- A receive (value or label-only) is `receive 0 1; invoke d` then the continuation. -/
  | recv {p : String} {lbl : SessionTypes.GlobalType.Label} {vt : Option SessionTypes.ValType}
      {cont : LocalTypeR} {is : List (Instr γ ε)} :
      LinearImpl d cont is →
      LinearImpl d (.recv p [(lbl, vt, cont)]) (Instr.receive 0 1 :: Instr.invoke d :: is)

/-- A linear implementation is an `Impl` block at any PC and environment,
leaving the environment unchanged. -/
theorem LinearImpl.toImpl {d : EffectRuntime.EffectAction ε} {t : LocalTypeR}
    {is : List (Instr γ ε)} (h : LinearImpl d t is) :
    ∀ pc env, Impl d pc env t is env := by
  induction h with
  | done => intro pc env; exact .done
  | send _ ih => intro pc env; exact .send (ih _ _)
  | recv _ ih => intro pc env; exact .recv (ih _ _)

/-- `compileInner` appends exactly the specified code on the linear fragment. -/
theorem compileInner_linear {d : EffectRuntime.EffectAction ε} {t : LocalTypeR}
    {is : List (Instr γ ε)} (h : LinearImpl d t is) :
    ∀ (code : List (Instr γ ε)) (lt : List (String × PC)),
      (compileInner d t code lt).1 = code ++ is := by
  induction h with
  | done => intro code lt; rw [compileInner]
  | send _ ih => intro code lt; rw [compileInner]; simp [ih]
  | recv _ ih => intro code lt; rw [compileInner]; simp [ih]

/-- **compile_refines_linear.** On the linear fragment, `compileLocalTypeR t`
is exactly the action-by-action implementation of `t` (the previous
`compile_refines`, kept as a corollary for existing users). -/
theorem compile_refines_linear {t : LocalTypeR} {is : List (Instr γ ε)}
    (h : LinearImpl (γ:=γ) default t is) : compileLocalTypeR (γ:=γ) (ε:=ε) t = is := by
  unfold compileLocalTypeR
  simp only
  rw [compileInner_linear h, List.nil_append]
  exact ensureTerminal_of_terminal (h.toImpl 0 []).terminal

end
