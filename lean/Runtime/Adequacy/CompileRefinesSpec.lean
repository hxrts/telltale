import Runtime.ProtocolMachine.Model.CompileLocalTypeR

/-! # Runtime.Adequacy.CompileRefinesSpec

Specification relation for the `LocalTypeR` bytecode compiler.

`Impl d pc env t is env'` says: starting at program counter `pc` with loop
environment `env`, local type `t` is implemented by the instruction block `is`
and leaves the loop environment at `env'`. The relation is a direct, clause by
clause transcription of what `compileInner d t code loopTargets` emits
(`code.length = pc`, `loopTargets = env`), covering every constructor:

* `end` (and empty branch lists) emit `halt`;
* a single send/receive branch (value or label-only, matching the Rust
  compiler) emits `send 0 1; invoke d` / `receive 0 1; invoke d`;
* a multi-branch send emits `offer 0 lbl₁` for the **first** label only and
  continues with the first continuation (no `invoke`), exactly as the compiler
  does today;
* a multi-branch receive emits a `choose` table whose entries are the start PCs
  of the consecutively laid-out branch blocks (`compileRecvBranchesAux`);
* `mu v body` records `(v, pc)` in the loop environment and emits the body;
* `var v` emits `jump target` when `v` is bound and `halt` otherwise.

`ImplBranches` is the companion relation for the tail of a receive branch list.
This file also proves the structural facts used downstream: every block is
non-empty and ends in `halt` or `jump`.
-/

/-
The Problem. The previous `LinearImpl` relation only covered single-branch,
non-recursive types, so `compile_refines` said nothing about choice or loops.

Solution Structure. State the relation as an inductive family indexed by the
start PC and loop environment, mirroring the compiler's accumulator discipline;
structural lemmas follow by mutual structural recursion on the derivation.
-/

set_option autoImplicit false

universe u

open SessionTypes.LocalTypeR

section

variable {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]

/-! ## The specification relation -/

mutual
  /-- `Impl d pc env t is env'`: block `is` placed at PC `pc` implements `t`
  under loop environment `env`, producing loop environment `env'`. -/
  inductive Impl (d : EffectRuntime.EffectAction ε) :
      Nat → List (String × PC) → LocalTypeR → List (Instr γ ε) → List (String × PC) → Prop
    /-- `end` is implemented by `halt`. -/
    | done {pc : Nat} {env : List (String × PC)} : Impl d pc env .end [.halt] env
    /-- An empty send branch list is implemented by `halt`. -/
    | sendNil {pc : Nat} {env : List (String × PC)} {p : String} :
        Impl d pc env (.send p []) [.halt] env
    /-- A single send branch (value or label-only) is `send 0 1; invoke d`
    then the continuation. -/
    | send {pc : Nat} {env env' : List (String × PC)} {p : String}
        {lbl : SessionTypes.GlobalType.Label} {vt : Option SessionTypes.ValType}
        {cont : LocalTypeR} {is : List (Instr γ ε)} :
        Impl d (pc + 2) env cont is env' →
        Impl d pc env (.send p [(lbl, vt, cont)]) (.send 0 1 :: .invoke d :: is) env'
    /-- A multi-branch send offers the first label and continues with the first
    continuation (the compiler's deterministic first-label choice). -/
    | offerMulti {pc : Nat} {env env' : List (String × PC)} {p : String}
        {lbl₁ : SessionTypes.GlobalType.Label} {vt₁ : Option SessionTypes.ValType}
        {cont₁ : LocalTypeR} {b₂ : BranchR} {rest : List BranchR} {is : List (Instr γ ε)} :
        Impl d (pc + 1) env cont₁ is env' →
        Impl d pc env (.send p ((lbl₁, vt₁, cont₁) :: b₂ :: rest)) (.offer 0 lbl₁.name :: is) env'
    /-- An empty receive branch list is implemented by `halt`. -/
    | recvNil {pc : Nat} {env : List (String × PC)} {p : String} :
        Impl d pc env (.recv p []) [.halt] env
    /-- A single receive branch (value or label-only) is `receive 0 1; invoke d`
    then the continuation. -/
    | recv {pc : Nat} {env env' : List (String × PC)} {p : String}
        {lbl : SessionTypes.GlobalType.Label} {vt : Option SessionTypes.ValType}
        {cont : LocalTypeR} {is : List (Instr γ ε)} :
        Impl d (pc + 2) env cont is env' →
        Impl d pc env (.recv p [(lbl, vt, cont)]) (.receive 0 1 :: .invoke d :: is) env'
    /-- A multi-branch receive is a `choose` table over consecutively placed
    branch blocks; the loop environment threads through the branches in order. -/
    | chooseMany {pc : Nat} {env env₁ env₂ env₃ : List (String × PC)} {p : String}
        {lbl₁ lbl₂ : SessionTypes.GlobalType.Label} {vt₁ vt₂ : Option SessionTypes.ValType}
        {cont₁ cont₂ : LocalTypeR} {rest : List BranchR}
        {is₁ is₂ isR : List (Instr γ ε)} {table : List (String × PC)} :
        Impl d (pc + 1) env cont₁ is₁ env₁ →
        Impl d (pc + 1 + is₁.length) env₁ cont₂ is₂ env₂ →
        ImplBranches d (pc + 1 + is₁.length + is₂.length) env₂ rest isR table env₃ →
        Impl d pc env (.recv p ((lbl₁, vt₁, cont₁) :: (lbl₂, vt₂, cont₂) :: rest))
          (.choose 0 ((lbl₁.name, pc + 1) :: (lbl₂.name, pc + 1 + is₁.length) :: table)
            :: (is₁ ++ is₂ ++ isR)) env₃
    /-- `mu v body` binds `v` to the current PC and emits the body. -/
    | mu {pc : Nat} {env env' : List (String × PC)} {v : String} {body : LocalTypeR}
        {is : List (Instr γ ε)} :
        Impl d pc ((v, pc) :: env) body is env' →
        Impl d pc env (.mu v body) is env'
    /-- A bound variable jumps to its recorded binder PC. -/
    | varBound {pc : Nat} {env : List (String × PC)} {v w : String} {target : PC} :
        env.find? (fun p => p.fst == v) = some (w, target) →
        Impl d pc env (.var v) [.jump target] env
    /-- An unbound variable halts. -/
    | varFree {pc : Nat} {env : List (String × PC)} {v : String} :
        env.find? (fun p => p.fst == v) = none →
        Impl d pc env (.var v) [.halt] env

  /-- `ImplBranches d pc env bs is table env'`: the receive branches `bs` are
  laid out consecutively from `pc` as `is`, with `table` recording each
  branch's start PC in order. -/
  inductive ImplBranches (d : EffectRuntime.EffectAction ε) :
      Nat → List (String × PC) → List BranchR → List (Instr γ ε) → List (String × PC) →
        List (String × PC) → Prop
    /-- No branches: no code, empty table. -/
    | nil {pc : Nat} {env : List (String × PC)} : ImplBranches d pc env [] [] [] env
    /-- One more branch: its block, then the rest at the next free PC. -/
    | cons {pc : Nat} {env env₁ env₂ : List (String × PC)}
        {lbl : SessionTypes.GlobalType.Label} {vt : Option SessionTypes.ValType}
        {cont : LocalTypeR} {rest : List BranchR} {is isR : List (Instr γ ε)}
        {table : List (String × PC)} :
        Impl d pc env cont is env₁ →
        ImplBranches d (pc + is.length) env₁ rest isR table env₂ →
        ImplBranches d pc env ((lbl, vt, cont) :: rest) (is ++ isR) ((lbl.name, pc) :: table) env₂
end

/-! ## `listSet` patching -/

/-- Patching the element just past a prefix replaces the head of the suffix. -/
theorem listSet_append_cons {α : Type u} (code : List α) (x y : α) (rest : List α) :
    listSet (code ++ x :: rest) code.length y = code ++ y :: rest := by
  induction code with
  | nil => rfl
  | cons c cs ih => simp [listSet, ih]

/-! ## Structural facts -/

/-- A block ends in `halt` or in a `jump`. -/
def TerminalBlock (is : List (Instr γ ε)) : Prop :=
  is.getLast? = some .halt ∨ ∃ k, is.getLast? = some (.jump k)

/-- Prepending keeps a terminal block terminal. -/
theorem TerminalBlock.cons {is : List (Instr γ ε)} (x : Instr γ ε) (h : TerminalBlock is) :
    TerminalBlock (x :: is) := by
  cases is with
  | nil => simp [TerminalBlock] at h
  | cons y ys => simpa [TerminalBlock] using h

/-- Appending a terminal block on the right yields a terminal block. -/
theorem TerminalBlock.append_right (l : List (Instr γ ε)) {is : List (Instr γ ε)}
    (h : TerminalBlock is) : TerminalBlock (l ++ is) := by
  induction l with
  | nil => simpa using h
  | cons x xs ih => exact ih.cons x

/-- Every implementation block is non-empty. -/
theorem Impl.length_pos {d : EffectRuntime.EffectAction ε} {pc : Nat}
    {env env' : List (String × PC)} {t : LocalTypeR} {is : List (Instr γ ε)}
    (h : Impl d pc env t is env') : 0 < is.length :=
  match h with
  | .mu h' => h'.length_pos
  | .done | .sendNil | .recvNil | .varFree _ | .varBound _ => by simp
  | .send _ | .recv _ | .offerMulti _ | .chooseMany _ _ _ => by simp

mutual
  /-- Every implementation block ends in `halt` or `jump`
  (so `ensureTerminal` leaves it unchanged). -/
  theorem Impl.terminal {d : EffectRuntime.EffectAction ε} {pc : Nat}
      {env env' : List (String × PC)} {t : LocalTypeR} {is : List (Instr γ ε)}
      (h : Impl d pc env t is env') : TerminalBlock is :=
    match h with
    | .done => Or.inl rfl
    | .sendNil => Or.inl rfl
    | .recvNil => Or.inl rfl
    | .varFree _ => Or.inl rfl
    | .varBound _ => Or.inr ⟨_, rfl⟩
    | .send h' => (h'.terminal.cons _).cons _
    | .recv h' => (h'.terminal.cons _).cons _
    | .offerMulti h' => h'.terminal.cons _
    | .mu h' => h'.terminal
    | .chooseMany _ h₂ hR =>
        match hR.terminal with
        | Or.inl hnil => by
            subst hnil
            rw [List.append_nil]
            exact (TerminalBlock.append_right _ h₂.terminal).cons _
        | Or.inr hT => by
            rw [List.append_assoc]
            exact (TerminalBlock.append_right _ (TerminalBlock.append_right _ hT)).cons _

  /-- A branch tail is empty or ends in `halt`/`jump`. -/
  theorem ImplBranches.terminal {d : EffectRuntime.EffectAction ε} {pc : Nat}
      {env env' : List (String × PC)} {bs : List BranchR} {is : List (Instr γ ε)}
      {table : List (String × PC)} (h : ImplBranches d pc env bs is table env') :
      is = [] ∨ TerminalBlock is :=
    match h with
    | .nil => Or.inl rfl
    | .cons h₁ hR =>
        match hR.terminal with
        | Or.inl hnil => Or.inr (by subst hnil; simpa using h₁.terminal)
        | Or.inr hT => Or.inr (TerminalBlock.append_right _ hT)
end

end
