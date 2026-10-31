import Runtime.Adequacy.CompileRefines
import Runtime.ProtocolMachine.Model.Program

/-! # Runtime.Adequacy.CompileRefinesImage

Multi-role image layout. `CodeImage.fromLocalTypes lts g` sorts the
(role, local type) pairs by role (`sortLocalTypesByRole`), then lays out the
roles' bytecode consecutively: role `i` is placed at `start_i`, its segment is
`relocateCode start_i (compileLocalTypeR lt_i)` (every `jump`/`choose`/`spawn`
target shifted by `start_i`), and `(role_i, start_i)` is appended to the entry
points. `roleLayout` is that layout as a recursive function and
`fromLocalTypes_layout` identifies the image with it.

`fromLocalTypes_refines` then says: for every index `i` into the sorted list,
the `i`-th entry point is `(role_i, start_i)`, the code at `start_i` is the
relocated compilation of `lt_i`, and that segment satisfies the compiler
specification `Impl default start_i [] lt_i` (relocation shifts the PC base
and the recorded binder PCs, `Impl.relocate`).

What `CodeImage.toRoleCodeImage` returns (stated, not proved here): for each
entry `(r, pc)` it takes the chunk of the image from `pc` up to the next
larger entry point (or the end of the image), un-relocates control targets by
`pc` with `mapExecutableTargets?`, and stores it under `r`; it refuses images
whose entries are duplicated, out of range, or lack an entry at PC `0`. For
`jump`/`choose`/`spawn` instructions `mapExecutableTargets?` exactly inverts
`relocateInstr` on in-chunk targets (`mapExecutableTargets?_relocate`); the
treatment of `invoke` depends on the `EffectRuntime` action model and is not
pinned down here.
-/

/-
The Problem. `compile_refines` speaks about one role's bytecode; the loader
consumes a multi-role image whose segments are relocated.

Solution Structure. Factor the fold in `fromLocalTypes` through `roleLayout`,
prove a positional characterisation of `roleLayout`, and lift `Impl` through
`relocateCode` by mutual structural recursion.
-/

set_option autoImplicit false

universe u

open SessionTypes.LocalTypeR

section

variable {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]

/-! ## Relocation of specification blocks -/

/-- Shift a recorded binder PC by `k`. -/
def shiftBinder (k : Nat) (x : String × PC) : String × PC := (x.1, k + x.2)

/-- `find?` on a shifted environment. -/
theorem find?_map_shiftBinder (k : Nat) (env : List (String × PC)) (v : String) :
    (env.map (shiftBinder k)).find? (fun p => p.fst == v) =
      (env.find? (fun p => p.fst == v)).map (shiftBinder k) := by
  induction env with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x.1 == v
    · simp [List.find?, shiftBinder, hx]
    · simp [List.find?, shiftBinder, hx, ih]

/-- Relocation preserves length. -/
@[simp] theorem relocateCode_length (k : Nat) (is : List (Instr γ ε)) :
    (relocateCode k is).length = is.length := by
  simp [relocateCode]

mutual
  /-- Relocating a specification block by `k` yields the specification block
  at PC `k + pc`, with all recorded binder PCs shifted by `k`. -/
  theorem Impl.relocate {d : EffectRuntime.EffectAction ε} {pc : Nat}
      {env env' : List (String × PC)} {t : LocalTypeR} {is : List (Instr γ ε)}
      (k : Nat) (h : Impl d pc env t is env') :
      Impl d (k + pc) (env.map (shiftBinder k)) t (relocateCode k is) (env'.map (shiftBinder k)) :=
    match h with
    | .done => .done
    | .sendNil => .sendNil
    | .recvNil => .recvNil
    | .send h' => by
        have ih := h'.relocate k
        rw [← Nat.add_assoc] at ih
        exact .send ih
    | .recv h' => by
        have ih := h'.relocate k
        rw [← Nat.add_assoc] at ih
        exact .recv ih
    | .offerMulti h' => by
        have ih := h'.relocate k
        rw [← Nat.add_assoc] at ih
        exact .offerMulti ih
    | .chooseMany (p := p) (lbl₁ := lbl₁) (lbl₂ := lbl₂) (vt₁ := vt₁) (vt₂ := vt₂)
        (is₁ := is₁) (is₂ := is₂) h₁ h₂ hR => by
        have ih₁ := h₁.relocate k
        have ih₂ := h₂.relocate k
        have ihR := hR.relocate k
        rw [← relocateCode_length k is₁] at ih₂ ihR
        rw [← relocateCode_length k is₂] at ihR
        simp only [← Nat.add_assoc] at ih₁ ih₂ ihR
        have := Impl.chooseMany (p := p) (lbl₁ := lbl₁) (lbl₂ := lbl₂) (vt₁ := vt₁) (vt₂ := vt₂)
          ih₁ ih₂ ihR
        convert this using 1
        simp [relocateCode, relocateInstr, shiftBinder, Function.comp_def, Nat.add_assoc]
    | .mu h' => .mu (h'.relocate k)
    | .varBound (w := w) (target := target) hf =>
        .varBound (w := w) (by rw [find?_map_shiftBinder, hf]; rfl)
    | .varFree hf => .varFree (by rw [find?_map_shiftBinder, hf]; rfl)

  /-- Relocating a branch tail by `k`. -/
  theorem ImplBranches.relocate {d : EffectRuntime.EffectAction ε} {pc : Nat}
      {env env' : List (String × PC)} {bs : List BranchR} {is : List (Instr γ ε)}
      {table : List (String × PC)} (k : Nat) (h : ImplBranches d pc env bs is table env') :
      ImplBranches d (k + pc) (env.map (shiftBinder k)) bs (relocateCode k is)
        (table.map (shiftBinder k)) (env'.map (shiftBinder k)) :=
    match h with
    | .nil => .nil
    | .cons (lbl := lbl) (vt := vt) (is := is₁) h₁ hR => by
        have ih₁ := h₁.relocate k
        have ihR := hR.relocate k
        rw [← relocateCode_length k is₁, ← Nat.add_assoc] at ihR
        simp only [relocateCode, List.map_append, List.map_cons]
        have := ImplBranches.cons (lbl := lbl) (vt := vt) ih₁ ihR
        simpa [relocateCode, List.length_map, shiftBinder] using this
end

/-! ## The layout function -/

/-- Consecutive per-role layout starting at `start`: relocated segments and
entry points. -/
def roleLayout [Inhabited (EffectRuntime.EffectAction ε)] :
    List (Role × LocalTypeR) → Nat → List (Instr γ ε) × List (Role × PC)
  | [], _ => ([], [])
  | (r, lt) :: rest, start =>
      let seg := relocateCode (γ:=γ) (ε:=ε) start (compileLocalTypeR lt)
      let tail := roleLayout rest (start + seg.length)
      (seg ++ tail.1, (r, start) :: tail.2)

/-- The fold inside `CodeImage.fromLocalTypes` computes `roleLayout`. -/
theorem fromLocalTypes_fold [Inhabited (EffectRuntime.EffectAction ε)]
    (ordered : List (Role × LocalTypeR)) :
    ∀ (code : List (Instr γ ε)) (eps : List (Role × PC)),
      ordered.foldl
        (fun (acc : List (Instr γ ε) × List (Role × PC)) (entry : Role × LocalTypeR) =>
          let (code, entryPoints) := acc
          let (role, lt) := entry
          let startPc := code.length
          let roleCode := compileLocalTypeR (γ:=γ) (ε:=ε) lt
          let code' := code ++ relocateCode (γ := γ) (ε := ε) startPc roleCode
          (code', entryPoints ++ [(role, startPc)])) (code, eps) =
        (code ++ (roleLayout (γ:=γ) (ε:=ε) ordered code.length).1,
          eps ++ (roleLayout (γ:=γ) (ε:=ε) ordered code.length).2) := by
  induction ordered with
  | nil => intro code eps; simp [roleLayout]
  | cons entry rest ih =>
    intro code eps
    obtain ⟨r, lt⟩ := entry
    simp only [List.foldl, roleLayout]
    rw [ih]
    simp [List.length_append]

/-- `CodeImage.fromLocalTypes` is `roleLayout` of the role-sorted input. -/
theorem fromLocalTypes_layout [Inhabited (EffectRuntime.EffectAction ε)]
    (lts : List (Role × LocalTypeR)) (g : GlobalType) :
    (CodeImage.fromLocalTypes (γ:=γ) (ε:=ε) lts g).program.code.toList =
        (roleLayout (γ:=γ) (ε:=ε) (sortLocalTypesByRole lts) 0).1 ∧
      (CodeImage.fromLocalTypes (γ:=γ) (ε:=ε) lts g).program.entryPoints =
        (roleLayout (γ:=γ) (ε:=ε) (sortLocalTypesByRole lts) 0).2 := by
  unfold CodeImage.fromLocalTypes
  simp only
  rw [fromLocalTypes_fold]
  simp

/-- Dropping a prefix plus `n` more elements. -/
theorem drop_append_add {α : Type u} (l₁ l₂ : List α) (n : Nat) :
    (l₁ ++ l₂).drop (l₁.length + n) = l₂.drop n := by
  induction l₁ with
  | nil => simp
  | cons x xs ih => simpa [Nat.succ_add] using ih

/-- Positional characterisation of `roleLayout`: the `i`-th entry point names
the `i`-th role at `start + off`, and the layout code at offset `off` is that
role's compilation relocated to `start + off`. -/
theorem roleLayout_spec [Inhabited (EffectRuntime.EffectAction ε)]
    (ordered : List (Role × LocalTypeR)) :
    ∀ (start i : Nat) (hi : i < ordered.length),
      ∃ off, (roleLayout (γ:=γ) (ε:=ε) ordered start).2[i]? = some (ordered[i].1, start + off) ∧
        ((roleLayout (γ:=γ) (ε:=ε) ordered start).1.drop off).take
            (compileLocalTypeR (γ:=γ) (ε:=ε) ordered[i].2).length =
          relocateCode (start + off) (compileLocalTypeR (γ:=γ) (ε:=ε) ordered[i].2) := by
  induction ordered with
  | nil => intro _ i hi; simp at hi
  | cons entry rest ih =>
    intro start i hi
    obtain ⟨r, lt⟩ := entry
    cases i with
    | zero =>
      refine ⟨0, by simp [roleLayout], ?_⟩
      simp only [roleLayout, Nat.add_zero, List.drop_zero, List.getElem_cons_zero]
      exact List.take_left' (by simp [relocateCode])
    | succ i =>
      have hi' : i < rest.length := by simpa using hi
      obtain ⟨off, h1, h3⟩ :=
        ih (start + (relocateCode (γ:=γ) (ε:=ε) start (compileLocalTypeR lt)).length) i hi'
      refine ⟨(relocateCode (γ:=γ) (ε:=ε) start (compileLocalTypeR lt)).length + off,
        by rw [← Nat.add_assoc]; simpa [roleLayout] using h1, ?_⟩
      simp only [roleLayout, List.getElem_cons_succ]
      rw [drop_append_add, ← Nat.add_assoc]
      exact h3

/-- **fromLocalTypes_refines.** In `CodeImage.fromLocalTypes lts g`, for every
index `i` into the role-sorted list, the `i`-th entry point is `(role_i, start_i)`,
the image code at `start_i` is `relocateCode start_i (compileLocalTypeR lt_i)`,
and that segment satisfies the compiler specification at PC `start_i`. -/
theorem fromLocalTypes_refines [Inhabited (EffectRuntime.EffectAction ε)]
    (lts : List (Role × LocalTypeR)) (g : GlobalType) :
    let img := CodeImage.fromLocalTypes (γ:=γ) (ε:=ε) lts g
    let ordered := sortLocalTypesByRole lts
    ∀ i (hi : i < ordered.length),
      ∃ pcᵢ env',
        img.program.entryPoints[i]? = some (ordered[i].1, pcᵢ) ∧
        (img.program.code.toList.drop pcᵢ).take
            (compileLocalTypeR (γ:=γ) (ε:=ε) ordered[i].2).length =
          relocateCode pcᵢ (compileLocalTypeR (γ:=γ) (ε:=ε) ordered[i].2) ∧
        Impl (γ:=γ) (default : EffectRuntime.EffectAction ε) pcᵢ [] ordered[i].2
          (relocateCode pcᵢ (compileLocalTypeR (γ:=γ) (ε:=ε) ordered[i].2)) env' := by
  intro img ordered i hi
  obtain ⟨hcode, heps⟩ := fromLocalTypes_layout (γ:=γ) (ε:=ε) lts g
  obtain ⟨pcᵢ, h1, h3⟩ := roleLayout_spec (γ:=γ) (ε:=ε) ordered 0 i hi
  rw [Nat.zero_add] at h1 h3
  obtain ⟨env', hImpl, _⟩ := compile_refines (γ:=γ) (ε:=ε) ordered[i].2
  refine ⟨pcᵢ, env'.map (shiftBinder pcᵢ), ?_, ?_, ?_⟩
  · show img.program.entryPoints[i]? = _
    rw [heps]; exact h1
  · show (img.program.code.toList.drop pcᵢ).take _ = _
    rw [hcode]; simpa using h3
  · simpa using hImpl.relocate pcᵢ

/-! ## Un-relocation by the role splitter -/

/-- Un-relocating an in-chunk relocated table recovers it. -/
theorem mapM_unrelocate (base size : Nat) :
    ∀ (table : List (Label × PC)), (∀ e ∈ table, size > e.2) →
      (table.map (fun (lbl, pc) => (lbl, base + pc))).mapM
        (fun entry => do
          let pc ← (fun pc => if base ≤ pc ∧ pc < base + size then some (pc - base) else none) entry.2
          pure (entry.1, pc)) = some table
  | [], _ => rfl
  | e :: rest, htab => by
    have he := htab e (List.mem_cons_self ..)
    have ih := mapM_unrelocate base size rest (fun e' he' => htab e' (List.mem_cons_of_mem _ he'))
    have h1 : base ≤ base + e.2 ∧ base + e.2 < base + size := ⟨Nat.le_add_right _ _, by omega⟩
    simp [h1, Function.comp_def] at ih ⊢
    try simp [ih]

/-- On `jump`/`choose`/`spawn` instructions whose targets land inside the
chunk `[base, base + size)`, `mapExecutableTargets?` with the chunk-relative
target map inverts `relocateInstr base`. Only control instructions are
covered; `invoke` depends on the action model. -/
theorem mapExecutableTargets?_relocate (base size : Nat) (i : Instr γ ε)
    (hctl : (∃ k, i = .jump k) ∨ (∃ chan table, i = .choose chan table) ∨
      (∃ k args, i = .spawn k args))
    (hin : ∀ k, (i = .jump k ∨ (∃ chan table, i = .choose chan table ∧ ∃ l, (l, k) ∈ table) ∨
      ∃ args, i = .spawn k args) → size > k) :
    mapExecutableTargets? (γ:=γ) (ε:=ε)
        (fun pc => if base ≤ pc ∧ pc < base + size then some (pc - base) else none)
        (relocateInstr base i) = some i := by
  rcases hctl with ⟨k, rfl⟩ | ⟨chan, table, rfl⟩ | ⟨k, args, rfl⟩
  · have := hin k (Or.inl rfl)
    simp [relocateInstr, mapExecutableTargets?, this]
  · simp only [relocateInstr, mapExecutableTargets?]
    have htab : ∀ e ∈ table, size > e.2 := fun e he =>
      hin e.2 (Or.inr (Or.inl ⟨chan, table, rfl, e.1, he⟩))
    rw [mapM_unrelocate base size table htab]
    rfl
  · have := hin k (Or.inr (Or.inr ⟨args, rfl⟩))
    simp [relocateInstr, mapExecutableTargets?, this]

end
