import Runtime.Adequacy.CompileRefinesSpec

/-! # Runtime.Adequacy.CompileRefinesInvariants

Program-counter invariants of the compiler specification `Impl`:

* the loop environment only grows (`Impl.env_sub`) and every new binding is a
  `mu` binder PC inside the emitted block (`Impl.env_new`);
* every `jump` in a block targets a recorded binder (`Impl.jump_mem`), hence
  lies inside the block when the incoming environment is empty (`Impl.jump_lt`);
* every `choose` table entry points inside the block (`Impl.choose_bounded`).
-/

/-
The Problem. Relocation (`CodeImage.fromLocalTypes`) and role splitting
(`toRoleCodeImage`) are only meaningful if control targets stay inside the
block they were compiled in; this has to be a theorem about the specification,
not a property checked at load time.

Solution Structure. Each invariant is proved by mutual structural recursion on
`Impl`/`ImplBranches`, with `Impl.length_pos` supplying the strictness needed
for the bounds.
-/

set_option autoImplicit false

universe u

open SessionTypes.LocalTypeR

section

variable {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
  {d : EffectRuntime.EffectAction ε}

/-! ## Loop environment -/

mutual
  /-- The loop environment only grows. -/
  theorem Impl.env_sub {pc : Nat} {env env' : List (String × PC)} {t : LocalTypeR}
      {is : List (Instr γ ε)} (h : Impl d pc env t is env') : ∀ x, x ∈ env → x ∈ env' :=
    match h with
    | .done | .sendNil | .recvNil | .varFree _ | .varBound _ => fun _ hx => hx
    | .send h' | .offerMulti h' | .recv h' => h'.env_sub
    | .mu h' => fun x hx => h'.env_sub x (List.mem_cons_of_mem _ hx)
    | .chooseMany h₁ h₂ hR => fun x hx => hR.env_sub x (h₂.env_sub x (h₁.env_sub x hx))

  /-- The loop environment only grows across a branch tail. -/
  theorem ImplBranches.env_sub {pc : Nat} {env env' : List (String × PC)} {bs : List BranchR}
      {is : List (Instr γ ε)} {table : List (String × PC)}
      (h : ImplBranches d pc env bs is table env') : ∀ x, x ∈ env → x ∈ env' :=
    match h with
    | .nil => fun _ hx => hx
    | .cons h₁ hR => fun x hx => hR.env_sub x (h₁.env_sub x hx)
end

/-- Shifting the bound by two instructions in front. -/
theorem Impl.env_new_shift2 {pc : Nat} {env env' : List (String × PC)} {t : LocalTypeR}
    {is : List (Instr γ ε)} (h : Impl d (pc + 2) env t is env')
    (hrec : ∀ x ∈ env', x ∈ env ∨ (pc + 2 ≤ x.2 ∧ pc + 2 + is.length > x.2))
    {a b : Instr γ ε} :
    ∀ x ∈ env', x ∈ env ∨ (pc ≤ x.2 ∧ pc + (a :: b :: is).length > x.2) := by
  intro x hx
  rcases hrec x hx with hx | hb
  · exact Or.inl hx
  · right; simp only [List.length_cons]; omega

/-- Shifting the bound by one instruction in front. -/
theorem Impl.env_new_shift1 {pc : Nat} {env env' : List (String × PC)} {t : LocalTypeR}
    {is : List (Instr γ ε)} (h : Impl d (pc + 1) env t is env')
    (hrec : ∀ x ∈ env', x ∈ env ∨ (pc + 1 ≤ x.2 ∧ pc + 1 + is.length > x.2))
    {a : Instr γ ε} :
    ∀ x ∈ env', x ∈ env ∨ (pc ≤ x.2 ∧ pc + (a :: is).length > x.2) := by
  intro x hx
  rcases hrec x hx with hx | hb
  · exact Or.inl hx
  · right; simp only [List.length_cons]; omega

mutual
  /-- Every binding in the output environment is either inherited or a `mu`
  binder PC inside the emitted block. -/
  theorem Impl.env_new {pc : Nat} {env env' : List (String × PC)} {t : LocalTypeR}
      {is : List (Instr γ ε)} (h : Impl d pc env t is env') :
      ∀ x ∈ env', x ∈ env ∨ (pc ≤ x.2 ∧ pc + is.length > x.2) :=
    match h with
    | .done | .sendNil | .recvNil | .varFree _ | .varBound _ => fun _ hx => Or.inl hx
    | .send h' => Impl.env_new_shift2 h' h'.env_new
    | .recv h' => Impl.env_new_shift2 h' h'.env_new
    | .offerMulti h' => Impl.env_new_shift1 h' h'.env_new
    | .mu h' => fun x hx => by
        have hpos := h'.length_pos
        rcases h'.env_new x hx with hx | hb
        · rcases List.mem_cons.mp hx with rfl | hx
          · right; simp only; omega
          · exact Or.inl hx
        · exact Or.inr hb
    | .chooseMany h₁ h₂ hR => fun x hx => by
        simp only [List.length_cons, List.length_append]
        rcases hR.env_new x hx with hx | hb
        · rcases h₂.env_new x hx with hx | hb
          · rcases h₁.env_new x hx with hx | hb
            · exact Or.inl hx
            · right; omega
          · right; omega
        · right; omega

  /-- Every binding produced by a branch tail is inherited or lies inside it. -/
  theorem ImplBranches.env_new {pc : Nat} {env env' : List (String × PC)} {bs : List BranchR}
      {is : List (Instr γ ε)} {table : List (String × PC)}
      (h : ImplBranches d pc env bs is table env') :
      ∀ x ∈ env', x ∈ env ∨ (pc ≤ x.2 ∧ pc + is.length > x.2) :=
    match h with
    | .nil => fun _ hx => Or.inl hx
    | .cons h₁ hR => fun x hx => by
        simp only [List.length_append]
        rcases hR.env_new x hx with hx | hb
        · rcases h₁.env_new x hx with hx | hb
          · exact Or.inl hx
          · right; omega
        · right; omega
end

/-! ## Jump targets -/

mutual
  /-- Every `jump` in a block targets a recorded binder PC. -/
  theorem Impl.jump_mem {pc : Nat} {env env' : List (String × PC)} {t : LocalTypeR}
      {is : List (Instr γ ε)} (h : Impl d pc env t is env') :
      ∀ k, Instr.jump k ∈ is → ∃ v, (v, k) ∈ env' :=
    match h with
    | .done | .sendNil | .recvNil | .varFree _ => fun k hk => by simp at hk
    | .varBound hf => fun k hk => by
        simp only [List.mem_singleton, Instr.jump.injEq] at hk
        subst hk
        exact ⟨_, List.mem_of_find?_eq_some hf⟩
    | .send h' => fun k hk => h'.jump_mem k (by simpa using hk)
    | .recv h' => fun k hk => h'.jump_mem k (by simpa using hk)
    | .offerMulti h' => fun k hk => h'.jump_mem k (by simpa using hk)
    | .mu h' => h'.jump_mem
    | .chooseMany (is₁ := is₁) (is₂ := is₂) (isR := isR) h₁ h₂ hR => fun k hk => by
        have hk' : Instr.jump k ∈ is₁ ++ is₂ ++ isR := by simpa using hk
        rcases List.mem_append.mp hk' with hk | hk
        rcases List.mem_append.mp hk with hk | hk
        · obtain ⟨v, hv⟩ := h₁.jump_mem k hk
          exact ⟨v, hR.env_sub _ (h₂.env_sub _ hv)⟩
        · obtain ⟨v, hv⟩ := h₂.jump_mem k hk
          exact ⟨v, hR.env_sub _ hv⟩
        · exact hR.jump_mem k hk

  /-- Every `jump` in a branch tail targets a recorded binder PC. -/
  theorem ImplBranches.jump_mem {pc : Nat} {env env' : List (String × PC)} {bs : List BranchR}
      {is : List (Instr γ ε)} {table : List (String × PC)}
      (h : ImplBranches d pc env bs is table env') :
      ∀ k, Instr.jump k ∈ is → ∃ v, (v, k) ∈ env' :=
    match h with
    | .nil => fun k hk => by simp at hk
    | .cons h₁ hR => fun k hk => by
        rcases List.mem_append.mp hk with hk | hk
        · obtain ⟨v, hv⟩ := h₁.jump_mem k hk
          exact ⟨v, hR.env_sub _ hv⟩
        · exact hR.jump_mem k hk
end

/-- With an empty incoming environment, every `jump` target is a `mu` binder
PC inside the block. -/
theorem Impl.jump_lt {pc : Nat} {env' : List (String × PC)} {t : LocalTypeR}
    {is : List (Instr γ ε)} (h : Impl d pc [] t is env') {k : PC}
    (hk : Instr.jump k ∈ is) : pc ≤ k ∧ pc + is.length > k := by
  obtain ⟨v, hv⟩ := h.jump_mem k hk
  rcases h.env_new _ hv with hx | hb
  · simp at hx
  · exact hb

/-! ## Choose tables -/

/-- Every table entry produced by a branch tail points inside the tail. -/
theorem ImplBranches.table_bounded {pc : Nat} {env env' : List (String × PC)}
    {bs : List BranchR} {is : List (Instr γ ε)} {table : List (String × PC)}
    (h : ImplBranches d pc env bs is table env') :
    ∀ e ∈ table, pc ≤ e.2 ∧ pc + is.length > e.2 := by
  induction bs generalizing pc env is table with
  | nil => cases h; simp
  | cons b rest ih =>
    cases h with
    | cons h₁ hR =>
      intro e he
      have hpos := h₁.length_pos
      simp only [List.length_append]
      rcases List.mem_cons.mp he with rfl | he
      · simp only; omega
      · have := ih hR e he; omega

/-- Choose bounds survive two non-`choose` instructions in front. -/
theorem Impl.choose_bounded_shift2 {pc : Nat} {env env' : List (String × PC)} {t : LocalTypeR}
    {is : List (Instr γ ε)} (h : Impl d (pc + 2) env t is env')
    (hrec : ∀ chan table, Instr.choose chan table ∈ is →
      ∀ e ∈ table, pc + 2 ≤ e.2 ∧ pc + 2 + is.length > e.2)
    {a b : Instr γ ε} (ha : ∀ chan table, a ≠ Instr.choose chan table)
    (hb : ∀ chan table, b ≠ Instr.choose chan table) :
    ∀ chan table, Instr.choose chan table ∈ a :: b :: is →
      ∀ e ∈ table, pc ≤ e.2 ∧ pc + (a :: b :: is).length > e.2 := by
  intro chan table hm e he
  simp only [List.length_cons]
  rcases List.mem_cons.mp hm with hm | hm
  · exact absurd hm.symm (ha chan table)
  rcases List.mem_cons.mp hm with hm | hm
  · exact absurd hm.symm (hb chan table)
  · have := hrec chan table hm e he; omega

/-- Choose bounds survive one non-`choose` instruction in front. -/
theorem Impl.choose_bounded_shift1 {pc : Nat} {env env' : List (String × PC)} {t : LocalTypeR}
    {is : List (Instr γ ε)} (h : Impl d (pc + 1) env t is env')
    (hrec : ∀ chan table, Instr.choose chan table ∈ is →
      ∀ e ∈ table, pc + 1 ≤ e.2 ∧ pc + 1 + is.length > e.2)
    {a : Instr γ ε} (ha : ∀ chan table, a ≠ Instr.choose chan table) :
    ∀ chan table, Instr.choose chan table ∈ a :: is →
      ∀ e ∈ table, pc ≤ e.2 ∧ pc + (a :: is).length > e.2 := by
  intro chan table hm e he
  simp only [List.length_cons]
  rcases List.mem_cons.mp hm with hm | hm
  · exact absurd hm.symm (ha chan table)
  · have := hrec chan table hm e he; omega

mutual
  /-- Every `choose` table entry in a block points inside the block. -/
  theorem Impl.choose_bounded {pc : Nat} {env env' : List (String × PC)} {t : LocalTypeR}
      {is : List (Instr γ ε)} (h : Impl d pc env t is env') :
      ∀ chan table, Instr.choose chan table ∈ is →
        ∀ e ∈ table, pc ≤ e.2 ∧ pc + is.length > e.2 :=
    match h with
    | .done | .sendNil | .recvNil | .varFree _ | .varBound _ => fun _ _ hm => by simp at hm
    | .send h' => Impl.choose_bounded_shift2 h' h'.choose_bounded (by simp) (by simp)
    | .recv h' => Impl.choose_bounded_shift2 h' h'.choose_bounded (by simp) (by simp)
    | .offerMulti h' => Impl.choose_bounded_shift1 h' h'.choose_bounded (by simp)
    | .mu h' => h'.choose_bounded
    | .chooseMany h₁ h₂ hR => fun chan table hm e he => by
        have hpos₁ := h₁.length_pos
        have hpos₂ := h₂.length_pos
        simp only [List.length_cons, List.length_append]
        simp only [List.mem_cons, reduceCtorEq, false_or, Instr.choose.injEq,
          List.mem_append] at hm
        rcases hm with ⟨_, rfl⟩ | (hm | hm) | hm
        · rcases List.mem_cons.mp he with rfl | he
          · simp only; omega
          rcases List.mem_cons.mp he with rfl | he
          · simp only; omega
          · have := hR.table_bounded e he; omega
        · have := h₁.choose_bounded chan table hm e he; omega
        · have := h₂.choose_bounded chan table hm e he; omega
        · have := hR.choose_bounded chan table hm e he; omega

  /-- Every `choose` table entry in a branch tail points inside the tail. -/
  theorem ImplBranches.choose_bounded {pc : Nat} {env env' : List (String × PC)}
      {bs : List BranchR} {is : List (Instr γ ε)} {table : List (String × PC)}
      (h : ImplBranches d pc env bs is table env') :
      ∀ chan table', Instr.choose chan table' ∈ is →
        ∀ e ∈ table', pc ≤ e.2 ∧ pc + is.length > e.2 :=
    match h with
    | .nil => fun _ _ hm => by simp at hm
    | .cons h₁ hR => fun chan table' hm e he => by
        simp only [List.length_append]
        rcases List.mem_append.mp hm with hm | hm
        · have := h₁.choose_bounded chan table' hm e he; omega
        · have := hR.choose_bounded chan table' hm e he; omega
end

end
