import RumpsteakV2.Protocol.Participation.Core


namespace RumpsteakV2.Protocol.Participation
/-! ## Participation and substitution/unfolding

These lemmas show that participation is preserved under unfolding. They are
useful for reasoning about `fullUnfoldIter` in projection proofs. -/

private theorem mem_substituteBranches_iff_forward
    {branches : List (Label × GlobalType)} {t : String} {repl : GlobalType}
    {label : Label} {cont' : GlobalType}
    (hmem : (label, cont') ∈ GlobalType.substituteBranches branches t repl) :
    ∃ cont, cont' = cont.substitute t repl ∧ (label, cont) ∈ branches := by
  -- Forward: substituted membership yields a source branch.
  induction branches with
  | nil =>
      simp [GlobalType.substituteBranches] at hmem
  | cons head tail ih =>
      cases head with
      | mk hlabel hcont =>
          have hmem' :
              (label, cont') = (hlabel, hcont.substitute t repl) ∨
                (label, cont') ∈ GlobalType.substituteBranches tail t repl := by
            simpa [GlobalType.substituteBranches] using (List.mem_cons).1 hmem
          cases hmem' with
          | inl hEq =>
              cases hEq
              exact ⟨hcont, rfl, by simp⟩
          | inr hmemTail =>
              rcases ih hmemTail with ⟨cont, hcont_eq, hmem''⟩
              exact ⟨cont, hcont_eq, by simp [hmem'']⟩

private theorem mem_substituteBranches_iff_backward
    {branches : List (Label × GlobalType)} {t : String} {repl : GlobalType}
    {label : Label} {cont' : GlobalType}
    (hmem : ∃ cont, cont' = cont.substitute t repl ∧ (label, cont) ∈ branches) :
    (label, cont') ∈ GlobalType.substituteBranches branches t repl := by
  -- Backward: source branch gives substituted membership.
  rcases hmem with ⟨cont, hcont_eq, hmem⟩
  induction branches with
  | nil =>
      simp at hmem
  | cons head tail ih =>
      cases head with
      | mk hlabel hcont =>
          have hmem' :
              (label, cont) = (hlabel, hcont) ∨ (label, cont) ∈ tail := by
            simpa using (List.mem_cons).1 hmem
          cases hmem' with
          | inl hEq =>
              cases hEq
              simp [GlobalType.substituteBranches, hcont_eq]
          | inr hmemTail =>
              have hmemSub :
                  (label, cont') ∈ GlobalType.substituteBranches tail t repl :=
                ih hmemTail
              exact List.mem_cons_of_mem _ hmemSub

private theorem mem_substituteBranches_iff
    {branches : List (Label × GlobalType)} {t : String} {repl : GlobalType}
    {label : Label} {cont' : GlobalType} :
    (label, cont') ∈ GlobalType.substituteBranches branches t repl ↔
      ∃ cont, cont' = cont.substitute t repl ∧ (label, cont) ∈ branches := by
  -- Combine forward/backward directions.
  constructor
  · exact mem_substituteBranches_iff_forward
  · exact mem_substituteBranches_iff_backward

private theorem part_of2_substitute_var (role : String) (v t : String) (repl : GlobalType)
    (h : part_of2 role ((GlobalType.var v).substitute t repl)) :
    part_of2 role (.var v) ∨ part_of2 role repl := by
  -- var case: substitution either returns repl or stays var.
  by_cases hvt : v = t
  · right
    simpa [GlobalType.substitute, hvt] using h
  · exact (not_part_of2_var role v (by simpa [GlobalType.substitute, hvt] using h)).elim

private theorem part_of2_substitute_comm (role : String) (sender receiver : String)
    (branches : List (Label × GlobalType)) (t : String) (repl : GlobalType)
    (ih : ∀ cont, part_of2 role (cont.substitute t repl) → part_of2 role cont ∨ part_of2 role repl)
    (h : part_of2 role ((GlobalType.comm sender receiver branches).substitute t repl)) :
    part_of2 role (.comm sender receiver branches) ∨ part_of2 role repl := by
  -- comm case: direct participation or recurse into a branch continuation.
  have hcases := part_of2_comm_inv (role := role)
    (sender := sender) (receiver := receiver) (branches := GlobalType.substituteBranches branches t repl) h
  cases hcases with
  | inl hpart =>
      left
      exact .intro _ (.comm_direct _ _ _ hpart)
  | inr hbranch =>
      rcases hbranch with ⟨label, cont', hmem, hcont'⟩
      rcases (mem_substituteBranches_iff.mp hmem) with ⟨cont, hcont_eq, hmem'⟩
      have hcont_subst : part_of2 role (cont.substitute t repl) := by
        simpa [hcont_eq] using hcont'
      cases ih cont hcont_subst with
      | inl hcont =>
          left
          exact .intro _ (.comm_branch _ _ label cont branches hmem' hcont)
      | inr hrepl =>
          right
          exact hrepl

private theorem part_of2_substitute_mu (role : String) (s : String) (body : GlobalType)
    (t : String) (repl : GlobalType)
    (ih : part_of2 role (body.substitute t repl) → part_of2 role body ∨ part_of2 role repl)
    (h : part_of2 role ((GlobalType.mu s body).substitute t repl)) :
    part_of2 role (.mu s body) ∨ part_of2 role repl := by
  -- mu case: shadowed substitution or recurse into body.
  by_cases hst : s = t
  · left
    simpa [GlobalType.substitute, hst] using h
  · have hbody : part_of2 role (body.substitute t repl) := by
      have hmu : part_of2 role (.mu s (body.substitute t repl)) := by
        simpa [GlobalType.substitute, hst] using h
      exact part_of2_mu_inv hmu
    cases ih hbody with
    | inl hbody_part =>
        left
        exact .intro _ (.mu _ _ hbody_part)
    | inr hrepl =>
        right
        exact hrepl

theorem part_of2_substitute (role : String) :
    ∀ g t repl, part_of2 role (g.substitute t repl) →
      part_of2 role g ∨ part_of2 role repl := by
  -- Structural recursion on g with explicit comm/mu cases.
  intro g t repl h
  match g with
  | .end =>
      exact (not_part_of2_end role h).elim
  | .var v =>
      exact part_of2_substitute_var role v t repl h
  | .comm sender receiver branches =>
      have ih : ∀ cont, part_of2 role (cont.substitute t repl) →
          part_of2 role cont ∨ part_of2 role repl :=
        fun cont hcont => part_of2_substitute role cont t repl hcont
      exact part_of2_substitute_comm role sender receiver branches t repl ih h
  | .mu s body =>
      have ih : part_of2 role (body.substitute t repl) →
          part_of2 role body ∨ part_of2 role repl :=
        fun hbody => part_of2_substitute role body t repl hbody
      exact part_of2_substitute_mu role s body t repl ih h
termination_by g _ _ _ => sizeOf g
decreasing_by
  all_goals
    simp_wf
    all_goals
      first
      | (simpa [GlobalType.comm.sizeOf_spec] using
          (sizeOf_elem_snd_lt_comm _ _ _ _ (by assumption)))
      | (simp only [sizeOf, GlobalType._sizeOf_1] at *; omega)

theorem part_of2_unfold (role : String) (g : GlobalType) :
    part_of2 role (GlobalType.unfold g) → part_of2 role g := by
  cases g with
  | «end» =>
      intro h
      simpa [GlobalType.unfold] using h
  | var v =>
      intro h
      simpa [GlobalType.unfold] using h
  | comm sender receiver branches =>
      intro h
      simpa [GlobalType.unfold] using h
  | mu t body =>
      intro h
      have hsub : part_of2 role (body.substitute t (.mu t body)) := by
        simpa [GlobalType.unfold] using h
      have hcases := part_of2_substitute role body t (.mu t body) hsub
      cases hcases with
      | inl hbody =>
          exact .intro _ (.mu _ _ hbody)
      | inr hmu =>
          exact hmu

theorem part_of2_unfold_iter (role : String) (g : GlobalType) :
    ∀ n, part_of2 role (Nat.rec g (fun _ acc => GlobalType.unfold acc) n) → part_of2 role g := by
  intro n
  induction n generalizing g with
  | zero =>
      intro h
      simpa using h
  | succ n ih =>
      intro h
      have h' : part_of2 role (GlobalType.unfold (Nat.rec g (fun _ acc => GlobalType.unfold acc) n)) := by
        simpa using h
      have h'' : part_of2 role (Nat.rec g (fun _ acc => GlobalType.unfold acc) n) :=
        part_of2_unfold role (Nat.rec g (fun _ acc => GlobalType.unfold acc) n) h'
      exact ih (g := g) h''

theorem part_of2_fullUnfoldIter (role : String) (g : GlobalType) :
    part_of2 role (GlobalType.fullUnfoldIter g) → part_of2 role g := by
  simpa [GlobalType.fullUnfoldIter] using
    (part_of2_unfold_iter role g g.muHeight)

theorem not_part_of2_fullUnfoldIter (role : String) (g : GlobalType)
    (h : ¬ part_of2 role g) : ¬ part_of2 role (GlobalType.fullUnfoldIter g) := by
  intro hfull
  exact h (part_of2_fullUnfoldIter role g hfull)

/-! ## Classification: participant or non-participant

This is the key lemma used in projection proofs. For closed, well-formed
global types, a role either:
1. Participates (part_of_all2 holds), or
2. Does not participate (and trans projects to EEnd)

Note: This requires well-formedness and closedness assumptions in the
full proof. We provide a simpler decidable version for finite global types. -/

mutual
  /-- Decidable participation check (for finite, unguarded global types).
      For recursive types, this only checks the body once to avoid divergence. -/
  def participates (role : String) : GlobalType → Bool
    | .end => false
    | .var _ => false
    | .mu _ body => participates role body
    | .comm sender receiver branches =>
        is_participant role sender receiver ||
        participatesBranches role branches

  /-- Helper for participates on branches. -/
  def participatesBranches (role : String) : List (Label × GlobalType) → Bool
    | [] => false
    | (_, cont) :: rest =>
        participates role cont || participatesBranches role rest
end

/-! ## Boolean participation equivalence -/

mutual
  private theorem part_of2_iff_participates_comm (role sender receiver : String)
      (branches : List (Label × GlobalType)) :
      part_of2 role (.comm sender receiver branches) ↔
        participates role (.comm sender receiver branches) = true := by
    constructor  -- comm case: direct participant or a participating branch
    · intro h
      cases part_of2_comm_inv (role := role) (sender := sender) (receiver := receiver)
          (branches := branches) h with
      | inl hpart =>
          have hpart' : is_participant role sender receiver = true := by
            simpa using hpart
          simp [participates, hpart']
      | inr hbranch =>
          obtain ⟨label, cont, hmem, hcont⟩ := hbranch
          have hbranches : participatesBranches role branches = true :=
            (participatesBranches_iff_part_of2 role branches).2 ⟨(label, cont), hmem, hcont⟩
          simp [participates, hbranches]
    · intro h
      simp [participates] at h
      cases h with
      | inl hpart =>
          exact .intro _ (.comm_direct _ _ _ hpart)
      | inr hbranches =>
          rcases (participatesBranches_iff_part_of2 role branches).1 hbranches with
            ⟨pair, hmem, hcont⟩
          exact .intro _ (.comm_branch _ _ pair.1 pair.2 _ hmem hcont)

  /-- `participates` is equivalent to `part_of2`. -/
  theorem part_of2_iff_participates (role : String) :
      ∀ g, part_of2 role g ↔ participates role g = true := by
    intro g
    cases g with
    | «end» =>
        constructor
        · intro h; exact (not_part_of2_end role h).elim
        · intro h; simp [participates] at h
    | var t =>
        constructor
        · intro h; exact (not_part_of2_var role t h).elim
        · intro h; simp [participates] at h
    | mu t body =>
        constructor
        · intro h
          have hbody : part_of2 role body := part_of2_mu_inv (t := t) h
          have ih := (part_of2_iff_participates role body).1 hbody
          simpa [participates] using ih
        · intro h
          simp [participates] at h
          have hbody : part_of2 role body :=
            (part_of2_iff_participates role body).2 h
          exact .intro _ (.mu _ _ hbody)
    | comm sender receiver branches =>
        exact part_of2_iff_participates_comm role sender receiver branches

  private theorem participatesBranches_iff_part_of2_cons (role : String)
      (label : Label) (cont : GlobalType) (tl : List (Label × GlobalType)) :
      participatesBranches role ((label, cont) :: tl) = true ↔
        ∃ pair, pair ∈ ((label, cont) :: tl) ∧ part_of2 role pair.2 := by
    constructor  -- cons case: head or tail contributes a participating continuation
    · intro h
      simp [participatesBranches, Bool.or_eq_true] at h
      cases h with
      | inl hcont =>
          exact ⟨(label, cont), by simp, (part_of2_iff_participates role cont).2 hcont⟩
      | inr hrest =>
          rcases (participatesBranches_iff_part_of2 role tl).1 hrest with ⟨pair, hmem, hpo⟩
          exact ⟨pair, by simp [hmem], hpo⟩
    · intro h
      obtain ⟨pair, hmem, hpo⟩ := h
      simp [participatesBranches]
      cases (List.mem_cons).1 hmem with
      | inl hEq =>
          cases hEq
          have hcont : participates role cont = true :=
            (part_of2_iff_participates role cont).1 hpo
          exact Or.inl hcont
      | inr hmemTail =>
          have hrest : participatesBranches role tl = true :=
            (participatesBranches_iff_part_of2 role tl).2 ⟨pair, hmemTail, hpo⟩
          exact Or.inr hrest

  /-- `participatesBranches` is equivalent to existence of a participating branch. -/
  theorem participatesBranches_iff_part_of2 (role : String) :
      ∀ branches,
        participatesBranches role branches = true ↔
          ∃ pair, pair ∈ branches ∧ part_of2 role pair.2 := by
    intro branches
    cases branches with
    | nil =>
        simp [participatesBranches]
    | cons hd tl =>
        obtain ⟨label, cont⟩ := hd
        exact participatesBranches_iff_part_of2_cons role label cont tl
end

theorem participates_comm_iff {role sender receiver : String} {branches : List (Label × GlobalType)} :
    participates role (.comm sender receiver branches) =
      (is_participant role sender receiver || participatesBranches role branches) := by
  rfl

theorem participates_mu_iff {role t : String} {body : GlobalType} :
    participates role (.mu t body) = participates role body := by
  rfl

/-- If participates returns false, the role is not a direct participant. -/
theorem not_participates_imp_not_participant {role sender receiver : String}
    {branches : List (Label × GlobalType)}
    (h : participates role (.comm sender receiver branches) = false) :
    ¬ is_participant role sender receiver := by
  simp only [participates, Bool.or_eq_false_iff] at h
  exact Bool.eq_false_iff.mp h.1

end RumpsteakV2.Protocol.Participation
