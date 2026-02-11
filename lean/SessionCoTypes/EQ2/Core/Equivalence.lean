import SessionCoTypes.EQ2.Core.Foundations

/-! # SessionCoTypes.EQ2.Core.Equivalence

Equivalence-oriented theorems for EQ2.
-/

/-
The Problem. Proofs using EQ2 usually need reflexivity/symmetry/transitivity
interfaces, while the fixed-point construction details live elsewhere.

Solution Structure. Keeps equivalence-property proofs in a focused module that
reuses the foundational EQ2 infrastructure.
-/

set_option linter.dupNamespace false
set_option linter.unusedTactic false

namespace SessionCoTypes.EQ2

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionCoTypes.CoinductiveRel

/-! ## Equivalence Properties -/

/-! ## Equivalence Properties -/

/-- BranchesRel is reflexive when the underlying relation is. -/
private theorem BranchesRel_refl {R : Rel} (hrefl : ∀ t, R t t) :
    ∀ bs, BranchesRel R bs bs := by
  intro bs
  induction bs with
  | nil => exact List.Forall₂.nil
  | cons head tail ih =>
      exact List.Forall₂.cons ⟨rfl, hrefl head.2.2⟩ ih

/-- BranchesRel is symmetric when the underlying relation is. -/
private theorem BranchesRel_symm {R : Rel}
    (hsymm : ∀ a b, R a b → R b a) :
    ∀ {bs cs}, BranchesRel R bs cs → BranchesRel R cs bs := by
  intro bs cs hrel
  induction hrel with
  | nil => exact List.Forall₂.nil
  | cons h _ ih =>
      exact List.Forall₂.cons ⟨h.1.symm, hsymm _ _ h.2⟩ ih

/-- BranchesRel is transitive when the underlying relation is. -/
private theorem BranchesRel_trans {R : Rel}
    (htrans : ∀ a b c, R a b → R b c → R a c) :
    ∀ {as bs cs}, BranchesRel R as bs → BranchesRel R bs cs → BranchesRel R as cs := by
  intro as bs cs hab hbc
  induction hab generalizing cs with
  | nil =>
      cases hbc
      exact List.Forall₂.nil
  | cons h _ ih =>
      cases hbc with
      | cons h' hbc' =>
          exact List.Forall₂.cons ⟨h.1.trans h'.1, htrans _ _ _ h.2 h'.2⟩ (ih hbc')

/-- Helper: construct EQ2 for mu from unfolding pairs. -/
private theorem EQ2_construct_mu (t : String) (body : LocalTypeR)
    (h1 : EQ2 (body.substitute t (.mu t body)) (.mu t body))
    (h2 : EQ2 (.mu t body) (body.substitute t (.mu t body))) :
    EQ2 (.mu t body) (.mu t body) := by
  have hfix : EQ2F EQ2 = EQ2 := EQ2_fixed
  have hf : EQ2F EQ2 (.mu t body) (.mu t body) := by
    simp only [EQ2F]
    exact ⟨h1, h2⟩
  exact Eq.mp (congrArg (fun R => R (.mu t body) (.mu t body)) hfix) hf

/-- Coinductive relation for reflexivity: diagonal plus unfolding pairs. -/
private def ReflRel : Rel := fun a b =>
  ∃ c n m, a = (LocalTypeR.unfold^[n]) c ∧ b = (LocalTypeR.unfold^[m]) c

private def NonMu (a : LocalTypeR) : Prop := ∀ t body, a ≠ .mu t body

private theorem nonmu_end : NonMu (.end : LocalTypeR) := by
  intro t body h; cases h

private theorem nonmu_var (v : String) : NonMu (.var v : LocalTypeR) := by
  intro t body h; cases h

private theorem nonmu_send (p : String) (bs : List BranchR) :
    NonMu (.send p bs : LocalTypeR) := by
  intro t body h; cases h

private theorem nonmu_recv (p : String) (bs : List BranchR) :
    NonMu (.recv p bs : LocalTypeR) := by
  intro t body h; cases h

private theorem unfold_iter_eq_of_nonmu (a : LocalTypeR) (h : NonMu a) :
    ∀ n, (LocalTypeR.unfold^[n]) a = a := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have hfix : LocalTypeR.unfold a = a := LocalTypeR.unfold_non_mu a h
      simp [Function.iterate_succ_apply', hfix, ih]

private theorem ReflRel_unfold_left {a b : LocalTypeR} (h : ReflRel a b) :
    ReflRel (LocalTypeR.unfold a) b := by
  rcases h with ⟨c, n, m, ha, hb⟩
  refine ⟨c, n + 1, m, ?_, hb⟩
  simp [ha, Function.iterate_succ_apply']

private theorem ReflRel_unfold_right {a b : LocalTypeR} (h : ReflRel a b) :
    ReflRel a (LocalTypeR.unfold b) := by
  rcases h with ⟨c, n, m, ha, hb⟩
  refine ⟨c, n, m + 1, ha, ?_⟩
  simp [hb, Function.iterate_succ_apply']

private theorem ReflRel_eq_of_nonmu {a b : LocalTypeR} (ha : NonMu a) (hb : NonMu b)
    (h : ReflRel a b) : a = b := by
  rcases h with ⟨c, n, m, ha', hb'⟩
  cases le_total n m with
  | inl hnm =>
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnm
      have hb'' : b = (LocalTypeR.unfold^[k]) ((LocalTypeR.unfold^[n]) c) := by
        calc
          b = (LocalTypeR.unfold^[m]) c := hb'
          _ = (LocalTypeR.unfold^[k + n]) c := by simp [hk, Nat.add_comm]
          _ = (LocalTypeR.unfold^[k]) ((LocalTypeR.unfold^[n]) c) := by
                simpa using
                  (Function.iterate_add_apply (f := LocalTypeR.unfold) k n c)
      have hb''' : b = (LocalTypeR.unfold^[k]) a := by simpa [ha'] using hb''
      have hfix : (LocalTypeR.unfold^[k]) a = a := unfold_iter_eq_of_nonmu a ha k
      have hb'''' : b = a := by simpa [hfix] using hb'''
      simpa using hb''''.symm
  | inr hmn =>
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmn
      have ha'' : a = (LocalTypeR.unfold^[k]) ((LocalTypeR.unfold^[m]) c) := by
        calc
          a = (LocalTypeR.unfold^[n]) c := ha'
          _ = (LocalTypeR.unfold^[k + m]) c := by simp [hk, Nat.add_comm]
          _ = (LocalTypeR.unfold^[k]) ((LocalTypeR.unfold^[m]) c) := by
                simpa using
                  (Function.iterate_add_apply (f := LocalTypeR.unfold) k m c)
      have ha''' : a = (LocalTypeR.unfold^[k]) b := by simpa [hb'] using ha''
      have hfix : (LocalTypeR.unfold^[k]) b = b := unfold_iter_eq_of_nonmu b hb k
      have ha'''' : a = b := by simpa [hfix] using ha'''
      exact ha''''

/-- ReflRel is a post-fixpoint of EQ2F.

This lemma encapsulates the coinductive reasoning for reflexivity. The proof requires
"coinduction up-to" techniques (as in Coq's paco library) because:

1. For mu types, EQ2F requires unfolding pairs to be in the relation
2. When `body.substitute t (mu t body)` is itself a mu, we get nested unfoldings
3. The nested case requires showing ReflRel holds for pairs that aren't directly
   in the definition (e.g., unfolding of an unfolding paired with the original)

The lemma is semantically sound because:
- EQ2 represents observational equality of infinite trees
- Any type is observationally equal to itself
- Unfolding a mu produces the same observations as the mu itself

Proving this constructively in Lean would require:
- Coinduction up-to equivalence (parametrized coinduction)
- Or a more sophisticated relation that captures transitive unfolding -/
private theorem ReflRel_postfix : ∀ a b, ReflRel a b → EQ2F ReflRel a b := by
  intro a b h
  have hrefl : ∀ t, ReflRel t t := fun t => ⟨t, 0, 0, rfl, rfl⟩
  cases a with
  | «end» =>
      cases b with
      | «end» => simp [EQ2F]
      | var v =>
          have hEq := ReflRel_eq_of_nonmu nonmu_end (nonmu_var v) h
          cases hEq
      | send p bs =>
          have hEq := ReflRel_eq_of_nonmu nonmu_end (nonmu_send p bs) h
          cases hEq
      | recv p bs =>
          have hEq := ReflRel_eq_of_nonmu nonmu_end (nonmu_recv p bs) h
          cases hEq
      | mu t body =>
          simpa [EQ2F] using (ReflRel_unfold_right h)
  | var x =>
      cases b with
      | «end» =>
          have hEq := ReflRel_eq_of_nonmu (nonmu_var x) nonmu_end h
          cases hEq
      | var y =>
          have hEq := ReflRel_eq_of_nonmu (nonmu_var x) (nonmu_var y) h
          cases hEq
          simp [EQ2F]
      | send p bs =>
          have hEq := ReflRel_eq_of_nonmu (nonmu_var x) (nonmu_send p bs) h
          cases hEq
      | recv p bs =>
          have hEq := ReflRel_eq_of_nonmu (nonmu_var x) (nonmu_recv p bs) h
          cases hEq
      | mu t body =>
          simpa [EQ2F] using (ReflRel_unfold_right h)
  | send p bs =>
      cases b with
      | «end» =>
          have hEq := ReflRel_eq_of_nonmu (nonmu_send p bs) nonmu_end h
          cases hEq
      | var y =>
          have hEq := ReflRel_eq_of_nonmu (nonmu_send p bs) (nonmu_var y) h
          cases hEq
      | send q cs =>
          have hEq := ReflRel_eq_of_nonmu (nonmu_send p bs) (nonmu_send q cs) h
          cases hEq
          have hbr : BranchesRel ReflRel bs bs :=
            BranchesRel_refl (R := ReflRel) hrefl bs
          exact ⟨rfl, hbr⟩
      | recv q cs =>
          have hEq := ReflRel_eq_of_nonmu (nonmu_send p bs) (nonmu_recv q cs) h
          cases hEq
      | mu t body =>
          simpa [EQ2F] using (ReflRel_unfold_right h)
  | recv p bs =>
      cases b with
      | «end» =>
          have hEq := ReflRel_eq_of_nonmu (nonmu_recv p bs) nonmu_end h
          cases hEq
      | var y =>
          have hEq := ReflRel_eq_of_nonmu (nonmu_recv p bs) (nonmu_var y) h
          cases hEq
      | send q cs =>
          have hEq := ReflRel_eq_of_nonmu (nonmu_recv p bs) (nonmu_send q cs) h
          cases hEq
      | recv q cs =>
          have hEq := ReflRel_eq_of_nonmu (nonmu_recv p bs) (nonmu_recv q cs) h
          cases hEq
          have hbr : BranchesRel ReflRel bs bs :=
            BranchesRel_refl (R := ReflRel) hrefl bs
          exact ⟨rfl, hbr⟩
      | mu t body =>
          simpa [EQ2F] using (ReflRel_unfold_right h)
  | mu t body =>
      cases b with
      | «end» =>
          simpa [EQ2F] using (ReflRel_unfold_left h)
      | var y =>
          simpa [EQ2F] using (ReflRel_unfold_left h)
      | send q cs =>
          simpa [EQ2F] using (ReflRel_unfold_left h)
      | recv q cs =>
          simpa [EQ2F] using (ReflRel_unfold_left h)
      | mu s body' =>
          simp [EQ2F]
          exact ⟨ReflRel_unfold_left h, ReflRel_unfold_right h⟩

/-- EQ2 is reflexive.

This proof uses coinduction on the relation ReflRel which captures the diagonal
plus unfolding pairs. The post-fixpoint property ReflRel_postfix encapsulates
the coinductive reasoning required for the mu case. -/
theorem EQ2_refl : ∀ t, EQ2 t t := by
  intro t
  have hinR : ReflRel t t := ⟨t, 0, 0, rfl, rfl⟩
  exact EQ2_coind ReflRel_postfix t t hinR

/-- Coinductive relation for symmetry: swap arguments of EQ2. -/
private def SymmRel : Rel := fun a b => EQ2 b a

/-- Convert BranchesRel EQ2 cs bs to BranchesRel SymmRel bs cs.
    Note: SymmRel a b = EQ2 b a, so BranchesRel SymmRel bs cs requires EQ2 c.2 b.2
    which is exactly what BranchesRel EQ2 cs bs provides. -/
private theorem BranchesRel_EQ2_to_SymmRel :
    ∀ {bs cs}, BranchesRel EQ2 cs bs → BranchesRel SymmRel bs cs := by
  intro bs cs hrel
  induction hrel with
  | nil => exact List.Forall₂.nil
  | cons h _ ih =>
      apply List.Forall₂.cons
      · exact ⟨h.1.symm, h.2⟩  -- SymmRel b.2 c.2 = EQ2 c.2 b.2 = h.2
      · exact ih

/-- SymmRel is a post-fixpoint of EQ2F. -/
private theorem SymmRel_postfix : ∀ a b, SymmRel a b → EQ2F SymmRel a b := by
  intro a b h
  have hba : EQ2 b a := h
  have hf : EQ2F EQ2 b a := EQ2_destruct hba
  -- Now we need to transform EQ2F EQ2 b a into EQ2F SymmRel a b
  -- Note: SymmRel a b = EQ2 b a, so EQ2F SymmRel a b needs R-relations where R = SymmRel
  cases a <;> cases b <;> simp only [EQ2F] at hf ⊢
  -- Most cases: hf already has the right form or needs swapping
  all_goals
    first
    | exact hf                                                    -- trivial (True) or direct match
    | exact hf.symm                                               -- var.var: need name equality swap
    | (obtain ⟨h1, h2⟩ := hf; exact ⟨h2, h1⟩)                     -- mu.mu: swap the two conjuncts
    | (obtain ⟨h1, h2⟩ := hf;                                     -- send/recv: partner + branches
       exact ⟨h1.symm, BranchesRel_EQ2_to_SymmRel h2⟩)

/-- EQ2 is symmetric. -/
theorem EQ2_symm {a b : LocalTypeR} (h : EQ2 a b) : EQ2 b a := by
  have hinR : SymmRel b a := h
  exact EQ2_coind SymmRel_postfix b a hinR

end SessionCoTypes.EQ2
