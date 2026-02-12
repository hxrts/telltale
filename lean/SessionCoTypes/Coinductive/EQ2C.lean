import Mathlib
import SessionCoTypes.Coinductive.LocalTypeC
import SessionCoTypes.Coinductive.Observable

set_option linter.dupNamespace false

/-! # EQ2C Bisimulation

Equi-recursive equality relation for coinductive session types via bisimulation. -/

/-
The Problem. Coinductive types can have different structural representations
that are semantically equivalent. In particular, mu-unfolding should be silent:
`mu x. T` should equal `T[x := mu x. T]`. We need an equi-recursive equality
relation EQ2C that captures this.

Solution Structure. Defines BranchesRelC for pointwise relation on branch lists,
ObservableRelC for one-step observable equality after mu-unfolding, EQ2CStep as
the bisimulation step function, and EQ2C as greatest fixpoint via Paco-style iteration.
-/

namespace SessionCoTypes.Coinductive

-- Alias Label to avoid ambiguity
abbrev Label := SessionTypes.GlobalType.Label

/-! ## Branch relation -/

/-- Branch relation: labels match and continuations are related by `R`. -/
def BranchesRelC (R : LocalTypeC → LocalTypeC → Prop)
    (bs cs : List (Label × LocalTypeC)) : Prop :=
  List.Forall₂ (fun b c => b.1 = c.1 ∧ R b.2 c.2) bs cs

lemma BranchesRelC_mono {R S : LocalTypeC → LocalTypeC → Prop}
    (h : ∀ a b, R a b → S a b) :
    ∀ {bs cs}, BranchesRelC R bs cs → BranchesRelC S bs cs := by
  intro bs cs hrel
  exact List.Forall₂.imp (fun a b hab => ⟨hab.1, h _ _ hab.2⟩) hrel

lemma BranchesRelC_refl (R : LocalTypeC → LocalTypeC → Prop)
    (h : ∀ t, R t t) : ∀ bs, BranchesRelC R bs bs := by
  intro bs
  induction bs with
  | nil => exact List.Forall₂.nil
  | cons b bs ih =>
      constructor
      · exact ⟨rfl, h b.2⟩
      · exact ih

lemma BranchesRelC_flip {R : LocalTypeC → LocalTypeC → Prop}
    (h : ∀ a b, R a b → R b a) :
    ∀ {bs cs}, BranchesRelC R bs cs → BranchesRelC R cs bs := by
  intro bs cs hrel
  induction hrel with
  | nil => exact List.Forall₂.nil
  | cons hbc hrest ih =>
      rcases hbc with ⟨hlabel, hrel⟩
      constructor
      · exact ⟨hlabel.symm, h _ _ hrel⟩
      · exact ih

lemma BranchesRelC_swap (R : LocalTypeC → LocalTypeC → Prop) :
    ∀ {bs cs}, BranchesRelC R bs cs → BranchesRelC (fun x y => R y x) cs bs := by
  intro bs cs hrel
  induction hrel with
  | nil => exact List.Forall₂.nil
  | cons hbc hrest ih =>
      rcases hbc with ⟨hlabel, hrel⟩
      constructor
      · exact ⟨hlabel.symm, hrel⟩
      · exact ih

/-! ### Branch Relation Composition -/

lemma BranchesRelC_comp {R S : LocalTypeC → LocalTypeC → Prop}
    (T : LocalTypeC → LocalTypeC → Prop) (hT : ∀ a c, T a c ↔ ∃ b, R a b ∧ S b c) :
    ∀ {bs cs ds}, BranchesRelC R bs cs → BranchesRelC S cs ds → BranchesRelC T bs ds := by
  intro bs cs ds hrel1 hrel2
  induction hrel1 generalizing ds with
  | nil =>
      cases hrel2
      exact List.Forall₂.nil
  | cons hbc hrest ih =>
      cases hrel2 with
      | cons hcd hrest2 =>
          rcases hbc with ⟨hlab1, hR⟩
          rcases hcd with ⟨hlab2, hS⟩
          have hT' : T _ _ := (hT _ _).2 ⟨_, hR, hS⟩
          refine List.Forall₂.cons ?_ (ih hrest2)
          exact ⟨hlab1.trans hlab2, hT'⟩

/-! ## Observable relation -/

/-- Observable relation between two coinductive types, parameterized by `R`.

This version is NOT indexed by specific `ObservableC` proofs (which would be meaningless
due to proof irrelevance in Prop). Instead, it directly states the relationship. -/
inductive ObservableRelC (R : LocalTypeC → LocalTypeC → Prop) (a b : LocalTypeC) : Prop
  | is_end (ha : UnfoldsToEndC a) (hb : UnfoldsToEndC b) : ObservableRelC R a b
  | is_var (v : String) (ha : UnfoldsToVarC a v) (hb : UnfoldsToVarC b v) : ObservableRelC R a b
  | is_send (p : String) (bs cs : List (Label × LocalTypeC))
      (ha : CanSendC a p bs) (hb : CanSendC b p cs) (hbr : BranchesRelC R bs cs) :
      ObservableRelC R a b
  | is_recv (p : String) (bs cs : List (Label × LocalTypeC))
      (ha : CanRecvC a p bs) (hb : CanRecvC b p cs) (hbr : BranchesRelC R bs cs) :
      ObservableRelC R a b

/-- Observable relation is reflexive (for a relation reflexive on states). -/
lemma ObservableRelC_refl (R : LocalTypeC → LocalTypeC → Prop) (hR : ∀ t, R t t)
    {a : LocalTypeC} (obs : ObservableC a) : ObservableRelC R a a := by
  cases obs with
  | is_end ha => exact ObservableRelC.is_end ha ha
  | is_var v ha => exact ObservableRelC.is_var v ha ha
  | is_send p bs ha =>
      exact ObservableRelC.is_send p bs bs ha ha (BranchesRelC_refl R hR bs)
  | is_recv p bs ha =>
      exact ObservableRelC.is_recv p bs bs ha ha (BranchesRelC_refl R hR bs)

/-- Observable relation is symmetric. -/
lemma ObservableRelC_symm {R : LocalTypeC → LocalTypeC → Prop}
    (hR : ∀ a b, R a b → R b a) {a b : LocalTypeC}
    (hrel : ObservableRelC R a b) : ObservableRelC R b a := by
  cases hrel with
  | is_end ha hb => exact ObservableRelC.is_end hb ha
  | is_var v ha hb => exact ObservableRelC.is_var v hb ha
  | is_send p bs cs ha hb hbr =>
      exact ObservableRelC.is_send p cs bs hb ha (BranchesRelC_flip hR hbr)
  | is_recv p bs cs ha hb hbr =>
      exact ObservableRelC.is_recv p cs bs hb ha (BranchesRelC_flip hR hbr)

/-- Observable relation is monotone in the underlying relation. -/
lemma ObservableRelC_mono {R S : LocalTypeC → LocalTypeC → Prop}
    (h : ∀ a b, R a b → S a b) {a b : LocalTypeC}
    (hrel : ObservableRelC R a b) : ObservableRelC S a b := by
  cases hrel with
  | is_end ha hb => exact ObservableRelC.is_end ha hb
  | is_var v ha hb => exact ObservableRelC.is_var v ha hb
  | is_send p bs cs ha hb hbr =>
      exact ObservableRelC.is_send p bs cs ha hb (BranchesRelC_mono h hbr)
  | is_recv p bs cs ha hb hbr =>
      exact ObservableRelC.is_recv p bs cs ha hb (BranchesRelC_mono h hbr)

/-! ## Determinism of Observables

To prove composition of observable relations, we need that a type can't have
two different kinds of observables (e.g., can't be both end and send). -/

/-- UnfoldsC is right-unique (functional): each μ has exactly one body. -/
private lemma UnfoldsC_rightUnique : Relator.RightUnique UnfoldsC := by
  intro a b c hab hac
  rcases hab with ⟨x, f, hdest, rfl⟩
  rcases hac with ⟨y, g, hdest', rfl⟩
  have hpair :
      (⟨LocalTypeHead.mu x, f⟩ : LocalTypeF LocalTypeC) =
        ⟨LocalTypeHead.mu y, g⟩ := by
    exact hdest.symm.trans hdest'
  cases hpair
  rfl

/-- If a type's head is not mu, UnfoldsC from it leads back to itself. -/
private lemma UnfoldsC_head_mu {t u : LocalTypeC} (h : UnfoldsC t u) : ∃ x, head t = .mu x := by
  rcases h with ⟨x, f, hdest, _⟩
  refine ⟨x, ?_⟩
  simp [head, hdest]

/-- If a type's head is not mu, UnfoldsToC leads only to itself. -/
private lemma UnfoldsToC_eq_of_head_ne_mu {l l' : LocalTypeC} (h : UnfoldsToC l l')
    (hn : ∀ x, head l ≠ .mu x) : l' = l := by
  rcases (Relation.ReflTransGen.cases_head h) with (hEq | hstep)
  · cases hEq
    rfl
  · rcases hstep with ⟨c, hstep, _⟩
    rcases UnfoldsC_head_mu hstep with ⟨x, hmu⟩
    exact (False.elim (hn x hmu))

/-- Two non-mu types reachable from the same source are equal.

This captures that μ-unfolding is deterministic: from any starting type `t`,
there is at most one non-mu type reachable via unfolding. This is because:
1. `UnfoldsC` is functional (each mu has exactly one body)
2. The reflexive-transitive closure preserves functionality for "terminal" states
3. Non-mu types are "terminal" (cannot unfold further)

This is a fundamental property of equi-recursive types. -/
theorem UnfoldsToC_unique :
    ∀ {t u1 u2 : LocalTypeC},
      UnfoldsToC t u1 → UnfoldsToC t u2 →
      ¬ (∃ x, head u1 = .mu x) → ¬ (∃ x, head u2 = .mu x) →
      u1 = u2 := by
  intro t u1 u2 h1 h2 hnomu1 hnomu2
  -- By totality: either UnfoldsToC u1 u2 or UnfoldsToC u2 u1
  have htot := Relation.ReflTransGen.total_of_right_unique (U := UnfoldsC_rightUnique) h1 h2
  cases htot with
  | inl h12 =>
      -- UnfoldsToC u1 u2, but u1 has non-mu head, so u2 = u1
      have hne : ∀ x, head u1 ≠ .mu x := by
        intro x heq
        exact hnomu1 ⟨x, heq⟩
      exact (UnfoldsToC_eq_of_head_ne_mu h12 hne).symm
  | inr h21 =>
      -- UnfoldsToC u2 u1, but u2 has non-mu head, so u1 = u2
      have hne : ∀ x, head u2 ≠ .mu x := by
        intro x heq
        exact hnomu2 ⟨x, heq⟩
      exact UnfoldsToC_eq_of_head_ne_mu h21 hne

/-- Corollary: observable heads are determined by the source type. -/
lemma observable_head_deterministic {t u1 u2 : LocalTypeC}
    (hunf1 : UnfoldsToC t u1) (hunf2 : UnfoldsToC t u2)
    (hnomu1 : ¬ (∃ x, head u1 = .mu x)) (hnomu2 : ¬ (∃ x, head u2 = .mu x)) :
    head u1 = head u2 := by
  have := UnfoldsToC_unique hunf1 hunf2 hnomu1 hnomu2
  simp [this]

/-! ## Exclusion lemmas -/
/-! ### End-Head Exclusion -/

/-- If a type unfolds to end, it cannot unfold to a var. -/
lemma not_end_and_var {t : LocalTypeC} (hend : UnfoldsToEndC t) (v : String) :
    ¬ UnfoldsToVarC t v := by
  intro hvar
  rcases hend with ⟨u1, hunf1, hhead1⟩
  rcases hvar with ⟨u2, hunf2, hhead2⟩
  have hnomu1 : ¬ (∃ x, head u1 = .mu x) := by simp [hhead1]
  have hnomu2 : ¬ (∃ x, head u2 = .mu x) := by simp [hhead2]
  have := observable_head_deterministic hunf1 hunf2 hnomu1 hnomu2
  simp [hhead1, hhead2] at this

/-- If a type unfolds to end, it cannot send. -/
lemma not_end_and_send {t : LocalTypeC} (hend : UnfoldsToEndC t) (p : String)
    (bs : List (Label × LocalTypeC)) : ¬ CanSendC t p bs := by
  intro hsend
  rcases hend with ⟨u1, hunf1, hhead1⟩
  rcases hsend with ⟨u2, labels, hunf2, hhead2, _⟩
  have hnomu1 : ¬ (∃ x, head u1 = .mu x) := by simp [hhead1]
  have hnomu2 : ¬ (∃ x, head u2 = .mu x) := by simp [hhead2]
  have := observable_head_deterministic hunf1 hunf2 hnomu1 hnomu2
  simp [hhead1, hhead2] at this

/-- If a type unfolds to end, it cannot recv. -/
lemma not_end_and_recv {t : LocalTypeC} (hend : UnfoldsToEndC t) (p : String)
    (bs : List (Label × LocalTypeC)) : ¬ CanRecvC t p bs := by
  intro hrecv
  rcases hend with ⟨u1, hunf1, hhead1⟩
  rcases hrecv with ⟨u2, labels, hunf2, hhead2, _⟩
  have hnomu1 : ¬ (∃ x, head u1 = .mu x) := by simp [hhead1]
  have hnomu2 : ¬ (∃ x, head u2 = .mu x) := by simp [hhead2]
  have := observable_head_deterministic hunf1 hunf2 hnomu1 hnomu2
  simp [hhead1, hhead2] at this

/-! ### Var-Head Exclusion -/

/-- If a type unfolds to var, it cannot send. -/
lemma not_var_and_send {t : LocalTypeC} (v : String) (hvar : UnfoldsToVarC t v)
    (p : String) (bs : List (Label × LocalTypeC)) : ¬ CanSendC t p bs := by
  intro hsend
  rcases hvar with ⟨u1, hunf1, hhead1⟩
  rcases hsend with ⟨u2, labels, hunf2, hhead2, _⟩
  have hnomu1 : ¬ (∃ x, head u1 = .mu x) := by simp [hhead1]
  have hnomu2 : ¬ (∃ x, head u2 = .mu x) := by simp [hhead2]
  have := observable_head_deterministic hunf1 hunf2 hnomu1 hnomu2
  simp [hhead1, hhead2] at this

/-- If a type unfolds to var, it cannot recv. -/
lemma not_var_and_recv {t : LocalTypeC} (v : String) (hvar : UnfoldsToVarC t v)
    (p : String) (bs : List (Label × LocalTypeC)) : ¬ CanRecvC t p bs := by
  intro hrecv
  rcases hvar with ⟨u1, hunf1, hhead1⟩
  rcases hrecv with ⟨u2, labels, hunf2, hhead2, _⟩
  have hnomu1 : ¬ (∃ x, head u1 = .mu x) := by simp [hhead1]
  have hnomu2 : ¬ (∃ x, head u2 = .mu x) := by simp [hhead2]
  have := observable_head_deterministic hunf1 hunf2 hnomu1 hnomu2
  simp [hhead1, hhead2] at this

/-! ### Send/Recv Kind Exclusion -/

/-- If a type can send, it cannot recv (with the same participant). -/
lemma not_send_and_recv {t : LocalTypeC} (p : String) (bs : List (Label × LocalTypeC))
    (hsend : CanSendC t p bs) (q : String) (cs : List (Label × LocalTypeC)) :
    ¬ CanRecvC t q cs := by
  intro hrecv
  rcases hsend with ⟨u1, labels1, hunf1, hhead1, _⟩
  rcases hrecv with ⟨u2, labels2, hunf2, hhead2, _⟩
  have hnomu1 : ¬ (∃ x, head u1 = .mu x) := by simp [hhead1]
  have hnomu2 : ¬ (∃ x, head u2 = .mu x) := by simp [hhead2]
  have := observable_head_deterministic hunf1 hunf2 hnomu1 hnomu2
  simp [hhead1, hhead2] at this

/-! ## Uniqueness of communication observables -/

/-- If two CanSendC hold for the same type, they have the same participant and branches. -/
lemma CanSendC_unique {t : LocalTypeC} {p1 p2 : String}
    {bs1 bs2 : List (Label × LocalTypeC)}
    (h1 : CanSendC t p1 bs1) (h2 : CanSendC t p2 bs2) : p1 = p2 ∧ bs1 = bs2 := by
  rcases h1 with ⟨u1, labels1, hunf1, hhead1, hbs1⟩
  rcases h2 with ⟨u2, labels2, hunf2, hhead2, hbs2⟩
  have hnomu1 : ¬ (∃ x, head u1 = .mu x) := by simp [hhead1]
  have hnomu2 : ¬ (∃ x, head u2 = .mu x) := by simp [hhead2]
  have hu_eq := UnfoldsToC_unique hunf1 hunf2 hnomu1 hnomu2
  subst hu_eq
  simp [hhead1] at hhead2
  constructor
  · exact hhead2.1
  · simp [hbs1, hbs2]

/-- If two CanRecvC hold for the same type, they have the same participant and branches. -/
lemma CanRecvC_unique {t : LocalTypeC} {p1 p2 : String}
    {bs1 bs2 : List (Label × LocalTypeC)}
    (h1 : CanRecvC t p1 bs1) (h2 : CanRecvC t p2 bs2) : p1 = p2 ∧ bs1 = bs2 := by
  rcases h1 with ⟨u1, labels1, hunf1, hhead1, hbs1⟩
  rcases h2 with ⟨u2, labels2, hunf2, hhead2, hbs2⟩
  have hnomu1 : ¬ (∃ x, head u1 = .mu x) := by simp [hhead1]
  have hnomu2 : ¬ (∃ x, head u2 = .mu x) := by simp [hhead2]
  have hu_eq := UnfoldsToC_unique hunf1 hunf2 hnomu1 hnomu2
  subst hu_eq
  simp [hhead1] at hhead2
  constructor
  · exact hhead2.1
  · simp [hbs1, hbs2]

/-! ## Observable relation composition -/

/-- Observable relation composes through relational composition.

This lemma establishes that ObservableRelC is closed under relational composition.
The key insight is that for the shared middle type `b`, the observable kinds must
match between `hrel1` and `hrel2`. The impossible cases are eliminated using
determinism lemmas. -/
lemma ObservableRelC_comp {R S : LocalTypeC → LocalTypeC → Prop}
    (T : LocalTypeC → LocalTypeC → Prop) (hT : ∀ a c, T a c ↔ ∃ b, R a b ∧ S b c)
    {a b c : LocalTypeC}
    (hrel1 : ObservableRelC R a b) (hrel2 : ObservableRelC S b c) :
    ObservableRelC T a c := by
  cases hrel1 with
  | is_end ha hb =>
      cases hrel2 with
      | is_end _ hc => exact ObservableRelC.is_end ha hc
      | is_var v hb' _ => exact absurd hb' (not_end_and_var hb v)
      | is_send p _ _ hb' _ _ => exact absurd hb' (not_end_and_send hb p _)
      | is_recv p _ _ hb' _ _ => exact absurd hb' (not_end_and_recv hb p _)
  | is_var v ha hb =>
      cases hrel2 with
      | is_end hb' _ => exact absurd hb (not_end_and_var hb' v)
      | is_var v' hb' hc =>
          -- Need v = v' from determinism
          rcases hb with ⟨u1, hunf1, hhead1⟩
          rcases hb' with ⟨u2, hunf2, hhead2⟩
          have hnomu1 : ¬ (∃ x, head u1 = .mu x) := by simp [hhead1]
          have hnomu2 : ¬ (∃ x, head u2 = .mu x) := by simp [hhead2]
          have heq := observable_head_deterministic hunf1 hunf2 hnomu1 hnomu2
          simp [hhead1, hhead2] at heq
          subst heq
          exact ObservableRelC.is_var v ha hc
      | is_send p _ _ hb' _ _ => exact absurd hb' (not_var_and_send v hb p _)
      | is_recv p _ _ hb' _ _ => exact absurd hb' (not_var_and_recv v hb p _)
  | is_send p bs cs ha hb hbr1 =>
      cases hrel2 with
      | is_end hb' _ => exact absurd hb (not_end_and_send hb' p _)
      | is_var v hb' _ => exact absurd hb (not_var_and_send v hb' p _)
      | is_send p' cs' ds hb' hc hbr2 =>
          -- Need p = p' and cs = cs' from determinism
          have ⟨hp, hcs⟩ := CanSendC_unique hb hb'
          subst hp hcs
          exact ObservableRelC.is_send p bs ds ha hc (BranchesRelC_comp T hT hbr1 hbr2)
      | is_recv q _ _ hb' _ _ => exact absurd hb' (not_send_and_recv p cs hb q _)
  | is_recv p bs cs ha hb hbr1 =>
      cases hrel2 with
      | is_end hb' _ => exact absurd hb (not_end_and_recv hb' p _)
      | is_var v hb' _ => exact absurd hb (not_var_and_recv v hb' p _)
      | is_send q bs' _ hb' _ _ => exact absurd hb (not_send_and_recv q bs' hb' p _)
      | is_recv p' cs' ds hb' hc hbr2 =>
          -- Need p = p' and cs = cs' from determinism
          have ⟨hp, hcs⟩ := CanRecvC_unique hb hb'
          subst hp hcs
          exact ObservableRelC.is_recv p bs ds ha hc (BranchesRelC_comp T hT hbr1 hbr2)

/-! ## EQ2C: Equi-recursive equality -/

/-- A relation is an EQ2C-bisimulation if it relates observable heads. -/
def IsBisimulationC (R : LocalTypeC → LocalTypeC → Prop) : Prop :=
  ∀ a b, R a b → ∃ (_obs_a : ObservableC a) (_obs_b : ObservableC b), ObservableRelC R a b

/-- Equi-recursive equality on `LocalTypeC`. -/
def EQ2C (a b : LocalTypeC) : Prop :=
  ∃ R, IsBisimulationC R ∧ R a b

/-! ## EQ2C is an equivalence -/

/-- Symmetry. -/
lemma EQ2C_symm {a b : LocalTypeC} (h : EQ2C a b) : EQ2C b a := by
  rcases h with ⟨R, hR, hab⟩
  let R' : LocalTypeC → LocalTypeC → Prop := fun x y => R y x
  have hswap :
      ∀ {x y}, ObservableRelC R x y → ObservableRelC R' y x := by
    intro x y hrel
    cases hrel with
    | is_end ha hb => exact ObservableRelC.is_end hb ha
    | is_var v ha hb => exact ObservableRelC.is_var v hb ha
    | is_send p bs cs ha hb hbr =>
        have hbr' : BranchesRelC R' cs bs := BranchesRelC_swap R hbr
        exact ObservableRelC.is_send p cs bs hb ha hbr'
    | is_recv p bs cs ha hb hbr =>
        have hbr' : BranchesRelC R' cs bs := BranchesRelC_swap R hbr
        exact ObservableRelC.is_recv p cs bs hb ha hbr'
  refine ⟨R', ?_, hab⟩
  intro x y hxy
  obtain ⟨obs_y, obs_x, hrel⟩ := hR y x hxy
  exact ⟨obs_x, obs_y, hswap hrel⟩

/-- Transitivity. -/
lemma EQ2C_trans {a b c : LocalTypeC} (hab : EQ2C a b) (hbc : EQ2C b c) : EQ2C a c := by
  rcases hab with ⟨R, hR, hab⟩
  rcases hbc with ⟨S, hS, hbc⟩
  let T : LocalTypeC → LocalTypeC → Prop := fun x z => ∃ y, R x y ∧ S y z
  refine ⟨T, ?_, ⟨b, hab, hbc⟩⟩
  intro x z hxz
  rcases hxz with ⟨y, hxy, hyz⟩
  obtain ⟨obs_x, obs_y, hrel_xy⟩ := hR x y hxy
  obtain ⟨obs_y', obs_z, hrel_yz⟩ := hS y z hyz
  refine ⟨obs_x, obs_z, ?_⟩
  exact ObservableRelC_comp T (by intro a c; rfl) hrel_xy hrel_yz

end SessionCoTypes.Coinductive
