import SessionCoTypes.Coinductive.RegularSystemBisim
import SessionCoTypes.Coinductive.RegularityLemmas
import SessionCoTypes.Coinductive.Bridge

/-! # Rational Fragment of Coinductive Types

The rational fragment consists of coinductive types with finite reachable subterm
graphs. These types admit finite-state coalgebra representations and decidable
bisimulation checking. -/

/-
The Problem. Coinductive types can have infinite structure, but many practical
session types are "rational" - they have only finitely many distinct subterms.
We need to identify this fragment and show it has finite representations.

Solution Structure. Defines `RationalC` as an alias for `Regular` (finite
reachable set). Proves `rational_has_finite_bisimulation` showing every rational
type is bisimilar to a finite coalgebra image, and `rational_has_finite_representation`
showing equality with that image.
-/

set_option linter.dupNamespace false

namespace SessionCoTypes.Coinductive

attribute [local instance] Classical.decEq

/-- Rational fragment of coinductive local types (finite reachable subterm graph). -/
def RationalC (t : LocalTypeC) : Prop := Nonempty (Regular t)

@[simp] lemma rationalC_iff_regular (t : LocalTypeC) : RationalC t ↔ Nonempty (Regular t) := Iff.rfl

/-- Erasure-transportability through finite coalgebra extraction. -/
def FiniteErasureTransportable (t : LocalTypeC) : Prop :=
  ∃ (n : Nat) (sys : FiniteSystem n) (start : Fin n),
    Bisim t (SystemToCoind sys start)

/-- Child-closure of the finite-system image under one unfolding step. -/
private lemma systemToCoind_child_closed {n : Nat} (sys : FiniteSystem n)
    {x c : LocalTypeC}
    (hx : ∃ i : Fin n, x = SystemToCoind sys i)
    (hchild : childRel x c) :
    ∃ j : Fin n, c = SystemToCoind sys j := by
  rcases hx with ⟨i, rfl⟩
  rcases hchild with ⟨s, f, k, hdest, hc⟩
  cases hsys : sys i with
  | mk hs hf =>
      have hdestCorec :
          PFunctor.M.dest (SystemToCoind sys i) =
            ⟨hs, PFunctor.M.corec sys ∘ hf⟩ := by
        simp [SystemToCoind, hsys, PFunctor.M.dest_corec]
      have hpair :
          (⟨s, f⟩ : LocalTypeF LocalTypeC) =
            ⟨hs, PFunctor.M.corec sys ∘ hf⟩ := by
        exact hdest.symm.trans hdestCorec
      cases hpair
      refine ⟨hf k, ?_⟩
      simpa [SystemToCoind, Function.comp] using hc.symm

/-- Reachable states of a finite-system unfolding lie in its finite image. -/
private lemma reachable_subset_system_image {n : Nat} (sys : FiniteSystem n) (start : Fin n) :
    Reachable (SystemToCoind sys start) ⊆ {c : LocalTypeC | ∃ i : Fin n, c = SystemToCoind sys i} := by
  intro c hc
  induction hc with
  | refl =>
      exact ⟨start, rfl⟩
  | tail hreach hchild ih =>
      exact systemToCoind_child_closed sys ih hchild

/-- Any finite-system unfolding is regular. -/
def systemToCoind_regular {n : Nat} (sys : FiniteSystem n) (start : Fin n) :
    Regular (SystemToCoind sys start) := by
  refine
    { states := List.ofFn (fun i : Fin n => SystemToCoind sys i)
      root_mem := ?_
      closed := ?_ }
  · exact List.mem_ofFn.2 ⟨start, rfl⟩
  · intro x hx c hchild
    rcases List.mem_ofFn.1 hx with ⟨i, rfl⟩
    rcases systemToCoind_child_closed sys (hx := ⟨i, rfl⟩) hchild with ⟨j, hj⟩
    exact List.mem_ofFn.2 ⟨j, hj.symm⟩

/-- Every rational coinductive type has a finite-state coalgebra bisimilar to it. -/
theorem rational_has_finite_bisimulation (t : LocalTypeC) (h : RationalC t) :
    ∃ (n : Nat) (sys : FiniteSystem n) (start : Fin n),
      Bisim t (SystemToCoind sys start) :=
  by
    rcases h with ⟨hr⟩
    exact Regular_implies_System t hr

/-- Erasure exactness (completeness): finite erasure witnesses imply rationality. -/
theorem finite_erasure_transportable_implies_rational (t : LocalTypeC)
    (h : FiniteErasureTransportable t) : RationalC t := by
  rcases h with ⟨n, sys, start, hb⟩
  have hregSys : Regular (SystemToCoind sys start) := systemToCoind_regular sys start
  have hsymm : Bisim (SystemToCoind sys start) t := Bisim_symm _ _ hb
  exact ⟨regular_of_bisim hsymm hregSys⟩

/-- Exact characterization of the rational fragment via finite erasure transport. -/
theorem rational_iff_finite_erasure_transportable (t : LocalTypeC) :
    RationalC t ↔ FiniteErasureTransportable t := by
  constructor
  · intro h
    exact rational_has_finite_bisimulation t h
  · intro h
    exact finite_erasure_transportable_implies_rational t h

/-- Relative maximality: any fragment transportable by finite erasure is a subset of `RationalC`. -/
theorem rational_maximal_for_finite_erasure
    (S : Set LocalTypeC)
    (hS : ∀ t, t ∈ S → FiniteErasureTransportable t) :
    S ⊆ {t : LocalTypeC | RationalC t} := by
  intro t ht
  exact finite_erasure_transportable_implies_rational t (hS t ht)

/-- Canonical principal witness for regular types: the extracted regular system. -/
theorem rational_principal_witness (t : LocalTypeC) (h : Regular t) :
    Bisim t (SystemToCoind (RegularSystem (witnessOfRegular h))
      (StateIndex (witnessOfRegular h) t)) := by
  let w := witnessOfRegular h
  let sys := RegularSystem w
  refine ⟨RegularBisim t h sys, RegularBisim_isBisimulation t h, ?_⟩
  refine ⟨t, w.root_mem, rfl, rfl⟩

/-- Any finite witness factors through the principal witness up to bisimulation. -/
theorem finite_witness_factors_through_principal
    (t : LocalTypeC) (h : Regular t)
    {n : Nat} {sys : FiniteSystem n} {start : Fin n}
    (hw : Bisim t (SystemToCoind sys start)) :
    Bisim (SystemToCoind (RegularSystem (witnessOfRegular h))
      (StateIndex (witnessOfRegular h) t))
      (SystemToCoind sys start) := by
  exact Bisim_trans _ _ _ (Bisim_symm _ _ (rational_principal_witness t h)) hw

/-- Witness invariance: any two finite erasure witnesses for the same type are bisimilar. -/
theorem finite_erasure_witness_invariant
    (t : LocalTypeC)
    {n₁ : Nat} {sys₁ : FiniteSystem n₁} {start₁ : Fin n₁}
    {n₂ : Nat} {sys₂ : FiniteSystem n₂} {start₂ : Fin n₂}
    (h₁ : Bisim t (SystemToCoind sys₁ start₁))
    (h₂ : Bisim t (SystemToCoind sys₂ start₂)) :
    Bisim (SystemToCoind sys₁ start₁) (SystemToCoind sys₂ start₂) := by
  exact Bisim_trans _ _ _ (Bisim_symm _ _ h₁) h₂

/-- Extensional witness invariance (equality form). -/
theorem finite_erasure_witness_invariant_eq
    (t : LocalTypeC)
    {n₁ : Nat} {sys₁ : FiniteSystem n₁} {start₁ : Fin n₁}
    {n₂ : Nat} {sys₂ : FiniteSystem n₂} {start₂ : Fin n₂}
    (h₁ : Bisim t (SystemToCoind sys₁ start₁))
    (h₂ : Bisim t (SystemToCoind sys₂ start₂)) :
    SystemToCoind sys₁ start₁ = SystemToCoind sys₂ start₂ :=
  (Bisim_eq_iff _ _).1 (finite_erasure_witness_invariant t h₁ h₂)

/-- Rationality is preserved under bisimulation. -/
theorem rational_closed_under_bisim {a b : LocalTypeC}
    (ha : RationalC a) (hab : Bisim a b) : RationalC b :=
  by
    rcases ha with ⟨hra⟩
    exact ⟨regular_of_bisim hab hra⟩

/-- Finite erasure transportability is stable under bisimulation on the left. -/
theorem finite_erasure_transportable_closed_under_bisim_left
    {a b : LocalTypeC} (hab : Bisim a b)
    (hb : FiniteErasureTransportable b) : FiniteErasureTransportable a := by
  rcases hb with ⟨n, sys, start, hsys⟩
  exact ⟨n, sys, start, Bisim_trans _ _ _ hab hsys⟩

/-- Finite erasure transportability is stable under bisimulation on the right. -/
theorem finite_erasure_transportable_closed_under_bisim_right
    {a b : LocalTypeC} (hab : Bisim a b)
    (ha : FiniteErasureTransportable a) : FiniteErasureTransportable b := by
  rcases ha with ⟨n, sys, start, hsys⟩
  exact ⟨n, sys, start, Bisim_trans _ _ _ (Bisim_symm _ _ hab) hsys⟩

/-- Operational adequacy: the principal extracted system replays exactly the source behavior. -/
theorem rational_principal_witness_adequacy (t : LocalTypeC) (h : Regular t) :
    SystemToCoind (RegularSystem (witnessOfRegular h))
      (StateIndex (witnessOfRegular h) t) = t := by
  have heq : t = SystemToCoind (RegularSystem (witnessOfRegular h))
      (StateIndex (witnessOfRegular h) t) :=
    (Bisim_eq_iff _ _).1 (rational_principal_witness t h)
  exact heq.symm

/-- Syntax-bridge exactness on inductive embeddings. -/
theorem toCoind_image_exact
    (r : SessionTypes.LocalTypeR.LocalTypeR) :
    RationalC (toCoind r) ↔ FiniteErasureTransportable (toCoind r) :=
  rational_iff_finite_erasure_transportable (toCoind r)

/-- Rational coinductive types coincide extensionally with a finite coalgebra image. -/
theorem rational_has_finite_representation (t : LocalTypeC) (h : RationalC t) :
    ∃ (n : Nat) (sys : FiniteSystem n) (start : Fin n),
      t = SystemToCoind sys start :=
  by
    rcases h with ⟨hr⟩
    exact Regular_implies_System_eq t hr

/-! ## Strict Boundary Witness -/

/-- Fresh mu-name stream used to witness a non-rational coinductive type. -/
private def muStreamName (n : Nat) : String := String.replicate n 'a'

/-- Coalgebra stepping through strictly fresh mu-binders. -/
private def muStreamStep (n : Nat) : LocalTypeF.Obj Nat :=
  ⟨.mu (muStreamName n), fun _ => n + 1⟩

/-- Infinite coinductive stream of distinct `mu` heads. -/
private def muStream (n : Nat) : LocalTypeC :=
  PFunctor.M.corec muStreamStep n

private lemma muStream_dest (n : Nat) :
    PFunctor.M.dest (muStream n) =
      ⟨.mu (muStreamName n), PFunctor.M.corec muStreamStep ∘ (fun _ => n + 1)⟩ := by
  simp [muStream, muStreamStep, PFunctor.M.dest_corec]

private lemma muStream_head (n : Nat) :
    head (muStream n) = .mu (muStreamName n) := by
  simp [head, muStream_dest]

private lemma muStream_child (n : Nat) :
    childRel (muStream n) (muStream (n + 1)) := by
  refine ⟨.mu (muStreamName n), (PFunctor.M.corec muStreamStep ∘ (fun _ => n + 1)), (), ?_, ?_⟩
  exact muStream_dest n
  simp [muStream, Function.comp]

private lemma muStream_reachable : ∀ n, muStream n ∈ Reachable (muStream 0)
  | 0 => Relation.ReflTransGen.refl
  | n + 1 => reachable_step (muStream_reachable n) (muStream_child n)

private lemma muStreamName_injective : Function.Injective muStreamName := by
  intro m n h
  have hlen : m = n := by
    have hlenEq := congrArg String.length h
    simpa [muStreamName, String.length_replicate] using hlenEq
  exact hlen

private lemma muStream_injective : Function.Injective muStream := by
  intro m n h
  have hhead := congrArg head h
  have hname : muStreamName m = muStreamName n := by
    simpa [muStream_head] using hhead
  exact muStreamName_injective hname

private lemma muStream_not_rational : ¬ RationalC (muStream 0) := by
  intro hreg
  rcases hreg with ⟨hreg⟩
  have hsubset : Set.range muStream ⊆ Reachable (muStream 0) := by
    intro c hc
    rcases hc with ⟨n, rfl⟩
    exact muStream_reachable n
  have hfiniteRange : (Set.range muStream).Finite := (finite_of_regular hreg).subset hsubset
  have hinfRange : (Set.range muStream).Infinite :=
    Set.infinite_range_of_injective muStream_injective
  exact hfiniteRange.not_infinite hinfRange

/-- Strict boundary witness: there exist coinductive types outside the rational fragment,
    hence outside finite erasure transportability as well. -/
theorem strict_boundary_witness :
    ∃ t : LocalTypeC, ¬ RationalC t ∧ ¬ FiniteErasureTransportable t := by
  refine ⟨muStream 0, muStream_not_rational, ?_⟩
  intro htransport
  exact muStream_not_rational (finite_erasure_transportable_implies_rational _ htransport)

end SessionCoTypes.Coinductive
