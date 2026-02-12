import Runtime.Proofs.VM.InstrSpec.ConfigEquivAcquire

/-! # Erasure Exactness and Instruction Basis

Instruction classification, basis completeness, and counterexample
infrastructure for proving VM instruction set exactness. -/

/-
The Problem. To prove the VM instruction set is exact (neither too
large nor too small), we classify instructions and show completeness:
every declared class is representable, and removing any class breaks
some property.

Solution Structure. Define `InstrClass` enumeration for instruction
categories. Provide `InstructionBasisCompleteness` predicate and
`MissingClassCounterexample` structure for exactness proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

section

/-! ## Instruction Classification -/

inductive InstrClass where
  | commValue
  | commChoice
  | sessionDomain
  | ownershipTransfer
  | epistemic
  | guard
  | effect
  | concurrency
  | regControl
  deriving DecidableEq, Repr, Inhabited

/-- Completeness form: every declared instruction class is representable. -/
def InstructionBasisCompleteness
    (declared : List InstrClass)
    (representable : InstrClass → Prop) : Prop :=
  ∀ c, c ∈ declared → representable c

/-- Counterexample witness interface: a missing class yields a non-representability witness. -/
structure MissingClassCounterexample
    (declared : List InstrClass)
    (representable : InstrClass → Prop) where
  missingClass : InstrClass
  missingInDeclared : missingClass ∈ declared
  notRepresentable : ¬ representable missingClass
  witnessId : String

/-- Representability predicate after dropping one declared class from consideration. -/
def droppedClassRepresentable
    (representable : InstrClass → Prop)
    (dropped : InstrClass) : InstrClass → Prop :=
  fun c => c ≠ dropped ∧ representable c

/-- Minimality form: dropping any class from the declared basis yields a witness. -/
def InstructionBasisMinimality
    (declared : List InstrClass)
    (representable : InstrClass → Prop) : Prop :=
  ∀ c, c ∈ declared →
    ∃ w : MissingClassCounterexample declared (droppedClassRepresentable representable c),
      w.missingClass = c

/-- Packaged exactness statement for VM instruction-basis claims. -/
def InstructionBasisExactness
    (declared : List InstrClass)
    (representable : InstrClass → Prop) : Prop :=
  InstructionBasisCompleteness declared representable ∧
  InstructionBasisMinimality declared representable

/-- Build exactness from separately provided completeness/minimality witnesses. -/
theorem instructionBasisExactness_of_components
    {declared : List InstrClass}
    {representable : InstrClass → Prop}
    (hComplete : InstructionBasisCompleteness declared representable)
    (hMinimal : InstructionBasisMinimality declared representable) :
    InstructionBasisExactness declared representable := by
  exact ⟨hComplete, hMinimal⟩

/-! ## Concrete Canonical Basis Instantiation -/

/-- Canonical class basis used by the concrete VM exactness instantiation. -/
def canonicalInstrBasis : List InstrClass :=
  [ .commValue
  , .commChoice
  , .sessionDomain
  , .ownershipTransfer
  , .epistemic
  , .guard
  , .effect
  , .concurrency
  , .regControl
  ]

/-- Canonical representability predicate for the declared VM class basis. -/
def canonicalRepresentable : InstrClass → Prop :=
  fun c => c ∈ canonicalInstrBasis

/-- Stable witness ids for drop-one-class minimality certificates. -/
def instrClassWitnessId : InstrClass → String
  | .commValue => "missing-commValue"
  | .commChoice => "missing-commChoice"
  | .sessionDomain => "missing-sessionDomain"
  | .ownershipTransfer => "missing-ownershipTransfer"
  | .epistemic => "missing-epistemic"
  | .guard => "missing-guard"
  | .effect => "missing-effect"
  | .concurrency => "missing-concurrency"
  | .regControl => "missing-regControl"

/-- Concrete completeness witness for the canonical VM class basis. -/
theorem canonicalInstrBasis_completeness :
    InstructionBasisCompleteness canonicalInstrBasis canonicalRepresentable := by
  intro c hIn
  exact hIn

/-- Concrete drop-one-class minimality witnesses for the canonical basis. -/
theorem canonicalInstrBasis_minimality :
    InstructionBasisMinimality canonicalInstrBasis canonicalRepresentable := by
  intro c hIn
  refine ⟨{ missingClass := c
          , missingInDeclared := hIn
          , notRepresentable := ?_
          , witnessId := instrClassWitnessId c }, rfl⟩
  intro hRep
  exact hRep.1 rfl

/-- Concrete end-to-end exactness theorem for the canonical VM class basis. -/
theorem canonicalInstrBasis_exactness :
    InstructionBasisExactness canonicalInstrBasis canonicalRepresentable := by
  exact instructionBasisExactness_of_components
    canonicalInstrBasis_completeness
    canonicalInstrBasis_minimality

/-! ## VM <-> Classical-Erasure Exact Correspondence -/

/-- The twelve classical erasures tracked by the paper/theory interface. -/
inductive ClassicalErasure where
  | identity
  | carrier
  | nullifier
  | gauge
  | labelProjection
  | domainRestriction
  | history
  | resourceReidentification
  | handlerAbstraction
  | permutation
  | observerProjection
  | timeParameter
  deriving DecidableEq, Repr, Inhabited

/-! ## Erasure Coverage and Irredundancy Definitions -/

/-- Which instruction class realizes which classical erasure. -/
def classRealizesErasure : InstrClass → ClassicalErasure → Prop
  | .commValue, .nullifier => True
  | .commChoice, .labelProjection => True
  | .sessionDomain, .identity => True
  | .sessionDomain, .domainRestriction => True
  | .ownershipTransfer, .carrier => True
  | .ownershipTransfer, .resourceReidentification => True
  | .epistemic, .observerProjection => True
  | .guard, .gauge => True
  | .effect, .handlerAbstraction => True
  | .concurrency, .permutation => True
  | .regControl, .history => True
  | .regControl, .timeParameter => True
  | _, _ => False

/-- Coverage: every tracked erasure is realized by some declared class. -/
def VMErasureCoverage (declared : List InstrClass) : Prop :=
  ∀ e : ClassicalErasure, ∃ c : InstrClass, c ∈ declared ∧ classRealizesErasure c e

/-- Irredundancy: each declared class has at least one uniquely realized erasure. -/
def VMErasureIrredundancy (declared : List InstrClass) : Prop :=
  ∀ c : InstrClass, c ∈ declared →
    ∃ e : ClassicalErasure,
      classRealizesErasure c e ∧
      ∀ c' : InstrClass, c' ∈ declared → c' ≠ c → ¬ classRealizesErasure c' e

/-- Exact correspondence package: coverage + irredundancy. -/
def VMErasureExactCorrespondence (declared : List InstrClass) : Prop :=
  VMErasureCoverage declared ∧ VMErasureIrredundancy declared

/-! ## Unique Erasure Witnesses -/

/-- Canonical unique erasure witness used for irredundancy proofs. -/
def uniqueErasureOfClass : InstrClass → ClassicalErasure
  | .commValue => .nullifier
  | .commChoice => .labelProjection
  | .sessionDomain => .domainRestriction
  | .ownershipTransfer => .carrier
  | .epistemic => .observerProjection
  | .guard => .gauge
  | .effect => .handlerAbstraction
  | .concurrency => .permutation
  | .regControl => .history

/-- Every class realizes its designated unique erasure witness. -/
theorem class_realizes_uniqueErasure (c : InstrClass) :
    classRealizesErasure c (uniqueErasureOfClass c) := by
  cases c <;> simp [uniqueErasureOfClass, classRealizesErasure]

/-- A class realizing another class's unique erasure must be that same class. -/
theorem eq_of_realizes_uniqueErasure {c c' : InstrClass}
    (hReal : classRealizesErasure c' (uniqueErasureOfClass c)) :
    c' = c := by
  cases c <;> cases c' <;> simp [uniqueErasureOfClass, classRealizesErasure] at hReal ⊢

/-! ## Canonical Coverage and Irredundancy Proofs -/

/-- Concrete coverage proof for the canonical VM class basis. -/
theorem canonicalInstrBasis_erasureCoverage :
    VMErasureCoverage canonicalInstrBasis := by
  intro e
  cases e with
  | identity =>
      exact ⟨.sessionDomain, by simp [canonicalInstrBasis], by simp [classRealizesErasure]⟩
  | carrier =>
      exact ⟨.ownershipTransfer, by simp [canonicalInstrBasis], by simp [classRealizesErasure]⟩
  | nullifier =>
      exact ⟨.commValue, by simp [canonicalInstrBasis], by simp [classRealizesErasure]⟩
  | gauge =>
      exact ⟨.guard, by simp [canonicalInstrBasis], by simp [classRealizesErasure]⟩
  | labelProjection =>
      exact ⟨.commChoice, by simp [canonicalInstrBasis], by simp [classRealizesErasure]⟩
  | domainRestriction =>
      exact ⟨.sessionDomain, by simp [canonicalInstrBasis], by simp [classRealizesErasure]⟩
  | history =>
      exact ⟨.regControl, by simp [canonicalInstrBasis], by simp [classRealizesErasure]⟩
  | resourceReidentification =>
      exact ⟨.ownershipTransfer, by simp [canonicalInstrBasis], by simp [classRealizesErasure]⟩
  | handlerAbstraction =>
      exact ⟨.effect, by simp [canonicalInstrBasis], by simp [classRealizesErasure]⟩
  | permutation =>
      exact ⟨.concurrency, by simp [canonicalInstrBasis], by simp [classRealizesErasure]⟩
  | observerProjection =>
      exact ⟨.epistemic, by simp [canonicalInstrBasis], by simp [classRealizesErasure]⟩
  | timeParameter =>
      exact ⟨.regControl, by simp [canonicalInstrBasis], by simp [classRealizesErasure]⟩

/-- Concrete irredundancy proof for the canonical VM class basis. -/
theorem canonicalInstrBasis_erasureIrredundancy :
    VMErasureIrredundancy canonicalInstrBasis := by
  intro c hIn
  refine ⟨uniqueErasureOfClass c, class_realizes_uniqueErasure c, ?_⟩
  intro c' hIn' hNe hReal
  have hEq : c' = c := eq_of_realizes_uniqueErasure hReal
  exact hNe hEq

/-- Concrete VM <-> erasure exact correspondence theorem. -/
theorem canonicalInstrBasis_vmErasureExactCorrespondence :
    VMErasureExactCorrespondence canonicalInstrBasis := by
  exact ⟨canonicalInstrBasis_erasureCoverage, canonicalInstrBasis_erasureIrredundancy⟩

/-! ## Erasure-Basis Isomorphism -/

/-- Erasure-level basis isomorphism: two instruction-class bases realize
    exactly the same classical erasures. -/
def VMErasureBasisIsomorphic
    (declared₁ declared₂ : List InstrClass) : Prop :=
  ∀ e : ClassicalErasure,
    (∃ c : InstrClass, c ∈ declared₁ ∧ classRealizesErasure c e) ↔
      (∃ c : InstrClass, c ∈ declared₂ ∧ classRealizesErasure c e)

/-- Any two bases with full erasure coverage are isomorphic in erasure expressivity. -/
theorem vmErasureBasisIsomorphic_of_coverages
    {declared₁ declared₂ : List InstrClass}
    (hCov₁ : VMErasureCoverage declared₁)
    (hCov₂ : VMErasureCoverage declared₂) :
    VMErasureBasisIsomorphic declared₁ declared₂ := by
  intro e
  constructor
  · intro _hLeft
    rcases hCov₂ e with ⟨c, hIn, hReal⟩
    exact ⟨c, hIn, hReal⟩
  · intro _hRight
    rcases hCov₁ e with ⟨c, hIn, hReal⟩
    exact ⟨c, hIn, hReal⟩

/-- Canonical uniqueness closure (up to erasure isomorphism):
    any basis with exact VM↔erasure correspondence is equivalent to the canonical basis. -/
theorem canonicalInstrBasis_uniqueUpToErasureIsomorphism
    {declared : List InstrClass}
    (hExact : VMErasureExactCorrespondence declared) :
    VMErasureBasisIsomorphic declared canonicalInstrBasis := by
  exact vmErasureBasisIsomorphic_of_coverages hExact.1 canonicalInstrBasis_erasureCoverage

/-! ## Canonical Morphism Generation -/

/-- Canonical morphism set used by erasure-generation exactness:
    instruction classes from the canonical basis plus `ConfigEquiv`-level quotient morphisms. -/
inductive CanonicalErasureMorphism where
  | instrClass (c : InstrClass)
  | configEquiv
  deriving DecidableEq, Repr, Inhabited

/-- Membership in the canonical morphism generator set. -/
def inCanonicalErasureMorphismSet : CanonicalErasureMorphism → Prop
  | .instrClass c => c ∈ canonicalInstrBasis
  | .configEquiv => True

/-- Erasure semantics induced by canonical morphisms. -/
def canonicalMorphismRealizesErasure : CanonicalErasureMorphism → ClassicalErasure → Prop
  | .instrClass c, e => classRealizesErasure c e
  | .configEquiv, .identity => True
  | .configEquiv, .permutation => True
  | .configEquiv, .resourceReidentification => True
  | .configEquiv, _ => False

/-- Generated-erasure side of the exactness theorem. -/
def GeneratedByCanonicalMorphisms (e : ClassicalErasure) : Prop :=
  ∃ m : CanonicalErasureMorphism,
    inCanonicalErasureMorphismSet m ∧ canonicalMorphismRealizesErasure m e

/-- Safety-side presentation used in the exactness theorem. -/
def SafeClassicalErasure (e : ClassicalErasure) : Prop :=
  (∃ c : InstrClass, c ∈ canonicalInstrBasis ∧ classRealizesErasure c e) ∨
    canonicalMorphismRealizesErasure .configEquiv e

/-! ## Generated-By Equivalence -/

/-- Full exactness form for the classical-erasure boundary:
    safe erasures are exactly those generated by canonical VM/ConfigEquiv morphisms. -/
theorem safeClassicalErasure_iff_generatedByCanonicalMorphisms
    (e : ClassicalErasure) :
    SafeClassicalErasure e ↔ GeneratedByCanonicalMorphisms e := by
  constructor
  · intro hSafe
    rcases hSafe with hInstr | hCfg
    · rcases hInstr with ⟨c, hIn, hReal⟩
      exact ⟨.instrClass c, hIn, hReal⟩
    · exact ⟨.configEquiv, trivial, hCfg⟩
  · intro hGen
    rcases hGen with ⟨m, hIn, hReal⟩
    cases m with
    | instrClass c =>
        exact Or.inl ⟨c, hIn, hReal⟩
    | configEquiv =>
        exact Or.inr hReal

/-- Every tracked classical erasure is generated by canonical morphisms. -/
theorem all_classicalErasures_generatedByCanonicalMorphisms :
    ∀ e : ClassicalErasure, GeneratedByCanonicalMorphisms e := by
  intro e
  have hCov := canonicalInstrBasis_erasureCoverage e
  rcases hCov with ⟨c, hIn, hReal⟩
  exact ⟨.instrClass c, hIn, hReal⟩


end
