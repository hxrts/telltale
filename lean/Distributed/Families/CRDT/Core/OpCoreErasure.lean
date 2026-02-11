import Distributed.Families.CRDT.Core.CoreModel

/-! # CRDT OpCore Erasure Theory

Erasure soundness, completeness, and maximality theorems for lowering
rich CRDT operation types to the canonical `OpCore` representation. -/

/-
The Problem. Rich CRDT types carry extra structure (timestamps, actor IDs,
metadata) beyond what the core lattice operations require. We need to
"erase" this to `OpCore` while preserving observable equivalence, and
show the erasure is both complete (covers all behaviors) and maximal
(no coarser sound erasure exists).

Solution Structure. Define `ErasureSoundness`, `ErasureCompleteness`,
`ErasureMaximality` predicates. Bundle into `WeakestOpCoreErasureTheorem`.
Provide `FamilyLoweringAdequacy` for family-level lowering proofs.
-/

set_option autoImplicit false

namespace Distributed
namespace CRDT

universe u v w x y z

/-! ## Erasure Predicates -/

abbrev ErasureMap (KRich : Type z) (OpTag : Type v) (Args : Type w) :=
  KRich → OpCore OpTag Args

/-- Erasure soundness: rich execution and erased-core execution agree observably. -/
def ErasureSoundness
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (evalRich : KRich → Context → State → State)
    (interp : OpCoreInterpreter State Context OpTag Args)
    (erase : ErasureMap KRich OpTag Args) : Prop :=
  ∀ kr ctx s, EqSafe M (evalRich kr ctx s) (evalCore interp (erase kr) ctx s)

/-- Erasure completeness: each `OpCore` behavior is realizable by some rich continuation. -/
def ErasureCompleteness
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args)
    (erase : ErasureMap KRich OpTag Args) : Prop :=
  ∀ kc : OpCore OpTag Args, ∃ kr : KRich,
    ∀ ctx s, EqSafe M (evalCore interp kc ctx s) (evalCore interp (erase kr) ctx s)

/-- Relative maximality: any equally-sound erasure factors through the chosen erasure. -/
def ErasureMaximality
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args)
    (erase : ErasureMap KRich OpTag Args) : Prop :=
  ∀ erase' : ErasureMap KRich OpTag Args,
    (∀ kr ctx s,
      EqSafe M (evalCore interp (erase' kr) ctx s) (evalCore interp (erase kr) ctx s)) →
      ∃ normalize : OpCore OpTag Args → OpCore OpTag Args,
        ∀ kr, erase' kr = normalize (erase kr)

/-- Weakest-core erasure theorem shape (soundness + completeness + maximality). -/
def WeakestOpCoreErasureTheorem
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (evalRich : KRich → Context → State → State)
    (interp : OpCoreInterpreter State Context OpTag Args)
    (erase : ErasureMap KRich OpTag Args) : Prop :=
  ErasureSoundness M evalRich interp erase ∧
  ErasureCompleteness M interp erase ∧
  ErasureMaximality M interp erase

/-- Lowering relation used by compile-time conformance gates. -/
abbrev LowerToCore (KRich : Type z) (OpTag : Type v) (Args : Type w) :=
  KRich → Option (OpCore OpTag Args)

/-- Compile-time gate: accept exactly when lowering evidence exists. -/
def conformanceGate
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (lower : LowerToCore KRich OpTag Args) (kr : KRich) : Bool :=
  (lower kr).isSome

/-- Conformance gate rejects operations that cannot be lowered to `OpCore`. -/
theorem conformanceGate_rejects_nonlowerable
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (lower : LowerToCore KRich OpTag Args) (kr : KRich)
    (h : lower kr = none) :
    conformanceGate lower kr = false := by
  simp [conformanceGate, h]

/-- Conformance gate accepts operations that lower to some `OpCore` payload. -/
theorem conformanceGate_accepts_lowerable
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (lower : LowerToCore KRich OpTag Args) (kr : KRich) (kc : OpCore OpTag Args)
    (h : lower kr = some kc) :
    conformanceGate lower kr = true := by
  simp [conformanceGate, h]

/-- Erasure premise bundle for least-expressive `OpCore` theorem proving. -/
structure ErasurePremises
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (KRich : Type z) (OpTag : Type v) (Args : Type w) (Enc : Type x) :
    Type (max u v w x y z) where
  evalRich : KRich → Context → State → State
  interp : OpCoreInterpreter State Context OpTag Args
  erase : ErasureMap KRich OpTag Args
  lower : LowerToCore KRich OpTag Args
  encode : OpCore OpTag Args → Enc
  decode : Enc → Option (OpCore OpTag Args)
  weakestWitness : WeakestOpCoreErasureTheorem M evalRich interp erase
  replayStableWitness : ReplayStableCoreEval interp
  serializationWitness : TransportSerializationInvariant encode decode
  lowerSound : ∀ kr kc, lower kr = some kc → kc = erase kr

/-- Derive weakest-core erasure theorem from explicit erasure premises. -/
theorem weakestOpCoreErasure_of_premises
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (p : ErasurePremises M KRich OpTag Args Enc) :
    WeakestOpCoreErasureTheorem M p.evalRich p.interp p.erase :=
  p.weakestWitness

/-- Derive replay stability of `OpCore` evaluation from erasure premises. -/
theorem opCoreReplayStable_of_premises
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (p : ErasurePremises M KRich OpTag Args Enc) :
    ReplayStableCoreEval p.interp :=
  p.replayStableWitness

/-- Derive transport-serialization invariance from erasure premises. -/
theorem opCoreSerializationInvariant_of_premises
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (p : ErasurePremises M KRich OpTag Args Enc) :
    TransportSerializationInvariant p.encode p.decode :=
  p.serializationWitness

/-- Conformance-gate theorem from lowering evidence. -/
theorem conformanceGate_of_loweringSound
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (p : ErasurePremises M KRich OpTag Args Enc) (kr : KRich) :
    conformanceGate p.lower kr = true ↔ ∃ kc, p.lower kr = some kc := by
  unfold conformanceGate
  constructor
  · intro hSome
    cases h : p.lower kr with
    | none =>
        simp [h] at hSome
    | some kc =>
        exact ⟨kc, rfl⟩
  · intro hLowered
    rcases hLowered with ⟨kc, hk⟩
    simp [hk]

/-- `ErasurePremises` viewed as an admissible serializable-AST continuation model. -/
abbrev SerializableASTContinuationModel
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (KRich : Type z) (OpTag : Type v) (Args : Type w) (Enc : Type x) :=
  ErasurePremises M KRich OpTag Args Enc

/-- Serializable continuation constructs unsupported by `OpCore` lowering. -/
def UnsupportedSerializableConstruct
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (p : SerializableASTContinuationModel M KRich OpTag Args Enc) (kr : KRich) : Prop :=
  p.lower kr = none

/-- Least-expressiveness: any admissible serializable AST model factors through `OpCore`. -/
theorem serializableAST_reducible_to_OpCore
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (p : SerializableASTContinuationModel M KRich OpTag Args Enc)
    (erase' : ErasureMap KRich OpTag Args)
    (hObs :
      ∀ kr ctx s,
        EqSafe M (evalCore p.interp (erase' kr) ctx s) (evalCore p.interp (p.erase kr) ctx s)) :
    ∃ normalize : OpCore OpTag Args → OpCore OpTag Args,
      ∀ kr, erase' kr = normalize (p.erase kr) := by
  exact (weakestOpCoreErasure_of_premises p).2.2 erase' hObs

/-- Classification theorem: rich constructs are either reducible to `OpCore` or rejected. -/
theorem serializableAST_reducible_or_rejected
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (p : SerializableASTContinuationModel M KRich OpTag Args Enc)
    (kr : KRich) (ctx : Context) (s : State) :
    (∃ kc, p.lower kr = some kc ∧ EqSafe M (p.evalRich kr ctx s) (evalCore p.interp kc ctx s)) ∨
      (UnsupportedSerializableConstruct p kr ∧ conformanceGate p.lower kr = false) := by
  cases hLower : p.lower kr with
  | none =>
      right
      exact ⟨hLower, conformanceGate_rejects_nonlowerable p.lower kr hLower⟩
  | some kc =>
      left
      have hSound : EqSafe M (p.evalRich kr ctx s) (evalCore p.interp (p.erase kr) ctx s) :=
        (weakestOpCoreErasure_of_premises p).1 kr ctx s
      have hk : kc = p.erase kr := p.lowerSound kr kc hLower
      refine ⟨kc, rfl, ?_⟩
      simpa [hk] using hSound

/-- A concrete rich continuation fragment equivalent to core payloads. -/
inductive CoreEquivalentKRich (OpTag : Type v) (Args : Type w) where
  | core : OpCore OpTag Args → CoreEquivalentKRich OpTag Args
  deriving Repr, DecidableEq, Inhabited

/-- Erasure for the core-equivalent rich fragment. -/
def eraseCoreEquivalent
    {OpTag : Type v} {Args : Type w} :
    CoreEquivalentKRich OpTag Args → OpCore OpTag Args
  | .core kc => kc

/-- Rich evaluator for the core-equivalent fragment. -/
def evalRichCoreEquivalent
    {State : Type u} {Context : Type v} {OpTag : Type w} {Args : Type x}
    (interp : OpCoreInterpreter State Context OpTag Args) :
    CoreEquivalentKRich OpTag Args → Context → State → State
  | .core kc, ctx, s => evalCore interp kc ctx s

/-- Lowering function for the core-equivalent fragment. -/
def lowerCoreEquivalent
    {OpTag : Type v} {Args : Type w} :
    LowerToCore (CoreEquivalentKRich OpTag Args) OpTag Args
  | .core kc => some kc

/-- Soundness for the core-equivalent erasure fragment. -/
theorem erasureSoundness_coreEquivalent
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args) :
    ErasureSoundness M (evalRichCoreEquivalent interp) interp eraseCoreEquivalent := by
  intro kr ctx s
  cases kr with
  | core kc =>
      rfl

/-- Completeness for the core-equivalent erasure fragment. -/
theorem erasureCompleteness_coreEquivalent
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args) :
    ErasureCompleteness M interp eraseCoreEquivalent := by
  intro kc
  refine ⟨CoreEquivalentKRich.core kc, ?_⟩
  intro ctx s
  rfl

/-- Maximality for the core-equivalent erasure fragment. -/
theorem erasureMaximality_coreEquivalent
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args) :
    ErasureMaximality M interp eraseCoreEquivalent := by
  intro erase' _hEq
  refine ⟨fun kc => erase' (.core kc), ?_⟩
  intro kr
  cases kr with
  | core kc => rfl

/-- Weakest-core erasure theorem for the core-equivalent rich fragment. -/
theorem weakestOpCoreErasure_coreEquivalent
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args) :
    WeakestOpCoreErasureTheorem M (evalRichCoreEquivalent interp) interp eraseCoreEquivalent := by
  refine ⟨?_, ?_, ?_⟩
  · exact erasureSoundness_coreEquivalent M interp
  · exact erasureCompleteness_coreEquivalent M interp
  · exact erasureMaximality_coreEquivalent M interp

/-- Lowering soundness for the core-equivalent rich fragment. -/
theorem lowerCoreEquivalent_sound
    {OpTag : Type v} {Args : Type w}
    (kr : CoreEquivalentKRich OpTag Args) (kc : OpCore OpTag Args)
    (h : lowerCoreEquivalent kr = some kc) :
    kc = eraseCoreEquivalent kr := by
  cases kr with
  | core kc' =>
      simp [lowerCoreEquivalent] at h
      simpa [eraseCoreEquivalent] using h.symm

/-- Conformance gate accepts all core-equivalent rich continuations. -/
theorem conformanceGate_coreEquivalent_true
    {OpTag : Type v} {Args : Type w}
    (kr : CoreEquivalentKRich OpTag Args) :
    conformanceGate lowerCoreEquivalent kr = true := by
  cases kr with
  | core kc =>
      simp [conformanceGate, lowerCoreEquivalent]

/-- Families that are exactly representable by `OpCore` payloads. -/
class CoreRepresentableFamily
    (KRich : Type z) (OpTag : Type v) (Args : Type w) where
  toCore : KRich → OpCore OpTag Args
  ofCore : OpCore OpTag Args → KRich
  toCore_ofCore : ∀ kc, toCore (ofCore kc) = kc
  ofCore_toCore : ∀ kr, ofCore (toCore kr) = kr

/-- Rich-step evaluator induced by a core-representable family embedding. -/
def evalRichCoreRepresentable
    {State : Type u} {Context : Type v} {OpTag : Type w} {Args : Type x}
    (interp : OpCoreInterpreter State Context OpTag Args)
    {KRich : Type y} [CoreRepresentableFamily KRich OpTag Args] :
    KRich → Context → State → State
  | kr, ctx, s => evalCore interp (CoreRepresentableFamily.toCore kr) ctx s

/-- Total lowering induced by a core-representable family embedding. -/
def lowerCoreRepresentable
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    [CoreRepresentableFamily KRich OpTag Args] :
    LowerToCore KRich OpTag Args :=
  fun kr => some (CoreRepresentableFamily.toCore kr)

/-- Totality of lowering for core-representable rich families. -/
theorem lowerCoreRepresentable_total
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    [CoreRepresentableFamily KRich OpTag Args] :
    ∀ kr : KRich, ∃ kc,
      lowerCoreRepresentable (KRich := KRich) (OpTag := OpTag) (Args := Args) kr = some kc := by
  intro kr
  exact ⟨CoreRepresentableFamily.toCore kr, rfl⟩

/-- Pointwise observational preservation for core-representable lowering. -/
theorem stepObsPreserved_coreRepresentable
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    [CoreRepresentableFamily KRich OpTag Args]
    (interp : OpCoreInterpreter State Context OpTag Args) :
    ∀ kr ctx s kc,
      lowerCoreRepresentable (KRich := KRich) (OpTag := OpTag) (Args := Args) kr = some kc →
        EqSafe M (evalRichCoreRepresentable interp kr ctx s) (evalCore interp kc ctx s) := by
  intro kr ctx s kc hLower
  simp [lowerCoreRepresentable] at hLower
  subst kc
  rfl

/-- Adequacy witness for one rich-family lowering into `OpCore`. -/
structure FamilyLoweringAdequacy
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (KRich : Type z) (OpTag : Type v) (Args : Type w) where
  interp : OpCoreInterpreter State Context OpTag Args
  evalRich : KRich → Context → State → State
  lower : LowerToCore KRich OpTag Args
  totalLowering : ∀ kr, ∃ kc, lower kr = some kc
  stepObsPreserved :
    ∀ kr ctx s kc, lower kr = some kc →
      EqSafe M (evalRich kr ctx s) (evalCore interp kc ctx s)

/-- Run-level envelope preservation induced by pointwise lowering adequacy. -/
theorem envelopePreserved_of_familyLowering
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (F : FamilyLoweringAdequacy M KRich OpTag Args)
    (runRich : Nat → KRich)
    (runCore : Nat → OpCore OpTag Args)
    (ctx : Context)
    (stateRun : Run State)
    (hLower : ∀ n, F.lower (runRich n) = some (runCore n)) :
    Envelope M
      (fun n => F.evalRich (runRich n) ctx (stateRun n))
      (fun n => evalCore F.interp (runCore n) ctx (stateRun n)) := by
  intro n
  exact F.stepObsPreserved (runRich n) ctx (stateRun n) (runCore n) (hLower n)

/-- Combined adequacy statement for one rich-family lowering. -/
def FamilyEnvelopeAdequate
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (F : FamilyLoweringAdequacy M KRich OpTag Args) : Prop :=
  (∀ kr, ∃ kc, F.lower kr = some kc) ∧
  (∀ kr ctx s kc, F.lower kr = some kc →
      EqSafe M (F.evalRich kr ctx s) (evalCore F.interp kc ctx s)) ∧
  (∀ (runRich : Nat → KRich) (runCore : Nat → OpCore OpTag Args)
      (ctx : Context) (stateRun : Run State),
      (∀ n, F.lower (runRich n) = some (runCore n)) →
        Envelope M
          (fun n => F.evalRich (runRich n) ctx (stateRun n))
          (fun n => evalCore F.interp (runCore n) ctx (stateRun n)))

/-- Every `FamilyLoweringAdequacy` witness yields `FamilyEnvelopeAdequate`. -/
theorem familyEnvelopeAdequate_of_lowering
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (F : FamilyLoweringAdequacy M KRich OpTag Args) :
    FamilyEnvelopeAdequate M F := by
  refine ⟨F.totalLowering, F.stepObsPreserved, ?_⟩
  intro runRich runCore ctx stateRun hLower
  exact envelopePreserved_of_familyLowering F runRich runCore ctx stateRun hLower

end CRDT
end Distributed
