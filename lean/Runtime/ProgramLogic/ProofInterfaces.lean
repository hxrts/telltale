import Runtime.VM.TypeClasses
import Runtime.VM.DomainComposition
import Runtime.IrisBridge

/-
The Problem. Proof-only specifications (Iris pre/postconditions and namespace
invariants) should not live in the runtime VM surface that will be ported.

Solution Structure. Provide proof-layer interfaces that extend the runtime
models with Iris predicates and namespace bookkeeping.
-/

set_option autoImplicit false
noncomputable section

universe u

variable [Telltale.TelltaleIris]

/-! ## Guard-layer invariants -/

class GuardLayerInv (γ : Type u) [GuardLayer γ] where
  -- Namespace for this guard layer's invariant (proof-only).
  layerNs : γ → Namespace

instance instGuardLayerInvUnit : GuardLayerInv Unit where
  -- Unit guard layer uses the root namespace.
  layerNs := fun _ => Namespace.root

private def combineNs (n₁ n₂ : Namespace) : Namespace :=
  -- Deterministic namespace combination for product layers.
  let _ := n₁
  let _ := n₂
  Namespace.append (Namespace.append Namespace.root "guard") "pair"

instance instGuardLayerInvProd (γ₁ γ₂ : Type u)
    [GuardLayer γ₁] [GuardLayer γ₂]
    [GuardLayerInv γ₁] [GuardLayerInv γ₂] : GuardLayerInv (γ₁ × γ₂) where
  -- Product layers combine component namespaces.
  layerNs := fun g => combineNs (GuardLayerInv.layerNs g.1) (GuardLayerInv.layerNs g.2)

/-! ## Guard-chain proof well-formedness -/

def GuardChain.proofNamespaces {γ : Type u} [GuardLayer γ] [GuardLayerInv γ]
    (chain : GuardChain γ) : List Namespace :=
  -- Extract namespaces in order for disjointness checks.
  chain.layers.map GuardLayerInv.layerNs

def GuardChain.proofWf {γ : Type u} [GuardLayer γ] [GuardLayerInv γ]
    (chain : GuardChain γ) : Prop :=
  -- Pairwise namespace disjointness for proof invariants.
  List.Pairwise
    (fun n₁ n₂ => Mask.disjoint (namespace_to_mask n₁) (namespace_to_mask n₂))
    (GuardChain.proofNamespaces chain)

/-! ## Effect proof specifications -/

class EffectProofSpec (ε : Type u) [EffectRuntime ε] where
  -- Pre- and post-conditions for effect actions (proof-only).
  pre : EffectRuntime.EffectAction ε → EffectRuntime.EffectCtx ε → iProp
  post : EffectRuntime.EffectAction ε → EffectRuntime.EffectCtx ε → iProp

instance instEffectProofSpecUnit : EffectProofSpec Unit where
  -- Unit effects carry no proof obligations.
  pre := fun _ _ => iProp.emp
  post := fun _ _ => iProp.emp

instance instEffectProofSpecSum (ε₁ ε₂ : Type u)
    [EffectRuntime ε₁] [EffectRuntime ε₂]
    [EffectProofSpec ε₁] [EffectProofSpec ε₂] : EffectProofSpec (Sum ε₁ ε₂) where
  -- Sum effects dispatch to the corresponding proof spec.
  pre := fun a ctx =>
    match a, ctx with
    | Sum.inl a1, (c1, _) => EffectProofSpec.pre a1 c1
    | Sum.inr a2, (_, c2) => EffectProofSpec.pre a2 c2
  post := fun a ctx =>
    match a, ctx with
    | Sum.inl a1, (c1, _) => EffectProofSpec.post a1 c1
    | Sum.inr a2, (_, c2) => EffectProofSpec.post a2 c2

instance instEffectProofSpecProd (ε₁ ε₂ : Type u)
    [EffectRuntime ε₁] [EffectRuntime ε₂]
    [EffectProofSpec ε₁] [EffectProofSpec ε₂] : EffectProofSpec (ε₁ × ε₂) where
  -- Product effects compose proof obligations via separation.
  pre := fun a ctx =>
    match a, ctx with
    | (a1, a2), (c1, c2) =>
        iProp.sep (EffectProofSpec.pre a1 c1) (EffectProofSpec.pre a2 c2)
  post := fun a ctx =>
    match a, ctx with
    | (a1, a2), (c1, c2) =>
        iProp.sep (EffectProofSpec.post a1 c1) (EffectProofSpec.post a2 c2)
