import Runtime.Shim.ResourceAlgebra

/-!
# Invariants: Fancy Updates and Invariants

Axiom shims for masks, fancy update modality, invariants, and cancelable invariants.
Retires when: iris.md Tasks 2–6 land.
Unblocks: Tasks 16, 19, 21, 23.
-/

set_option autoImplicit false

/-! ## Masks and Namespaces -/

axiom Mask : Type
axiom Mask.top : Mask
axiom Mask.empty : Mask
axiom Mask.diff : Mask → Mask → Mask
axiom Mask.union : Mask → Mask → Mask
axiom Mask.subseteq : Mask → Mask → Prop
axiom Mask.disjoint : Mask → Mask → Prop
axiom Mask.singleton : Nat → Mask

axiom Namespace : Type
axiom Namespace.root : Namespace
axiom Namespace.append : Namespace → String → Namespace
axiom Namespace.append_nat : Namespace → Nat → Namespace
axiom namespace_to_mask : Namespace → Mask
axiom namespace_disjoint (N₁ N₂ : Namespace) (h : N₁ ≠ N₂) :
    Mask.disjoint (namespace_to_mask N₁) (namespace_to_mask N₂)

/-! ## Fancy Update Modality -/

axiom fupd (E₁ E₂ : Mask) : iProp → iProp
axiom fupd_intro (E : Mask) (P : iProp) : iProp.entails P (fupd E E P)
axiom fupd_mono (E₁ E₂ : Mask) (P Q : iProp) :
    iProp.entails P Q → iProp.entails (fupd E₁ E₂ P) (fupd E₁ E₂ Q)
axiom fupd_trans (E₁ E₂ E₃ : Mask) (P : iProp) :
    iProp.entails (fupd E₁ E₂ (fupd E₂ E₃ P)) (fupd E₁ E₃ P)
axiom fupd_frame_r (E₁ E₂ : Mask) (P Q : iProp) :
    iProp.entails (iProp.sep (fupd E₁ E₂ P) Q) (fupd E₁ E₂ (iProp.sep P Q))
axiom fupd_mask_subseteq (E₁ E₂ : Mask) (hSub : Mask.subseteq E₂ E₁) :
    iProp.entails iProp.emp (fupd E₁ E₂ (fupd E₂ E₁ iProp.emp))

/-! ## Invariants -/

axiom inv (N : Namespace) (P : iProp) : iProp
axiom inv_persistent (N : Namespace) (P : iProp) :
    iProp.entails (inv N P) (iProp.persistently (inv N P))
axiom inv_alloc (N : Namespace) (E : Mask) (P : iProp) :
    iProp.entails (iProp.later P) (fupd E E (inv N P))
axiom inv_acc (N : Namespace) (E : Mask) (P : iProp)
    (hSub : Mask.subseteq (namespace_to_mask N) E) :
    iProp.entails (inv N P) (fupd E (Mask.diff E (namespace_to_mask N))
      (iProp.sep (iProp.later P)
        (iProp.wand (iProp.later P) (fupd (Mask.diff E (namespace_to_mask N)) E iProp.emp))))

/-! ## Cancelable Invariants -/

axiom CancelToken : Type
axiom cancel_token_own : CancelToken → iProp
axiom cinv (N : Namespace) (ct : CancelToken) (P : iProp) : iProp
axiom cinv_persistent (N : Namespace) (ct : CancelToken) (P : iProp) :
    iProp.entails (cinv N ct P) (iProp.persistently (cinv N ct P))
axiom cinv_alloc (N : Namespace) (E : Mask) (P : iProp) :
    iProp.entails (iProp.later P) (fupd E E (iProp.exist fun ct =>
      iProp.sep (cinv N ct P) (cancel_token_own ct)))
axiom cinv_acc (N : Namespace) (E : Mask) (ct : CancelToken) (P : iProp)
    (hSub : Mask.subseteq (namespace_to_mask N) E) :
    iProp.entails (cinv N ct P)
      (fupd E (Mask.diff E (namespace_to_mask N))
        (iProp.sep (iProp.later P)
          (iProp.wand (iProp.later P) (fupd (Mask.diff E (namespace_to_mask N)) E iProp.emp))))
axiom cinv_cancel (N : Namespace) (E : Mask) (ct : CancelToken) (P : iProp)
    (hSub : Mask.subseteq (namespace_to_mask N) E) :
    iProp.entails (iProp.sep (cinv N ct P) (cancel_token_own ct))
      (fupd E (Mask.diff E (namespace_to_mask N)) (iProp.later P))
