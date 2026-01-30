import Runtime.Shim.ResourceAlgebra

/-!
# SavedProp: Saved Propositions and Ghost Variables

Axiom shims for saved propositions and ghost variables.
Retires when: iris_2.md Tasks 9E–9F land.
Unblocks: Tasks 16, 20.
-/

set_option autoImplicit false

/-! ## Saved Propositions -/

axiom saved_prop_own (γ : GhostName) (P : iProp) : iProp
axiom saved_prop_alloc (P : iProp) :
    iProp.entails iProp.emp (bupd (iProp.exist fun γ => saved_prop_own γ P))
axiom saved_prop_agree (γ : GhostName) (P Q : iProp) :
    iProp.entails (iProp.sep (saved_prop_own γ P) (saved_prop_own γ Q))
      (iProp.sep (iProp.later (iProp.wand P Q)) (iProp.later (iProp.wand Q P)))
axiom saved_prop_persistent (γ : GhostName) (P : iProp) :
    iProp.entails (saved_prop_own γ P) (iProp.persistently (saved_prop_own γ P))

/-! ## Ghost Variables -/

axiom ghost_var (γ : GhostName) {α : Type} (a : α) : iProp
axiom ghost_var_alloc {α : Type} (a : α) :
    iProp.entails iProp.emp (bupd (iProp.exist fun γ => ghost_var γ a))
axiom ghost_var_agree {α : Type} (γ : GhostName) (a b : α) :
    iProp.entails (iProp.sep (ghost_var γ a) (ghost_var γ b)) (iProp.pure (a = b))
axiom ghost_var_update {α : Type} (γ : GhostName) (a b : α) :
    iProp.entails (ghost_var γ a) (bupd (ghost_var γ b))
