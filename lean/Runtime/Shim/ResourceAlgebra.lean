/-!
# ResourceAlgebra: Resource Algebra and Ghost State

Axiom shims for resource algebra primitives.
Retires when: iris.md Tasks 1+3+8, iris_2.md Task 9D land.
Unblocks: Tasks 13, 14, 15, 18, 20, 24.
-/

set_option autoImplicit false

/-! ## Core iProp and Separation Logic -/

axiom GhostName : Type
axiom iProp : Type
axiom iProp.entails : iProp → iProp → Prop
axiom iProp.emp : iProp
axiom iProp.sep : iProp → iProp → iProp
axiom iProp.wand : iProp → iProp → iProp
axiom iProp.pure : Prop → iProp
axiom iProp.later : iProp → iProp
axiom iProp.persistently : iProp → iProp
axiom iProp.exist {α : Type} : (α → iProp) → iProp
axiom iProp.forall {α : Type} : (α → iProp) → iProp

-- Separation logic rules
axiom sep_comm (P Q : iProp) :
    iProp.entails (iProp.sep P Q) (iProp.sep Q P)
axiom sep_assoc (P Q R : iProp) :
    iProp.entails (iProp.sep (iProp.sep P Q) R) (iProp.sep P (iProp.sep Q R))
axiom sep_mono (P P' Q Q' : iProp) :
    iProp.entails P P' → iProp.entails Q Q' →
    iProp.entails (iProp.sep P Q) (iProp.sep P' Q')
axiom wand_intro (P Q R : iProp) :
    iProp.entails (iProp.sep P Q) R → iProp.entails P (iProp.wand Q R)
axiom wand_elim (P Q : iProp) :
    iProp.entails (iProp.sep (iProp.wand P Q) P) Q
axiom pure_intro (φ : Prop) (P : iProp) :
    φ → iProp.entails P (iProp.sep (iProp.pure φ) P)
axiom pure_elim (φ : Prop) (P : iProp) :
    (φ → iProp.entails iProp.emp P) → iProp.entails (iProp.pure φ) P
axiom persistently_idemp (P : iProp) :
    iProp.entails (iProp.persistently (iProp.persistently P)) (iProp.persistently P)
axiom persistently_sep_dup (P : iProp) :
    iProp.entails (iProp.persistently P) (iProp.sep (iProp.persistently P) (iProp.persistently P))

/-! ## Ghost Ownership -/

-- Placeholder typeclasses for RA interface
class Valid (α : Type) where valid : α → Prop
class Included (α : Type) where included : α → α → Prop
class FramePreservingUpdate (α : Type) where fpu : α → α → Prop
class LocalUpdate (α : Type) where lu : (α × α) → (α × α) → Prop

axiom own (γ : GhostName) {α : Type} (a : α) : iProp

/-! ## Basic Update Modality -/

axiom bupd : iProp → iProp
axiom bupd_mono (P Q : iProp) :
    iProp.entails P Q → iProp.entails (bupd P) (bupd Q)
axiom bupd_intro (P : iProp) : iProp.entails P (bupd P)
axiom bupd_trans (P : iProp) : iProp.entails (bupd (bupd P)) (bupd P)
axiom bupd_frame_r (P Q : iProp) :
    iProp.entails (iProp.sep (bupd P) Q) (bupd (iProp.sep P Q))

axiom own_update (γ : GhostName) {α : Type} (a b : α)
    [FramePreservingUpdate α] :
    iProp.entails (own γ a) (bupd (own γ b))
axiom own_alloc {α : Type} (a : α) [Valid α] :
    iProp.entails iProp.emp (bupd (iProp.exist fun γ => own γ a))

/-! ## Auth RA -/

axiom Auth (α : Type) : Type
axiom Auth.auth {α : Type} (a : α) : Auth α
axiom Auth.frag {α : Type} (b : α) : Auth α
axiom auth_frag_included {α : Type} (γ : GhostName) (a b : α)
    [Included α] :
    iProp.entails (iProp.sep (own γ (Auth.auth a)) (own γ (Auth.frag b)))
      (iProp.pure (Included.included b a))
axiom auth_update {α : Type} (γ : GhostName) (a a' b b' : α)
    [LocalUpdate α] :
    iProp.entails (iProp.sep (own γ (Auth.auth a)) (own γ (Auth.frag b)))
      (bupd (iProp.sep (own γ (Auth.auth a')) (own γ (Auth.frag b'))))

/-! ## Ghost Map -/

axiom GMap (K V : Type) : Type
axiom GMap.lookup {K V : Type} : GMap K V → K → Option V
axiom GMap.insert {K V : Type} : GMap K V → K → V → GMap K V
axiom GMap.delete {K V : Type} : GMap K V → K → GMap K V

axiom ghost_map_auth (γ : GhostName) {K V : Type} (m : GMap K V) : iProp
axiom ghost_map_elem (γ : GhostName) {K V : Type} (k : K) (v : V) : iProp
axiom ghost_map_alloc {K V : Type} (m : GMap K V) :
    iProp.entails iProp.emp (bupd (iProp.exist fun γ =>
      iProp.sep (ghost_map_auth γ m)
        (iProp.forall fun k => iProp.forall fun v =>
          iProp.wand (iProp.pure (GMap.lookup m k = some v)) (ghost_map_elem γ k v))))
axiom ghost_map_lookup {K V : Type} (γ : GhostName) (k : K) (v : V) (m : GMap K V) :
    iProp.entails (iProp.sep (ghost_map_auth γ m) (ghost_map_elem γ k v))
      (iProp.pure (GMap.lookup m k = some v))
axiom ghost_map_insert {K V : Type} (γ : GhostName) (k : K) (v : V) (m : GMap K V)
    (hNone : GMap.lookup m k = none) :
    iProp.entails (ghost_map_auth γ m)
      (bupd (iProp.sep (ghost_map_auth γ (GMap.insert m k v)) (ghost_map_elem γ k v)))
axiom ghost_map_update {K V : Type} (γ : GhostName) (k : K) (v v' : V) (m : GMap K V) :
    iProp.entails (iProp.sep (ghost_map_auth γ m) (ghost_map_elem γ k v))
      (bupd (iProp.sep (ghost_map_auth γ (GMap.insert m k v')) (ghost_map_elem γ k v')))
axiom ghost_map_delete {K V : Type} (γ : GhostName) (k : K) (v : V) (m : GMap K V) :
    iProp.entails (iProp.sep (ghost_map_auth γ m) (ghost_map_elem γ k v))
      (bupd (ghost_map_auth γ (GMap.delete m k)))

/-! ## Big Separating Conjunction -/

axiom big_sepL {α : Type} (Φ : α → iProp) : List α → iProp
axiom big_sepM {K V : Type} (Φ : K → V → iProp) : GMap K V → iProp
axiom big_sepL_nil {α : Type} (Φ : α → iProp) :
    iProp.entails (big_sepL Φ []) iProp.emp
axiom big_sepL_cons {α : Type} (Φ : α → iProp) (x : α) (l : List α) :
    iProp.entails (big_sepL Φ (x :: l)) (iProp.sep (Φ x) (big_sepL Φ l))
axiom big_sepL_app {α : Type} (Φ : α → iProp) (l₁ l₂ : List α) :
    iProp.entails (big_sepL Φ (l₁ ++ l₂)) (iProp.sep (big_sepL Φ l₁) (big_sepL Φ l₂))
axiom big_sepM_insert {K V : Type} (Φ : K → V → iProp) (m : GMap K V) (k : K) (v : V)
    (hNone : GMap.lookup m k = none) :
    iProp.entails (big_sepM Φ (GMap.insert m k v)) (iProp.sep (Φ k v) (big_sepM Φ m))
axiom big_sepM_lookup {K V : Type} (Φ : K → V → iProp) (m : GMap K V) (k : K) (v : V)
    (hLook : GMap.lookup m k = some v) :
    iProp.entails (big_sepM Φ m) (iProp.sep (Φ k v) (big_sepM Φ (GMap.delete m k)))
