import Protocol.Coherence.Renaming
/-! # Protocol.Coherence.ConfigEquivRenaming
Renaming algebra and cancellation lemmas used by coherence-configuration equivalence.
-/

/-
The Problem. The configuration-equivalence layer depends on a reusable core of
session-id isomorphisms and renaming composition/identity facts for values,
local types, endpoints, and environments.

Solution Structure.
1. Define session isomorphisms and their induced renamings.
2. Prove composition and identity laws for renaming functions.
3. Prove inverse-cancellation lemmas under isomorphisms.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section
/-! ## Session Isomorphisms -/

/-- A bijection on session IDs, given by explicit inverses. -/
structure SessionIso where
  -- Forward map on session IDs.
  fwd : SessionId → SessionId
  -- Inverse map on session IDs.
  bwd : SessionId → SessionId
  -- Left inverse property.
  left_inv : ∀ s, bwd (fwd s) = s
  -- Right inverse property.
  right_inv : ∀ s, fwd (bwd s) = s

namespace SessionIso

/-- Forward renaming from an isomorphism. -/
def toRenaming (σ : SessionIso) : SessionRenaming :=
  { f := σ.fwd
    inv := σ.bwd
    left_inv := σ.left_inv
    inj := by
      -- Injectivity follows by applying the inverse to both sides.
      intro s1 s2 h
      have := congrArg σ.bwd h
      simpa [σ.left_inv] using this }

/-- Inverse renaming from an isomorphism. -/
def invRenaming (σ : SessionIso) : SessionRenaming :=
  { f := σ.bwd
    inv := σ.fwd
    left_inv := σ.right_inv
    inj := by
      -- Injectivity follows by applying the forward map to both sides.
      intro s1 s2 h
      have := congrArg σ.fwd h
      simpa [σ.right_inv] using this }

/-- Identity isomorphism on session IDs. -/
def id : SessionIso :=
  { fwd := fun s => s
    bwd := fun s => s
    left_inv := by
      -- Identity composes to identity.
      intro s; rfl
    right_inv := by
      -- Symmetric argument for the right inverse.
      intro s; rfl }

/-- Symmetric isomorphism (swap directions). -/
def symm (σ : SessionIso) : SessionIso :=
  { fwd := σ.bwd
    bwd := σ.fwd
    left_inv := by
      -- Swapping turns right-inverse into left-inverse.
      intro s; simpa using (σ.right_inv s)
    right_inv := by
      -- Swapping turns left-inverse into right-inverse.
      intro s; simpa using (σ.left_inv s) }

/-- Composition of isomorphisms (σ₂ ∘ σ₁). -/
def comp (σ₂ σ₁ : SessionIso) : SessionIso :=
  { fwd := fun s => σ₂.fwd (σ₁.fwd s)
    bwd := fun s => σ₁.bwd (σ₂.bwd s)
    left_inv := by
      -- Inverses compose in the opposite order.
      intro s; simp [σ₁.left_inv, σ₂.left_inv]
    right_inv := by
      -- Forward maps compose in order.
      intro s; simp [σ₁.right_inv, σ₂.right_inv] }

end SessionIso

namespace SessionRenaming

/-- Identity session renaming. -/
def id : SessionRenaming :=
  { f := fun s => s
    inv := fun s => s
    left_inv := by
      intro s
      rfl
    inj := by
      -- Identity is injective by reflexivity.
      intro s1 s2 h; simpa using h }

/-- Composition of renamings (ρ₂ ∘ ρ₁). -/
def comp (ρ₂ ρ₁ : SessionRenaming) : SessionRenaming :=
  { f := fun s => ρ₂.f (ρ₁.f s)
    inv := fun s => ρ₁.inv (ρ₂.inv s)
    left_inv := by
      intro s
      simp [ρ₂.left_inv, ρ₁.left_inv]
    inj := by
      -- Injectivity comes from injectivity of each component.
      intro s1 s2 h
      apply ρ₁.inj
      apply ρ₂.inj
      exact h }

end SessionRenaming

namespace SessionIso

/-- `toRenaming` of the identity is the identity renaming. -/
theorem toRenaming_id : SessionIso.toRenaming SessionIso.id = SessionRenaming.id := by
  -- Definitional after unfolding.
  rfl

end SessionIso

/-! ## Size-Of Arithmetic Helpers -/

private theorem lt_add_of_pos_left_add_right (n k m : Nat) : n < 1 + (k + n) + m := by
  have hpos : 0 < 1 + k := by
    simpa [Nat.add_comm] using (Nat.succ_pos k)
  have h : n < (1 + k) + n := by
    exact Nat.lt_add_of_pos_left (k:=1 + k) (n:=n) hpos
  have h' : n < (1 + k) + n + m :=
    Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
  simpa [Nat.add_assoc] using h'

private theorem lt_add_of_pos_left_add_right_mid (n k m : Nat) : n < 1 + (k + (n + m)) := by
  simpa [Nat.add_assoc] using
    (lt_add_of_pos_left_add_right (n:=n) (k:=k) (m:=m))

private theorem lt_add_of_pos_left_add_right_last (n k m : Nat) : n < 1 + (k + (m + n)) := by
  simpa [Nat.add_assoc] using
    (lt_add_of_pos_left_add_right (n:=n) (k:=k + m) (m:=0))

private theorem lt_add_of_pos_left_add_right_mid_succ (n k m : Nat) : n < 1 + (1 + (k + (n + m))) := by
  simpa [Nat.add_assoc] using
    (lt_add_of_pos_left_add_right_mid (n:=n) (k:=1 + k) (m:=m))

private theorem sizeOf_lt_send_expanded (r : Role) (T : ValType) (L : LocalType) :
    sizeOf L < 1 + sizeOf r + sizeOf T + sizeOf L := by
  have h : sizeOf L < 1 + (sizeOf r + sizeOf T + sizeOf L) := by
    simpa [Nat.add_assoc] using
      (lt_add_of_pos_left_add_right (n:=sizeOf L) (k:=sizeOf r + sizeOf T) (m:=0))
  simpa [Nat.add_assoc] using h

private theorem sizeOf_lt_recv_expanded (r : Role) (T : ValType) (L : LocalType) :
    sizeOf L < 1 + sizeOf r + sizeOf T + sizeOf L := by
  have h : sizeOf L < 1 + (sizeOf r + sizeOf T + sizeOf L) := by
    simpa [Nat.add_assoc] using
      (lt_add_of_pos_left_add_right (n:=sizeOf L) (k:=sizeOf r + sizeOf T) (m:=0))
  simpa [Nat.add_assoc] using h

private theorem sizeOf_lt_select_expanded (r : Role) (bs : List (Label × LocalType)) :
    sizeOf bs < 1 + sizeOf r + sizeOf bs := by
  have h : sizeOf bs < 1 + (sizeOf r + sizeOf bs) := by
    simpa [Nat.add_assoc] using
      (lt_add_of_pos_left_add_right (n:=sizeOf bs) (k:=sizeOf r) (m:=0))
  simpa [Nat.add_assoc] using h

private theorem sizeOf_lt_branch_expanded (r : Role) (bs : List (Label × LocalType)) :
    sizeOf bs < 1 + sizeOf r + sizeOf bs := by
  have h : sizeOf bs < 1 + (sizeOf r + sizeOf bs) := by
    simpa [Nat.add_assoc] using
      (lt_add_of_pos_left_add_right (n:=sizeOf bs) (k:=sizeOf r) (m:=0))
  simpa [Nat.add_assoc] using h

private theorem sizeOf_lt_mu_expanded (L : LocalType) :
    sizeOf L < 1 + sizeOf L := by
  have h : sizeOf L < 1 + (0 + sizeOf L) := by
    simpa [Nat.add_assoc] using
      (lt_add_of_pos_left_add_right (n:=sizeOf L) (k:=0) (m:=0))
  simpa [Nat.add_assoc] using h

private theorem sizeOf_lt_branch_head_expanded (l : Label) (L : LocalType) (tl : List (Label × LocalType)) :
    sizeOf L < 1 + (1 + sizeOf l + sizeOf L) + sizeOf tl := by
  have h : sizeOf L < 1 + (1 + (sizeOf l + (sizeOf L + sizeOf tl))) := by
    simpa [Nat.add_assoc] using
      (lt_add_of_pos_left_add_right_mid_succ (n:=sizeOf L) (k:=sizeOf l) (m:=sizeOf tl))
  simpa [Nat.add_assoc] using h

private theorem sizeOf_lt_branch_tail_expanded (l : Label) (L : LocalType) (tl : List (Label × LocalType)) :
    sizeOf tl < 1 + (1 + sizeOf l + sizeOf L) + sizeOf tl := by
  have h : sizeOf tl < 1 + ((1 + sizeOf l) + (sizeOf L + sizeOf tl)) := by
    simpa [Nat.add_assoc] using
      (lt_add_of_pos_left_add_right_last (n:=sizeOf tl) (k:=1 + sizeOf l) (m:=sizeOf L))
  simpa [Nat.add_assoc] using h

/-! ## Renaming Composition and Identity -/

/-- Value-type renaming composes. -/
theorem renameValType_comp (ρ₂ ρ₁ : SessionRenaming) :
    ∀ T, renameValType (SessionRenaming.comp ρ₂ ρ₁) T =
      renameValType ρ₂ (renameValType ρ₁ T) := by
  -- Structural recursion on value types.
  intro T
  induction T with
  | unit => rfl
  | bool => rfl
  | nat => rfl
  | string => rfl
  | prod T1 T2 ih1 ih2 =>
      simp [renameValType, ih1, ih2]
  | chan sid role =>
      simp [renameValType, SessionRenaming.comp]

/-- Mapping value types with a composed renaming equals a single map. -/
theorem map_renameValType_comp (ρ₂ ρ₁ : SessionRenaming) (ts : List ValType) :
    ts.map (renameValType ρ₂ ∘ renameValType ρ₁) =
      ts.map (renameValType (SessionRenaming.comp ρ₂ ρ₁)) := by
  -- Structural recursion on traces.
  induction ts with
  | nil => simp
  | cons t ts ih =>
      simp [renameValType_comp, ih, Function.comp]

/-- Value-type renaming by identity is a no-op. -/
theorem renameValType_id : ∀ T, renameValType SessionRenaming.id T = T := by
  -- Structural recursion on value types.
  intro T
  induction T with
  | unit => rfl
  | bool => rfl
  | nat => rfl
  | string => rfl
  | prod T1 T2 ih1 ih2 =>
      simp [renameValType, ih1, ih2]
  | chan sid role =>
      simp [renameValType, SessionRenaming.id]

/-- Renaming value types by identity is the identity function. -/
theorem renameValType_id_fun : renameValType SessionRenaming.id = id := by
  funext T
  exact renameValType_id T

mutual

/-- Local-type renaming composes. -/
theorem renameLocalType_comp (ρ₂ ρ₁ : SessionRenaming) :
    ∀ L, renameLocalType (SessionRenaming.comp ρ₂ ρ₁) L =
      renameLocalType ρ₂ (renameLocalType ρ₁ L) := by
  -- Structural recursion on local types.
  intro L
  cases L with
  | send r T L =>
      simp [renameLocalType, renameValType_comp,
        renameLocalType_comp (ρ₂:=ρ₂) (ρ₁:=ρ₁) L]
  | recv r T L =>
      simp [renameLocalType, renameValType_comp,
        renameLocalType_comp (ρ₂:=ρ₂) (ρ₁:=ρ₁) L]
  | select r bs =>
      simp [renameLocalType, renameBranches_comp (ρ₂:=ρ₂) (ρ₁:=ρ₁) bs]
  | branch r bs =>
      simp [renameLocalType, renameBranches_comp (ρ₂:=ρ₂) (ρ₁:=ρ₁) bs]
  | end_ =>
      simp [renameLocalType]
  | var n =>
      simp [renameLocalType]
  | mu L =>
      simp [renameLocalType, renameLocalType_comp (ρ₂:=ρ₂) (ρ₁:=ρ₁) L]
termination_by L => sizeOf L
decreasing_by
  all_goals
    simpa using (sizeOf_lt_branch_head_expanded (l:=_) (L:=_) (tl:=_))

/-- Branch renaming composes pointwise. -/
theorem renameBranches_comp (ρ₂ ρ₁ : SessionRenaming) :
    ∀ bs, renameBranches (SessionRenaming.comp ρ₂ ρ₁) bs =
      renameBranches ρ₂ (renameBranches ρ₁ bs) := by
  -- Structural recursion on branch lists.
  intro bs
  cases bs with
  | nil =>
      simp [renameBranches]
  | cons hd tl =>
      cases hd with
      | mk l L =>
          simp [renameBranches, renameLocalType_comp (ρ₂:=ρ₂) (ρ₁:=ρ₁) L,
            renameBranches_comp (ρ₂:=ρ₂) (ρ₁:=ρ₁) tl]
termination_by bs => sizeOf bs
decreasing_by
  all_goals
    simpa using (sizeOf_lt_branch_head_expanded (l:=_) (L:=_) (tl:=_))

end

/-- Mapping local types with a composed renaming equals a single map. -/
theorem map_renameLocalType_comp (ρ₂ ρ₁ : SessionRenaming) (o : Option LocalType) :
    o.map (renameLocalType ρ₂ ∘ renameLocalType ρ₁) =
      o.map (renameLocalType (SessionRenaming.comp ρ₂ ρ₁)) := by
  -- Case split on the option.
  cases o <;> simp [renameLocalType_comp, Function.comp]

mutual

/-- Local-type renaming by identity is a no-op. -/
theorem renameLocalType_id : ∀ L, renameLocalType SessionRenaming.id L = L := by
  -- Structural recursion on local types.
  intro L
  cases L with
  | send r T L =>
      simp [renameLocalType, renameValType_id, renameLocalType_id L]
  | recv r T L =>
      simp [renameLocalType, renameValType_id, renameLocalType_id L]
  | select r bs =>
      simp [renameLocalType, renameBranches_id bs]
  | branch r bs =>
      simp [renameLocalType, renameBranches_id bs]
  | end_ =>
      simp [renameLocalType]
  | var n =>
      simp [renameLocalType]
  | mu L =>
      simp [renameLocalType, renameLocalType_id L]
termination_by L => sizeOf L
decreasing_by
  all_goals
    simpa using (sizeOf_lt_branch_head_expanded (l:=_) (L:=_) (tl:=_))

/-- Branch renaming by identity is a no-op. -/
theorem renameBranches_id : ∀ bs, renameBranches SessionRenaming.id bs = bs := by
  -- Structural recursion on branch lists.
  intro bs
  cases bs with
  | nil =>
      simp [renameBranches]
  | cons hd tl =>
      cases hd with
      | mk l L =>
          simp [renameBranches, renameLocalType_id L, renameBranches_id tl]
termination_by bs => sizeOf bs
decreasing_by
  all_goals
    simpa using (sizeOf_lt_branch_head_expanded (l:=_) (L:=_) (tl:=_))

end

/-- Endpoint renaming composes. -/
theorem renameEndpoint_comp (ρ₂ ρ₁ : SessionRenaming) (e : Endpoint) :
    renameEndpoint (SessionRenaming.comp ρ₂ ρ₁) e =
      renameEndpoint ρ₂ (renameEndpoint ρ₁ e) := by
  -- By unfolding definitions of endpoint renaming.
  rfl

/-- Endpoint renaming by identity is a no-op. -/
theorem renameEndpoint_id (e : Endpoint) :
    renameEndpoint SessionRenaming.id e = e := by
  -- By case analysis on the endpoint.
  cases e
  rfl

/-- Edge renaming composes. -/
theorem renameEdge_comp (ρ₂ ρ₁ : SessionRenaming) (e : Edge) :
    renameEdge (SessionRenaming.comp ρ₂ ρ₁) e =
      renameEdge ρ₂ (renameEdge ρ₁ e) := by
  -- By unfolding definitions of edge renaming.
  rfl

/-- Edge renaming by identity is a no-op. -/
theorem renameEdge_id (e : Edge) :
    renameEdge SessionRenaming.id e = e := by
  -- By case analysis on the edge.
  cases e
  rfl

/-- Value renaming composes. -/
theorem renameValue_comp (ρ₂ ρ₁ : SessionRenaming) :
    ∀ v, renameValue (SessionRenaming.comp ρ₂ ρ₁) v =
      renameValue ρ₂ (renameValue ρ₁ v) := by
  -- Structural recursion on runtime values.
  intro v
  induction v with
  | unit => rfl
  | bool b => rfl
  | nat n => rfl
  | string s => rfl
  | prod v1 v2 ih1 ih2 =>
      simp [renameValue, ih1, ih2]
  | chan e =>
      simp [renameValue, renameEndpoint_comp]

/-- Value renaming by identity is a no-op. -/
theorem renameValue_id : ∀ v, renameValue SessionRenaming.id v = v := by
  -- Structural recursion on runtime values.
  intro v
  induction v with
  | unit => rfl
  | bool b => rfl
  | nat n => rfl
  | string s => rfl
  | prod v1 v2 ih1 ih2 =>
      simp [renameValue, ih1, ih2]
  | chan e =>
      simp [renameValue, SessionRenaming.id, renameEndpoint]

/-- GEnv renaming composes. -/
theorem renameGEnv_comp (ρ₂ ρ₁ : SessionRenaming) (G : GEnv) :
    renameGEnv (SessionRenaming.comp ρ₂ ρ₁) G =
      renameGEnv ρ₂ (renameGEnv ρ₁ G) := by
  -- Pointwise map composition on the list representation.
  induction G with
  | nil => rfl
  | cons hd tl ih =>
      cases hd with
      | mk e L =>
          simp [renameGEnv, renameEndpoint_comp, renameLocalType_comp]

mutual

/-- Value-type renaming is canceled by the inverse isomorphism. -/
theorem renameValType_left_inv (σ : SessionIso) :
    ∀ T, renameValType (SessionIso.invRenaming σ) (renameValType (SessionIso.toRenaming σ) T) = T := by
  -- Structural recursion on value types.
  intro T
  induction T with
  | unit => rfl
  | bool => rfl
  | nat => rfl
  | string => rfl
  | prod T1 T2 ih1 ih2 =>
      simp [renameValType, ih1, ih2]
  | chan sid role =>
      simp [renameValType, SessionIso.toRenaming, SessionIso.invRenaming, σ.left_inv]

/-- Local-type renaming is canceled by the inverse isomorphism. -/
theorem renameLocalType_left_inv (σ : SessionIso) :
    ∀ L, renameLocalType (SessionIso.invRenaming σ) (renameLocalType (SessionIso.toRenaming σ) L) = L := by
  -- Structural recursion on local types.
  intro L
  cases L with
  | send r T L =>
      simp [renameLocalType, renameValType_left_inv, renameLocalType_left_inv (σ:=σ) L]
  | recv r T L =>
      simp [renameLocalType, renameValType_left_inv, renameLocalType_left_inv (σ:=σ) L]
  | select r bs =>
      simp [renameLocalType, renameBranches_left_inv (σ:=σ) bs]
  | branch r bs =>
      simp [renameLocalType, renameBranches_left_inv (σ:=σ) bs]
  | end_ =>
      simp [renameLocalType]
  | var n =>
      simp [renameLocalType]
  | mu L =>
      simp [renameLocalType, renameLocalType_left_inv (σ:=σ) L]
termination_by L => sizeOf L
decreasing_by
  all_goals
    simpa using (sizeOf_lt_branch_head_expanded (l:=_) (L:=_) (tl:=_))

/-- Branch renaming is canceled by the inverse isomorphism. -/
theorem renameBranches_left_inv (σ : SessionIso) :
    ∀ bs, renameBranches (SessionIso.invRenaming σ) (renameBranches (SessionIso.toRenaming σ) bs) = bs := by
  -- Structural recursion on branch lists.
  intro bs
  cases bs with
  | nil =>
      simp [renameBranches]
  | cons hd tl =>
      cases hd with
      | mk l L =>
          simp [renameBranches, renameLocalType_left_inv (σ:=σ) L,
            renameBranches_left_inv (σ:=σ) tl]
termination_by bs => sizeOf bs
decreasing_by
  all_goals
    simpa using (sizeOf_lt_branch_head_expanded (l:=_) (L:=_) (tl:=_))

end

/-! ## Inverse Renaming Maps -/

/-- Mapping value types with inverse-after-forward renaming is identity. -/
theorem map_renameValType_left_inv (σ : SessionIso) (ts : List ValType) :
    ts.map (renameValType (SessionIso.invRenaming σ) ∘
      renameValType (SessionIso.toRenaming σ)) = ts := by
  -- Structural recursion on traces.
  induction ts with
  | nil => simp
  | cons t ts ih =>
      simp [renameValType_left_inv, ih, Function.comp]
end
