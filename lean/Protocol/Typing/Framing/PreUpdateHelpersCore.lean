
import Protocol.Environments.Core
import Protocol.Typing.StepLemmas
import Protocol.Typing.MergeLemmas
import Protocol.Typing.Framing.Lemmas

/-! # Typing Framing: Pre-Update Helpers Core

Foundational helper lemmas for framed pre-update preservation.
-/

/-
The Problem. Pre-update preservation needs reusable base lemmas for lookup
bridges, disjointness projections, endpoint alignment, and left-frame updates.

Solution Structure.
1. Bridge visible/full environment lookups and store typing.
2. Project and repack disjointness/owned disjointness across splits.
3. Provide endpoint and left-frame update alignment helpers.
-/

/- ## Structured Block 1 -/
set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section
-- Framed Pre-Update Helpers
/-- Bridge visible lookup (`Ssh ++ Sown.left`) to full lookup (`SEnvAll`) under
    shared/owned disjointness and owned right/left disjointness. -/
lemma lookup_s_env_all_of_visible
    {Ssh : SEnv} {Sown : OwnedEnv} {x : Var} {T : ValType} :
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    lookupSEnv (Ssh ++ Sown.left) x = some T →
    lookupSEnv (SEnvAll Ssh Sown) x = some T := by
  intro hDisjShAll hOwnDisj hVis
  cases hSh : lookupSEnv Ssh x with
  | some Tsh =>
      have hEqT : Tsh = T := by
        have hShVis : lookupSEnv (Ssh ++ Sown.left) x = some Tsh :=
          lookup_s_env_append_left (S₁:=Ssh) (S₂:=Sown.left) (x:=x) (T:=Tsh) hSh
        exact Option.some.inj (by simpa [hVis] using hShVis.symm)
      have hOwnNone : lookupSEnv (Sown : SEnv) x = none := by
        exact lookup_s_env_none_of_disjoint_left
          (S₁:=(Sown : SEnv)) (S₂:=Ssh) (x:=x) (T:=Tsh)
          (disjoint_s_symm hDisjShAll) hSh
      have hRightNone : lookupSEnv Sown.right x = none := by
        cases hR : lookupSEnv Sown.right x with
        | none => exact rfl
        | some Tr =>
            have hOwnSome : lookupSEnv (Sown : SEnv) x = some Tr := by
              simpa [OwnedEnv.all] using
                (lookup_s_env_append_left (S₁:=Sown.right) (S₂:=Sown.left) (x:=x) (T:=Tr) hR)
            have hOwnNone' : lookupSEnv (Sown.right ++ Sown.left) x = none := by
              simpa [OwnedEnv.all] using hOwnNone
            have hContra : False := by
              simpa [OwnedEnv.all, hOwnNone'] using hOwnSome
            cases hContra
      have hPrefixSh : lookupSEnv (Ssh ++ Sown.right) x = some Tsh := by
        have hPrefix := lookup_s_env_append_left (S₁:=Ssh) (S₂:=Sown.right) (x:=x) (T:=Tsh) hSh
        simpa [hRightNone] using hPrefix
      have hAllSh :
          lookupSEnv ((Ssh ++ Sown.right) ++ Sown.left) x = some Tsh :=
        lookup_s_env_append_left (S₁:=Ssh ++ Sown.right) (S₂:=Sown.left) (x:=x) (T:=Tsh) hPrefixSh
      simpa [SEnvAll, List.append_assoc, hEqT] using hAllSh
  -- Visible Lookup Bridge: Owned-Left Branch
  | none =>
      have hLeftSome : lookupSEnv Sown.left x = some T := by
        have hVisRight := lookup_s_env_append_right (S₁:=Ssh) (S₂:=Sown.left) (x:=x) hSh
        simpa [hVisRight] using hVis
      have hRightNone : lookupSEnv Sown.right x = none := by
        exact lookup_s_env_none_of_disjoint_left
          (S₁:=Sown.right) (S₂:=Sown.left) (x:=x) (T:=T)
          hOwnDisj hLeftSome
/- ## Structured Block 2 -/
      have hOwnSome : lookupSEnv (Sown : SEnv) x = some T := by
        have hOwnRight := lookup_s_env_append_right (S₁:=Sown.right) (S₂:=Sown.left) (x:=x) hRightNone
        simpa [hOwnRight] using hLeftSome
      have hAll :
          lookupSEnv (SEnvAll Ssh Sown) x = some T := by
        have hAllRight := lookup_s_env_append_right (S₁:=Ssh) (S₂:=(Sown : SEnv)) (x:=x) hSh
        calc
          lookupSEnv (SEnvAll Ssh Sown) x = lookupSEnv (Sown : SEnv) x := by
            simpa [s_env_all_all] using hAllRight
          _ = some T := hOwnSome
      exact hAll

-- Store Typing Visibility Bridges

/-- Bridge full store typing (`SEnvAll`) to visible store typing (`SEnvVisible`). -/
lemma store_typed_visible_of_all
    {G : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore} :
    StoreTyped G (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    StoreTypedVisible G Ssh Sown store := by
  intro hStore hDisjShAll hOwnDisj x v T hStoreX hVis
  have hAll : lookupSEnv (SEnvAll Ssh Sown) x = some T :=
    lookup_s_env_all_of_visible (Ssh:=Ssh) (Sown:=Sown) (x:=x) (T:=T) hDisjShAll hOwnDisj hVis
  exact hStore x v T hStoreX hAll

/-- Bridge full strong store typing to strong-visible store typing. -/
lemma store_typed_strong_visible_of_all_strong
    {G : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore} :
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    StoreTypedStrongVisible G Ssh Sown store := by
  intro hStrong hDisjShAll hOwnDisj
  refine ⟨hStrong.sameDomain, ?_⟩
  exact store_typed_visible_of_all (G:=G) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
    hStrong.typeCorr hDisjShAll hOwnDisj

-- Disjointness Projection Helpers

/-- Disjointness is stable when appending on the right. -/
lemma disjoint_s_append_right_pu {S₁ S₂ S₃ : SEnv} :
    DisjointS S₁ S₂ →
    DisjointS S₁ S₃ →
    DisjointS S₁ (S₂ ++ S₃) := by
  intro hDisj hDisj'
  have hLeft : DisjointS S₂ S₁ := disjoint_s_symm hDisj
  have hRight : DisjointS S₃ S₁ := disjoint_s_symm hDisj'
  have hAppend : DisjointS (S₂ ++ S₃) S₁ :=
    disjoint_s_append_left hLeft hRight
  exact disjoint_s_symm hAppend

/-- Project shared-vs-owned disjointness to the owned right segment. -/
lemma disjoint_s_owned_right_pu {S₁ : SEnv} {Sown : OwnedEnv} :
    DisjointS S₁ (Sown : SEnv) →
    DisjointS S₁ Sown.right := by
  intro hDisj
  have hSub : SEnvDomSubset Sown.right (Sown : SEnv) := by
    simpa [OwnedEnv.all] using
      (s_env_dom_subset_append_left (S₁:=Sown.right) (S₂:=Sown.left))
  exact disjoint_s_of_domsubset_right hSub hDisj

/-- Project shared-vs-owned disjointness to the owned left segment. -/
lemma disjoint_s_owned_left_pu {S₁ : SEnv} {Sown : OwnedEnv} :
/- ## Structured Block 3 -/
    DisjointS S₁ (Sown : SEnv) →
    DisjointS S₁ Sown.left := by
  intro hDisj
  have hSub : SEnvDomSubset Sown.left (Sown : SEnv) := by
    simpa [OwnedEnv.all] using
      (s_env_dom_subset_append_right (S₁:=Sown.right) (S₂:=Sown.left))
  exact disjoint_s_of_domsubset_right hSub hDisj

/-- Split disjointness against an appended environment (left side). -/
lemma disjoint_s_split_left_pu {Ssh S₁ S₂ : SEnv} :
    DisjointS Ssh (S₁ ++ S₂) → DisjointS Ssh S₁ := by
  intro hDisj
  have hSub : SEnvDomSubset S₁ (S₁ ++ S₂) := by
    simpa using (s_env_dom_subset_append_left (S₁:=S₁) (S₂:=S₂))
  exact disjoint_s_of_domsubset_right hSub hDisj

/-- Split disjointness against an appended environment (right side). -/
lemma disjoint_s_split_right_pu {Ssh S₁ S₂ : SEnv} :
    DisjointS Ssh (S₁ ++ S₂) → DisjointS Ssh S₂ := by
  intro hDisj
  have hSub : SEnvDomSubset S₂ (S₁ ++ S₂) := by
    simpa using (s_env_dom_subset_append_right (S₁:=S₁) (S₂:=S₂))
  exact disjoint_s_of_domsubset_right hSub hDisj

-- Split/Repack Helpers

/-- If shared is disjoint from full owned env, it is disjoint from both split parts. -/
lemma disjoint_s_split_from_owned_left_pu
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv}
    (split : ParSplit Sown.left G) :
    DisjointS Ssh (Sown : SEnv) →
    DisjointS Ssh split.S1 ∧ DisjointS Ssh split.S2 := by
  intro hDisj
  have hLeftAll : DisjointS Ssh (split.S1 ++ split.S2) := by
    simpa [split.hS] using (disjoint_s_owned_left_pu (Sown:=Sown) hDisj)
  exact ⟨disjoint_s_split_left_pu hLeftAll, disjoint_s_split_right_pu hLeftAll⟩

/-- Repack shared disjointness for a new owned split. -/
lemma disjoint_s_owned_repack_pu
    {Ssh : SEnv} {Sright Sleft Smid : SEnv} :
    DisjointS Ssh Sright →
    DisjointS Ssh Sleft →
    DisjointS Ssh Smid →
    DisjointS Ssh ({ right := Sright ++ Smid, left := Sleft } : OwnedEnv) := by
  intro hRight hLeft hMid
  have hRight' : DisjointS Ssh (Sright ++ Smid) :=
    disjoint_s_append_right_pu hRight hMid
  have hAll : DisjointS Ssh ((Sright ++ Smid) ++ Sleft) :=
    disjoint_s_append_right_pu hRight' hLeft
  simpa [OwnedEnv.all, List.append_assoc] using hAll

-- Owned Disjointness Under Split Framing

/-- Owned right/left disjointness after framing split.S2 on the right and split.S1 on the left. -/
lemma owned_disjoint_sub_left_pu
    {Sown : OwnedEnv} {G : GEnv} (split : ParSplit Sown.left G) :
    OwnedDisjoint Sown →
    DisjointS split.S1 split.S2 →
    OwnedDisjoint ({ right := Sown.right ++ split.S2, left := split.S1 } : OwnedEnv) := by
  intro hOwn hDisjS
  have hOwnLeftAll : DisjointS Sown.right (split.S1 ++ split.S2) := by
    simpa [OwnedDisjoint, split.hS] using hOwn
  have hR1 : DisjointS Sown.right split.S1 := disjoint_s_split_left_pu hOwnLeftAll
  have hS2S1 : DisjointS split.S2 split.S1 := disjoint_s_symm hDisjS
/- ## Structured Block 4 -/
  have hAll : DisjointS (Sown.right ++ split.S2) split.S1 :=
    disjoint_s_append_left hR1 hS2S1
  simpa [OwnedDisjoint, OwnedEnv.all] using hAll

/-- Owned right/left disjointness after framing split.S1 on the right and split.S2 on the left. -/
lemma owned_disjoint_sub_right_pu
    {Sown : OwnedEnv} {G : GEnv} (split : ParSplit Sown.left G) :
    OwnedDisjoint Sown →
    DisjointS split.S1 split.S2 →
    OwnedDisjoint ({ right := Sown.right ++ split.S1, left := split.S2 } : OwnedEnv) := by
  intro hOwn hDisjS
  have hOwnLeftAll : DisjointS Sown.right (split.S1 ++ split.S2) := by
    simpa [OwnedDisjoint, split.hS] using hOwn
  have hR2 : DisjointS Sown.right split.S2 := disjoint_s_split_right_pu hOwnLeftAll
  have hAll : DisjointS (Sown.right ++ split.S1) split.S2 :=
    disjoint_s_append_left hR2 hDisjS
  simpa [OwnedDisjoint, OwnedEnv.all] using hAll

-- Endpoint Alignment Via Store Typing

/-- Helper: align endpoints via store typing. -/
lemma endpoint_eq_of_store
    {Gstore Ssh Sown store} {k : Var} {e e' : Endpoint} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    lookupStr store k = some (.chan e) →
    lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) →
    e = e' := by
  -- Use store typing and channel inversion to identify endpoints.
  intro hStore hk hk'
  have hkTyped : HasTypeVal Gstore (.chan e) (.chan e'.sid e'.role) :=
    hStore k (.chan e) (.chan e'.sid e'.role) hk hk'
  have hValEq : (Value.chan e) = Value.chan ⟨e'.sid, e'.role⟩ := by
    simpa using (has_type_val_chan_inv hkTyped)
  cases e
  cases e'
  cases hValEq
  rfl

/-- Helper: align endpoints via store typing from a visible (`Ssh ++ Sown.left`) lookup. -/
lemma endpoint_eq_of_store_visible
    {Gstore Ssh Sown store} {k : Var} {e e' : Endpoint} :
    StoreTypedVisible Gstore Ssh Sown store →
    lookupStr store k = some (.chan e) →
    lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e'.sid e'.role) →
    e = e' := by
  intro hStoreVis hk hkVis
  have hkTyped : HasTypeVal Gstore (.chan e) (.chan e'.sid e'.role) :=
    hStoreVis k (.chan e) (.chan e'.sid e'.role) hk hkVis
  have hValEq : (Value.chan e) = Value.chan ⟨e'.sid, e'.role⟩ := by
    simpa using (has_type_val_chan_inv hkTyped)
  cases e
  cases e'
  cases hValEq
  rfl

-- Left-Frame Update Extraction

/-- Helper: pull a left update out of a right-framed G. -/
lemma update_g_left_of_step
    {G₁ G₂ G G' G₁' : GEnv} {e : Endpoint} {L L0 : LocalType} :
    G = G₁ ++ G₂ →
    G' = G₁' ++ G₂ →
    lookupG G₁ e = some L0 →
/- ## Structured Block 5 -/
    updateG G e L = G' →
    G₁' = updateG G₁ e L := by
  -- Rewrite the update and cancel the shared right frame.
  intro hEq hEq' hG₁e hGout
  have hUpd : updateG (G₁ ++ G₂) e L = updateG G₁ e L ++ G₂ :=
    update_g_append_left_hit (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L0) (L':=L) hG₁e
  apply append_left_eq_of_eq
  calc
    G₁' ++ G₂ = updateG (G₁ ++ G₂) e L := by
      simpa [hEq, hEq'] using hGout.symm
    _ = updateG G₁ e L ++ G₂ := by simpa [hUpd]


end
