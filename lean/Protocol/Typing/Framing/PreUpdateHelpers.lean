import Protocol.Environments.Core
import Protocol.Typing.StepLemmas
import Protocol.Typing.MergeLemmas
import Protocol.Typing.Framing.Lemmas

/-
Shared helper lemmas for framed pre-update preservation. These provide alignment
facts for endpoints, local types, labels, and framed updates.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ### Framed Pre-Update Helpers -/
/-- Bridge visible lookup (`Ssh ++ Sown.left`) to full lookup (`SEnvAll`) under
    shared/owned disjointness and owned right/left disjointness. -/
lemma lookupSEnv_all_of_visible
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
          lookupSEnv_append_left (S₁:=Ssh) (S₂:=Sown.left) (x:=x) (T:=Tsh) hSh
        exact Option.some.inj (by simpa [hVis] using hShVis.symm)
      have hOwnNone : lookupSEnv (Sown : SEnv) x = none := by
        exact lookupSEnv_none_of_disjoint_left
          (S₁:=(Sown : SEnv)) (S₂:=Ssh) (x:=x) (T:=Tsh)
          (DisjointS_symm hDisjShAll) hSh
      have hRightNone : lookupSEnv Sown.right x = none := by
        cases hR : lookupSEnv Sown.right x with
        | none => exact rfl
        | some Tr =>
            have hOwnSome : lookupSEnv (Sown : SEnv) x = some Tr := by
              simpa [OwnedEnv.all] using
                (lookupSEnv_append_left (S₁:=Sown.right) (S₂:=Sown.left) (x:=x) (T:=Tr) hR)
            have hOwnNone' : lookupSEnv (Sown.right ++ Sown.left) x = none := by
              simpa [OwnedEnv.all] using hOwnNone
            have hContra : False := by
              simpa [OwnedEnv.all, hOwnNone'] using hOwnSome
            cases hContra
      have hPrefixSh : lookupSEnv (Ssh ++ Sown.right) x = some Tsh := by
        have hPrefix := lookupSEnv_append_left (S₁:=Ssh) (S₂:=Sown.right) (x:=x) (T:=Tsh) hSh
        simpa [hRightNone] using hPrefix
      have hAllSh :
          lookupSEnv ((Ssh ++ Sown.right) ++ Sown.left) x = some Tsh :=
        lookupSEnv_append_left (S₁:=Ssh ++ Sown.right) (S₂:=Sown.left) (x:=x) (T:=Tsh) hPrefixSh
      simpa [SEnvAll, List.append_assoc, hEqT] using hAllSh
  | none =>
      have hLeftSome : lookupSEnv Sown.left x = some T := by
        have hVisRight := lookupSEnv_append_right (S₁:=Ssh) (S₂:=Sown.left) (x:=x) hSh
        simpa [hVisRight] using hVis
      have hRightNone : lookupSEnv Sown.right x = none := by
        exact lookupSEnv_none_of_disjoint_left
          (S₁:=Sown.right) (S₂:=Sown.left) (x:=x) (T:=T)
          hOwnDisj hLeftSome
      have hOwnSome : lookupSEnv (Sown : SEnv) x = some T := by
        have hOwnRight := lookupSEnv_append_right (S₁:=Sown.right) (S₂:=Sown.left) (x:=x) hRightNone
        simpa [hOwnRight] using hLeftSome
      have hAll :
          lookupSEnv (SEnvAll Ssh Sown) x = some T := by
        have hAllRight := lookupSEnv_append_right (S₁:=Ssh) (S₂:=(Sown : SEnv)) (x:=x) hSh
        calc
          lookupSEnv (SEnvAll Ssh Sown) x = lookupSEnv (Sown : SEnv) x := by
            simpa [SEnvAll_all] using hAllRight
          _ = some T := hOwnSome
      exact hAll

/-- Bridge full store typing (`SEnvAll`) to visible store typing (`SEnvVisible`). -/
lemma StoreTypedVisible_of_all
    {G : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore} :
    StoreTyped G (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    StoreTypedVisible G Ssh Sown store := by
  intro hStore hDisjShAll hOwnDisj x v T hStoreX hVis
  have hAll : lookupSEnv (SEnvAll Ssh Sown) x = some T :=
    lookupSEnv_all_of_visible (Ssh:=Ssh) (Sown:=Sown) (x:=x) (T:=T) hDisjShAll hOwnDisj hVis
  exact hStore x v T hStoreX hAll

/-- Bridge full strong store typing to strong-visible store typing. -/
lemma StoreTypedStrongVisible_of_allStrong
    {G : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore} :
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    StoreTypedStrongVisible G Ssh Sown store := by
  intro hStrong hDisjShAll hOwnDisj
  refine ⟨hStrong.sameDomain, ?_⟩
  exact StoreTypedVisible_of_all (G:=G) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
    hStrong.typeCorr hDisjShAll hOwnDisj

/-- Disjointness is stable when appending on the right. -/
lemma DisjointS_append_right_pu {S₁ S₂ S₃ : SEnv} :
    DisjointS S₁ S₂ →
    DisjointS S₁ S₃ →
    DisjointS S₁ (S₂ ++ S₃) := by
  intro hDisj hDisj'
  have hLeft : DisjointS S₂ S₁ := DisjointS_symm hDisj
  have hRight : DisjointS S₃ S₁ := DisjointS_symm hDisj'
  have hAppend : DisjointS (S₂ ++ S₃) S₁ :=
    DisjointS_append_left hLeft hRight
  exact DisjointS_symm hAppend

/-- Project shared-vs-owned disjointness to the owned right segment. -/
lemma DisjointS_owned_right_pu {S₁ : SEnv} {Sown : OwnedEnv} :
    DisjointS S₁ (Sown : SEnv) →
    DisjointS S₁ Sown.right := by
  intro hDisj
  have hSub : SEnvDomSubset Sown.right (Sown : SEnv) := by
    simpa [OwnedEnv.all] using
      (SEnvDomSubset_append_left (S₁:=Sown.right) (S₂:=Sown.left))
  exact DisjointS_of_domsubset_right hSub hDisj

/-- Project shared-vs-owned disjointness to the owned left segment. -/
lemma DisjointS_owned_left_pu {S₁ : SEnv} {Sown : OwnedEnv} :
    DisjointS S₁ (Sown : SEnv) →
    DisjointS S₁ Sown.left := by
  intro hDisj
  have hSub : SEnvDomSubset Sown.left (Sown : SEnv) := by
    simpa [OwnedEnv.all] using
      (SEnvDomSubset_append_right (S₁:=Sown.right) (S₂:=Sown.left))
  exact DisjointS_of_domsubset_right hSub hDisj

/-- Split disjointness against an appended environment (left side). -/
lemma DisjointS_split_left_pu {Ssh S₁ S₂ : SEnv} :
    DisjointS Ssh (S₁ ++ S₂) → DisjointS Ssh S₁ := by
  intro hDisj
  have hSub : SEnvDomSubset S₁ (S₁ ++ S₂) := by
    simpa using (SEnvDomSubset_append_left (S₁:=S₁) (S₂:=S₂))
  exact DisjointS_of_domsubset_right hSub hDisj

/-- Split disjointness against an appended environment (right side). -/
lemma DisjointS_split_right_pu {Ssh S₁ S₂ : SEnv} :
    DisjointS Ssh (S₁ ++ S₂) → DisjointS Ssh S₂ := by
  intro hDisj
  have hSub : SEnvDomSubset S₂ (S₁ ++ S₂) := by
    simpa using (SEnvDomSubset_append_right (S₁:=S₁) (S₂:=S₂))
  exact DisjointS_of_domsubset_right hSub hDisj

/-- If shared is disjoint from full owned env, it is disjoint from both split parts. -/
lemma DisjointS_split_from_owned_left_pu
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv}
    (split : ParSplit Sown.left G) :
    DisjointS Ssh (Sown : SEnv) →
    DisjointS Ssh split.S1 ∧ DisjointS Ssh split.S2 := by
  intro hDisj
  have hLeftAll : DisjointS Ssh (split.S1 ++ split.S2) := by
    simpa [split.hS] using (DisjointS_owned_left_pu (Sown:=Sown) hDisj)
  exact ⟨DisjointS_split_left_pu hLeftAll, DisjointS_split_right_pu hLeftAll⟩

/-- Repack shared disjointness for a new owned split. -/
lemma DisjointS_owned_repack_pu
    {Ssh : SEnv} {Sright Sleft Smid : SEnv} :
    DisjointS Ssh Sright →
    DisjointS Ssh Sleft →
    DisjointS Ssh Smid →
    DisjointS Ssh ({ right := Sright ++ Smid, left := Sleft } : OwnedEnv) := by
  intro hRight hLeft hMid
  have hRight' : DisjointS Ssh (Sright ++ Smid) :=
    DisjointS_append_right_pu hRight hMid
  have hAll : DisjointS Ssh ((Sright ++ Smid) ++ Sleft) :=
    DisjointS_append_right_pu hRight' hLeft
  simpa [OwnedEnv.all, List.append_assoc] using hAll

/-- Owned right/left disjointness after framing split.S2 on the right and split.S1 on the left. -/
lemma OwnedDisjoint_sub_left_pu
    {Sown : OwnedEnv} {G : GEnv} (split : ParSplit Sown.left G) :
    OwnedDisjoint Sown →
    DisjointS split.S1 split.S2 →
    OwnedDisjoint ({ right := Sown.right ++ split.S2, left := split.S1 } : OwnedEnv) := by
  intro hOwn hDisjS
  have hOwnLeftAll : DisjointS Sown.right (split.S1 ++ split.S2) := by
    simpa [OwnedDisjoint, split.hS] using hOwn
  have hR1 : DisjointS Sown.right split.S1 := DisjointS_split_left_pu hOwnLeftAll
  have hS2S1 : DisjointS split.S2 split.S1 := DisjointS_symm hDisjS
  have hAll : DisjointS (Sown.right ++ split.S2) split.S1 :=
    DisjointS_append_left hR1 hS2S1
  simpa [OwnedDisjoint, OwnedEnv.all] using hAll

/-- Owned right/left disjointness after framing split.S1 on the right and split.S2 on the left. -/
lemma OwnedDisjoint_sub_right_pu
    {Sown : OwnedEnv} {G : GEnv} (split : ParSplit Sown.left G) :
    OwnedDisjoint Sown →
    DisjointS split.S1 split.S2 →
    OwnedDisjoint ({ right := Sown.right ++ split.S1, left := split.S2 } : OwnedEnv) := by
  intro hOwn hDisjS
  have hOwnLeftAll : DisjointS Sown.right (split.S1 ++ split.S2) := by
    simpa [OwnedDisjoint, split.hS] using hOwn
  have hR2 : DisjointS Sown.right split.S2 := DisjointS_split_right_pu hOwnLeftAll
  have hAll : DisjointS (Sown.right ++ split.S1) split.S2 :=
    DisjointS_append_left hR2 hDisjS
  simpa [OwnedDisjoint, OwnedEnv.all] using hAll

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
    simpa using (HasTypeVal_chan_inv hkTyped)
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
    simpa using (HasTypeVal_chan_inv hkTyped)
  cases e
  cases e'
  cases hValEq
  rfl

/-- Helper: pull a left update out of a right-framed G. -/
lemma updateG_left_of_step
    {G₁ G₂ G G' G₁' : GEnv} {e : Endpoint} {L L0 : LocalType} :
    G = G₁ ++ G₂ →
    G' = G₁' ++ G₂ →
    lookupG G₁ e = some L0 →
    updateG G e L = G' →
    G₁' = updateG G₁ e L := by
  -- Rewrite the update and cancel the shared right frame.
  intro hEq hEq' hG₁e hGout
  have hUpd : updateG (G₁ ++ G₂) e L = updateG G₁ e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L0) (L':=L) hG₁e
  apply append_left_eq_of_eq
  calc
    G₁' ++ G₂ = updateG (G₁ ++ G₂) e L := by
      simpa [hEq, hEq'] using hGout.symm
    _ = updateG G₁ e L ++ G₂ := by simpa [hUpd]

/-! ### Left-Frame Helpers (Step Cases) -/

/-- Helper: align the local type in a send step under a right frame. -/
lemma send_localtype_eq
    {G₁ G₂ G : GEnv} {e : Endpoint} {target q : Role} {T T' : ValType}
    {L L' : LocalType} :
    G = G₁ ++ G₂ →
    lookupG G₁ e = some (.send q T' L') →
    lookupG G e = some (.send target T L) →
    L' = L := by
  -- Rewrite the global lookup through the left frame and compare constructors.
  intro hEq hG₁e hG
  have hG'' : lookupG G e = some (.send q T' L') := by
    have hLookup : lookupG (G₁ ++ G₂) e = some (.send q T' L') :=
      lookupG_append_left (G₁:=G₁) (G₂:=G₂) hG₁e
    simpa [hEq] using hLookup
  have : some (LocalType.send target T L) = some (LocalType.send q T' L') := by
    simpa [hG] using hG''
  cases Option.some.inj this
  rfl

/-- Helper: align the types in a recv step under a right frame. -/
lemma recv_types_eq
    {G₁ G₂ G : GEnv} {e : Endpoint} {source p : Role} {T T' : ValType}
    {L L' : LocalType} :
    G = G₁ ++ G₂ →
    lookupG G₁ e = some (.recv p T' L') →
    lookupG G e = some (.recv source T L) →
    T' = T ∧ L' = L := by
  -- Compare the recv constructors after rewriting the left-framed lookup.
  intro hEq hG₁e hG
  have hG'' : lookupG G e = some (.recv p T' L') := by
    have hLookup : lookupG (G₁ ++ G₂) e = some (.recv p T' L') :=
      lookupG_append_left (G₁:=G₁) (G₂:=G₂) hG₁e
    simpa [hEq] using hLookup
  have : some (LocalType.recv source T L) = some (LocalType.recv p T' L') := by
    simpa [hG] using hG''
  cases Option.some.inj this
  exact ⟨rfl, rfl⟩

/-! ### Left-Frame Alignment Helpers -/

/-- Helper: align the branches in a select step under a right frame. -/
lemma select_branches_eq
    {G₁ G₂ G : GEnv} {e : Endpoint} {target q : Role}
    {bs bs' : List (Label × LocalType)} :
    G = G₁ ++ G₂ →
    lookupG G₁ e = some (.select q bs') →
    lookupG G e = some (.select target bs) →
    bs' = bs := by
  -- Compare the select constructors after rewriting the left-framed lookup.
  intro hEq hG₁e hG
  have hG'' : lookupG G e = some (.select q bs') := by
    have hLookup : lookupG (G₁ ++ G₂) e = some (.select q bs') :=
      lookupG_append_left (G₁:=G₁) (G₂:=G₂) hG₁e
    simpa [hEq] using hLookup
  have : some (LocalType.select target bs) = some (LocalType.select q bs') := by
    simpa [hG] using hG''
  cases Option.some.inj this
  rfl

/-- Helper: align the branches in a branch step under a right frame. -/
lemma branch_branches_eq
    {G₁ G₂ G : GEnv} {e : Endpoint} {source p : Role}
    {bs bs' : List (Label × LocalType)} :
    G = G₁ ++ G₂ →
    lookupG G₁ e = some (.branch p bs') →
    lookupG G e = some (.branch source bs) →
    bs' = bs := by
  -- Compare the branch constructors after rewriting the left-framed lookup.
  intro hEq hG₁e hG
  have hG'' : lookupG G e = some (.branch p bs') := by
    have hLookup : lookupG (G₁ ++ G₂) e = some (.branch p bs') :=
      lookupG_append_left (G₁:=G₁) (G₂:=G₂) hG₁e
    simpa [hEq] using hLookup
  have : some (LocalType.branch source bs) = some (LocalType.branch p bs') := by
    simpa [hG] using hG''
  cases Option.some.inj this
  rfl

/-- Helper: align the chosen label in a select step. -/
lemma select_label_eq
    {bs bs' : List (Label × LocalType)} {ℓ : Label} {L L' : LocalType} :
    bs' = bs →
    bs'.find? (fun b => b.1 == ℓ) = some (ℓ, L') →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    L' = L := by
  -- Rewrite the branch list and compare the `find?` results.
  intro hBs hFind' hFind
  subst hBs
  have hEq : some (ℓ, L) = some (ℓ, L') := by
    simpa [hFind] using hFind'
  cases hEq
  rfl

/-- Helper: transport branch lookup across equal branch lists. -/
lemma branch_find_eq
    {bs bs' : List (Label × LocalType)} {ℓ : Label} {L : LocalType} :
    bs' = bs →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    bs'.find? (fun b => b.1 == ℓ) = some (ℓ, L) := by
  -- Rewrite the branch list and reuse the original lookup.
  intro hBs hFind
  simpa [hBs] using hFind

/-! ### Right-Frame Alignment Helpers -/

/-- Helper: align the local type in a send step under a left frame. -/
lemma send_localtype_eq_right
    {G₁ G₂ G : GEnv} {e : Endpoint} {target q : Role} {T T' : ValType}
    {L L' : LocalType} :
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    lookupG G₂ e = some (.send q T' L') →
    lookupG G e = some (.send target T L) →
    L' = L := by
  -- Rewrite the global lookup through the right frame and compare constructors.
  intro hDisj hEq hG₂e hG
  have hNone : lookupG G₁ e = none := lookupG_none_of_disjoint hDisj hG₂e
  have hLookup : lookupG (G₁ ++ G₂) e = some (.send q T' L') := by
    have hEqG := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hNone
    simpa [hEqG] using hG₂e
  have hG'' : lookupG G e = some (.send q T' L') := by
    simpa [hEq] using hLookup
  have : some (LocalType.send target T L) = some (LocalType.send q T' L') := by
    exact hG.symm.trans hG''
  cases Option.some.inj this
  rfl

/-- Helper: align the types in a recv step under a left frame. -/
lemma recv_types_eq_right
    {G₁ G₂ G : GEnv} {e : Endpoint} {source p : Role} {T T' : ValType}
    {L L' : LocalType} :
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    lookupG G₂ e = some (.recv p T' L') →
    lookupG G e = some (.recv source T L) →
    T' = T ∧ L' = L := by
  -- Rewrite the global lookup through the right frame and compare constructors.
  intro hDisj hEq hG₂e hG
  have hNone : lookupG G₁ e = none := lookupG_none_of_disjoint hDisj hG₂e
  have hLookup : lookupG (G₁ ++ G₂) e = some (.recv p T' L') := by
    have hEqG := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hNone
    simpa [hEqG] using hG₂e
  have hG'' : lookupG G e = some (.recv p T' L') := by
    simpa [hEq] using hLookup
  have : some (LocalType.recv source T L) = some (LocalType.recv p T' L') := by
    exact hG.symm.trans hG''
  cases Option.some.inj this
  exact ⟨rfl, rfl⟩

/-- Helper: align the branches in a select step under a left frame. -/
lemma select_branches_eq_right
    {G₁ G₂ G : GEnv} {e : Endpoint} {target q : Role}
    {bs bs' : List (Label × LocalType)} :
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    lookupG G₂ e = some (.select q bs') →
    lookupG G e = some (.select target bs) →
    bs' = bs := by
  -- Rewrite the global lookup through the right frame and compare constructors.
  intro hDisj hEq hG₂e hG
  have hNone : lookupG G₁ e = none := lookupG_none_of_disjoint hDisj hG₂e
  have hLookup : lookupG (G₁ ++ G₂) e = some (.select q bs') := by
    have hEqG := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hNone
    simpa [hEqG] using hG₂e
  have hG'' : lookupG G e = some (.select q bs') := by
    simpa [hEq] using hLookup
  have : some (LocalType.select target bs) = some (LocalType.select q bs') := by
    exact hG.symm.trans hG''
  cases Option.some.inj this
  rfl

/-- Helper: align the branches in a branch step under a left frame. -/
lemma branch_branches_eq_right
    {G₁ G₂ G : GEnv} {e : Endpoint} {source p : Role}
    {bs bs' : List (Label × LocalType)} :
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    lookupG G₂ e = some (.branch p bs') →
    lookupG G e = some (.branch source bs) →
    bs' = bs := by
  -- Rewrite the global lookup through the right frame and compare constructors.
  intro hDisj hEq hG₂e hG
  have hNone : lookupG G₁ e = none := lookupG_none_of_disjoint hDisj hG₂e
  have hLookup : lookupG (G₁ ++ G₂) e = some (.branch p bs') := by
    have hEqG := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hNone
    simpa [hEqG] using hG₂e
  have hG'' : lookupG G e = some (.branch p bs') := by
    simpa [hEq] using hLookup
  have : some (LocalType.branch source bs) = some (LocalType.branch p bs') := by
    exact hG.symm.trans hG''
  cases Option.some.inj this
  rfl

/-- Helper: pull a right update out of a left-framed G. -/
lemma updateG_right_of_step
    {G₁ G₂ G G' G₂' : GEnv} {e : Endpoint} {L L0 : LocalType} :
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G' = G₁ ++ G₂' →
    lookupG G₂ e = some L0 →
    updateG G e L = G' →
    G₂' = updateG G₂ e L := by
  -- Rewrite the update and cancel the shared left frame.
  intro hDisj hEq hEq' hG₂e hGout
  have hNone : lookupG G₁ e = none := lookupG_none_of_disjoint hDisj hG₂e
  have hUpd : updateG (G₁ ++ G₂) e L = G₁ ++ updateG G₂ e L :=
    updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  apply append_right_eq_of_eq
  calc
    G₁ ++ G₂' = updateG (G₁ ++ G₂) e L := by
      simpa [hEq, hEq'] using hGout.symm
    _ = G₁ ++ updateG G₂ e L := by simpa [hUpd]

/-- Helper: swap the left-owned prefix inside store typing. -/
lemma store_typed_left_swap
    {Gstore : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore} {S1 S2 : SEnv} :
    StoreTyped Gstore (SEnvAll Ssh { right := Sown.right, left := S1 ++ S2 }) store →
    DisjointS S1 S2 →
    StoreTyped Gstore (SEnvAll Ssh { right := Sown.right ++ S2, left := S1 }) store := by
  -- Use the swap lemma to reorder the left-owned environment.
  intro hStore hDisj x v T hStoreX hLookup
  have hLookup' :
      lookupSEnv (Ssh ++ (Sown.right ++ (S2 ++ S1))) x = some T := by
    simpa [SEnvAll, List.append_assoc] using hLookup
  have hSwap :=
    lookupSEnv_swap_left_prefix (Ssh:=Ssh ++ Sown.right) (S₁:=S2) (S₂:=S1) (S₃:=(∅ : SEnv))
      (DisjointS_symm hDisj) x
  have hSwap' :
      lookupSEnv (Ssh ++ (Sown.right ++ (S2 ++ S1))) x =
        lookupSEnv (Ssh ++ (Sown.right ++ (S1 ++ S2))) x := by
    simpa [SEnvAll, List.append_assoc] using hSwap
  have hLookup'' :
      lookupSEnv (Ssh ++ (Sown.right ++ (S1 ++ S2))) x = some T := by
    simpa [hSwap'] using hLookup'
  exact hStore x v T hStoreX (by simpa [SEnvAll, List.append_assoc] using hLookup'')
