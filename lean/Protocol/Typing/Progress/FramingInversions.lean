
import Protocol.Typing.Progress.Helpers

/-! # Framing Inversions for Progress

Inversion lemmas relating visible SEnv lookups to full SEnvAll lookups,
enabling progress proofs to extract store values from typing judgments. -/

/-
The Problem. Progress proofs need to extract concrete values from the
store based on typing. Typing uses `SEnvVisible` but store typing uses
`SEnvAll`. We need inversion lemmas relating these.

Solution Structure. Prove `lookup_s_env_all_of_visible_prog` showing that
visible lookup implies full lookup under disjointness. Use this to
bridge typing judgments to store access in progress proofs.
-/

/- ## Structured Block 1 -/
set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

-- Visible to Full Lookup

lemma lookup_s_env_all_of_visible_prog
    {Ssh : SEnv} {Sown : OwnedEnv} {x : Var} {T : ValType}
    (hDisjShAll : DisjointS Ssh (Sown : SEnv))
    (hOwnDisj : OwnedDisjoint Sown)
    (hVis : lookupSEnv (Ssh ++ Sown.left) x = some T) :
    lookupSEnv (SEnvAll Ssh Sown) x = some T := by
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
  -- Visible-to-Full Lookup: Shared-Miss Case
  | none =>
      have hLeftSome : lookupSEnv Sown.left x = some T := by
        have hVisRight := lookup_s_env_append_right (S₁:=Ssh) (S₂:=Sown.left) (x:=x) hSh
        simpa [hVisRight] using hVis
      have hRightNone : lookupSEnv Sown.right x = none := by
        exact lookup_s_env_none_of_disjoint_left
          (S₁:=Sown.right) (S₂:=Sown.left) (x:=x) (T:=T)
          hOwnDisj hLeftSome
      have hOwnSome : lookupSEnv (Sown : SEnv) x = some T := by
/- ## Structured Block 2 -/
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

-- Store Lookup Bridge

lemma store_lookup_of_visible_lookup
    {G : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore}
    {x : Var} {T : ValType}
    (hStore : StoreTypedStrong G (SEnvAll Ssh Sown) store)
    (hDisjShAll : DisjointS Ssh (Sown : SEnv))
    (hOwnDisj : OwnedDisjoint Sown)
    (hVis : lookupSEnv (Ssh ++ Sown.left) x = some T) :
    ∃ v, lookupStr store x = some v ∧ HasTypeVal G v T := by
  have hStoreVis : StoreTypedStrongVisible G Ssh Sown store :=
    store_typed_strong_visible_of_all_strong (G:=G) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
      hStore hDisjShAll hOwnDisj
  simpa [SEnvVisible] using
    (store_lookup_of_visible_lookup_strong_visible (G:=G) (Ssh:=Ssh) (Sown:=Sown)
      (store:=store) (x:=x) (T:=T) hStoreVis hVis)

-- Owned-Environment Disjointness Reframing

lemma owned_disjoint_sub_left
    {Sown : OwnedEnv} {G : GEnv} (split : ParSplit Sown.left G) :
    OwnedDisjoint Sown →
    DisjointS split.S1 split.S2 →
    OwnedDisjoint ({ right := Sown.right ++ split.S2, left := split.S1 } : OwnedEnv) := by
  intro hOwn hDisjS
  have hOwnLeftAll : DisjointS Sown.right (split.S1 ++ split.S2) := by
    simpa [OwnedDisjoint, split.hS] using hOwn
  have hR1 : DisjointS Sown.right split.S1 := disjoint_s_split_left hOwnLeftAll
  have hS2S1 : DisjointS split.S2 split.S1 := disjoint_s_symm hDisjS
  have hAll : DisjointS (Sown.right ++ split.S2) split.S1 :=
    disjoint_s_append_left hR1 hS2S1
  simpa [OwnedDisjoint, OwnedEnv.all] using hAll

lemma owned_disjoint_sub_right
    {Sown : OwnedEnv} {G : GEnv} (split : ParSplit Sown.left G) :
    OwnedDisjoint Sown →
    DisjointS split.S1 split.S2 →
    OwnedDisjoint ({ right := Sown.right ++ split.S1, left := split.S2 } : OwnedEnv) := by
  intro hOwn hDisjS
  have hOwnLeftAll : DisjointS Sown.right (split.S1 ++ split.S2) := by
    simpa [OwnedDisjoint, split.hS] using hOwn
  have hR2 : DisjointS Sown.right split.S2 := disjoint_s_split_right hOwnLeftAll
  have hS1S2 : DisjointS split.S1 split.S2 := hDisjS
  have hAll : DisjointS (Sown.right ++ split.S1) split.S2 :=
    disjoint_s_append_left hR2 hS1S2
  simpa [OwnedDisjoint, OwnedEnv.all] using hAll

-- Endpoint Equality from Store Typing

/- ## Structured Block 3 -/
lemma channel_endpoint_eq_of_store_visible
    {G : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore}
    {k : Var} {e e' : Endpoint}
    (hStore : StoreTypedStrong G (SEnvAll Ssh Sown) store)
    (hDisjShAll : DisjointS Ssh (Sown : SEnv))
    (hOwnDisj : OwnedDisjoint Sown)
    (hk : lookupSEnv (Ssh ++ Sown.left) k = some (ValType.chan e.sid e.role))
    (hkStr : lookupStr store k = some (Value.chan e')) :
    e' = e := by
  obtain ⟨vk, hkStr', hkTyped⟩ :=
    store_lookup_of_visible_lookup hStore hDisjShAll hOwnDisj hk
  have hkChan : vk = Value.chan e := has_type_val_chan_inv hkTyped
  have hkStr'' : lookupStr store k = some (Value.chan e) := by
    simpa [hkChan] using hkStr'
  have hEqOpt : some (Value.chan e') = some (Value.chan e) := by
    simpa [hkStr] using hkStr''
  have hEq : (Value.chan e') = (Value.chan e) := Option.some.inj hEqOpt
  cases hEq
  rfl

-- GEnv Framing for Pre-Out Typing

lemma has_type_proc_pre_out_send_inv
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k x : Var}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh Sown G (.send k x) Sfin Gfin W Δ →
    ∃ (e : Endpoint) (q : Role) (T : ValType) (L : LocalType),
      lookupSEnv (Ssh ++ Sown.left) k = some (ValType.chan e.sid e.role) ∧
      lookupG G e = some (.send q T L) := by
  intro h
  cases h with
  | send hk hG hx => exact ⟨_, _, _, _, hk, hG⟩

lemma has_type_proc_pre_out_recv_inv
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k x : Var}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh Sown G (.recv k x) Sfin Gfin W Δ →
    ∃ (e : Endpoint) (p : Role) (T : ValType) (L : LocalType),
      lookupSEnv (Ssh ++ Sown.left) k = some (ValType.chan e.sid e.role) ∧
      lookupG G e = some (.recv p T L) := by
  intro h
  cases h with
  | recv_new hk hG hNoSh hNoOwnL => exact ⟨_, _, _, _, hk, hG⟩
  | recv_old hk hG hNoSh hOwn => exact ⟨_, _, _, _, hk, hG⟩

lemma has_type_proc_pre_out_select_inv
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k : Var} {l : Label}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh Sown G (.select k l) Sfin Gfin W Δ →
    ∃ (e : Endpoint) (q : Role) (bs : List (Label × LocalType)),
      lookupSEnv (Ssh ++ Sown.left) k = some (ValType.chan e.sid e.role) ∧
      lookupG G e = some (.select q bs) := by
  intro h
  cases h with
  | select hk hG hbs => exact ⟨_, _, _, hk, hG⟩

/- ## Structured Block 4 -/
lemma has_type_proc_pre_out_branch_inv
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k : Var} {procs : List (Label × Process)}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh Sown G (.branch k procs) Sfin Gfin W Δ →
    ∃ (e : Endpoint) (p : Role) (bs : List (Label × LocalType)),
      lookupSEnv (Ssh ++ Sown.left) k = some (ValType.chan e.sid e.role) ∧
      lookupG G e = some (.branch p bs) := by
  intro h
  cases h with
  | branch hk hG hLen hLabels hBodies hOutLbl hSess hDom hRight => exact ⟨_, _, _, hk, hG⟩

-- GEnv Update Framing

lemma update_g_full_eq_update_g_mid
    {Gfull Gleft Gmid Gright : GEnv} {e : Endpoint} {L L' : LocalType} {G' : GEnv} :
    Gfull = Gleft ++ Gmid ++ Gright →
    DisjointG Gleft Gmid →
    lookupG Gmid e = some L →
    G' = updateG Gfull e L' →
    G' = Gleft ++ updateG Gmid e L' ++ Gright := by
  intro hGfull hDisjL hG hGout
  have hNoneLeft : lookupG Gleft e = none :=
    disjoint_g_lookup_left (G₁:=Gmid) (G₂:=Gleft) (disjoint_g_symm hDisjL) hG
  have hLookupMid : lookupG (Gleft ++ Gmid) e = some L := by
    have hEq' := lookup_g_append_right (G₁:=Gleft) (G₂:=Gmid) (e:=e) hNoneLeft
    simpa [hEq'] using hG
  have hUpdRight :=
    update_g_append_left_hit (G₁:=Gleft ++ Gmid) (G₂:=Gright) (e:=e) (L':=L') hLookupMid
  have hUpdLeft :=
    update_g_append_left (G₁:=Gleft) (G₂:=Gmid) (e:=e) (L:=L') hNoneLeft
  have hGout' : G' = updateG ((Gleft ++ Gmid) ++ Gright) e L' := by
    simpa [hGfull, List.append_assoc] using hGout
  calc
    G' = updateG ((Gleft ++ Gmid) ++ Gright) e L' := hGout'
    _ = updateG (Gleft ++ Gmid) e L' ++ Gright := hUpdRight
    _ = Gleft ++ updateG Gmid e L' ++ Gright := by
      simp [hUpdLeft, List.append_assoc]

-- Typed-Step Frame Preservation (Communication Cases)

lemma typed_step_preserves_frames_send
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfull Gleft Gmid Gright : GEnv}
    {store : VarStore}
    {k x : Var} {eStep : Endpoint} {Lstep : LocalType}
    {G' : GEnv} {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    (hGfull : Gfull = Gleft ++ Gmid ++ Gright) →
    (hDisjL : DisjointG Gleft Gmid) →
    (hStore : StoreTypedStrong Gfull (SEnvAll Ssh Sown) store) →
    (hDisjShAll : DisjointS Ssh (Sown : SEnv)) →
    (hOwnDisj : OwnedDisjoint Sown) →
    (hOut : HasTypeProcPreOut Ssh Sown Gmid (.send k x) Sfin Gfin W Δ) →
    (hkStr : lookupStr store k = some (.chan eStep)) →
    (hGout : G' = updateG Gfull eStep Lstep) →
    ∃ Gmid', G' = Gleft ++ Gmid' ++ Gright := by
  intro hGfull hDisjL hStore hDisjShAll hOwnDisj hOut hkStr hGout
  rcases has_type_proc_pre_out_send_inv hOut with ⟨eOut, qOut, TOut, LOut, hk, hG⟩
/- ## Structured Block 5 -/
  have hEq : eStep = eOut :=
    channel_endpoint_eq_of_store_visible (hStore:=hStore) (k:=k) (e:=eOut) (e':=eStep)
      hDisjShAll hOwnDisj hk hkStr
  subst hEq
  refine ⟨updateG Gmid eStep Lstep, ?_⟩
  exact update_g_full_eq_update_g_mid hGfull hDisjL hG hGout

-- Typed-Step Frame Preservation (Receive Case)

lemma typed_step_preserves_frames_recv
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfull Gleft Gmid Gright : GEnv}
    {store : VarStore}
    {k x : Var} {eStep : Endpoint} {Lstep : LocalType}
    {G' : GEnv} {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    (hGfull : Gfull = Gleft ++ Gmid ++ Gright) →
    (hDisjL : DisjointG Gleft Gmid) →
    (hStore : StoreTypedStrong Gfull (SEnvAll Ssh Sown) store) →
    (hDisjShAll : DisjointS Ssh (Sown : SEnv)) →
    (hOwnDisj : OwnedDisjoint Sown) →
    (hOut : HasTypeProcPreOut Ssh Sown Gmid (.recv k x) Sfin Gfin W Δ) →
    (hkStr : lookupStr store k = some (.chan eStep)) →
    (hGout : G' = updateG Gfull eStep Lstep) →
    ∃ Gmid', G' = Gleft ++ Gmid' ++ Gright := by
  intro hGfull hDisjL hStore hDisjShAll hOwnDisj hOut hkStr hGout
  rcases has_type_proc_pre_out_recv_inv hOut with ⟨eOut, pOut, TOut, LOut, hk, hG⟩
  have hEq : eStep = eOut :=
    channel_endpoint_eq_of_store_visible (hStore:=hStore) (k:=k) (e:=eOut) (e':=eStep)
      hDisjShAll hOwnDisj hk hkStr
  subst hEq
  refine ⟨updateG Gmid eStep Lstep, ?_⟩
  exact update_g_full_eq_update_g_mid hGfull hDisjL hG hGout

-- Typed-Step Frame Preservation (Select Case)

lemma typed_step_preserves_frames_select
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfull Gleft Gmid Gright : GEnv}
    {store : VarStore}
    {k : Var} {ℓ : Label} {eStep : Endpoint} {Lstep : LocalType}
    {G' : GEnv} {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    (hGfull : Gfull = Gleft ++ Gmid ++ Gright) →
    (hDisjL : DisjointG Gleft Gmid) →
    (hStore : StoreTypedStrong Gfull (SEnvAll Ssh Sown) store) →
    (hDisjShAll : DisjointS Ssh (Sown : SEnv)) →
    (hOwnDisj : OwnedDisjoint Sown) →
    (hOut : HasTypeProcPreOut Ssh Sown Gmid (.select k ℓ) Sfin Gfin W Δ) →
    (hkStr : lookupStr store k = some (.chan eStep)) →
    (hGout : G' = updateG Gfull eStep Lstep) →
    ∃ Gmid', G' = Gleft ++ Gmid' ++ Gright := by
  intro hGfull hDisjL hStore hDisjShAll hOwnDisj hOut hkStr hGout
  rcases has_type_proc_pre_out_select_inv hOut with ⟨eOut, qOut, bsOut, hk, hG⟩
  have hEq : eStep = eOut :=
    channel_endpoint_eq_of_store_visible (hStore:=hStore) (k:=k) (e:=eOut) (e':=eStep)
      hDisjShAll hOwnDisj hk hkStr
  subst hEq
  refine ⟨updateG Gmid eStep Lstep, ?_⟩
  exact update_g_full_eq_update_g_mid hGfull hDisjL hG hGout

-- Typed-Step Frame Preservation (Branch Case)

/- ## Structured Block 6 -/
lemma typed_step_preserves_frames_branch
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfull Gleft Gmid Gright : GEnv}
    {store : VarStore}
    {k : Var} {procs : List (Label × Process)} {eStep : Endpoint} {Lstep : LocalType}
    {G' : GEnv} {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    (hGfull : Gfull = Gleft ++ Gmid ++ Gright) →
    (hDisjL : DisjointG Gleft Gmid) →
    (hStore : StoreTypedStrong Gfull (SEnvAll Ssh Sown) store) →
    (hDisjShAll : DisjointS Ssh (Sown : SEnv)) →
    (hOwnDisj : OwnedDisjoint Sown) →
    (hOut : HasTypeProcPreOut Ssh Sown Gmid (.branch k procs) Sfin Gfin W Δ) →
    (hkStr : lookupStr store k = some (.chan eStep)) →
    (hGout : G' = updateG Gfull eStep Lstep) →
    ∃ Gmid', G' = Gleft ++ Gmid' ++ Gright := by
  intro hGfull hDisjL hStore hDisjShAll hOwnDisj hOut hkStr hGout
  rcases has_type_proc_pre_out_branch_inv hOut with ⟨eOut, pOut, bsOut, hk, hG⟩
  have hEq : eStep = eOut :=
    channel_endpoint_eq_of_store_visible (hStore:=hStore) (k:=k) (e:=eOut) (e':=eStep)
      hDisjShAll hOwnDisj hk hkStr
  subst hEq
  refine ⟨updateG Gmid eStep Lstep, ?_⟩
  exact update_g_full_eq_update_g_mid hGfull hDisjL hG hGout

-- Use has_type_proc_pre_out_frame_g_right/left from Protocol.Typing.Framing.


end
