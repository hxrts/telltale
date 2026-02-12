import Protocol.Typing.Framing.Lemmas.LeftParTransport

/-! # Middle Frame Specification

Specification of the middle-frame preservation property, defining the
goal shape for the main inductive proof. -/

/-
The Problem. The middle-frame theorem has a complex statement with many
parameters and conditions. Defining it directly in the main theorem
makes the proof hard to navigate.

Solution Structure. Define `HasTypeProcPreOut_preserved_sub_middle_frame_spec`
as the full specification. Define `MiddleFrameGoal` as a specialized
version bound to a concrete `TypedStep` for use in induction hypotheses.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Specification Definitions -/

def HasTypeProcPreOut_preserved_sub_middle_frame_spec : Prop :=
  ∀ {Gstore Gleft Gmid Gright G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' Sfin Gfin W Δ},
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    DisjointG Gleft Gmid →
    DisjointG Gleft Gright →
    DisjointG Gmid Gright →
    G = Gleft ++ Gmid ++ Gright →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    DisjointS Sown.right Sfin.left →
    HasTypeProcPreOut Ssh Sown Gmid P Sfin Gfin W Δ →
    ∃ Gmid' W' Δ', G' = Gleft ++ Gmid' ++ Gright ∧
      SessionsOf Gmid' ⊆ SessionsOf Gmid ∧
      HasTypeProcPreOut Ssh Sown' Gmid' P' Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ

/-- Recursive middle-frame goal specialized to a concrete `TypedStep`. -/
def MiddleFrameGoal
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'}
    (hTS : TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P') : Prop :=
  ∀ {Gstore Gleft Gmid Gright Sfin Gfin W Δ},
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    DisjointG Gleft Gmid →
    DisjointG Gleft Gright →
    DisjointG Gmid Gright →
    G = Gleft ++ Gmid ++ Gright →
    DisjointS Sown.right Sfin.left →
    HasTypeProcPreOut Ssh Sown Gmid P Sfin Gfin W Δ →
    ∃ Gmid' W' Δ', G' = Gleft ++ Gmid' ++ Gright ∧
      SessionsOf Gmid' ⊆ SessionsOf Gmid ∧
      HasTypeProcPreOut Ssh Sown' Gmid' P' Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ

/-- Lift a visible lookup (`Ssh ++ Sown.left`) into `SEnvAll` under owned disjointness. -/
lemma lookupSEnv_all_of_visible_owned
    {Ssh : SEnv} {Sown : OwnedEnv} {x : Var} {T : ValType} :
    OwnedDisjoint Sown →
    lookupSEnv (SEnvVisible Ssh Sown) x = some T →
    lookupSEnv (SEnvAll Ssh Sown) x = some T := by
  intro hOwn hVis
  simpa [SEnvVisible] using
    (lookupSEnv_all_frame_prefix_ofLeft
      (Ssh:=Ssh) (S₁:=Sown.right) (S₂:=Sown.left) (x:=x) (T:=T)
      hOwn (by simpa [SEnvVisible] using hVis))

/-- Align channel endpoints from `StoreTyped` and a visible channel typing fact. -/
lemma endpoint_eq_of_store_visible_all
    {Gstore : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore}
    {k : Var} {e e' : Endpoint} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    OwnedDisjoint Sown →
    lookupStr store k = some (.chan e) →
    lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e'.sid e'.role) →
    e = e' := by
  intro hStore hOwn hkStore hkVis
  have hkAll : lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) :=
    lookupSEnv_all_of_visible_owned (Ssh:=Ssh) (Sown:=Sown) (x:=k)
      (T:=.chan e'.sid e'.role) hOwn hkVis
  have hChanTy : HasTypeVal Gstore (.chan e) (.chan e'.sid e'.role) :=
    hStore k (.chan e) (.chan e'.sid e'.role) hkStore hkAll
  have hValEq : (Value.chan e) = Value.chan ⟨e'.sid, e'.role⟩ := by
    simpa using (HasTypeVal_chan_inv hChanTy)
  cases e
  cases e'
  cases hValEq
  rfl

lemma length_updateG_hit {G : GEnv} {e : Endpoint} {L L' : LocalType} :
    lookupG G e = some L →
    (updateG G e L').length = G.length := by
  intro hLookup
  induction G with
  | nil =>
      simp [lookupG] at hLookup
  | cons hd tl ih =>
      cases hd with
      | mk e' L'' =>
          by_cases hEq : e = e'
          · subst hEq
            simp [lookupG] at hLookup
            simp [updateG]
          · have h' : lookupG tl e = some L := by
              have hbeq : (e == e') = false := by
                exact beq_eq_false_iff_ne.mpr hEq
              simpa [lookupG, List.lookup, hbeq] using hLookup
            simp [updateG, hEq, ih h']

lemma SessionsOf_left_subset_of_update
    {G₁ G₂ : GEnv} {e : Endpoint} {L L0 : LocalType} {G₁' : GEnv} :
    lookupG (G₁ ++ G₂) e = some L0 →
    updateG (G₁ ++ G₂) e L = G₁' ++ G₂ →
    SessionsOf G₁' ⊆ SessionsOf G₁ := by
  intro hLookup hUpd
  by_cases hLeft : lookupG G₁ e = none
  · have hUpd' :
        updateG (G₁ ++ G₂) e L = G₁ ++ updateG G₂ e L :=
        updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hLeft
    have hEq : G₁' ++ G₂ = G₁ ++ updateG G₂ e L := by
      simpa [hUpd'] using hUpd.symm
    have hLookupG2 : lookupG G₂ e = some L0 := by
      have hLookup' :=
        lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hLeft
      simpa [hLookup'] using hLookup
    have hLenG2 : (updateG G₂ e L).length = G₂.length :=
      length_updateG_hit (G:=G₂) (e:=e) (L:=L0) (L':=L) hLookupG2
    have hLen : G₁'.length = G₁.length := by
      have hLen' := congrArg List.length hEq
      simp [List.length_append, hLenG2] at hLen'
      exact hLen'
    have hG₁' : G₁' = G₁ := List.append_inj_left hEq hLen
    intro s hs
    simpa [hG₁'] using hs
  · cases hSome : lookupG G₁ e with
    | none => exact (hLeft hSome).elim
    | some L1 =>
        have hUpd' :
            updateG (G₁ ++ G₂) e L = updateG G₁ e L ++ G₂ :=
          updateG_append_left_hit (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L1) (L':=L) hSome
        have hEq : G₁' ++ G₂ = updateG G₁ e L ++ G₂ := by
          simpa [hUpd'] using hUpd.symm
        have hLen : G₁'.length = (updateG G₁ e L).length := by
          have hLen' := congrArg List.length hEq
          simp [List.length_append] at hLen'
          exact hLen'
        have hG₁' : G₁' = updateG G₁ e L := List.append_inj_left hEq hLen
        have hSess :
            SessionsOf (updateG G₁ e L) = SessionsOf G₁ :=
          SessionsOf_updateG_eq (G:=G₁) (e:=e) (L:=L) (L':=L1) hSome
        intro s hs
        have hs' : s ∈ SessionsOf (updateG G₁ e L) := by
          simpa [hG₁'] using hs
        simpa [hSess] using hs'

lemma SessionsOf_right_subset_of_update
    {G₁ G₂ : GEnv} {e : Endpoint} {L L0 : LocalType} {G₂' : GEnv} :
    lookupG (G₁ ++ G₂) e = some L0 →
    updateG (G₁ ++ G₂) e L = G₁ ++ G₂' →
    SessionsOf G₂' ⊆ SessionsOf G₂ := by
  intro hLookup hUpd
  by_cases hLeft : lookupG G₁ e = none
  · have hUpd' :
        updateG (G₁ ++ G₂) e L = G₁ ++ updateG G₂ e L :=
        updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hLeft
    have hEq : G₁ ++ G₂' = G₁ ++ updateG G₂ e L := by
      simpa [hUpd'] using hUpd.symm
    have hG₂' : G₂' = updateG G₂ e L :=
      List.append_inj_right hEq rfl
    have hLookupG2 : lookupG G₂ e = some L0 := by
      have hLookup' :=
        lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hLeft
      simpa [hLookup'] using hLookup
    have hSess :
        SessionsOf (updateG G₂ e L) = SessionsOf G₂ :=
      SessionsOf_updateG_eq (G:=G₂) (e:=e) (L:=L) (L':=L0) hLookupG2
    intro s hs
    have hs' : s ∈ SessionsOf (updateG G₂ e L) := by
      simpa [hG₂'] using hs
    simpa [hSess] using hs'
  · cases hSome : lookupG G₁ e with
    | none => exact (hLeft hSome).elim
    | some L1 =>
        have hUpd' :
            updateG (G₁ ++ G₂) e L = updateG G₁ e L ++ G₂ :=
          updateG_append_left_hit (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L1) (L':=L) hSome
        have hEq : G₁ ++ G₂' = updateG G₁ e L ++ G₂ := by
          simpa [hUpd'] using hUpd.symm
        have hLenG1 : (updateG G₁ e L).length = G₁.length :=
          length_updateG_hit (G:=G₁) (e:=e) (L:=L1) (L':=L) hSome
        have hG₂' : G₂' = G₂ :=
          List.append_inj_right hEq hLenG1.symm
        intro s hs
        simpa [hG₂'] using hs

lemma append_left_eq_of_eq {α : Type} {l1 l2 r : List α} (h : l1 ++ r = l2 ++ r) :
    l1 = l2 := by
  have hLen := congrArg List.length h
  simp [List.length_append] at hLen
  exact List.append_inj_left h hLen

lemma append_right_eq_of_eq {α : Type} {l r1 r2 : List α} (h : l ++ r1 = l ++ r2) :
    r1 = r2 := by
  have hLen := congrArg List.length h
  simp [List.length_append] at hLen
  exact List.append_inj_right h rfl

/-- Updating an endpoint known to live in the middle segment preserves outer frames. -/
lemma updateG_append_middle_hit
    {Gleft Gmid Gright : GEnv} {e : Endpoint} {L0 L : LocalType} :
    lookupG Gleft e = none →
    lookupG Gmid e = some L0 →
    updateG (Gleft ++ Gmid ++ Gright) e L =
      Gleft ++ updateG Gmid e L ++ Gright := by
  intro hNoneLeft hSomeMid
  have hOut :
      updateG (Gleft ++ (Gmid ++ Gright)) e L =
        Gleft ++ updateG (Gmid ++ Gright) e L :=
    updateG_append_left (G₁:=Gleft) (G₂:=Gmid ++ Gright) (e:=e) (L:=L) hNoneLeft
  have hMid :
      updateG (Gmid ++ Gright) e L = updateG Gmid e L ++ Gright :=
    updateG_append_left_hit (G₁:=Gmid) (G₂:=Gright) (e:=e) (L:=L0) (L':=L) hSomeMid
  calc
    updateG (Gleft ++ Gmid ++ Gright) e L
        = updateG (Gleft ++ (Gmid ++ Gright)) e L := by simp [List.append_assoc]
    _ = Gleft ++ updateG (Gmid ++ Gright) e L := hOut
    _ = Gleft ++ (updateG Gmid e L ++ Gright) := by simp [hMid]
    _ = Gleft ++ updateG Gmid e L ++ Gright := by simp [List.append_assoc]

/-- Extract the middle segment from an updated three-way append. -/
lemma updateG_append_middle_cancel
    {Gleft Gmid Gright Gmid' : GEnv} {e : Endpoint} {L0 L : LocalType} :
    lookupG Gleft e = none →
    lookupG Gmid e = some L0 →
    updateG (Gleft ++ Gmid ++ Gright) e L = Gleft ++ Gmid' ++ Gright →
    Gmid' = updateG Gmid e L := by
  intro hNoneLeft hSomeMid hEq
  have hUpd := updateG_append_middle_hit (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
    (e:=e) (L0:=L0) (L:=L) hNoneLeft hSomeMid
  have hEq' : Gleft ++ (Gmid' ++ Gright) = Gleft ++ (updateG Gmid e L ++ Gright) := by
    calc
      Gleft ++ (Gmid' ++ Gright) = Gleft ++ Gmid' ++ Gright := by simp [List.append_assoc]
      _ = updateG (Gleft ++ Gmid ++ Gright) e L := hEq.symm
      _ = Gleft ++ updateG Gmid e L ++ Gright := hUpd
      _ = Gleft ++ (updateG Gmid e L ++ Gright) := by simp [List.append_assoc]
  have hCancelLeft : Gmid' ++ Gright = updateG Gmid e L ++ Gright := by
    exact append_right_eq_of_eq hEq'
  exact append_left_eq_of_eq hCancelLeft

/-- Session set of a middle update remains within the original middle segment. -/
lemma SessionsOf_subset_middle_update
    {Gmid : GEnv} {e : Endpoint} {L0 L : LocalType} :
    lookupG Gmid e = some L0 →
    SessionsOf (updateG Gmid e L) ⊆ SessionsOf Gmid := by
  intro hSome s hs
  have hEqSess :
      SessionsOf (updateG Gmid e L) = SessionsOf Gmid :=
    SessionsOf_updateG_eq (G:=Gmid) (e:=e) (L:=L) (L':=L0) hSome
  simpa [hEqSess] using hs

/-- Lift a middle-segment lookup into the full framed environment. -/
lemma lookupG_middle_to_full
    {Gleft Gmid Gright : GEnv} {e : Endpoint} {L0 : LocalType} :
    lookupG Gleft e = none →
    lookupG Gmid e = some L0 →
    lookupG (Gleft ++ Gmid ++ Gright) e = some L0 := by
  intro hNoneLeft hSomeMid
  have hStep :
      lookupG (Gleft ++ Gmid) e = some L0 := by
    exact lookupG_append_right (G₁:=Gleft) (G₂:=Gmid) (e:=e) hNoneLeft |>.trans hSomeMid
  exact lookupG_append_left (G₁:=Gleft ++ Gmid) (G₂:=Gright) (e:=e) hStep

/-- A lookup in the middle segment is absent from any disjoint right frame. -/
lemma lookupG_middle_none_right
    {Gmid Gright : GEnv} {e : Endpoint} {L0 : LocalType} :
    DisjointG Gmid Gright →
    lookupG Gmid e = some L0 →
    lookupG Gright e = none := by
  intro hDisj hSomeMid
  exact lookupG_none_of_disjoint (G₁:=Gright) (G₂:=Gmid) (DisjointG_symm hDisj) hSomeMid

/-- Package middle update output as a framed decomposition witness. -/
lemma updateG_middle_witness
    {Gleft Gmid Gright G' : GEnv} {e : Endpoint} {L0 L : LocalType} :
    lookupG Gleft e = none →
    lookupG Gmid e = some L0 →
    G' = updateG (Gleft ++ Gmid ++ Gright) e L →
    ∃ Gmid', G' = Gleft ++ Gmid' ++ Gright ∧ Gmid' = updateG Gmid e L := by
  intro hNoneLeft hSomeMid hG'
  refine ⟨updateG Gmid e L, ?_, rfl⟩
  calc
    G' = updateG (Gleft ++ Gmid ++ Gright) e L := hG'
    _ = Gleft ++ updateG Gmid e L ++ Gright :=
      updateG_append_middle_hit (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
        (e:=e) (L0:=L0) (L:=L) hNoneLeft hSomeMid

/-- Recover the stepped endpoint lookup in the middle segment for a pre-out send judgment. -/
lemma middle_send_lookup_of_pre
    {Gstore : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {Gmid : GEnv}
    {store : VarStore} {k x : Var} {e : Endpoint}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    OwnedDisjoint Sown →
    lookupStr store k = some (.chan e) →
    HasTypeProcPreOut Ssh Sown Gmid (.send k x) Sfin Gfin W Δ →
    ∃ q T L, lookupG Gmid e = some (.send q T L) := by
  intro hStore hOwn hkStore hPre
  cases hPre with
  | send hkMid hGmid hxMid =>
      rename_i eMid q T L
      have hEqE : e = eMid :=
        endpoint_eq_of_store_visible_all
          (Gstore:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
          (k:=k) (e:=e) (e':=eMid) hStore hOwn hkStore hkMid
      exact ⟨q, T, L, by simpa [hEqE] using hGmid⟩

/-- Recover the stepped endpoint lookup in the middle segment for a pre-out recv judgment. -/
lemma middle_recv_lookup_of_pre
    {Gstore : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {Gmid : GEnv}
    {store : VarStore} {k x : Var} {e : Endpoint}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    OwnedDisjoint Sown →
    lookupStr store k = some (.chan e) →
    HasTypeProcPreOut Ssh Sown Gmid (.recv k x) Sfin Gfin W Δ →
    ∃ p T L, lookupG Gmid e = some (.recv p T L) := by
  intro hStore hOwn hkStore hPre
  cases hPre with
  | recv_new hkMid hGmid hNoSh hNoOwnL =>
      rename_i eMid p T L
      have hEqE : e = eMid :=
        endpoint_eq_of_store_visible_all
          (Gstore:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
          (k:=k) (e:=e) (e':=eMid) hStore hOwn hkStore hkMid
      exact ⟨p, T, L, by simpa [hEqE] using hGmid⟩
  | recv_old hkMid hGmid hNoSh hOwnL =>
      rename_i eMid p T L T'
      have hEqE : e = eMid :=
        endpoint_eq_of_store_visible_all
          (Gstore:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
          (k:=k) (e:=e) (e':=eMid) hStore hOwn hkStore hkMid
      exact ⟨p, T, L, by simpa [hEqE] using hGmid⟩

/-- Recover the stepped endpoint lookup in the middle segment for a pre-out select judgment. -/
lemma middle_select_lookup_of_pre
    {Gstore : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {Gmid : GEnv}
    {store : VarStore} {k : Var} {ℓ : Label} {e : Endpoint}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    OwnedDisjoint Sown →
    lookupStr store k = some (.chan e) →
    HasTypeProcPreOut Ssh Sown Gmid (.select k ℓ) Sfin Gfin W Δ →
    ∃ q bs, lookupG Gmid e = some (.select q bs) := by
  intro hStore hOwn hkStore hPre
  cases hPre with
  | select hkMid hGmid hFind =>
      rename_i eMid q bs L
      have hEqE : e = eMid :=
        endpoint_eq_of_store_visible_all
          (Gstore:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
          (k:=k) (e:=e) (e':=eMid) hStore hOwn hkStore hkMid
      exact ⟨q, bs, by simpa [hEqE] using hGmid⟩

/-- Recover the stepped endpoint lookup in the middle segment for a pre-out branch judgment. -/
lemma middle_branch_lookup_of_pre
    {Gstore : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {Gmid : GEnv}
    {store : VarStore} {k : Var} {procs : List (Label × Process)} {e : Endpoint}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    OwnedDisjoint Sown →
    lookupStr store k = some (.chan e) →
    HasTypeProcPreOut Ssh Sown Gmid (.branch k procs) Sfin Gfin W Δ →
    ∃ p bs, lookupG Gmid e = some (.branch p bs) := by
  intro hStore hOwn hkStore hPre
  cases hPre with
  | branch hkMid hGmid hLen hLbl hBodies hOut hSess hDom hRight =>
      rename_i eMid p bs
      have hEqE : e = eMid :=
        endpoint_eq_of_store_visible_all
          (Gstore:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
          (k:=k) (e:=e) (e':=eMid) hStore hOwn hkStore hkMid
      exact ⟨p, bs, by simpa [hEqE] using hGmid⟩

/-- Decompose a middle `send` update inside a three-way framed global environment. -/
lemma middle_send_update_decompose
    {Gleft Gmid Gright G G' : GEnv} {e : Endpoint}
    {q target : Role} {Tmid T : ValType} {Lmid L : LocalType} :
    DisjointG Gleft Gmid →
    G = Gleft ++ Gmid ++ Gright →
    lookupG Gmid e = some (.send q Tmid Lmid) →
    G' = updateG G e L →
    ∃ Gmid', G' = Gleft ++ Gmid' ++ Gright ∧
      SessionsOf Gmid' ⊆ SessionsOf Gmid ∧
      Gmid' = updateG Gmid e L := by
  intro hDisjLM hEq hMid hUpd
  have hNoneLeft : lookupG Gleft e = none :=
    lookupG_none_of_disjoint (G₁:=Gleft) (G₂:=Gmid) hDisjLM hMid
  refine ⟨updateG Gmid e L, ?_, ?_, rfl⟩
  · calc
      G' = updateG G e L := hUpd
      _ = updateG (Gleft ++ Gmid ++ Gright) e L := by simpa [hEq]
      _ = Gleft ++ updateG Gmid e L ++ Gright :=
        updateG_append_middle_hit (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
          (e:=e) (L0:=.send q Tmid Lmid) (L:=L) hNoneLeft hMid
  · exact SessionsOf_subset_middle_update (Gmid:=Gmid) (e:=e)
      (L0:=.send q Tmid Lmid) (L:=L) hMid

/-- Constructive middle-frame preservation for a `send` step. -/
lemma preserved_sub_middle_send
    {Gstore Gleft Gmid Gright G : GEnv} {D D' : DEnv}
    {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore} {bufs bufs' : Buffers}
    {k x : Var} {e : Endpoint} {target : Role} {T : ValType} {L : LocalType}
    {G' : GEnv}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    OwnedDisjoint Sown →
    DisjointG Gleft Gmid →
    G = Gleft ++ Gmid ++ Gright →
    lookupStr store k = some (.chan e) →
    lookupG G e = some (.send target T L) →
    G' = updateG G e L →
    TypedStep G D Ssh Sown store bufs (.send k x) G' D' Sown store bufs' .skip →
    HasTypeProcPreOut Ssh Sown Gmid (.send k x) Sfin Gfin W Δ →
    ∃ Gmid' W' Δ', G' = Gleft ++ Gmid' ++ Gright ∧
      SessionsOf Gmid' ⊆ SessionsOf Gmid ∧
      HasTypeProcPreOut Ssh Sown Gmid' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hStore hOwn hDisjLM hEqG hkStore hGstep hGupd hTS hPre
  cases hTS with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      cases hPre with
      | send hkMid hGmid hxMid =>
          rename_i eMid q Tmid Lmid
          have hEqE : e = eMid :=
            endpoint_eq_of_store_visible_all
              (Gstore:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
              (k:=k) (e:=e) (e':=eMid) hStore hOwn hkStore hkMid
          have hMid : lookupG Gmid e = some (.send q Tmid Lmid) := by
            simpa [hEqE] using hGmid
          have hNoneLeft : lookupG Gleft e = none :=
            lookupG_none_of_disjoint (G₁:=Gleft) (G₂:=Gmid) hDisjLM hMid
          have hFullMid : lookupG G e = some (.send q Tmid Lmid) := by
            calc
              lookupG G e = lookupG (Gleft ++ Gmid ++ Gright) e := by simpa [hEqG]
              _ = some (.send q Tmid Lmid) :=
                lookupG_middle_to_full (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
                  (e:=e) (L0:=.send q Tmid Lmid) hNoneLeft hMid
          have hSendEq : LocalType.send target T L = LocalType.send q Tmid Lmid := by
            exact Option.some.inj (by simpa [hGstep] using hFullMid)
          have hL : L = Lmid := by
            cases hSendEq
            rfl
          obtain ⟨Gmid', hEqG', hSubSess, hMid'⟩ :=
            middle_send_update_decompose (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
              (G:=G) (G':=G') (e:=e)
              (q:=q) (target:=target) (Tmid:=Tmid) (T:=T) (Lmid:=Lmid) (L:=L)
              hDisjLM hEqG hMid hGupd
          refine ⟨Gmid', [], ∅, hEqG', hSubSess, ?_, ?_, ?_⟩
          · have hGmidEq : Gmid' = updateG Gmid eMid Lmid := by
              calc
                Gmid' = updateG Gmid e L := hMid'
                _ = updateG Gmid e Lmid := by simpa [hL]
                _ = updateG Gmid eMid Lmid := by simpa [hEqE]
            simpa [hGmidEq] using
              (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown) (G:=Gmid'))
          · intro y hy
            cases hy
          · intro y Ty hy
            cases hy

end
