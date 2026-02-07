import Protocol.Typing.Preservation

/-!
# MPST Process Typing

This module defines the typing rules for MPST processes.

## Key Judgments

- `HasTypeProcN n S G D P`: Process P is well-typed under environments S, G, D
  with maximum session ID n
- `WTConfigN n S G D C`: Configuration C is well-typed

## Typing Rules

- **Skip**: `⊢ skip` (always well-typed)
- **Seq**: `⊢ P` and `⊢ Q` implies `⊢ seq P Q`
- **Par**: `⊢ P` and `⊢ Q` with split contexts implies `⊢ par P Q`
- **Send**: If `S[k] = chan (sid, r)` and `G[sid,r] = !q(T).L` and `S[x] = T`,
            then `⊢ send k x` and G[sid,r] ↦ L
- **Recv**: If `S[k] = chan (sid, r)` and `G[sid,r] = ?p(T).L`,
            then `⊢ recv k x` and G[sid,r] ↦ L, S[x] ↦ T
- **Select**: If `S[k] = chan (sid, r)` and `G[sid,r] = ⊕q{ℓᵢ: Lᵢ}`,
              then `⊢ select k ℓⱼ` and G[sid,r] ↦ Lⱼ
- **Branch**: If `S[k] = chan (sid, r)` and `G[sid,r] = &p{ℓᵢ: Lᵢ}`,
              then `⊢ branch k [(ℓᵢ, Pᵢ)]` if each Pᵢ is typed under Lᵢ
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

noncomputable section

/-! ### Progress Helpers -/

private theorem findLabel_eq {α : Type} {lbl lbl' : Label} {xs : List (Label × α)} {v : α}
    (h : xs.find? (fun b => b.1 == lbl) = some (lbl', v)) : lbl' = lbl := by
  have hPred : (lbl' == lbl) := (List.find?_eq_some_iff_append (xs := xs)
    (p := fun b => b.1 == lbl) (b := (lbl', v))).1 h |>.1
  have hPred' : (lbl' == lbl) = true := by
    simpa using hPred
  exact (beq_iff_eq).1 hPred'

def BlockedProc (store : VarStore) (bufs : Buffers) : Process → Prop
  | .recv k _ =>
      ∃ e source,
        lookupStr store k = some (.chan e) ∧
        lookupBuf bufs { sid := e.sid, sender := source, receiver := e.role } = []
  | .branch k _ =>
      ∃ e source,
        lookupStr store k = some (.chan e) ∧
        lookupBuf bufs { sid := e.sid, sender := source, receiver := e.role } = []
  | .seq P _ =>
      BlockedProc store bufs P
  | .par _ _ P Q =>
      BlockedProc store bufs P ∧ BlockedProc store bufs Q
  | _ => False

private lemma DisjointS_right_empty (S : SEnv) : DisjointS S (∅ : SEnv) := by
  intro x T₁ T₂ hL1 hL2
  have : lookupSEnv (∅ : SEnv) x = none := lookupSEnv_empty x
  cases hL2

private lemma DisjointS_left_empty (S : SEnv) : DisjointS (∅ : SEnv) S := by
  intro x T₁ T₂ hL1 hL2
  have : lookupSEnv (∅ : SEnv) x = none := lookupSEnv_empty x
  cases hL1

private lemma SessionsOf_empty : SessionsOf ([] : GEnv) = ∅ := by
  ext s; constructor
  · intro h
    rcases h with ⟨e, L, hLookup, hSid⟩
    simp [lookupG] at hLookup
  · intro h
    cases h

private lemma TypedStep_preserves_right
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    Sown'.right = Sown.right := by
  intro hStep
  induction hStep with
  | recv =>
      simp [OwnedEnv.updateLeft, *]
  | assign =>
      simp [OwnedEnv.updateLeft, *]
  | seq_step _ ih => exact ih
  | _ => rfl

private lemma channel_endpoint_eq_of_store
    {G : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore}
    {k : Var} {e e' : Endpoint} :
    (hStore : StoreTypedStrong G (SEnvAll Ssh Sown) store) →
    lookupSEnv (SEnvAll Ssh Sown) k = some (ValType.chan e.sid e.role) →
    lookupStr store k = some (Value.chan e') →
    e' = e := by
  intro hStore hk hkStr
  obtain ⟨vk, hkStr', hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
  have hkChan : vk = Value.chan e := HasTypeVal_chan_inv hkTyped
  have hkStr'' : lookupStr store k = some (Value.chan e) := by
    simpa [hkChan] using hkStr'
  have hEqOpt : some (Value.chan e') = some (Value.chan e) := by
    simpa [hkStr] using hkStr''
  have hEq : (Value.chan e') = (Value.chan e) := Option.some.inj hEqOpt
  cases hEq
  rfl

private lemma DisjointG_right_empty (G : GEnv) : DisjointG G [] := by
  simp [DisjointG, GEnvDisjoint, SessionsOf_empty]

private lemma DisjointG_left_empty (G : GEnv) : DisjointG [] G := by
  simp [DisjointG, GEnvDisjoint, SessionsOf_empty]

private lemma DEnv_find_empty (e : Edge) : (∅ : DEnv).find? e = none := by
  rfl

private lemma SessionsOfD_empty : SessionsOfD (∅ : DEnv) = ∅ := by
  ext s; constructor
  · intro h
    rcases h with ⟨e, ts, hFind, hSid⟩
    have : (∅ : DEnv).find? e = none := DEnv_find_empty e
    cases hFind
  · intro h
    cases h

private lemma DisjointD_right_empty (D : DEnv) : DisjointD D (∅ : DEnv) := by
  simp [DisjointD, SessionsOfD_empty]

private lemma DisjointD_left_empty (D : DEnv) : DisjointD (∅ : DEnv) D := by
  simp [DisjointD, SessionsOfD_empty]

private lemma DConsistent_empty (G : GEnv) : DConsistent G (∅ : DEnv) := by
  simp [DConsistent, SessionsOfD_empty]

private theorem DEnv_append_empty_right (D : DEnv) : D ++ (∅ : DEnv) = D :=
  DEnvUnion_empty_right D

private theorem DEnv_append_empty_left (D : DEnv) : (∅ : DEnv) ++ D = D :=
  DEnvUnion_empty_left D

private lemma SEnv_append_empty_right (S : SEnv) : S ++ (∅ : SEnv) = S := by
  simpa using (List.append_nil S)

private lemma SEnv_append_empty_left (S : SEnv) : (∅ : SEnv) ++ S = S := by
  simpa using (List.nil_append S)

/-! ### Store Typing Rearrangements (Local Helpers) -/

private lemma lookupSEnv_comm_of_disjoint {S₁ S₂ : SEnv} (hDisj : DisjointS S₁ S₂) :
    ∀ x, lookupSEnv (S₁ ++ S₂) x = lookupSEnv (S₂ ++ S₁) x := by
  intro x
  cases hLeft : lookupSEnv S₁ x with
  | some T =>
      have hNone : lookupSEnv S₂ x = none :=
        lookupSEnv_none_of_disjoint_left (S₁:=S₂) (S₂:=S₁) (DisjointS_symm hDisj) hLeft
      have hA := lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T) hLeft
      have hB := lookupSEnv_append_right (S₁:=S₂) (S₂:=S₁) (x:=x) hNone
      simpa [hA, hB, hLeft]
  | none =>
      have hA := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hLeft
      cases hRight : lookupSEnv S₂ x with
      | some T =>
          have hB := lookupSEnv_append_left (S₁:=S₂) (S₂:=S₁) (x:=x) (T:=T) hRight
          simpa [hA, hB, hRight]
      | none =>
          have hB := lookupSEnv_append_right (S₁:=S₂) (S₂:=S₁) (x:=x) hRight
          simpa [hA, hB, hRight, hLeft]

private lemma lookupSEnv_swap_left {S₁ S₂ S₃ : SEnv} (hDisj : DisjointS S₁ S₂) :
    ∀ x, lookupSEnv ((S₁ ++ S₂) ++ S₃) x = lookupSEnv ((S₂ ++ S₁) ++ S₃) x := by
  intro x
  cases hLeft : lookupSEnv (S₁ ++ S₂) x with
  | some T =>
      have hA := lookupSEnv_append_left (S₁:=S₁ ++ S₂) (S₂:=S₃) (x:=x) (T:=T) hLeft
      have hSwap := lookupSEnv_comm_of_disjoint hDisj x
      have hLeft' : lookupSEnv (S₂ ++ S₁) x = some T := by
        simpa [hSwap] using hLeft
      have hB := lookupSEnv_append_left (S₁:=S₂ ++ S₁) (S₂:=S₃) (x:=x) (T:=T) hLeft'
      have hA' : lookupSEnv (S₁ ++ (S₂ ++ S₃)) x = some T := by
        simpa [List.append_assoc] using hA
      have hB' : lookupSEnv (S₂ ++ (S₁ ++ S₃)) x = some T := by
        simpa [List.append_assoc] using hB
      simpa [hA', hB']
  | none =>
      have hA := lookupSEnv_append_right (S₁:=S₁ ++ S₂) (S₂:=S₃) (x:=x) hLeft
      have hSwap := lookupSEnv_comm_of_disjoint hDisj x
      have hNone : lookupSEnv (S₂ ++ S₁) x = none := by
        simpa [hSwap] using hLeft
      have hB := lookupSEnv_append_right (S₁:=S₂ ++ S₁) (S₂:=S₃) (x:=x) hNone
      have hA' : lookupSEnv (S₁ ++ (S₂ ++ S₃)) x = lookupSEnv S₃ x := by
        simpa [List.append_assoc] using hA
      have hB' : lookupSEnv (S₂ ++ (S₁ ++ S₃)) x = lookupSEnv S₃ x := by
        simpa [List.append_assoc] using hB
      simpa [hA', hB']

private lemma lookupSEnv_swap_left_prefix {Ssh S₁ S₂ S₃ : SEnv} (hDisj : DisjointS S₁ S₂) :
    ∀ x, lookupSEnv (SEnvAll Ssh ((S₁ ++ S₂) ++ S₃)) x =
      lookupSEnv (SEnvAll Ssh (S₂ ++ (S₁ ++ S₃))) x := by
  intro x
  cases hS : lookupSEnv Ssh x with
  | some Ty =>
      have hLeft :=
        lookupSEnv_append_left (S₁:=Ssh) (S₂:=((S₁ ++ S₂) ++ S₃)) (x:=x) (T:=Ty) hS
      have hRight :=
        lookupSEnv_append_left (S₁:=Ssh) (S₂:=(S₂ ++ (S₁ ++ S₃))) (x:=x) (T:=Ty) hS
      have hLeft' : lookupSEnv (Ssh ++ (S₁ ++ (S₂ ++ S₃))) x = some Ty := by
        simpa [List.append_assoc] using hLeft
      simpa [SEnvAll, hLeft', hRight]
  | none =>
      have hLeft := lookupSEnv_append_right (S₁:=Ssh) (S₂:=((S₁ ++ S₂) ++ S₃)) (x:=x) hS
      have hRight := lookupSEnv_append_right (S₁:=Ssh) (S₂:=(S₂ ++ (S₁ ++ S₃))) (x:=x) hS
      have hLeft' : lookupSEnv ((S₁ ++ S₂) ++ S₃) x = lookupSEnv (S₂ ++ (S₁ ++ S₃)) x := by
        simpa using (lookupSEnv_swap_left (S₁:=S₁) (S₂:=S₂) (S₃:=S₃) hDisj x)
      have hLeft'' : lookupSEnv (Ssh ++ (S₁ ++ (S₂ ++ S₃))) x =
          lookupSEnv ((S₁ ++ S₂) ++ S₃) x := by
        simpa [List.append_assoc] using hLeft
      have hRight'' : lookupSEnv (Ssh ++ (S₂ ++ (S₁ ++ S₃))) x =
          lookupSEnv (S₂ ++ (S₁ ++ S₃)) x := by
        simpa [List.append_assoc] using hRight
      calc
        lookupSEnv (SEnvAll Ssh ((S₁ ++ S₂) ++ S₃)) x
            = lookupSEnv (Ssh ++ (S₁ ++ (S₂ ++ S₃))) x := by
                simp [SEnvAll, List.append_assoc]
        _ = lookupSEnv ((S₁ ++ S₂) ++ S₃) x := hLeft''
        _ = lookupSEnv (S₂ ++ (S₁ ++ S₃)) x := hLeft'
        _ = lookupSEnv (Ssh ++ (S₂ ++ (S₁ ++ S₃))) x := by
                symm; exact hRight''
        _ = lookupSEnv (SEnvAll Ssh (S₂ ++ (S₁ ++ S₃))) x := by
                simp [SEnvAll]

private lemma StoreTypedStrong_rewriteS {G : GEnv} {S S' : SEnv} {store : VarStore}
    (hEq : ∀ x, lookupSEnv S x = lookupSEnv S' x) :
    StoreTypedStrong G S store → StoreTypedStrong G S' store := by
  intro hStore
  refine ⟨?_, ?_⟩
  · intro x
    simpa [hEq x] using hStore.sameDomain x
  ·
    intro x v T hStr hS'
    have hS : lookupSEnv S x = some T := by
      simpa [hEq x] using hS'
    exact hStore.typeCorr x v T hStr hS

private lemma StoreTypedStrong_swap_S_left_prefix
    {G : GEnv} {Ssh S₁ S₂ S₃ : SEnv} {store : VarStore}
    (hDisj : DisjointS S₁ S₂) :
    StoreTypedStrong G (SEnvAll Ssh ((S₁ ++ S₂) ++ S₃)) store →
    StoreTypedStrong G (SEnvAll Ssh (S₂ ++ (S₁ ++ S₃))) store := by
  intro hStore
  apply StoreTypedStrong_rewriteS (S:=SEnvAll Ssh ((S₁ ++ S₂) ++ S₃))
    (S':=SEnvAll Ssh (S₂ ++ (S₁ ++ S₃))) (store:=store)
  · intro x
    exact lookupSEnv_swap_left_prefix (Ssh:=Ssh) (S₁:=S₁) (S₂:=S₂) (S₃:=S₃) hDisj x
  · exact hStore

/-! ### GEnv Framing for Pre-Out Typing -/

private lemma HasTypeProcPreOut_send_inv
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k x : Var}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh Sown G (.send k x) Sfin Gfin W Δ →
    ∃ (e : Endpoint) (q : Role) (T : ValType) (L : LocalType),
      lookupSEnv (SEnvAll Ssh Sown) k = some (ValType.chan e.sid e.role) ∧
      lookupG G e = some (.send q T L) := by
  intro h
  cases h with
  | send hk hG hx => exact ⟨_, _, _, _, hk, hG⟩

private lemma HasTypeProcPreOut_recv_inv
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k x : Var}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh Sown G (.recv k x) Sfin Gfin W Δ →
    ∃ (e : Endpoint) (p : Role) (T : ValType) (L : LocalType),
      lookupSEnv (SEnvAll Ssh Sown) k = some (ValType.chan e.sid e.role) ∧
      lookupG G e = some (.recv p T L) := by
  intro h
  cases h with
  | recv_new hk hG hNoSh hNoOwnR hNoOwnL => exact ⟨_, _, _, _, hk, hG⟩
  | recv_old hk hG hNoSh hNoOwnR hOwn => exact ⟨_, _, _, _, hk, hG⟩

private lemma HasTypeProcPreOut_select_inv
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k : Var} {l : Label}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh Sown G (.select k l) Sfin Gfin W Δ →
    ∃ (e : Endpoint) (q : Role) (bs : List (Label × LocalType)),
      lookupSEnv (SEnvAll Ssh Sown) k = some (ValType.chan e.sid e.role) ∧
      lookupG G e = some (.select q bs) := by
  intro h
  cases h with
  | select hk hG hbs => exact ⟨_, _, _, hk, hG⟩

private lemma HasTypeProcPreOut_branch_inv
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k : Var} {procs : List (Label × Process)}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh Sown G (.branch k procs) Sfin Gfin W Δ →
    ∃ (e : Endpoint) (p : Role) (bs : List (Label × LocalType)),
      lookupSEnv (SEnvAll Ssh Sown) k = some (ValType.chan e.sid e.role) ∧
      lookupG G e = some (.branch p bs) := by
  intro h
  cases h with
  | branch hk hG hLen hLabels hBodies hOutLbl hDom => exact ⟨_, _, _, hk, hG⟩

private lemma updateG_full_eq_updateG_mid
    {Gfull Gleft Gmid Gright : GEnv} {e : Endpoint} {L L' : LocalType} {G' : GEnv} :
    Gfull = Gleft ++ Gmid ++ Gright →
    DisjointG Gleft Gmid →
    lookupG Gmid e = some L →
    G' = updateG Gfull e L' →
    G' = Gleft ++ updateG Gmid e L' ++ Gright := by
  intro hGfull hDisjL hG hGout
  have hNoneLeft : lookupG Gleft e = none :=
    DisjointG_lookup_left (G₁:=Gmid) (G₂:=Gleft) (DisjointG_symm hDisjL) hG
  have hLookupMid : lookupG (Gleft ++ Gmid) e = some L := by
    have hEq' := lookupG_append_right (G₁:=Gleft) (G₂:=Gmid) (e:=e) hNoneLeft
    simpa [hEq'] using hG
  have hUpdRight :=
    updateG_append_left_hit (G₁:=Gleft ++ Gmid) (G₂:=Gright) (e:=e) (L':=L') hLookupMid
  have hUpdLeft :=
    updateG_append_left (G₁:=Gleft) (G₂:=Gmid) (e:=e) (L:=L') hNoneLeft
  have hGout' : G' = updateG ((Gleft ++ Gmid) ++ Gright) e L' := by
    simpa [hGfull, List.append_assoc] using hGout
  calc
    G' = updateG ((Gleft ++ Gmid) ++ Gright) e L' := hGout'
    _ = updateG (Gleft ++ Gmid) e L' ++ Gright := hUpdRight
    _ = Gleft ++ updateG Gmid e L' ++ Gright := by
      simp [hUpdLeft, List.append_assoc]

private lemma TypedStep_preserves_frames_send
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfull Gleft Gmid Gright : GEnv}
    {store : VarStore}
    {k x : Var} {eStep : Endpoint} {Lstep : LocalType}
    {G' : GEnv} {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    (hGfull : Gfull = Gleft ++ Gmid ++ Gright) →
    (hDisjL : DisjointG Gleft Gmid) →
    (hStore : StoreTypedStrong Gfull (SEnvAll Ssh Sown) store) →
    (hOut : HasTypeProcPreOut Ssh Sown Gmid (.send k x) Sfin Gfin W Δ) →
    (hkStr : lookupStr store k = some (.chan eStep)) →
    (hGout : G' = updateG Gfull eStep Lstep) →
    ∃ Gmid', G' = Gleft ++ Gmid' ++ Gright := by
  intro hGfull hDisjL hStore hOut hkStr hGout
  rcases HasTypeProcPreOut_send_inv hOut with ⟨eOut, qOut, TOut, LOut, hk, hG⟩
  have hEq : eStep = eOut :=
    channel_endpoint_eq_of_store (hStore:=hStore) (k:=k) (e:=eOut) (e':=eStep) hk hkStr
  subst hEq
  refine ⟨updateG Gmid eStep Lstep, ?_⟩
  exact updateG_full_eq_updateG_mid hGfull hDisjL hG hGout

private lemma TypedStep_preserves_frames_recv
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfull Gleft Gmid Gright : GEnv}
    {store : VarStore}
    {k x : Var} {eStep : Endpoint} {Lstep : LocalType}
    {G' : GEnv} {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    (hGfull : Gfull = Gleft ++ Gmid ++ Gright) →
    (hDisjL : DisjointG Gleft Gmid) →
    (hStore : StoreTypedStrong Gfull (SEnvAll Ssh Sown) store) →
    (hOut : HasTypeProcPreOut Ssh Sown Gmid (.recv k x) Sfin Gfin W Δ) →
    (hkStr : lookupStr store k = some (.chan eStep)) →
    (hGout : G' = updateG Gfull eStep Lstep) →
    ∃ Gmid', G' = Gleft ++ Gmid' ++ Gright := by
  intro hGfull hDisjL hStore hOut hkStr hGout
  rcases HasTypeProcPreOut_recv_inv hOut with ⟨eOut, pOut, TOut, LOut, hk, hG⟩
  have hEq : eStep = eOut :=
    channel_endpoint_eq_of_store (hStore:=hStore) (k:=k) (e:=eOut) (e':=eStep) hk hkStr
  subst hEq
  refine ⟨updateG Gmid eStep Lstep, ?_⟩
  exact updateG_full_eq_updateG_mid hGfull hDisjL hG hGout

private lemma TypedStep_preserves_frames_select
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfull Gleft Gmid Gright : GEnv}
    {store : VarStore}
    {k : Var} {ℓ : Label} {eStep : Endpoint} {Lstep : LocalType}
    {G' : GEnv} {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    (hGfull : Gfull = Gleft ++ Gmid ++ Gright) →
    (hDisjL : DisjointG Gleft Gmid) →
    (hStore : StoreTypedStrong Gfull (SEnvAll Ssh Sown) store) →
    (hOut : HasTypeProcPreOut Ssh Sown Gmid (.select k ℓ) Sfin Gfin W Δ) →
    (hkStr : lookupStr store k = some (.chan eStep)) →
    (hGout : G' = updateG Gfull eStep Lstep) →
    ∃ Gmid', G' = Gleft ++ Gmid' ++ Gright := by
  intro hGfull hDisjL hStore hOut hkStr hGout
  rcases HasTypeProcPreOut_select_inv hOut with ⟨eOut, qOut, bsOut, hk, hG⟩
  have hEq : eStep = eOut :=
    channel_endpoint_eq_of_store (hStore:=hStore) (k:=k) (e:=eOut) (e':=eStep) hk hkStr
  subst hEq
  refine ⟨updateG Gmid eStep Lstep, ?_⟩
  exact updateG_full_eq_updateG_mid hGfull hDisjL hG hGout

private lemma TypedStep_preserves_frames_branch
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfull Gleft Gmid Gright : GEnv}
    {store : VarStore}
    {k : Var} {procs : List (Label × Process)} {eStep : Endpoint} {Lstep : LocalType}
    {G' : GEnv} {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    (hGfull : Gfull = Gleft ++ Gmid ++ Gright) →
    (hDisjL : DisjointG Gleft Gmid) →
    (hStore : StoreTypedStrong Gfull (SEnvAll Ssh Sown) store) →
    (hOut : HasTypeProcPreOut Ssh Sown Gmid (.branch k procs) Sfin Gfin W Δ) →
    (hkStr : lookupStr store k = some (.chan eStep)) →
    (hGout : G' = updateG Gfull eStep Lstep) →
    ∃ Gmid', G' = Gleft ++ Gmid' ++ Gright := by
  intro hGfull hDisjL hStore hOut hkStr hGout
  rcases HasTypeProcPreOut_branch_inv hOut with ⟨eOut, pOut, bsOut, hk, hG⟩
  have hEq : eStep = eOut :=
    channel_endpoint_eq_of_store (hStore:=hStore) (k:=k) (e:=eOut) (e':=eStep) hk hkStr
  subst hEq
  refine ⟨updateG Gmid eStep Lstep, ?_⟩
  exact updateG_full_eq_updateG_mid hGfull hDisjL hG hGout

-- Use HasTypeProcPreOut_frame_G_right/left from Protocol.Typing.Framing.

private lemma TypedStep_preserves_frames
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfull Gleft Gmid Gright : GEnv}
    {D : DEnv} {store : VarStore} {bufs : Buffers} {P : Process}
    {G' : GEnv} {D' : DEnv} {Sown' : OwnedEnv} {store' : VarStore} {bufs' : Buffers} {P' : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    Gfull = Gleft ++ Gmid ++ Gright →
    DisjointG Gleft Gmid →
    DisjointG Gleft Gright →
    DisjointG Gmid Gright →
    StoreTypedStrong Gfull (SEnvAll Ssh Sown) store →
    HasTypeProcPreOut Ssh Sown Gmid P Sfin Gfin W Δ →
    TypedStep Gfull D Ssh Sown store bufs P
      G' D' Sown' store' bufs' P' →
    ∃ Gmid', G' = Gleft ++ Gmid' ++ Gright := by
  intro hGfull hDisjL hDisjLR hDisjR hStore hOut hStep
  induction hStep generalizing Gleft Gmid Gright Sfin Gfin W Δ with
  | send =>
      rename_i Gfull D Ssh Sown store bufs k x eStep target Tstep Lstep v sendEdge G' D' bufs'
        hkStr hxStr hGStep hS hv hRecvReady hEdge hGout hDout hBufsOut
      exact TypedStep_preserves_frames_send (hGfull:=hGfull) (hDisjL:=hDisjL)
        (hStore:=hStore) (hOut:=hOut) hkStr hGout
  | recv =>
      rename_i Gfull D Ssh Sown store bufs k x eStep source Tstep Lstep v vs recvEdge G' D' Sown' store' bufs'
        hkStr hGStep hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut
      exact TypedStep_preserves_frames_recv (hGfull:=hGfull) (hDisjL:=hDisjL)
        (hStore:=hStore) (hOut:=hOut) hkStr hGout
  | select =>
      rename_i Gfull D Ssh Sown store bufs k ℓ eStep target bsStep Lstep selectEdge G' D' bufs'
        hkStr hGStep hFind hTargetReady hEdge hGout hDout hBufsOut
      exact TypedStep_preserves_frames_select (hGfull:=hGfull) (hDisjL:=hDisjL)
        (hStore:=hStore) (hOut:=hOut) hkStr hGout
  | branch =>
      rename_i Gfull D Ssh Sown store bufs k procs eStep source bsStep ℓ P Lstep vs branchEdge G' D' bufs'
        hkStr hGStep hEdge hBuf hFindP hFindBs hTrace hGout hDout hBufsOut
      exact TypedStep_preserves_frames_branch (hGfull:=hGfull) (hDisjL:=hDisjL)
        (hStore:=hStore) (hOut:=hOut) hkStr hGout
  | assign =>
      rename_i Gfull D Ssh Sown store bufs x v T S' store' hv hSout hStoreOut
      cases hOut <;> refine ⟨Gmid, ?_⟩ <;> simpa [List.append_assoc, hGfull]
  | seq_step =>
      rename_i Gfull D Ssh Sown G' D' Sown' store bufs store' bufs' P P' Q hStepP ih
      cases hOut with
      | seq hP hQ =>
          exact ih hGfull hDisjL hDisjLR hDisjR hStore hP
  | seq_skip =>
      rename_i Gfull D Ssh Sown store bufs Q
      cases hOut with
      | seq hP hQ =>
          refine ⟨Gmid, ?_⟩
          simpa [List.append_assoc, hGfull]
  | par_left splitFull hSlen' hGlen' hStepP hDisjGfull hDisjD hDisjSfull ih =>
      rename_i Ssh Sown store bufs store' bufs' P P' Q Gfull D₁ D₂ G₁' D₁' S₁' nS nG
      cases hOut with
      | par split hSlen hGlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
          hDisjW hDisjΔ hS1 hS2 hP hQ =>
          rename_i S1out S2out S1out' S2out' G1out G2out W1out W2out Δ1out Δ2out
          have hSeq : splitFull.S1 ++ splitFull.S2 = split.S1 ++ split.S2 := by
            rw [← splitFull.hS, ← split.hS]
          have hSlenEq : splitFull.S1.length = split.S1.length :=
            hSlen'.trans hSlen.symm
          have hS1Eq : splitFull.S1 = split.S1 := List.append_inj_left hSeq hSlenEq
          have hS2Eq : splitFull.S2 = split.S2 := List.append_inj_right hSeq hSlenEq
          have hStoreBase :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll (Ssh ++ Sown.right) ((split.S1 ++ split.S2) ++ (∅ : SEnv))) store := by
            simpa [hGfull, SEnvAll, split.hS, List.append_assoc] using hStore
          have hStoreSwap :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll (Ssh ++ Sown.right) (split.S2 ++ (split.S1 ++ (∅ : SEnv)))) store :=
            StoreTypedStrong_swap_S_left_prefix (Ssh:=Ssh ++ Sown.right)
              (S₁:=split.S1) (S₂:=split.S2) (S₃:=∅) hDisjS
              (by simpa [List.append_assoc] using hStoreBase)
          have hStoreL :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store := by
            simpa [SEnvAll, List.append_assoc] using hStoreSwap
          have hStoreR :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store := by
            simpa [hGfull, SEnvAll, split.hS, List.append_assoc] using hStore
          have hSubG1 : SessionsOf split.G1 ⊆ SessionsOf Gmid := by
            intro s hs
            simpa [split.hG] using SessionsOf_append_left (G₂:=split.G2) hs
          have hSubG2 : SessionsOf split.G2 ⊆ SessionsOf Gmid := by
            intro s hs
            simpa [split.hG] using SessionsOf_append_right (G₁:=split.G1) hs
          have hDisjGleftG1 : DisjointG Gleft split.G1 := by
            have hSym : DisjointG Gmid Gleft := DisjointG_symm hDisjL
            have hTmp : DisjointG split.G1 Gleft := DisjointG_of_subset_left hSubG1 hSym
            exact DisjointG_symm hTmp
          have hDisjGleftG2 : DisjointG Gleft split.G2 := by
            have hSym : DisjointG Gmid Gleft := DisjointG_symm hDisjL
            have hTmp : DisjointG split.G2 Gleft := DisjointG_of_subset_left hSubG2 hSym
            exact DisjointG_symm hTmp
          have hDisjG1Right : DisjointG split.G1 Gright :=
            DisjointG_of_subset_left hSubG1 hDisjR
          have hDisjG2Right : DisjointG split.G2 Gright :=
            DisjointG_of_subset_left hSubG2 hDisjR
          have hDisjLeftRight : DisjointG Gleft (split.G2 ++ Gright) := by
            have hLeft : DisjointG split.G2 Gleft := DisjointG_symm hDisjGleftG2
            have hRight : DisjointG Gright Gleft := DisjointG_symm hDisjLR
            have hCombined : DisjointG (split.G2 ++ Gright) Gleft :=
              DisjointG_append_left hLeft hRight
            exact DisjointG_symm hCombined
          have hDisjMidRight : DisjointG split.G1 (split.G2 ++ Gright) := by
            have hLeft : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
            have hRight : DisjointG Gright split.G1 := DisjointG_symm hDisjG1Right
            have hTmp : DisjointG (split.G2 ++ Gright) split.G1 :=
              DisjointG_append_left hLeft hRight
            exact DisjointG_symm hTmp
          have hGfull' : Gfull = Gleft ++ split.G1 ++ (split.G2 ++ Gright) := by
            calc
              Gfull = Gleft ++ Gmid ++ Gright := hGfull
              _ = Gleft ++ (split.G1 ++ split.G2) ++ Gright := by
                simpa [split.hG]
              _ = Gleft ++ split.G1 ++ (split.G2 ++ Gright) := by
                simp [List.append_assoc]
          have hStoreL' :
              StoreTypedStrong (Gleft ++ split.G1 ++ (split.G2 ++ Gright))
                (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store := by
            simpa [split.hG, List.append_assoc] using hStoreL
          have hStoreL'' :
              StoreTypedStrong Gfull
                (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store := by
            simpa [hGfull'] using hStoreL'
          have hStoreL''' :
              StoreTypedStrong Gfull
                (SEnvAll Ssh { right := Sown.right ++ splitFull.S2, left := splitFull.S1 }) store := by
            simpa [hS1Eq, hS2Eq] using hStoreL''
          have hP' :
              HasTypeProcPreOut Ssh { right := Sown.right ++ splitFull.S2, left := splitFull.S1 } split.G1 P
                { right := Sown.right ++ splitFull.S2, left := S1out' } G1out W1out Δ1out := by
            simpa [hS1, hS2, hS1Eq, hS2Eq] using hP
          have hStepP' :
              TypedStep (Gleft ++ split.G1 ++ (split.G2 ++ Gright))
                (D₁ ++ D₂) Ssh { right := Sown.right ++ split.S2, left := split.S1 }
                store bufs P
                (G₁' ++ splitFull.G2) (D₁' ++ D₂)
                { right := Sown.right ++ split.S2, left := S₁' } store' bufs' P' := by
            simpa [hGfull', hS1Eq, hS2Eq, split.hG, List.append_assoc] using hStepP
          have hStepP'' :
              TypedStep Gfull (D₁ ++ D₂) Ssh { right := Sown.right ++ split.S2, left := split.S1 }
                store bufs P
                (G₁' ++ splitFull.G2) (D₁' ++ D₂)
                { right := Sown.right ++ split.S2, left := S₁' } store' bufs' P' := by
            simpa [hGfull'] using hStepP'
          rcases ih hGfull' hDisjGleftG1 hDisjLeftRight hDisjMidRight hStoreL''' hP' with
            ⟨Gmid', hShape⟩
          refine ⟨Gmid' ++ split.G2, ?_⟩
          simp [hShape, List.append_assoc]
  | par_right splitFull hSlen' hGlen' hStepQ hDisjGfull hDisjD hDisjSfull ih =>
      rename_i Ssh Sown store bufs store' bufs' P Q Q' Gfull D₁ D₂ G₂' D₂' S₂' nS nG
      cases hOut with
      | par split hSlen hGlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
          hDisjW hDisjΔ hS1 hS2 hP hQ =>
          rename_i S1out S2out S1out' S2out' G1out G2out W1out W2out Δ1out Δ2out
          have hSeq : splitFull.S1 ++ splitFull.S2 = split.S1 ++ split.S2 := by
            rw [← splitFull.hS, ← split.hS]
          have hSlenEq : splitFull.S1.length = split.S1.length :=
            hSlen'.trans hSlen.symm
          have hS1Eq : splitFull.S1 = split.S1 := List.append_inj_left hSeq hSlenEq
          have hS2Eq : splitFull.S2 = split.S2 := List.append_inj_right hSeq hSlenEq
          have hStoreBase :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll (Ssh ++ Sown.right) ((split.S1 ++ split.S2) ++ (∅ : SEnv))) store := by
            simpa [hGfull, SEnvAll, split.hS, List.append_assoc] using hStore
          have hStoreSwap :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll (Ssh ++ Sown.right) (split.S2 ++ (split.S1 ++ (∅ : SEnv)))) store :=
            StoreTypedStrong_swap_S_left_prefix (Ssh:=Ssh ++ Sown.right)
              (S₁:=split.S1) (S₂:=split.S2) (S₃:=∅) hDisjS
              (by simpa [List.append_assoc] using hStoreBase)
          have hStoreL :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store := by
            simpa [SEnvAll, List.append_assoc] using hStoreSwap
          have hStoreR :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store := by
            simpa [hGfull, SEnvAll, split.hS, List.append_assoc] using hStore
          have hSubG1 : SessionsOf split.G1 ⊆ SessionsOf Gmid := by
            intro s hs
            simpa [split.hG] using SessionsOf_append_left (G₂:=split.G2) hs
          have hSubG2 : SessionsOf split.G2 ⊆ SessionsOf Gmid := by
            intro s hs
            simpa [split.hG] using SessionsOf_append_right (G₁:=split.G1) hs
          have hDisjGleftG1 : DisjointG Gleft split.G1 := by
            have hSym : DisjointG Gmid Gleft := DisjointG_symm hDisjL
            have hTmp : DisjointG split.G1 Gleft := DisjointG_of_subset_left hSubG1 hSym
            exact DisjointG_symm hTmp
          have hDisjGleftG2 : DisjointG Gleft split.G2 := by
            have hSym : DisjointG Gmid Gleft := DisjointG_symm hDisjL
            have hTmp : DisjointG split.G2 Gleft := DisjointG_of_subset_left hSubG2 hSym
            exact DisjointG_symm hTmp
          have hDisjG1Right : DisjointG split.G1 Gright :=
            DisjointG_of_subset_left hSubG1 hDisjR
          have hDisjG2Right : DisjointG split.G2 Gright :=
            DisjointG_of_subset_left hSubG2 hDisjR
          have hDisjLeftMid : DisjointG (Gleft ++ split.G1) split.G2 :=
            DisjointG_append_left hDisjGleftG2 hDisjG
          have hDisjLeftRight : DisjointG (Gleft ++ split.G1) Gright :=
            DisjointG_append_left hDisjLR hDisjG1Right
          have hGfull' : Gfull = (Gleft ++ split.G1) ++ split.G2 ++ Gright := by
            calc
              Gfull = Gleft ++ Gmid ++ Gright := hGfull
              _ = Gleft ++ (split.G1 ++ split.G2) ++ Gright := by
                simpa [split.hG]
              _ = (Gleft ++ split.G1) ++ split.G2 ++ Gright := by
                simp [List.append_assoc]
          have hStoreR' :
              StoreTypedStrong ((Gleft ++ split.G1) ++ split.G2 ++ Gright)
                (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store := by
            simpa [split.hG, List.append_assoc] using hStoreR
          have hStoreR'' :
              StoreTypedStrong Gfull
                (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store := by
            simpa [hGfull'] using hStoreR'
          have hStoreR''' :
              StoreTypedStrong Gfull
                (SEnvAll Ssh { right := Sown.right ++ splitFull.S1, left := splitFull.S2 }) store := by
            simpa [hS1Eq, hS2Eq] using hStoreR''
          have hQ' :
              HasTypeProcPreOut Ssh { right := Sown.right ++ splitFull.S1, left := splitFull.S2 } split.G2 Q
                { right := Sown.right ++ splitFull.S1, left := S2out' } G2out W2out Δ2out := by
            simpa [hS1, hS2, hS1Eq, hS2Eq] using hQ
          have hStepQ' :
              TypedStep ((Gleft ++ split.G1) ++ split.G2 ++ Gright)
                (D₁ ++ D₂) Ssh { right := Sown.right ++ split.S1, left := split.S2 }
                store bufs Q
                (splitFull.G1 ++ G₂') (D₁ ++ D₂')
                { right := Sown.right ++ split.S1, left := S₂' } store' bufs' Q' := by
            simpa [hGfull', hS1Eq, hS2Eq, split.hG, List.append_assoc] using hStepQ
          have hStepQ'' :
              TypedStep Gfull (D₁ ++ D₂) Ssh { right := Sown.right ++ split.S1, left := split.S2 }
                store bufs Q
                (splitFull.G1 ++ G₂') (D₁ ++ D₂')
                { right := Sown.right ++ split.S1, left := S₂' } store' bufs' Q' := by
            simpa [hGfull'] using hStepQ'
          rcases ih hGfull' hDisjLeftMid hDisjLeftRight hDisjG2Right hStoreR''' hQ' with
            ⟨Gmid', hShape⟩
          refine ⟨split.G1 ++ Gmid', ?_⟩
          simp [hShape, List.append_assoc]
  | par_skip_left =>
      rename_i Gfull D Ssh Sown store bufs Q nS nG
      cases hOut with
      | par _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          refine ⟨Gmid, ?_⟩
          simpa [List.append_assoc] using hGfull
  | par_skip_right =>
      rename_i Gfull D Ssh Sown store bufs P nS nG
      cases hOut with
      | par _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          refine ⟨Gmid, ?_⟩
          simpa [List.append_assoc] using hGfull

private lemma progress_send
    {G D Ssh Sown store bufs k x Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G (.send k x) Sfin Gfin W Δ →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    SendReady G D →
    ∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs (.send k x)
      G' D' Sown' store' bufs' P' := by
  intro hOut hStore hReady
  cases hOut with
  | send hk hG hx =>
      rename_i e q T L
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      obtain ⟨v, hxStr, hv⟩ := store_lookup_of_senv_lookup hStore hx
      have hRecvReady := hReady e q T L hG
      exact ⟨_, _, _, _, _, _, TypedStep.send hkStr hxStr hG hx hv hRecvReady rfl rfl rfl rfl⟩

private lemma progress_recv
    {G D Ssh Sown store bufs k x Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G (.recv k x) Sfin Gfin W Δ →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    BuffersTyped G D bufs →
    HeadCoherent G D →
    RoleComplete G →
    (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs (.recv k x)
      G' D' Sown' store' bufs' P') ∨
    BlockedProc store bufs (.recv k x) := by
  intro hOut hStore hBufs hHead hComplete
  cases hOut with
  | recv_new hk hG hNoSh hNoOwnR hNoOwnL =>
      rename_i e p T L
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      set recvEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
      have hActiveRecv : ActiveEdge G recvEdge := by
        have hGrecv : lookupG G { sid := recvEdge.sid, role := recvEdge.receiver } = some (.recv p T L) := by
          simpa [recvEdge] using hG
        rcases RoleComplete_recv hComplete hG with ⟨Lsender, hGsender⟩
        exact ActiveEdge_of_endpoints (e:=recvEdge) hGsender hGrecv
      cases hBuf : lookupBuf bufs recvEdge with
      | nil =>
          right
          refine ⟨e, p, hkStr, ?_⟩
          simpa [recvEdge, hBuf]
      | cons v vs =>
          left
          have hTypedEdge := hBufs recvEdge
          rcases hTypedEdge with ⟨hLen, hTyping⟩
          have h0buf : 0 < (lookupBuf bufs recvEdge).length := by
            simp [hBuf]
          have h0trace : 0 < (lookupD D recvEdge).length := by
            simpa [hLen] using h0buf
          have hTyped0 := hTyping 0 h0buf
          have hv' := by
            simpa [hBuf] using hTyped0
          cases hTrace : lookupD D recvEdge with
          | nil =>
              simp [hTrace] at h0trace
          | cons T' ts =>
              have hHeadEdge := hHead recvEdge hActiveRecv
              have hEq : T = T' := by
                simpa [HeadCoherent, hG, recvEdge, hTrace] using hHeadEdge
              have hEq' : T' = T := by
                simpa using hEq.symm
              have hv : HasTypeVal G v T := by
                simpa [hTrace, hEq'] using hv'
              have hTraceHead : (lookupD D recvEdge).head? = some T := by
                simp [hTrace, hEq]
              exact ⟨_, _, _, _, _, _, TypedStep.recv hkStr hG rfl hBuf hv hTraceHead rfl rfl rfl rfl rfl⟩
  | recv_old hk hG hNoSh hNoOwnR hOwn =>
      rename_i e p T L T'
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      set recvEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
      have hActiveRecv : ActiveEdge G recvEdge := by
        have hGrecv : lookupG G { sid := recvEdge.sid, role := recvEdge.receiver } = some (.recv p T L) := by
          simpa [recvEdge] using hG
        rcases RoleComplete_recv hComplete hG with ⟨Lsender, hGsender⟩
        exact ActiveEdge_of_endpoints (e:=recvEdge) hGsender hGrecv
      cases hBuf : lookupBuf bufs recvEdge with
      | nil =>
          right
          refine ⟨e, p, hkStr, ?_⟩
          simpa [recvEdge, hBuf]
      | cons v vs =>
          left
          have hTypedEdge := hBufs recvEdge
          rcases hTypedEdge with ⟨hLen, hTyping⟩
          have h0buf : 0 < (lookupBuf bufs recvEdge).length := by
            simp [hBuf]
          have h0trace : 0 < (lookupD D recvEdge).length := by
            simpa [hLen] using h0buf
          have hTyped0 := hTyping 0 h0buf
          have hv' := by
            simpa [hBuf] using hTyped0
          cases hTrace : lookupD D recvEdge with
          | nil =>
              simp [hTrace] at h0trace
          | cons T' ts =>
              have hHeadEdge := hHead recvEdge hActiveRecv
              have hEq : T = T' := by
                simpa [HeadCoherent, hG, recvEdge, hTrace] using hHeadEdge
              have hEq' : T' = T := by
                simpa using hEq.symm
              have hv : HasTypeVal G v T := by
                simpa [hTrace, hEq'] using hv'
              have hTraceHead : (lookupD D recvEdge).head? = some T := by
                simp [hTrace, hEq]
              exact ⟨_, _, _, _, _, _, TypedStep.recv hkStr hG rfl hBuf hv hTraceHead rfl rfl rfl rfl rfl⟩

private lemma progress_select
    {G D Ssh Sown store bufs k ℓ Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G (.select k ℓ) Sfin Gfin W Δ →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    SelectReady G D →
    ∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs (.select k ℓ)
      G' D' Sown' store' bufs' P' := by
  intro hOut hStore hSelectReady
  cases hOut with
  | select hk hG hbs =>
      rename_i e q bs L
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      have hTargetReady := hSelectReady e q bs ℓ L hG hbs
      exact ⟨_, _, _, _, _, _, TypedStep.select hkStr hG hbs hTargetReady rfl rfl rfl rfl⟩

private lemma progress_branch
    {G D Ssh Sown store bufs k procs Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G (.branch k procs) Sfin Gfin W Δ →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    BuffersTyped G D bufs →
    HeadCoherent G D →
    ValidLabels G D bufs →
    RoleComplete G →
    (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs (.branch k procs)
      G' D' Sown' store' bufs' P') ∨
    BlockedProc store bufs (.branch k procs) := by
  intro hOut hStore hBufs hHead hValid hComplete
  cases hOut with
  | branch hk hG hLen hLabels hBodies hOutLbl hDom =>
      rename_i e p bs
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      set branchEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
      have hActiveBranch : ActiveEdge G branchEdge := by
        have hGrecv : lookupG G { sid := branchEdge.sid, role := branchEdge.receiver } =
            some (.branch p bs) := by
          simpa [branchEdge] using hG
        rcases RoleComplete_branch hComplete hG with ⟨Lsender, hGsender⟩
        exact ActiveEdge_of_endpoints (e:=branchEdge) hGsender hGrecv
      cases hBuf : lookupBuf bufs branchEdge with
      | nil =>
          right
          refine ⟨e, p, hkStr, ?_⟩
          simpa [branchEdge, hBuf]
      | cons v vs =>
          left
          have hTypedEdge := hBufs branchEdge
          rcases hTypedEdge with ⟨hLenBuf, hTyping⟩
          have h0buf : 0 < (lookupBuf bufs branchEdge).length := by
            simp [hBuf]
          have h0trace : 0 < (lookupD D branchEdge).length := by
            simpa [hLenBuf] using h0buf
          have hTyped0 := hTyping 0 h0buf
          have hv' := by
            simpa [hBuf] using hTyped0
          cases hTrace : lookupD D branchEdge with
          | nil =>
              simp [hTrace] at h0trace
          | cons T' ts =>
              have hHeadEdge := hHead branchEdge hActiveBranch
              have hEq : T' = .string := by
                simpa [HeadCoherent, hG, branchEdge, hTrace] using hHeadEdge
              have hv := by
                simpa [hTrace, hEq] using hv'
              cases hv with
              | string lbl =>
                  have hValidEdge := hValid branchEdge p bs hActiveBranch
                    (by simpa [branchEdge] using hG)
                  have hBsSome : (bs.find? (fun b => b.1 == lbl)).isSome := by
                    simpa [hBuf] using hValidEdge
                  rcases (Option.isSome_iff_exists).1 hBsSome with ⟨b, hFindBs⟩
                  cases b with
                  | mk lbl' L =>
                      have hLbl : lbl' = lbl :=
                        findLabel_eq (xs := bs) (lbl := lbl) (lbl' := lbl') (v := L) hFindBs
                      subst lbl'
                      have hMemBs : (lbl, L) ∈ bs := List.mem_of_find?_eq_some hFindBs
                      rcases (List.mem_iff_getElem).1 hMemBs with ⟨i, hi, hGetBs⟩
                      have hip : i < procs.length := by
                        simpa [hLen] using hi
                      have hLabelAt : (procs.get ⟨i, hip⟩).1 = lbl := by
                        have hLblEq := hLabels i hi hip
                        simpa [hGetBs] using hLblEq
                      have hPred : (fun b => b.1 == lbl) (procs.get ⟨i, hip⟩) := by
                        exact (beq_iff_eq).2 hLabelAt
                      have hFindPIsSome : (procs.find? (fun b => b.1 == lbl)).isSome := by
                        cases hFindP : procs.find? (fun b => b.1 == lbl) with
                        | none =>
                            have hNo : ∀ x ∈ procs, ¬ (fun b => b.1 == lbl) x := by
                              simpa [List.find?_eq_none] using hFindP
                            have hMemP : procs.get ⟨i, hip⟩ ∈ procs := List.get_mem procs ⟨i, hip⟩
                            have hContra : False := (hNo _ hMemP) hPred
                            simpa using hContra
                        | some b =>
                            simp
                      rcases (Option.isSome_iff_exists).1 hFindPIsSome with ⟨bP, hFindP⟩
                      cases bP with
                      | mk lblP P =>
                          have hLblP : lblP = lbl :=
                            findLabel_eq (xs := procs) (lbl := lbl) (lbl' := lblP) (v := P) hFindP
                          subst hLblP
                          have hTraceHead : (lookupD D branchEdge).head? = some .string := by
                            simp [hTrace, hEq]
                          exact ⟨_, _, _, _, _, _, TypedStep.branch hkStr hG rfl hBuf hFindP hFindBs hTraceHead rfl rfl rfl⟩

private lemma progress_assign
    {G D Ssh Sown store bufs x v Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G (.assign x v) Sfin Gfin W Δ →
    ∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs (.assign x v)
      G' D' Sown' store' bufs' P' := by
  intro hOut
  cases hOut with
  | assign_new hNoSh hNoOwnR hNoOwnL hv =>
      exact ⟨_, _, _, _, _, _, TypedStep.assign hv rfl rfl⟩
  | assign_old hNoSh hNoOwnR hOwn hv =>
      exact ⟨_, _, _, _, _, _, TypedStep.assign hv rfl rfl⟩

private theorem progress_typed_aux {G D Ssh Sown store bufs P Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    BuffersTyped G D bufs →
    Coherent G D →
    HeadCoherent G D →
    ValidLabels G D bufs →
    RoleComplete G →
    SendReady G D →
    SelectReady G D →
    DConsistent G D →
    (P = .skip) ∨
      (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
        G' D' Sown' store' bufs' P') ∨
      BlockedProc store bufs P := by
  intro hOut hStore hBufs hCoh hHead hValid hComplete hReady hSelectReady hCons
  cases P with
  | skip =>
      left; rfl
  | send k x =>
      right; left
      exact progress_send hOut hStore hReady
  | recv k x =>
      have hProg := progress_recv hOut hStore hBufs hHead hComplete
      cases hProg with
      | inl hStep =>
          right; left; exact hStep
      | inr hBlocked =>
          right; right; exact hBlocked
  | select k ℓ =>
      right; left
      exact progress_select hOut hStore hSelectReady
  | branch k procs =>
      have hProg := progress_branch hOut hStore hBufs hHead hValid hComplete
      cases hProg with
      | inl hStep =>
          right; left; exact hStep
      | inr hBlocked =>
          right; right; exact hBlocked
  | seq P Q =>
      cases hOut with
      | seq hP hQ =>
          have hProgP :=
            progress_typed_aux hP hStore hBufs hCoh hHead hValid hComplete hReady hSelectReady hCons
          cases hProgP with
          | inl hSkip =>
              right; left
              subst hSkip
              exact ⟨_, _, _, store, bufs, Q, TypedStep.seq_skip⟩
          | inr hRest =>
              cases hRest with
              | inl hStep =>
                  rcases hStep with ⟨G', D', S', store', bufs', P', hStep⟩
                  right; left
                  exact ⟨_, _, _, _, _, _, TypedStep.seq_step hStep⟩
              | inr hBlocked =>
                  right; right
                  simpa [BlockedProc] using hBlocked
  | par nS nG P Q =>
      cases hOut with
      | par split hSlen hGlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
          hDisjW hDisjΔ hS1 hS2 hP hQ =>
          cases hS1
          cases hS2
          -- Store typing for left and right processes.
          have hStoreBase :
              StoreTypedStrong G (SEnvAll (Ssh ++ Sown.right) ((split.S1 ++ split.S2) ++ (∅ : SEnv))) store := by
            simpa [SEnvAll, split.hS, List.append_assoc] using hStore
          have hStoreSwap :
              StoreTypedStrong G (SEnvAll (Ssh ++ Sown.right) (split.S2 ++ (split.S1 ++ (∅ : SEnv)))) store :=
            StoreTypedStrong_swap_S_left_prefix (Ssh:=Ssh ++ Sown.right)
              (S₁:=split.S1) (S₂:=split.S2) (S₃:=∅) hDisjS
              (by simpa [List.append_assoc] using hStoreBase)
          have hStoreL :
              StoreTypedStrong G (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store := by
            simpa [SEnvAll, List.append_assoc] using hStoreSwap
          have hStoreR :
              StoreTypedStrong G (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store := by
            simpa [SEnvAll, split.hS, List.append_assoc] using hStore

          -- Frame pre-out typing to full G.
          have hP_full :=
            HasTypeProcPreOut_frame_G_right (Ssh:=Ssh)
              (Sown:={ right := Sown.right ++ split.S2, left := split.S1 })
              (G:=split.G1) (Gfr:=split.G2) hDisjG hP
          have hQ_full :=
            HasTypeProcPreOut_frame_G_left (Ssh:=Ssh)
              (Sown:={ right := Sown.right ++ split.S1, left := split.S2 })
              (Gfr:=split.G1) (G:=split.G2) hDisjG hQ
          simp only [← split.hG] at hP_full hQ_full

          -- Progress on left process.
          have hProgP :=
            progress_typed_aux hP_full hStoreL hBufs hCoh hHead hValid hComplete hReady hSelectReady hCons
          cases hProgP with
          | inl hSkipP =>
              right; left
              subst hSkipP
              exact ⟨_, _, _, store, bufs, Q, TypedStep.par_skip_left⟩
          | inr hRestP =>
              cases hRestP with
              | inl hStepP =>
                  rcases hStepP with ⟨G', D', S', store', bufs', P', hStep⟩
                  -- TODO: derive shape G' = G₁' ++ split.G2 from hStep.
                  have hGshape : ∃ G₁', G' = G₁' ++ split.G2 := by
                    have hShape :=
                      TypedStep_preserves_frames (Gleft:=[]) (Gmid:=split.G1) (Gright:=split.G2)
                        (by simpa [split.hG])
                        (DisjointG_left_empty split.G1) (DisjointG_left_empty split.G2) hDisjG
                        hStoreL hP hStep
                    rcases hShape with ⟨G₁', hShape⟩
                    refine ⟨G₁', ?_⟩
                    simpa [List.append_assoc] using hShape
                  rcases hGshape with ⟨G₁', hGshape⟩
                  have hRightEq : S'.right = Sown.right ++ split.S2 :=
                    TypedStep_preserves_right hStep
                  have hStep' :
                      TypedStep G (D ++ (∅ : DEnv)) Ssh { right := Sown.right ++ split.S2, left := split.S1 }
                        store bufs P
                        (G₁' ++ split.G2) (D' ++ (∅ : DEnv))
                        { right := Sown.right ++ split.S2, left := S'.left }
                        store' bufs' P' := by
                    cases hGshape
                    cases S' with
                    | mk right left =>
                        have hRightEq' : right = Sown.right ++ split.S2 := by
                          simpa using hRightEq
                        cases hRightEq'
                        simpa [DEnv_append_empty_right] using hStep
                  right; left
                  refine ⟨G₁' ++ split.G2, D' ++ (∅ : DEnv),
                      { right := Sown.right, left := S'.left ++ split.S2 },
                      store', bufs', .par S'.left.length G₁'.length P' Q, ?_⟩
                  simpa [List.append_assoc, DEnv_append_empty_right] using
                    (TypedStep.par_left (split:=split) (D₁:=D) (D₂:=∅) (G₁':=G₁') (D₁':=D') (S₁':=S'.left)
                      (P:=P) (Q:=Q)
                      hSlen hGlen hStep' hDisjG (DisjointD_right_empty D) hDisjS)
              | inr hBlockedP =>
                  -- Progress on right process.
                  have hProgQ :=
                    progress_typed_aux hQ_full hStoreR hBufs hCoh hHead hValid hComplete hReady hSelectReady hCons
                  cases hProgQ with
                  | inl hSkipQ =>
                      right; left
                      subst hSkipQ
                      exact ⟨_, _, _, store, bufs, P, TypedStep.par_skip_right⟩
                  | inr hRestQ =>
                      cases hRestQ with
                      | inl hStepQ =>
                          rcases hStepQ with ⟨G', D', S', store', bufs', Q', hStep⟩
                          -- TODO: derive shape G' = split.G1 ++ G₂' from hStep.
                          have hGshape : ∃ G₂', G' = split.G1 ++ G₂' := by
                            have hShape :=
                              TypedStep_preserves_frames (Gleft:=split.G1) (Gmid:=split.G2) (Gright:=[])
                                (by simpa [split.hG])
                                hDisjG (DisjointG_right_empty split.G1) (DisjointG_right_empty split.G2)
                                hStoreR hQ hStep
                            rcases hShape with ⟨G₂', hShape⟩
                            refine ⟨G₂', ?_⟩
                            simpa [List.append_assoc] using hShape
                          rcases hGshape with ⟨G₂', hGshape⟩
                          have hRightEq : S'.right = Sown.right ++ split.S1 :=
                            TypedStep_preserves_right hStep
                          have hStep' :
                              TypedStep G ((∅ : DEnv) ++ D) Ssh { right := Sown.right ++ split.S1, left := split.S2 }
                                store bufs Q
                                (split.G1 ++ G₂') ((∅ : DEnv) ++ D')
                                { right := Sown.right ++ split.S1, left := S'.left }
                                store' bufs' Q' := by
                            cases hGshape
                            cases S' with
                            | mk right left =>
                                have hRightEq' : right = Sown.right ++ split.S1 := by
                                  simpa using hRightEq
                                cases hRightEq'
                                simpa [DEnv_append_empty_left] using hStep
                          right; left
                          refine ⟨split.G1 ++ G₂', (∅ : DEnv) ++ D',
                              { right := Sown.right, left := split.S1 ++ S'.left },
                              store', bufs', .par split.S1.length split.G1.length P Q', ?_⟩
                          simpa [List.append_assoc, DEnv_append_empty_left] using
                            (TypedStep.par_right (split:=split) (D₁:=∅) (D₂:=D) (G₂':=G₂') (D₂':=D') (S₂':=S'.left)
                              (P:=P) (Q:=Q)
                              hSlen hGlen hStep' hDisjG (DisjointD_left_empty D) hDisjS)
                      | inr hBlockedQ =>
                          right; right
                          exact And.intro (by simpa using hBlockedP) (by simpa using hBlockedQ)
  | newSession roles f P =>
      cases hOut
  | assign x v =>
      right; left
      exact progress_assign hOut

/-- Progress theorem: A complete well-formed process can either step or is in a final/blocked state.

    **Proof strategy**: Case analysis on process P:
    - `skip`: Terminates
    - `send k x`: Derive TypedStep.send from lookupG via HasTypeProcPre inversion
    - `recv k x`: Check buffer - if non-empty, derive TypedStep.recv; else blocked
    - `seq P Q`: Use IH on P or skip elimination
    - `par P Q`: Use IH on P or Q or skip elimination -/
theorem progress_typed {G D Ssh Sown store bufs P} :
    WellFormedComplete G D Ssh Sown store bufs P →
    (P = .skip) ∨
    (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
      G' D' Sown' store' bufs' P') ∨
    BlockedProc store bufs P := by
  intro hWF
  rcases hWF with ⟨hWF, hComplete⟩
  unfold LocalTypeR.WellFormed at hWF
  obtain ⟨hStore, hBufs, hCoh, hHead, hValid, hCompat, hDisjS, hCons, hDCons, hPreOut⟩ := hWF
  obtain ⟨Sfin, Gfin, Wfin, Δfin, hOut⟩ := hPreOut
  have hReady : SendReady G D := Compatible_to_SendReady hCompat
  have hSelectReady : SelectReady G D := Compatible_to_SelectReady hCompat
  exact progress_typed_aux hOut hStore hBufs hCoh hHead hValid hComplete hReady hSelectReady hDCons

/-! ### Convenience Wrapper -/

/-- Progress with explicit RoleComplete (keeps the old WellFormed ergonomics). -/
theorem progress_typed_with_rolecomplete {G D Ssh Sown store bufs P} :
    LocalTypeR.WellFormed G D Ssh Sown store bufs P →
    RoleComplete G →
    (P = .skip) ∨
    (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
      G' D' Sown' store' bufs' P') ∨
    BlockedProc store bufs P := by
  intro hWF hComplete
  exact progress_typed (G:=G) (D:=D) (Ssh:=Ssh) (Sown:=Sown) (store:=store) (bufs:=bufs) (P:=P)
    ⟨hWF, hComplete⟩

/-  Subject reduction (soundness) theorem moved to Protocol.Preservation
    to avoid circular dependency (Step is defined in Semantics which imports Typing).

    **Theorem**: TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
                 Step ⟨P, store, bufs, G, D, n⟩ ⟨P', store', bufs', G', D', n⟩

    This will be proven in Preservation.lean after TypedStep is available. -/

end
