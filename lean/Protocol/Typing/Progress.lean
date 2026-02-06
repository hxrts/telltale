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
  cases hStep <;> simp [OwnedEnv.updateLeft]

private lemma channel_endpoint_eq_of_store
    {G : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore}
    {k : Var} {e e' : Endpoint} :
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e.sid e.role) →
    lookupStr store k = some (.chan e') →
    e' = e := by
  intro hStore hk hkStr
  obtain ⟨vk, hkStr', hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
  have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
  have hkStr'' : lookupStr store k = some (.chan e) := by
    simpa [hkChan] using hkStr'
  have hEqOpt : some (.chan e') = some (.chan e) := by
    simpa [hkStr] using hkStr''
  have hEq : (.chan e') = (.chan e) := Option.some.inj hEqOpt
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
      simpa [hA, hB, hLeft] using rfl
  | none =>
      have hLeft' : lookupSEnv S₂ x = lookupSEnv (S₂ ++ S₁) x := by
        by_cases hS2 : lookupSEnv S₂ x = none
        · have hB := lookupSEnv_append_right (S₁:=S₂) (S₂:=S₁) (x:=x) hS2
          simpa [hS2] using hB
        · cases hS2' : lookupSEnv S₂ x with
          | none => exact (hS2 hS2').elim
          | some T =>
              have hA := lookupSEnv_append_left (S₁:=S₂) (S₂:=S₁) (x:=x) (T:=T) hS2'
              simpa [hS2'] using hA
      have hA := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hLeft
      have hB := lookupSEnv_append_right (S₁:=S₂) (S₂:=S₁) (x:=x) (by
        by_cases hS2 : lookupSEnv S₂ x = none
        · exact hS2
        · cases hS2' : lookupSEnv S₂ x with
          | none => exact (hS2 hS2').elim
          | some T =>
              have : False := (hDisj x T T) (by simpa [hLeft] using hLeft) hS2'
              exact this.elim)
      simpa [hA, hB] using rfl

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
                simp [SEnvAll, List.append_assoc]

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

private lemma lookupG_none_of_disjoint {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂)
    {e : Endpoint} {L : LocalType} (hLookup : lookupG G₂ e = some L) :
    lookupG G₁ e = none := by
  by_cases hNone : lookupG G₁ e = none
  · exact hNone
  · cases hSome : lookupG G₁ e with
    | none => exact (hNone hSome).elim
    | some L₁ =>
        have hSid₁ : e.sid ∈ SessionsOf G₁ := ⟨e, L₁, hSome, rfl⟩
        have hSid₂ : e.sid ∈ SessionsOf G₂ := ⟨e, L, hLookup, rfl⟩
        have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hSid₁, hSid₂⟩
        have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = ∅ := hDisj
        have : e.sid ∈ (∅ : Set SessionId) := by
          simpa [hEmpty] using hInter
        exact this.elim

private lemma HasTypeProcPreOut_frame_G_right
    {Ssh : SEnv} {Sown : OwnedEnv} {G Gfr : GEnv} {P : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointG G Gfr →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    HasTypeProcPreOut Ssh Sown (G ++ Gfr) P Sfin (Gfin ++ Gfr) W Δ := by
  intro hDisj h
  induction h with
  | skip =>
      simpa using (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr))
  | send hk hG hx =>
      have hG' := lookupG_append_left (G₂:=Gfr) hG
      have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
        (L:=.send q T L) (L':=L) hG
      simpa [hUpd] using (HasTypeProcPreOut.send (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr) hk hG' hx)
  | recv_new hk hG hNoSh hNoOwnR hNoOwnL =>
      have hG' := lookupG_append_left (G₂:=Gfr) hG
      have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
        (L:=.recv p T L) (L':=L) hG
      simpa [hUpd] using
        (HasTypeProcPreOut.recv_new (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr) hk hG' hNoSh hNoOwnR hNoOwnL)
  | recv_old hk hG hNoSh hNoOwnR hOwn =>
      have hG' := lookupG_append_left (G₂:=Gfr) hG
      have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
        (L:=.recv p T L) (L':=L) hG
      simpa [hUpd] using
        (HasTypeProcPreOut.recv_old (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr) hk hG' hNoSh hNoOwnR hOwn)
  | select hk hG hbs =>
      have hG' := lookupG_append_left (G₂:=Gfr) hG
      have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
        (L:=.select q bs) (L':=L) hG
      simpa [hUpd] using
        (HasTypeProcPreOut.select (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr) hk hG' hbs)
  | branch hk hG hLen hLabels hBodies hOutLbl hDom =>
      have hG' := lookupG_append_left (G₂:=Gfr) hG
      have hOutLbl' : ∀ i (hi : i < procs.length),
          HasTypeProcPreOut Ssh Sown (updateG (G ++ Gfr) e (bs.get ⟨i, by
            simpa [hLen] using hi⟩).2)
            (procs.get ⟨i, hi⟩).2 Sfin Gfin W Δ := by
        intro i hi
        have hOut := hOutLbl i hi
        -- Frame right by Gfr on each branch
        have hDisj' : DisjointG (updateG G e (bs.get ⟨i, by simpa [hLen] using hi⟩).2) Gfr := by
          have hEq := SessionsOf_updateG_eq (G:=G) (e:=e) (L:= (bs.get ⟨i, by simpa [hLen] using hi⟩).2)
            (L':=.branch p bs) hG
          have hSub : SessionsOf (updateG G e (bs.get ⟨i, by simpa [hLen] using hi⟩).2) ⊆ SessionsOf G := by
            intro s hs
            simpa [hEq] using hs
          exact DisjointG_of_subset_left hSub hDisj
        have hOut' := HasTypeProcPreOut_frame_G_right (Ssh:=Ssh) (Sown:=Sown)
          (G:=updateG G e (bs.get ⟨i, by simpa [hLen] using hi⟩).2) (Gfr:=Gfr) hDisj' hOut
        -- rewrite updateG on the framed G
        have hUpd :=
          updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
            (L:=.branch p bs) (L':=(bs.get ⟨i, by simpa [hLen] using hi⟩).2) hG
        simpa [hUpd] using hOut'
      exact HasTypeProcPreOut.branch (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr)
        hk hG' hLen hLabels hBodies hOutLbl' hDom
  | seq hP hQ ihP ihQ =>
      exact HasTypeProcPreOut.seq ihP ihQ
  | par split hSlen hGlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hS1 hS2 hP hQ ihP ihQ =>
      -- Extend split.G2 with Gfr on the right
      let splitOut : ParSplit Sown.left (G ++ Gfr) :=
        { S1 := split.S1, S2 := split.S2, G1 := split.G1, G2 := split.G2 ++ Gfr
          hS := by simpa [split.hS] using hS1
          hG := by
            simpa [split.hG, List.append_assoc] }
      have hSubG : SessionsOf split.G1 ⊆ SessionsOf G := by
        intro s hs
        simpa [split.hG] using SessionsOf_append_left (G₂:=split.G2) hs
      have hDisjG1fr : DisjointG split.G1 Gfr := DisjointG_of_subset_left hSubG hDisj
      have hDisjGOut : DisjointG splitOut.G1 splitOut.G2 := by
        have hDisjG' : DisjointG split.G1 (split.G2 ++ Gfr) :=
          DisjointG_append_left hDisjG hDisjG1fr
        simpa [splitOut] using hDisjG'
      have hQ' := HasTypeProcPreOut_frame_G_right (Ssh:=Ssh)
        (Sown:={ right := Sown.right ++ split.S1, left := split.S2 })
        (G:=split.G2) (Gfr:=Gfr) (DisjointG_symm hDisjG1fr) hQ
      have hGfin' : (G₁' ++ G₂') ++ Gfr = G₁' ++ (G₂' ++ Gfr) := by
        simp [List.append_assoc]
      refine HasTypeProcPreOut.par splitOut ?_ ?_ ?_ ?_ ?_ ?_ hDisjGOut hDisjS
        hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ ?_ ?_ ihP ?_
      · simpa [splitOut] using hSlen
      · simpa [splitOut] using hGlen
      · simpa [hSfin] using rfl
      · simpa [hGfin, hGfin', splitOut] using rfl
      · simpa [hW] using rfl
      · simpa [hΔ] using rfl
      · simpa [splitOut] using hS1
      · simpa [splitOut] using hS2
      · -- Q framed on the right
        simpa [splitOut] using hQ'
  | assign_new hNoSh hNoOwnR hNoOwnL hv =>
      exact HasTypeProcPreOut.assign_new hNoSh hNoOwnR hNoOwnL hv
  | assign_old hNoSh hNoOwnR hOwn hv =>
      exact HasTypeProcPreOut.assign_old hNoSh hNoOwnR hOwn hv

private lemma HasTypeProcPreOut_frame_G_left
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfr G : GEnv} {P : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointG Gfr G →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    HasTypeProcPreOut Ssh Sown (Gfr ++ G) P Sfin (Gfr ++ Gfin) W Δ := by
  intro hDisj h
  induction h with
  | skip =>
      simpa using (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G))
  | send hk hG hx =>
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hG' := lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone
      have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
      simpa [hUpd] using (HasTypeProcPreOut.send (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G) hk hG' hx)
  | recv_new hk hG hNoSh hNoOwnR hNoOwnL =>
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hG' := lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone
      have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
      simpa [hUpd] using
        (HasTypeProcPreOut.recv_new (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G) hk hG' hNoSh hNoOwnR hNoOwnL)
  | recv_old hk hG hNoSh hNoOwnR hOwn =>
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hG' := lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone
      have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
      simpa [hUpd] using
        (HasTypeProcPreOut.recv_old (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G) hk hG' hNoSh hNoOwnR hOwn)
  | select hk hG hbs =>
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hG' := lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone
      have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
      simpa [hUpd] using
        (HasTypeProcPreOut.select (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G) hk hG' hbs)
  | branch hk hG hLen hLabels hBodies hOutLbl hDom =>
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hG' := lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone
      have hOutLbl' : ∀ i (hi : i < procs.length),
          HasTypeProcPreOut Ssh Sown (updateG (Gfr ++ G) e (bs.get ⟨i, by
            simpa [hLen] using hi⟩).2)
            (procs.get ⟨i, hi⟩).2 Sfin Gfin W Δ := by
        intro i hi
        have hOut := hOutLbl i hi
        have hDisj' : DisjointG Gfr (updateG G e (bs.get ⟨i, by simpa [hLen] using hi⟩).2) := by
          have hEq := SessionsOf_updateG_eq (G:=G) (e:=e) (L:= (bs.get ⟨i, by simpa [hLen] using hi⟩).2)
            (L':=.branch p bs) hG
          have hSub : SessionsOf (updateG G e (bs.get ⟨i, by simpa [hLen] using hi⟩).2) ⊆ SessionsOf G := by
            intro s hs
            simpa [hEq] using hs
          exact DisjointG_of_subset_left hSub (DisjointG_symm hDisj) |> DisjointG_symm
        have hOut' := HasTypeProcPreOut_frame_G_left (Ssh:=Ssh) (Sown:=Sown)
          (Gfr:=Gfr) (G:=updateG G e (bs.get ⟨i, by simpa [hLen] using hi⟩).2) hDisj' hOut
        have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e)
          (L:=(bs.get ⟨i, by simpa [hLen] using hi⟩).2) hNone
        simpa [hUpd] using hOut'
      exact HasTypeProcPreOut.branch (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G)
        hk hG' hLen hLabels hBodies hOutLbl' hDom
  | seq hP hQ ihP ihQ =>
      exact HasTypeProcPreOut.seq ihP ihQ
  | par split hSlen hGlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hS1 hS2 hP hQ ihP ihQ =>
      -- Extend split.G1 with Gfr on the left
      let splitOut : ParSplit Sown.left (Gfr ++ G) :=
        { S1 := split.S1, S2 := split.S2, G1 := Gfr ++ split.G1, G2 := split.G2
          hS := by simpa [split.hS] using hS1
          hG := by
            simpa [split.hG, List.append_assoc] }
      have hSubG : SessionsOf split.G1 ⊆ SessionsOf G := by
        intro s hs
        simpa [split.hG] using SessionsOf_append_left (G₂:=split.G2) hs
      have hDisjG1fr : DisjointG Gfr split.G1 := DisjointG_of_subset_left hSubG hDisj
      have hDisjGOut : DisjointG splitOut.G1 splitOut.G2 := by
        have hDisjG' : DisjointG (Gfr ++ split.G1) split.G2 :=
          DisjointG_append_left hDisjG1fr hDisjG
        simpa [splitOut] using hDisjG'
      have hP' := HasTypeProcPreOut_frame_G_left (Ssh:=Ssh)
        (Sown:={ right := Sown.right ++ split.S2, left := split.S1 })
        (Gfr:=Gfr) (G:=split.G1) hDisjG1fr hP
      have hGfin' : Gfr ++ (G₁' ++ G₂') = (Gfr ++ G₁') ++ G₂' := by
        simp [List.append_assoc]
      refine HasTypeProcPreOut.par splitOut ?_ ?_ ?_ ?_ ?_ ?_ hDisjGOut hDisjS
        hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ ?_ ?_ ?_ ihQ
      · simpa [splitOut] using hSlen
      · simpa [splitOut] using hGlen
      · simpa [hSfin] using rfl
      · simpa [hGfin, hGfin', splitOut] using rfl
      · simpa [hW] using rfl
      · simpa [hΔ] using rfl
      · simpa [splitOut] using hS1
      · simpa [splitOut] using hS2
      · simpa [splitOut] using hP'
  | assign_new hNoSh hNoOwnR hNoOwnL hv =>
      exact HasTypeProcPreOut.assign_new hNoSh hNoOwnR hNoOwnL hv
  | assign_old hNoSh hNoOwnR hOwn hv =>
      exact HasTypeProcPreOut.assign_old hNoSh hNoOwnR hOwn hv

private lemma TypedStep_preserves_frames
    {Ssh : SEnv} {Sown : OwnedEnv} {Gleft Gmid Gright : GEnv}
    {D : DEnv} {store : VarStore} {bufs : Buffers} {P : Process}
    {G' : GEnv} {D' : DEnv} {Sown' : OwnedEnv} {store' : VarStore} {bufs' : Buffers} {P' : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointG Gleft Gmid →
    DisjointG Gleft Gright →
    DisjointG Gmid Gright →
    StoreTypedStrong (Gleft ++ Gmid ++ Gright) (SEnvAll Ssh Sown) store →
    HasTypeProcPreOut Ssh Sown Gmid P Sfin Gfin W Δ →
    TypedStep (Gleft ++ Gmid ++ Gright) D Ssh Sown store bufs P
      G' D' Sown' store' bufs' P' →
    ∃ Gmid', G' = Gleft ++ Gmid' ++ Gright := by
  intro hDisjL hDisjLR hDisjR hStore hOut hStep
  induction hStep generalizing Gleft Gmid Gright Sfin Gfin W Δ with
  | send =>
      intro hDisjL hDisjLR hDisjR hStore hOut
      rename_i Gfull D Ssh Sown store bufs k x eStep target T Lstep v sendEdge G' D' bufs'
        hkStr hxStr hGStep hS hv hRecvReady hEdge hGout hDout hBufsOut
      cases hOut with
      | send hk hG hx =>
          have hEq : eStep = e :=
            channel_endpoint_eq_of_store (hStore:=hStore) (k:=k) (e:=e) (e':=eStep) hk hkStr
          subst hEq
          have hNoneLeft : lookupG Gleft e = none :=
            DisjointG_lookup_left (G₁:=Gmid) (G₂:=Gleft) (DisjointG_symm hDisjL) hG
          have hLookupMid : lookupG (Gleft ++ Gmid) e = some (.send q T L) := by
            have hEq' := lookupG_append_right (G₁:=Gleft) (G₂:=Gmid) (e:=e) hNoneLeft
            simpa [hEq'] using hG
          have hUpdRight :=
            updateG_append_left_hit (G₁:=Gleft ++ Gmid) (G₂:=Gright) (e:=e) (L':=Lstep) hLookupMid
          have hUpdLeft :=
            updateG_append_left (G₁:=Gleft) (G₂:=Gmid) (e:=e) (L:=Lstep) hNoneLeft
          refine ⟨updateG Gmid e Lstep, ?_⟩
          simp [hGout, hUpdRight, hUpdLeft, List.append_assoc]
  | recv =>
      intro hDisjL hDisjLR hDisjR hStore hOut
      rename_i Gfull D Ssh Sown store bufs k x eStep source T Lstep v vs recvEdge G' D' Sown' store' bufs'
        hkStr hGStep hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut
      cases hOut with
      | recv_new hk hG hNoSh hNoOwnR hNoOwnL =>
          have hEq : eStep = e :=
            channel_endpoint_eq_of_store (hStore:=hStore) (k:=k) (e:=e) (e':=eStep) hk hkStr
          subst hEq
          have hNoneLeft : lookupG Gleft e = none :=
            DisjointG_lookup_left (G₁:=Gmid) (G₂:=Gleft) (DisjointG_symm hDisjL) hG
          have hLookupMid : lookupG (Gleft ++ Gmid) e = some (.recv p T L) := by
            have hEq' := lookupG_append_right (G₁:=Gleft) (G₂:=Gmid) (e:=e) hNoneLeft
            simpa [hEq'] using hG
          have hUpdRight :=
            updateG_append_left_hit (G₁:=Gleft ++ Gmid) (G₂:=Gright) (e:=e) (L':=Lstep) hLookupMid
          have hUpdLeft :=
            updateG_append_left (G₁:=Gleft) (G₂:=Gmid) (e:=e) (L:=Lstep) hNoneLeft
          refine ⟨updateG Gmid e Lstep, ?_⟩
          simp [hGout, hUpdRight, hUpdLeft, List.append_assoc]
      | recv_old hk hG hNoSh hNoOwnR hOwn =>
          have hEq : eStep = e :=
            channel_endpoint_eq_of_store (hStore:=hStore) (k:=k) (e:=e) (e':=eStep) hk hkStr
          subst hEq
          have hNoneLeft : lookupG Gleft e = none :=
            DisjointG_lookup_left (G₁:=Gmid) (G₂:=Gleft) (DisjointG_symm hDisjL) hG
          have hLookupMid : lookupG (Gleft ++ Gmid) e = some (.recv p T L) := by
            have hEq' := lookupG_append_right (G₁:=Gleft) (G₂:=Gmid) (e:=e) hNoneLeft
            simpa [hEq'] using hG
          have hUpdRight :=
            updateG_append_left_hit (G₁:=Gleft ++ Gmid) (G₂:=Gright) (e:=e) (L':=Lstep) hLookupMid
          have hUpdLeft :=
            updateG_append_left (G₁:=Gleft) (G₂:=Gmid) (e:=e) (L:=Lstep) hNoneLeft
          refine ⟨updateG Gmid e Lstep, ?_⟩
          simp [hGout, hUpdRight, hUpdLeft, List.append_assoc]
  | select =>
      intro hDisjL hDisjLR hDisjR hStore hOut
      rename_i Gfull D Ssh Sown store bufs k ℓ eStep target bs Lstep selectEdge G' D' bufs'
        hkStr hGStep hFind hTargetReady hEdge hGout hDout hBufsOut
      cases hOut with
      | select hk hG hbs =>
          have hEq : eStep = e :=
            channel_endpoint_eq_of_store (hStore:=hStore) (k:=k) (e:=e) (e':=eStep) hk hkStr
          subst hEq
          have hNoneLeft : lookupG Gleft e = none :=
            DisjointG_lookup_left (G₁:=Gmid) (G₂:=Gleft) (DisjointG_symm hDisjL) hG
          have hLookupMid : lookupG (Gleft ++ Gmid) e = some (.select q bs) := by
            have hEq' := lookupG_append_right (G₁:=Gleft) (G₂:=Gmid) (e:=e) hNoneLeft
            simpa [hEq'] using hG
          have hUpdRight :=
            updateG_append_left_hit (G₁:=Gleft ++ Gmid) (G₂:=Gright) (e:=e) (L':=Lstep) hLookupMid
          have hUpdLeft :=
            updateG_append_left (G₁:=Gleft) (G₂:=Gmid) (e:=e) (L:=Lstep) hNoneLeft
          refine ⟨updateG Gmid e Lstep, ?_⟩
          simp [hGout, hUpdRight, hUpdLeft, List.append_assoc]
  | branch =>
      intro hDisjL hDisjLR hDisjR hStore hOut
      rename_i Gfull D Ssh Sown store bufs k procs eStep source bs ℓ P Lstep vs branchEdge G' D' bufs'
        hkStr hGStep hEdge hBuf hFindP hFindBs hTrace hGout hDout hBufsOut
      cases hOut with
      | branch hk hG hLen hLabels hBodies hOutLbl hDom =>
          have hEq : eStep = e :=
            channel_endpoint_eq_of_store (hStore:=hStore) (k:=k) (e:=e) (e':=eStep) hk hkStr
          subst hEq
          have hNoneLeft : lookupG Gleft e = none :=
            DisjointG_lookup_left (G₁:=Gmid) (G₂:=Gleft) (DisjointG_symm hDisjL) hG
          have hLookupMid : lookupG (Gleft ++ Gmid) e = some (.branch p bs) := by
            have hEq' := lookupG_append_right (G₁:=Gleft) (G₂:=Gmid) (e:=e) hNoneLeft
            simpa [hEq'] using hG
          have hUpdRight :=
            updateG_append_left_hit (G₁:=Gleft ++ Gmid) (G₂:=Gright) (e:=e) (L':=Lstep) hLookupMid
          have hUpdLeft :=
            updateG_append_left (G₁:=Gleft) (G₂:=Gmid) (e:=e) (L:=Lstep) hNoneLeft
          refine ⟨updateG Gmid e Lstep, ?_⟩
          simp [hGout, hUpdRight, hUpdLeft, List.append_assoc]
  | assign =>
      intro hDisjL hDisjLR hDisjR hStore hOut
      rename_i Gfull D Ssh Sown store bufs x v T S' store' hv hSout hStoreOut
      cases hOut <;> refine ⟨Gmid, ?_⟩ <;> simp [List.append_assoc]
  | seq_step =>
      intro hDisjL hDisjLR hDisjR hStore hOut
      rename_i Gfull D Ssh Sown G' D' Sown' store bufs store' bufs' P P' Q hStepP ih
      cases hOut with
      | seq hP hQ =>
          exact ih hDisjL hDisjLR hDisjR hStore hP hStepP
  | seq_skip =>
      intro hDisjL hDisjLR hDisjR hStore hOut
      rename_i Gfull D Ssh Sown store bufs Q
      cases hOut with
      | seq hP hQ =>
          refine ⟨Gmid, ?_⟩
          simp [List.append_assoc]
  | par_left =>
      intro hDisjL hDisjLR hDisjR hStore hOut
      rename_i Ssh Sown store bufs store' bufs' P P' Q Gfull D₁ D₂ G₁' D₁' S₁' nS nG splitFull
        hSlen' hGlen' hStepP hDisjGfull hDisjD hDisjSfull ih
      cases hOut with
      | par split hSlen hGlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
          hDisjW hDisjΔ hS1 hS2 hP hQ =>
          have hSeq : splitFull.S1 ++ splitFull.S2 = split.S1 ++ split.S2 := by
            rw [← splitFull.hS, ← split.hS]
          have hSlenEq : splitFull.S1.length = split.S1.length :=
            hSlen'.trans hSlen.symm
          have hS1Eq : splitFull.S1 = split.S1 := List.append_inj_left hSeq hSlenEq
          have hS2Eq : splitFull.S2 = split.S2 := List.append_inj_right hSeq hSlenEq
          have hStoreBase :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll (Ssh ++ Sown.right) ((split.S1 ++ split.S2) ++ (∅ : SEnv))) store := by
            simpa [SEnvAll, split.hS, List.append_assoc] using hStore
          have hStoreSwap :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll (Ssh ++ Sown.right) (split.S2 ++ (split.S1 ++ (∅ : SEnv)))) store :=
            StoreTypedStrong_swap_S_left_prefix (Ssh:=Ssh ++ Sown.right)
              (S₁:=split.S1) (S₂:=split.S2) (S₃:=∅) (DisjointS_symm hDisjS)
              (by simpa [List.append_assoc] using hStoreBase)
          have hStoreL :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store := by
            simpa [SEnvAll, List.append_assoc] using hStoreSwap
          have hStoreR :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store := by
            simpa [SEnvAll, split.hS, List.append_assoc] using hStore
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
          have hDisjLeftRight : DisjointG Gleft (split.G2 ++ Gright) :=
            DisjointG_append_left hDisjGleftG2 hDisjLR
          have hDisjMidRight : DisjointG split.G1 (split.G2 ++ Gright) :=
            DisjointG_append_left hDisjG hDisjG1Right
          have hStoreL' :
              StoreTypedStrong (Gleft ++ split.G1 ++ (split.G2 ++ Gright))
                (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store := by
            simpa [split.hG, List.append_assoc] using hStoreL
          have hStepP' :
              TypedStep (Gleft ++ split.G1 ++ (split.G2 ++ Gright))
                (D₁ ++ D₂) Ssh { right := Sown.right ++ split.S2, left := split.S1 }
                store bufs P
                (G₁' ++ splitFull.G2) (D₁' ++ D₂)
                { right := Sown.right ++ split.S2, left := S₁' } store' bufs' P' := by
            simpa [hS1Eq, hS2Eq, split.hG, List.append_assoc] using hStepP
          rcases ih hDisjGleftG1 hDisjLeftRight hDisjMidRight hStoreL' hP hStepP' with ⟨Gmid', hShape⟩
          refine ⟨Gmid' ++ split.G2, ?_⟩
          simp [hShape, List.append_assoc]
  | par_right =>
      intro hDisjL hDisjLR hDisjR hStore hOut
      rename_i Ssh Sown store bufs store' bufs' P Q Q' Gfull D₁ D₂ G₂' D₂' S₂' nS nG splitFull
        hSlen' hGlen' hStepQ hDisjGfull hDisjD hDisjSfull ih
      cases hOut with
      | par split hSlen hGlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
          hDisjW hDisjΔ hS1 hS2 hP hQ =>
          have hSeq : splitFull.S1 ++ splitFull.S2 = split.S1 ++ split.S2 := by
            rw [← splitFull.hS, ← split.hS]
          have hSlenEq : splitFull.S1.length = split.S1.length :=
            hSlen'.trans hSlen.symm
          have hS1Eq : splitFull.S1 = split.S1 := List.append_inj_left hSeq hSlenEq
          have hS2Eq : splitFull.S2 = split.S2 := List.append_inj_right hSeq hSlenEq
          have hStoreBase :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll (Ssh ++ Sown.right) ((split.S1 ++ split.S2) ++ (∅ : SEnv))) store := by
            simpa [SEnvAll, split.hS, List.append_assoc] using hStore
          have hStoreSwap :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll (Ssh ++ Sown.right) (split.S2 ++ (split.S1 ++ (∅ : SEnv)))) store :=
            StoreTypedStrong_swap_S_left_prefix (Ssh:=Ssh ++ Sown.right)
              (S₁:=split.S1) (S₂:=split.S2) (S₃:=∅) (DisjointS_symm hDisjS)
              (by simpa [List.append_assoc] using hStoreBase)
          have hStoreL :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store := by
            simpa [SEnvAll, List.append_assoc] using hStoreSwap
          have hStoreR :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store := by
            simpa [SEnvAll, split.hS, List.append_assoc] using hStore
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
          have hStoreR' :
              StoreTypedStrong ((Gleft ++ split.G1) ++ split.G2 ++ Gright)
                (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store := by
            simpa [split.hG, List.append_assoc] using hStoreR
          have hStepQ' :
              TypedStep ((Gleft ++ split.G1) ++ split.G2 ++ Gright)
                (D₁ ++ D₂) Ssh { right := Sown.right ++ split.S1, left := split.S2 }
                store bufs Q
                (splitFull.G1 ++ G₂') (D₁ ++ D₂')
                { right := Sown.right ++ split.S1, left := S₂' } store' bufs' Q' := by
            simpa [hS1Eq, hS2Eq, split.hG, List.append_assoc] using hStepQ
          rcases ih hDisjLeftMid hDisjLeftRight hDisjG2Right hStoreR' hQ hStepQ' with ⟨Gmid', hShape⟩
          refine ⟨split.G1 ++ Gmid', ?_⟩
          simp [hShape, List.append_assoc]
  | par_skip_left =>
      intro hDisjL hDisjLR hDisjR hStore hOut
      rename_i Gfull D Ssh Sown store bufs Q nS nG
      cases hOut with
      | par _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          refine ⟨Gmid, ?_⟩
          simp [List.append_assoc]
  | par_skip_right =>
      intro hDisjL hDisjLR hDisjR hStore hOut
      rename_i Gfull D Ssh Sown store bufs P nS nG
      cases hOut with
      | par _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          refine ⟨Gmid, ?_⟩
          simp [List.append_assoc]

private theorem progress_typed_aux {G D Ssh Sown store bufs P Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    BuffersTyped G D bufs →
    Coherent G D →
    HeadCoherent G D →
    ValidLabels G D bufs →
    SendReady G D →
    SelectReady G D →
    DConsistent G D →
    (P = .skip) ∨
      (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
        G' D' Sown' store' bufs' P') ∨
      BlockedProc store bufs P := by
  intro hOut hStore hBufs hCoh hHead hValid hReady hSelectReady hCons
  cases P with
  | skip =>
      left; rfl
  | send k x =>
      cases hOut with
      | send hk hG hx =>
          rename_i e q T L
          right; left
          obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
          have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
          subst hkChan
          obtain ⟨v, hxStr, hv⟩ := store_lookup_of_senv_lookup hStore hx
          have hRecvReady := hReady e q T L hG
          exact ⟨_, _, _, _, _, _, TypedStep.send hkStr hxStr hG hx hv hRecvReady rfl rfl rfl rfl⟩
  | recv k x =>
      cases hOut with
      | recv_new hk hG hNoSh hNoOwnR hNoOwnL =>
          rename_i e p T L
          obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
          have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
          subst hkChan
          set recvEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
          cases hBuf : lookupBuf bufs recvEdge with
          | nil =>
              right; right
              refine ⟨e, p, hkStr, ?_⟩
              simpa [recvEdge, hBuf]
          | cons v vs =>
              right; left
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
                  have hHeadEdge := hHead recvEdge
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
          cases hBuf : lookupBuf bufs recvEdge with
          | nil =>
              right; right
              refine ⟨e, p, hkStr, ?_⟩
              simpa [recvEdge, hBuf]
          | cons v vs =>
              right; left
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
                  have hHeadEdge := hHead recvEdge
                  have hEq : T = T' := by
                    simpa [HeadCoherent, hG, recvEdge, hTrace] using hHeadEdge
                  have hEq' : T' = T := by
                    simpa using hEq.symm
                  have hv : HasTypeVal G v T := by
                    simpa [hTrace, hEq'] using hv'
                  have hTraceHead : (lookupD D recvEdge).head? = some T := by
                    simp [hTrace, hEq]
                  exact ⟨_, _, _, _, _, _, TypedStep.recv hkStr hG rfl hBuf hv hTraceHead rfl rfl rfl rfl rfl⟩
  | select k ℓ =>
      cases hOut with
      | select hk hG hbs =>
          rename_i e q bs L
          right; left
          obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
          have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
          subst hkChan
          have hTargetReady := hSelectReady e q bs ℓ L hG hbs
          exact ⟨_, _, _, _, _, _, TypedStep.select hkStr hG hbs hTargetReady rfl rfl rfl rfl⟩
  | branch k procs =>
      cases hOut with
      | branch hk hG hLen hLabels hBodies hOutLbl hDom =>
          rename_i e p bs
          obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
          have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
          subst hkChan
          set branchEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
          cases hBuf : lookupBuf bufs branchEdge with
          | nil =>
              right; right
              refine ⟨e, p, hkStr, ?_⟩
              simpa [branchEdge, hBuf]
          | cons v vs =>
              right; left
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
                  have hHeadEdge := hHead branchEdge
                  have hEq : T' = .string := by
                    simpa [HeadCoherent, hG, branchEdge, hTrace] using hHeadEdge
                  have hv := by
                    simpa [hTrace, hEq] using hv'
                  cases hv with
                  | string lbl =>
                      have hValidEdge := hValid branchEdge p bs (by simpa [branchEdge] using hG)
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
  | seq P Q =>
      cases hOut with
      | seq hP hQ =>
          have hProgP :=
            progress_typed_aux hP hStore hBufs hCoh hHead hValid hReady hSelectReady hCons
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
          -- Store typing for left and right processes.
          have hStoreBase :
              StoreTypedStrong G (SEnvAll (Ssh ++ Sown.right) ((split.S1 ++ split.S2) ++ (∅ : SEnv))) store := by
            simpa [SEnvAll, split.hS, List.append_assoc] using hStore
          have hStoreSwap :
              StoreTypedStrong G (SEnvAll (Ssh ++ Sown.right) (split.S2 ++ (split.S1 ++ (∅ : SEnv)))) store :=
            StoreTypedStrong_swap_S_left_prefix (Ssh:=Ssh ++ Sown.right)
              (S₁:=split.S1) (S₂:=split.S2) (S₃:=∅) (DisjointS_symm hDisjS)
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
              (Gfr:=split.G1) (G:=split.G2) (DisjointG_symm hDisjG) hQ

          -- Progress on left process.
          have hProgP :=
            progress_typed_aux hP_full hStoreL hBufs hCoh hHead hValid hReady hSelectReady hCons
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
                        (DisjointG_left_empty split.G1) (DisjointG_left_empty split.G2) hDisjG
                        hStoreL hP hStep
                    rcases hShape with ⟨G₁', hShape⟩
                    refine ⟨G₁', ?_⟩
                    simpa [List.append_assoc] using hShape
                  rcases hGshape with ⟨G₁', hGshape⟩
                  have hRightEq : S'.right = Sown.right ++ split.S2 :=
                    TypedStep_preserves_right hStep
                  have hS' :
                      S' = { right := Sown.right ++ split.S2, left := S'.left } := by
                    cases S'
                    simp [hRightEq]
                  have hStep' :
                      TypedStep G (D ++ (∅ : DEnv)) Ssh { right := Sown.right ++ split.S2, left := split.S1 }
                        store bufs P
                        (G₁' ++ split.G2) (D' ++ (∅ : DEnv))
                        { right := Sown.right ++ split.S2, left := S'.left }
                        store' bufs' P' := by
                    simpa [DEnv_append_empty_right, hGshape, hS'] using hStep
                  right; left
                  refine ⟨_, _, _, _, _, _, ?_⟩
                  exact TypedStep.par_left (split:=split) (D₁:=D) (D₂:=∅) (G₁':=G₁') (D₁':=D') (S₁':=S'.left)
                    hSlen hGlen hStep' hDisjG (DisjointD_right_empty D) hDisjS
              | inr hBlockedP =>
                  -- Progress on right process.
                  have hProgQ :=
                    progress_typed_aux hQ_full hStoreR hBufs hCoh hHead hValid hReady hSelectReady hCons
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
                                hDisjG (DisjointG_right_empty split.G1) (DisjointG_right_empty split.G2)
                                hStoreR hQ hStep
                            rcases hShape with ⟨G₂', hShape⟩
                            refine ⟨G₂', ?_⟩
                            simpa [List.append_assoc] using hShape
                          rcases hGshape with ⟨G₂', hGshape⟩
                          have hRightEq : S'.right = Sown.right ++ split.S1 :=
                            TypedStep_preserves_right hStep
                          have hS' :
                              S' = { right := Sown.right ++ split.S1, left := S'.left } := by
                            cases S'
                            simp [hRightEq]
                          have hStep' :
                              TypedStep G ((∅ : DEnv) ++ D) Ssh { right := Sown.right ++ split.S1, left := split.S2 }
                                store bufs Q
                                (split.G1 ++ G₂') ((∅ : DEnv) ++ D')
                                { right := Sown.right ++ split.S1, left := S'.left }
                                store' bufs' Q' := by
                            simpa [DEnv_append_empty_left, hGshape, hS'] using hStep
                          right; left
                          refine ⟨_, _, _, _, _, _, ?_⟩
                          exact TypedStep.par_right (split:=split) (D₁:=∅) (D₂:=D) (G₂':=G₂') (D₂':=D') (S₂':=S'.left)
                            hSlen hGlen hStep' hDisjG (DisjointD_left_empty D) hDisjS
                      | inr hBlockedQ =>
                          right; right
                          exact And.intro (by simpa using hBlockedP) (by simpa using hBlockedQ)
  | newSession roles f P =>
      cases hOut
  | assign x v =>
      cases hOut with
      | assign_new hNoSh hNoOwnR hNoOwnL hv =>
          right; left
          exact ⟨_, _, _, _, _, _, TypedStep.assign hv rfl rfl⟩
      | assign_old hNoSh hNoOwnR hOwn hv =>
          right; left
          exact ⟨_, _, _, _, _, _, TypedStep.assign hv rfl rfl⟩

/-- Progress theorem: A well-formed process can either step or is in a final/blocked state.

    **Proof strategy**: Case analysis on process P:
    - `skip`: Terminates
    - `send k x`: Derive TypedStep.send from lookupG via HasTypeProcPre inversion
    - `recv k x`: Check buffer - if non-empty, derive TypedStep.recv; else blocked
    - `seq P Q`: Use IH on P or skip elimination
    - `par P Q`: Use IH on P or Q or skip elimination -/
theorem progress_typed {G D Ssh Sown store bufs P} :
    LocalTypeR.WellFormed G D Ssh Sown store bufs P →
    (P = .skip) ∨
    (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
      G' D' Sown' store' bufs' P') ∨
    BlockedProc store bufs P := by
  intro hWF
  unfold LocalTypeR.WellFormed at hWF
  obtain ⟨hStore, hBufs, hCoh, hHead, hValid, hCompat, hDisjS, hCons, hDCons, hPreOut⟩ := hWF
  obtain ⟨Sfin, Gfin, Wfin, Δfin, hOut⟩ := hPreOut
  have hReady : SendReady G D := Compatible_to_SendReady hCompat
  have hSelectReady : SelectReady G D := Compatible_to_SelectReady hCompat
  exact progress_typed_aux hOut hStore hBufs hCoh hHead hValid hReady hSelectReady hDCons

/-  Subject reduction (soundness) theorem moved to Protocol.Preservation
    to avoid circular dependency (Step is defined in Semantics which imports Typing).

    **Theorem**: TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
                 Step ⟨P, store, bufs, G, D, n⟩ ⟨P', store', bufs', G', D', n⟩

    This will be proven in Preservation.lean after TypedStep is available. -/

end
