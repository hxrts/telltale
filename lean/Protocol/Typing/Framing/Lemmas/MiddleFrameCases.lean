import Protocol.Typing.Framing.Lemmas.MiddleFrameSpec

/-! # Middle Frame Cases

Per-constructor case lemmas for middle-frame preservation, showing
typed steps in a three-way split `Gleft ++ Gmid ++ Gright` preserve
the middle portion's typing structure. -/

/-
The Problem. For preservation with parallel composition, we split GEnv
into three parts. When a step occurs in the middle, we need to show
the step's effect stays within Gmid and typing is preserved.

Solution Structure. Prove `preserved_sub_middle_select`, `_branch`,
`_send`, `_recv` lemmas. Each extracts the endpoint equality, shows
the update stays in Gmid, and reconstructs the output typing.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

-- Select Case

lemma preserved_sub_middle_select
    {Gstore Gleft Gmid Gright G : GEnv} {D D' : DEnv}
    {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore} {bufs bufs' : Buffers}
    {k : Var} {ℓ : Label} {e : Endpoint} {target : Role}
    {bs : List (Label × LocalType)} {L : LocalType}
    {G' : GEnv}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    OwnedDisjoint Sown →
    DisjointG Gleft Gmid →
    G = Gleft ++ Gmid ++ Gright →
    lookupStr store k = some (.chan e) →
    lookupG G e = some (.select target bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    G' = updateG G e L →
    TypedStep G D Ssh Sown store bufs (.select k ℓ) G' D' Sown store bufs' .skip →
    HasTypeProcPreOut Ssh Sown Gmid (.select k ℓ) Sfin Gfin W Δ →
    ∃ Gmid' W' Δ', G' = Gleft ++ Gmid' ++ Gright ∧
      SessionsOf Gmid' ⊆ SessionsOf Gmid ∧
      HasTypeProcPreOut Ssh Sown Gmid' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  -- Select Case: Transport and Witness Packing
  intro hStore hOwn hDisjLM hEqG hkStore hGstep hFindStep hGupd hTS hPre
  cases hTS with
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      cases hPre with
      | select hkMid hGmid hFindMid =>
          rename_i eMid q bsMid Lmid
          have hEqE : e = eMid :=
            endpoint_eq_of_store_visible_all
              (Gstore:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
              (k:=k) (e:=e) (e':=eMid) hStore hOwn hkStore hkMid
          have hMid : lookupG Gmid e = some (.select q bsMid) := by
            simpa [hEqE] using hGmid
          have hNoneLeft : lookupG Gleft e = none :=
            lookupG_none_of_disjoint (G₁:=Gleft) (G₂:=Gmid) hDisjLM hMid
          have hFullMid : lookupG G e = some (.select q bsMid) := by
            calc
              lookupG G e = lookupG (Gleft ++ Gmid ++ Gright) e := by simpa [hEqG]
              _ = some (.select q bsMid) :=
                lookupG_middle_to_full (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
                  (e:=e) (L0:=.select q bsMid) hNoneLeft hMid
          have hSelEq : LocalType.select target bs = LocalType.select q bsMid := by
            exact Option.some.inj (by simpa [hGstep] using hFullMid)
          have hBs : bs = bsMid := by
            cases hSelEq
            rfl
          have hFindMid' : bs.find? (fun b => b.1 == ℓ) = some (ℓ, Lmid) := by
            simpa [hBs] using hFindMid
          have hL : Lmid = L := by
            have hPair : (ℓ, L) = (ℓ, Lmid) := by
              simpa [hFindStep] using hFindMid'
            exact (congrArg Prod.snd hPair).symm
          have hGupd' : G' = updateG (Gleft ++ Gmid ++ Gright) e L := by
            simpa [hEqG] using hGupd
          obtain ⟨Gmid', hEqG', hMid'⟩ :=
            updateG_middle_witness (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
              (G':=G') (e:=e) (L0:=.select q bsMid) (L:=L) hNoneLeft hMid hGupd'
          have hSubSess : SessionsOf Gmid' ⊆ SessionsOf Gmid := by
            rw [hMid']
            exact SessionsOf_subset_middle_update (Gmid:=Gmid) (e:=e)
              (L0:=.select q bsMid) (L:=L) hMid
          -- Select Case: Final Framed Post-State Witness
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

-- Recv Case

/-- Constructive middle-frame preservation for a `recv` step. -/
lemma preserved_sub_middle_recv
    {Gstore Gleft Gmid Gright G : GEnv} {D D' : DEnv}
    {Ssh : SEnv} {Sown Sown' : OwnedEnv}
    {store store' : VarStore} {bufs bufs' : Buffers}
    {k x : Var} {e : Endpoint} {source : Role} {T : ValType} {L : LocalType}
    {G' : GEnv}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    OwnedDisjoint Sown →
    DisjointG Gleft Gmid →
    G = Gleft ++ Gmid ++ Gright →
    lookupStr store k = some (.chan e) →
    lookupG G e = some (.recv source T L) →
    G' = updateG G e L →
    Sown' = OwnedEnv.updateLeft Sown x T →
    TypedStep G D Ssh Sown store bufs (.recv k x) G' D' Sown' store' bufs' .skip →
    HasTypeProcPreOut Ssh Sown Gmid (.recv k x) Sfin Gfin W Δ →
    ∃ Gmid' W' Δ', G' = Gleft ++ Gmid' ++ Gright ∧
      SessionsOf Gmid' ⊆ SessionsOf Gmid ∧
      HasTypeProcPreOut Ssh Sown' Gmid' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hStore hOwn hDisjLM hEqG hkStore hGstep hGupd hSownUpd hTS hPre
  cases hTS with
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      cases hPre with
      | recv_new hkMid hGmid hNoSh hNoOwnL =>
          rename_i eMid p Tmid Lmid
          have hEqE : e = eMid :=
            endpoint_eq_of_store_visible_all
              (Gstore:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
              (k:=k) (e:=e) (e':=eMid) hStore hOwn hkStore hkMid
          have hMid : lookupG Gmid e = some (.recv p Tmid Lmid) := by
            simpa [hEqE] using hGmid
          have hNoneLeft : lookupG Gleft e = none :=
            lookupG_none_of_disjoint (G₁:=Gleft) (G₂:=Gmid) hDisjLM hMid
          have hFullMid : lookupG G e = some (.recv p Tmid Lmid) := by
            calc
              lookupG G e = lookupG (Gleft ++ Gmid ++ Gright) e := by simpa [hEqG]
              _ = some (.recv p Tmid Lmid) :=
                lookupG_middle_to_full (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
                  (e:=e) (L0:=.recv p Tmid Lmid) hNoneLeft hMid
          -- Recv Case (`recv_new`): Align Step Payload and Continuation
          have hRecvEq : LocalType.recv source T L = LocalType.recv p Tmid Lmid := by
            exact Option.some.inj (by simpa [hGstep] using hFullMid)
          have hT : Tmid = T := by
            cases hRecvEq
            rfl
          have hL : Lmid = L := by
            cases hRecvEq
            rfl
          have hGupd' : G' = updateG (Gleft ++ Gmid ++ Gright) e L := by
            simpa [hEqG] using hGupd
          obtain ⟨Gmid', hEqG', hMid'⟩ :=
            updateG_middle_witness (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
              (G':=G') (e:=e) (L0:=.recv p Tmid Lmid) (L:=L) hNoneLeft hMid hGupd'
          have hSubSess : SessionsOf Gmid' ⊆ SessionsOf Gmid := by
            rw [hMid']
            exact SessionsOf_subset_middle_update (Gmid:=Gmid) (e:=e)
              (L0:=.recv p Tmid Lmid) (L:=L) hMid
          -- Recv Case (`recv_new`): Final Framed Witness
          refine ⟨Gmid', [], ∅, hEqG', hSubSess, ?_, ?_, ?_⟩
          · have hSownEq : Sown' = OwnedEnv.updateLeft Sown x Tmid := by
              calc
                Sown' = OwnedEnv.updateLeft Sown x T := hSownUpd
                _ = OwnedEnv.updateLeft Sown x Tmid := by simpa [hT]
            have hGmidEq : Gmid' = updateG Gmid eMid Lmid := by
              calc
                Gmid' = updateG Gmid e L := hMid'
                _ = updateG Gmid e Lmid := by simpa [hL]
                _ = updateG Gmid eMid Lmid := by simpa [hEqE]
            simpa [hSownEq, hGmidEq] using
              (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown') (G:=Gmid'))
          · intro y hy
            cases hy
          · intro y Ty hy
            cases hy
      -- Recv Case (`recv_old`)
      | recv_old hkMid hGmid hNoSh hOwnL =>
          rename_i eMid p Tmid Lmid Told
          have hEqE : e = eMid :=
            endpoint_eq_of_store_visible_all
              (Gstore:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
              (k:=k) (e:=e) (e':=eMid) hStore hOwn hkStore hkMid
          have hMid : lookupG Gmid e = some (.recv p Tmid Lmid) := by
            simpa [hEqE] using hGmid
          have hNoneLeft : lookupG Gleft e = none :=
            lookupG_none_of_disjoint (G₁:=Gleft) (G₂:=Gmid) hDisjLM hMid
          have hFullMid : lookupG G e = some (.recv p Tmid Lmid) := by
            calc
              lookupG G e = lookupG (Gleft ++ Gmid ++ Gright) e := by simpa [hEqG]
              _ = some (.recv p Tmid Lmid) :=
                lookupG_middle_to_full (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
                  (e:=e) (L0:=.recv p Tmid Lmid) hNoneLeft hMid
          have hRecvEq : LocalType.recv source T L = LocalType.recv p Tmid Lmid := by
            exact Option.some.inj (by simpa [hGstep] using hFullMid)
          have hT : Tmid = T := by
            cases hRecvEq
            rfl
          have hL : Lmid = L := by
            cases hRecvEq
            rfl
          have hGupd' : G' = updateG (Gleft ++ Gmid ++ Gright) e L := by
            simpa [hEqG] using hGupd
          obtain ⟨Gmid', hEqG', hMid'⟩ :=
            updateG_middle_witness (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
              (G':=G') (e:=e) (L0:=.recv p Tmid Lmid) (L:=L) hNoneLeft hMid hGupd'
          have hSubSess : SessionsOf Gmid' ⊆ SessionsOf Gmid := by
            rw [hMid']
            exact SessionsOf_subset_middle_update (Gmid:=Gmid) (e:=e)
              (L0:=.recv p Tmid Lmid) (L:=L) hMid
          -- Recv Case (`recv_old`): Final Framed Witness
          refine ⟨Gmid', [], ∅, hEqG', hSubSess, ?_, ?_, ?_⟩
          · have hSownEq : Sown' = OwnedEnv.updateLeft Sown x Tmid := by
              calc
                Sown' = OwnedEnv.updateLeft Sown x T := hSownUpd
                _ = OwnedEnv.updateLeft Sown x Tmid := by simpa [hT]
            have hGmidEq : Gmid' = updateG Gmid eMid Lmid := by
              calc
                Gmid' = updateG Gmid e L := hMid'
                _ = updateG Gmid e Lmid := by simpa [hL]
                _ = updateG Gmid eMid Lmid := by simpa [hEqE]
            simpa [hSownEq, hGmidEq] using
              (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown') (G:=Gmid'))
          · intro y hy
            cases hy
          · intro y Ty hy
            cases hy

-- Branch Case

/-- Constructive middle-frame preservation for a `branch` step. -/
lemma preserved_sub_middle_branch
    {Gstore Gleft Gmid Gright G : GEnv} {D D' : DEnv}
    {Ssh : SEnv} {Sown : OwnedEnv}
    {store : VarStore} {bufs bufs' : Buffers}
    {k : Var} {procs : List (Label × Process)} {e : Endpoint} {source : Role}
    {bs : List (Label × LocalType)} {ℓ : Label} {P : Process} {L : LocalType}
    {G' : GEnv}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    OwnedDisjoint Sown →
    DisjointG Gleft Gmid →
    G = Gleft ++ Gmid ++ Gright →
    lookupStr store k = some (.chan e) →
    lookupG G e = some (.branch source bs) →
    procs.find? (fun b => b.1 == ℓ) = some (ℓ, P) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    G' = updateG G e L →
    TypedStep G D Ssh Sown store bufs (.branch k procs) G' D' Sown store bufs' P →
    HasTypeProcPreOut Ssh Sown Gmid (.branch k procs) Sfin Gfin W Δ →
    ∃ Gmid' W' Δ', G' = Gleft ++ Gmid' ++ Gright ∧
      SessionsOf Gmid' ⊆ SessionsOf Gmid ∧
      HasTypeProcPreOut Ssh Sown Gmid' P Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hStore hOwn hDisjLM hEqG hkStore hGstep hFindPstep hFindTstep hGupd hTS hPre
  cases hTS with
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      cases hPre with
      | branch hkMid hGmid hLen hLbl hPreBodies hPost hSess hDom hRight =>
          rename_i eMid p bsMid
          have hEqE : e = eMid :=
            endpoint_eq_of_store_visible_all
              (Gstore:=Gstore) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
              (k:=k) (e:=e) (e':=eMid) hStore hOwn hkStore hkMid
          have hMid : lookupG Gmid e = some (.branch p bsMid) := by
            simpa [hEqE] using hGmid
          have hNoneLeft : lookupG Gleft e = none :=
            lookupG_none_of_disjoint (G₁:=Gleft) (G₂:=Gmid) hDisjLM hMid
          -- Branch Case: Align Middle Lookup with Framed Global Lookup
          have hFullMid : lookupG G e = some (.branch p bsMid) := by
            calc
              lookupG G e = lookupG (Gleft ++ Gmid ++ Gright) e := by simpa [hEqG]
              _ = some (.branch p bsMid) :=
                lookupG_middle_to_full (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
                  (e:=e) (L0:=.branch p bsMid) hNoneLeft hMid
          have hBranchEq : LocalType.branch source bs = LocalType.branch p bsMid := by
            exact Option.some.inj (by simpa [hGstep] using hFullMid)
          have hBs : bs = bsMid := by
            cases hBranchEq
            rfl
          have hFindTmid : bsMid.find? (fun b => b.1 == ℓ) = some (ℓ, L) := by
            simpa [hBs] using hFindTstep
          have hPre' : HasTypeProcPreOut Ssh Sown (updateG Gmid eMid L) P Sfin Gfin W Δ :=
            hPost ℓ P L hFindPstep hFindTmid
          have hGupd' : G' = updateG (Gleft ++ Gmid ++ Gright) e L := by
            simpa [hEqG] using hGupd
          obtain ⟨Gmid', hEqG', hMid'⟩ :=
            updateG_middle_witness (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
              (G':=G') (e:=e) (L0:=.branch p bsMid) (L:=L) hNoneLeft hMid hGupd'
          -- Branch Case: Package Framed Post-State Witness
          have hSubSess : SessionsOf Gmid' ⊆ SessionsOf Gmid := by
            rw [hMid']
            exact SessionsOf_subset_middle_update (Gmid:=Gmid) (e:=e)
              (L0:=.branch p bsMid) (L:=L) hMid
          -- Branch Case: Final Framed Witness
          refine ⟨Gmid', W, Δ, hEqG', hSubSess, ?_, FootprintSubset_refl, SEnvDomSubset_refl⟩
          have hGmidEq : Gmid' = updateG Gmid eMid L := by
            simpa [hEqE] using hMid'
          simpa [hGmidEq] using hPre'

-- Assign Case

/-- Constructive middle-frame preservation for an `assign` step. -/
lemma preserved_sub_middle_assign
    {Gleft Gmid Gright G G' : GEnv} {D : DEnv}
    {Ssh : SEnv} {Sown Sown' : OwnedEnv}
    {store store' : VarStore} {bufs : Buffers}
    {x : Var} {v : Value} {Tstep : ValType}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointG Gleft Gmid →
    G = Gleft ++ Gmid ++ Gright →
    G' = G →
    Sown' = OwnedEnv.updateLeft Sown x Tstep →
    HasTypeVal G v Tstep →
    TypedStep G D Ssh Sown store bufs (.assign x v) G' D Sown' store' bufs .skip →
    HasTypeProcPreOut Ssh Sown Gmid (.assign x v) Sfin Gfin W Δ →
    ∃ Gmid' W' Δ', G' = Gleft ++ Gmid' ++ Gright ∧
      SessionsOf Gmid' ⊆ SessionsOf Gmid ∧
      HasTypeProcPreOut Ssh Sown' Gmid' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hDisjLM hEqG hEqG' hSownUpd hvStep hTS hPre
  cases hTS with
  | assign hv hSout hStoreOut =>
      cases hPre with
      | assign_new hNoSh hNoOwnL hvMid =>
          rename_i Tpre
          have hvG : HasTypeVal G v Tstep := hvStep
          have hvGmid : HasTypeVal G v Tpre := by
            refine HasTypeVal_mono Gmid G v Tpre hvMid ?_
            intro e L hLookMid
            have hNoneLeft : lookupG Gleft e = none :=
              lookupG_none_of_disjoint (G₁:=Gleft) (G₂:=Gmid) hDisjLM hLookMid
            have hLookFull :
                lookupG (Gleft ++ Gmid ++ Gright) e = some L :=
              lookupG_middle_to_full (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
                (e:=e) (L0:=L) hNoneLeft hLookMid
            simpa [hEqG] using hLookFull
          have hEqT : Tpre = Tstep := HasTypeVal_unique hvGmid hvG
          have hSownEq : Sown' = OwnedEnv.updateLeft Sown x Tpre := by
            calc
              Sown' = OwnedEnv.updateLeft Sown x Tstep := hSownUpd
              _ = OwnedEnv.updateLeft Sown x Tpre := by simpa [hEqT]
          refine ⟨Gmid, [], ∅, by simpa [hEqG'] using hEqG, by intro s hs; exact hs, ?_, ?_, ?_⟩
          · simpa [hSownEq] using
              (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown') (G:=Gmid))
          · intro y hy
            cases hy
          · intro y Ty hy
            cases hy
      -- Assign Case (`assign_old`)
      | assign_old hNoSh hOwnL hvMid =>
          rename_i Tpre Told
          have hvG : HasTypeVal G v Tstep := hvStep
          have hvGmid : HasTypeVal G v Tpre := by
            refine HasTypeVal_mono Gmid G v Tpre hvMid ?_
            intro e L hLookMid
            have hNoneLeft : lookupG Gleft e = none :=
              lookupG_none_of_disjoint (G₁:=Gleft) (G₂:=Gmid) hDisjLM hLookMid
            have hLookFull :
                lookupG (Gleft ++ Gmid ++ Gright) e = some L :=
              lookupG_middle_to_full (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
                (e:=e) (L0:=L) hNoneLeft hLookMid
            simpa [hEqG] using hLookFull
          have hEqT : Tpre = Tstep := HasTypeVal_unique hvGmid hvG
          have hSownEq : Sown' = OwnedEnv.updateLeft Sown x Tpre := by
            calc
              Sown' = OwnedEnv.updateLeft Sown x Tstep := hSownUpd
              _ = OwnedEnv.updateLeft Sown x Tpre := by simpa [hEqT]
          refine ⟨Gmid, [], ∅, by simpa [hEqG'] using hEqG, by intro s hs; exact hs, ?_, ?_, ?_⟩
          · simpa [hSownEq] using
              (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown') (G:=Gmid))
          · intro y hy
            cases hy
          · intro y Ty hy
            cases hy

-- Sequential Cases

/-- Constructive middle-frame preservation for `seq_skip`. -/
lemma preserved_sub_middle_seq_skip
    {Gleft Gmid Gright G : GEnv} {D : DEnv}
    {Ssh : SEnv} {Sown : OwnedEnv}
    {store : VarStore} {bufs : Buffers}
    {Q : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    G = Gleft ++ Gmid ++ Gright →
    TypedStep G D Ssh Sown store bufs (.seq .skip Q) G D Sown store bufs Q →
    HasTypeProcPreOut Ssh Sown Gmid (.seq .skip Q) Sfin Gfin W Δ →
    ∃ Gmid' W' Δ', G = Gleft ++ Gmid' ++ Gright ∧
      SessionsOf Gmid' ⊆ SessionsOf Gmid ∧
      HasTypeProcPreOut Ssh Sown Gmid' Q Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hEqG hTS hPre
  cases hTS with
  | seq_skip =>
      cases hPre with
      | seq hP hQ =>
          rename_i W₁ W₂ Δ₁ Δ₂
          cases hP
          refine ⟨Gmid, W₂, Δ₂, hEqG, ?_, ?_, ?_, ?_⟩
          · intro s hs
            exact hs
          · simpa using hQ
          · simpa using (FootprintSubset_refl (W:=W₂))
          · simpa using (SEnvDomSubset_append_right (S₁:=∅) (S₂:=Δ₂))

-- Sequential Case: `seq_step` via Recursive Middle Goal

/-- Constructive middle-frame preservation for `seq_step`, assuming recursive middle preservation. -/
lemma preserved_sub_middle_seq_step
    {Gstore Gleft Gmid Gright G G' : GEnv} {D D' : DEnv}
    {Ssh : SEnv} {Sown Sown' : OwnedEnv}
    {store store' : VarStore} {bufs bufs' : Buffers}
    {P P' Q : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    DisjointG Gleft Gmid →
    DisjointG Gleft Gright →
    DisjointG Gmid Gright →
    G = Gleft ++ Gmid ++ Gright →
    (hStep : TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P') →
    MiddleFrameGoal (hTS := hStep) →
    DisjointS Sown.right Sfin.left →
    HasTypeProcPreOut Ssh Sown Gmid (.seq P Q) Sfin Gfin W Δ →
    ∃ Gmid' W' Δ', G' = Gleft ++ Gmid' ++ Gright ∧
      SessionsOf Gmid' ⊆ SessionsOf Gmid ∧
      HasTypeProcPreOut Ssh Sown' Gmid' (.seq P' Q) Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hStore hDisjShAll hOwn hDisjLM hDisjLR hDisjMR hEqG hStep hMiddle hDisjRightFin hPre
  cases hPre with
  | seq hP hQ =>
      rename_i S₁ G₁ W₁ W₂ Δ₁ Δ₂
      have hDomQ : SEnvDomSubset S₁.left Sfin.left := HasTypeProcPreOut_domsubset hQ
      have hDisjRightMid : DisjointS Sown.right S₁.left :=
        DisjointS_of_domsubset_right hDomQ hDisjRightFin
      obtain ⟨Gmid₁, W₁', Δ₁', hEqG₁, hSubSess, hP', hSubW, hSubΔ⟩ :=
        hMiddle
          (Gstore:=Gstore) (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
          (Sfin:=S₁) (Gfin:=G₁) (W:=W₁) (Δ:=Δ₁)
          hStore hDisjShAll hOwn hDisjLM hDisjLR hDisjMR hEqG
          hDisjRightMid hP
      refine ⟨Gmid₁, W₁' ++ W₂, Δ₁' ++ Δ₂, hEqG₁, hSubSess, ?_, ?_, ?_⟩
      · exact HasTypeProcPreOut.seq hP' hQ
      · exact FootprintSubset_append_left hSubW
      · exact SEnvDomSubset_append_left_of_domsubset hSubΔ

-- Parallel Helper Lemmas

lemma ParSplit.sides_eq_of_len
    {S : SEnv} {G₁ G₂ : GEnv}
    (split₁ : ParSplit S G₁) (split₂ : ParSplit S G₂) :
    split₁.S1.length = split₂.S1.length →
    split₁.S1 = split₂.S1 ∧ split₁.S2 = split₂.S2 := by
  intro hLen
  have hSeq : split₁.S1 ++ split₁.S2 = split₂.S1 ++ split₂.S2 := by
    calc
      split₁.S1 ++ split₁.S2 = S := by simpa [split₁.hS]
      _ = split₂.S1 ++ split₂.S2 := by simpa [split₂.hS]
  exact ⟨List.append_inj_left hSeq hLen, List.append_inj_right hSeq hLen⟩

lemma StoreTyped_par_left_inner
    {Gstore : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv}
    {split : ParSplit Sown.left G} {store : VarStore} :
    DisjointS split.S1 split.S2 →
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    StoreTyped Gstore (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store := by
  intro hDisj hStore x v T hx hLookup
  have hInner :
      lookupSEnv (SEnvAll (Ssh ++ Sown.right) (split.S2 ++ (split.S1 ++ ([] : SEnv)))) x = some T := by
    simpa [SEnvAll, List.append_assoc] using hLookup
  have hSwap :=
    lookupSEnv_swap_left_prefix
      (Ssh:=Ssh ++ Sown.right) (S₁:=split.S1) (S₂:=split.S2) (S₃:=[]) hDisj x
  have hSwap' :
      lookupSEnv (Ssh ++ (Sown.right ++ (split.S1 ++ split.S2))) x =
        lookupSEnv (Ssh ++ (Sown.right ++ (split.S2 ++ split.S1))) x := by
    simpa [SEnvAll, List.append_assoc] using hSwap
  have hOuter' :
      lookupSEnv (Ssh ++ (Sown.right ++ (split.S1 ++ split.S2))) x = some T := by
    simpa [hSwap'] using hInner
  have hOuter : lookupSEnv (SEnvAll Ssh Sown) x = some T := by
    simpa [SEnvAll, split.hS, List.append_assoc] using hOuter'
  exact hStore x v T hx hOuter


end
