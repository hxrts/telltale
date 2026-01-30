import Protocol.Typing.Part6
import Batteries.Data.RBMap.Lemmas

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
open Batteries

noncomputable section

/-! ## Preservation Theorems -/

/-- TypedStep preserves coherence.

    **Proof strategy**: Case analysis on TypedStep constructor:
    - `send`: Use `Coherent_send_preserved` with hRecvReady derived from coherence
    - `recv`: Use `Coherent_recv_preserved`
    - `assign`: G and D unchanged
    - `seq_step`, `seq_skip`: IH or G/D unchanged
    - `par_*`: Disjoint resources remain coherent -/
theorem typed_step_preserves_coherence {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    Coherent G D →
    Coherent G' D'
  | @TypedStep.send G D Ssh Sown store bufs k x e target T L v sendEdge Gout Dout bufsOut hk hx hG hS hv hRecvReady hEdge hGout hDout hBufsOut, hCoh => by
    -- Use Coherent_send_preserved with explicit arguments
    -- After rewriting with the equalities, Gout = updateG G e L and Dout = appendD D sendEdge T
    rw [hGout, hDout, hEdge]
    unfold appendD
    exact @Coherent_send_preserved G D e target T L hCoh hG hRecvReady
  | @TypedStep.recv G D Ssh Sown store bufs k x e source T L v vs recvEdge Gout Dout SownOut storeOut bufsOut hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut, hCoh => by
    -- Use Coherent_recv_preserved with explicit arguments
    rw [hGout, hDout]
    have hTrace' : (lookupD D { sid := e.sid, sender := source, receiver := e.role }).head? = some T := by
      rw [← hEdge]; exact hTrace
    rw [hEdge]
    exact @Coherent_recv_preserved G D e source T L hCoh hG hTrace'
  | @TypedStep.select G D Ssh Sown store bufs k ℓ e target bs L selectEdge Gout Dout bufsOut hk hG hFind hTargetReady hEdge hGout hDout hBufsOut, hCoh => by
    -- Use Coherent_select_preserved with explicit arguments
    rw [hGout, hDout, hEdge]
    unfold appendD
    exact @Coherent_select_preserved G D e target bs ℓ L hCoh hG hFind hTargetReady
  | @TypedStep.branch G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge Gout Dout bufsOut hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut, hCoh => by
    -- Use Coherent_branch_preserved with explicit arguments
    have hTrace' : (lookupD D { sid := e.sid, sender := source, receiver := e.role }).head? = some .string := by
      rw [← hEdge]; exact hTrace
    rw [hGout, hDout, hEdge]
    exact @Coherent_branch_preserved G D e source bs ℓ L hCoh hG hFindT hTrace'
  | .assign _ _ _, hCoh => by
    -- G and D unchanged
    exact hCoh
  | .seq_step hTS, hCoh =>
    -- Inductive hypothesis on sub-transition
    typed_step_preserves_coherence hTS hCoh
  | .seq_skip, hCoh =>
    -- No change
    hCoh
  | @TypedStep.par_left Ssh store bufs store' bufs' P P' Q S G D₁ D₂ G₁' D₁' S₁' split
      hTS hDisjG hDisjD hDisjS hConsL hConsR, hCoh => by
    -- Left transition preserves its part, right unchanged.
    have hCohMerged : Coherent (split.G1 ++ split.G2) (D₁ ++ D₂) := by
      simpa [split.hG] using hCoh
    have hCohL : Coherent split.G1 D₁ := Coherent_split_left hCohMerged hDisjG
    have hCohL' : Coherent G₁' D₁' := typed_step_preserves_coherence hTS hCohL
    have hCohR : Coherent split.G2 D₂ := Coherent_split_right hCohMerged hDisjG hConsL
    have hSubG : SessionsOf G₁' ⊆ SessionsOf split.G1 := SessionsOf_subset_of_TypedStep hTS
    have hDisjG' : DisjointG G₁' split.G2 := DisjointG_of_subset_left hSubG hDisjG
    have hSubD : SessionsOfD D₁' ⊆ SessionsOf split.G1 := by
      intro s hs
      have hs' : s ∈ SessionsOfD D₁ ∪ SessionsOf split.G1 := SessionsOfD_subset_of_TypedStep hTS hs
      cases hs' with
      | inl hD1 => exact hConsL hD1
      | inr hG1 => exact hG1
    intro e Lrecv hGrecv
    set senderEp : Endpoint := { sid := e.sid, role := e.sender }
    set recvEp : Endpoint := { sid := e.sid, role := e.receiver }
    have hInvRecv := lookupG_append_inv (G₁:=G₁') (G₂:=split.G2) (e:=recvEp) hGrecv
    cases hInvRecv with
    | inl hRecvLeft =>
        have hSidLeft : e.sid ∈ SessionsOf G₁' := ⟨recvEp, Lrecv, hRecvLeft, rfl⟩
        have hD2none : D₂.find? e = none := lookupD_none_of_disjointG hDisjG' hConsR hSidLeft
        have hTraceEq : lookupD (D₁' ++ D₂) e = lookupD D₁' e :=
          lookupD_append_left_of_right_none (D₁:=D₁') (D₂:=D₂) (e:=e) hD2none
        have hCohEdge := hCohL' e Lrecv hRecvLeft
        rcases hCohEdge with ⟨Lsender, hGsenderLeft, hConsume⟩
        have hGsenderMerged : lookupG (G₁' ++ split.G2) senderEp = some Lsender :=
          lookupG_append_left (G₁:=G₁') (G₂:=split.G2) hGsenderLeft
        refine ⟨Lsender, hGsenderMerged, ?_⟩
        simpa [hTraceEq] using hConsume
    | inr hRecvRight =>
        have hSidRight : e.sid ∈ SessionsOf split.G2 := ⟨recvEp, Lrecv, hRecvRight.2, rfl⟩
        have hDisjGsym : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
        have hD1none : D₁'.find? e = none :=
          lookupD_none_of_disjointG (G₁:=split.G2) (G₂:=split.G1) (D₂:=D₁') hDisjGsym hSubD hSidRight
        have hTraceEq : lookupD (D₁' ++ D₂) e = lookupD D₂ e :=
          lookupD_append_right (D₁:=D₁') (D₂:=D₂) (e:=e) hD1none
        have hCohEdge := hCohR e Lrecv hRecvRight.2
        rcases hCohEdge with ⟨Lsender, hGsenderRight, hConsume⟩
        have hNot : e.sid ∉ SessionsOf G₁' := by
          intro hIn
          have hInter : e.sid ∈ SessionsOf G₁' ∩ SessionsOf split.G2 := ⟨hIn, hSidRight⟩
          have hEmpty : SessionsOf G₁' ∩ SessionsOf split.G2 = (∅ : Set SessionId) := hDisjG'
          have : e.sid ∈ (∅ : Set SessionId) := by
            simpa [hEmpty] using hInter
          exact this.elim
        have hG1none : lookupG G₁' senderEp = none := lookupG_none_of_not_session hNot
        have hSenderEq := lookupG_append_right (G₁:=G₁') (G₂:=split.G2) (e:=senderEp) hG1none
        have hGsenderMerged : lookupG (G₁' ++ split.G2) senderEp = some Lsender := by
          simpa [hSenderEq] using hGsenderRight
        refine ⟨Lsender, hGsenderMerged, ?_⟩
        simpa [hTraceEq] using hConsume
  | @TypedStep.par_right Ssh store bufs store' bufs' P Q Q' S G D₁ D₂ G₂' D₂' S₂' split
      hTS hDisjG hDisjD hDisjS hConsL hConsR, hCoh => by
    -- Right transition preserves its part, left unchanged.
    have hCohMerged : Coherent (split.G1 ++ split.G2) (D₁ ++ D₂) := by
      simpa [split.hG] using hCoh
    have hCohL : Coherent split.G1 D₁ := Coherent_split_left hCohMerged hDisjG
    have hCohR : Coherent split.G2 D₂ := Coherent_split_right hCohMerged hDisjG hConsL
    have hCohR' : Coherent G₂' D₂' := typed_step_preserves_coherence hTS hCohR
    have hSubG : SessionsOf G₂' ⊆ SessionsOf split.G2 := SessionsOf_subset_of_TypedStep hTS
    have hDisjG' : DisjointG split.G1 G₂' := by
      -- reuse subset on the right
      have hDisjGsym : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
      have hDisjG'' : DisjointG G₂' split.G1 := DisjointG_of_subset_left hSubG hDisjGsym
      exact DisjointG_symm hDisjG''
    have hSubD : SessionsOfD D₂' ⊆ SessionsOf split.G2 := by
      intro s hs
      have hs' : s ∈ SessionsOfD D₂ ∪ SessionsOf split.G2 := SessionsOfD_subset_of_TypedStep hTS hs
      cases hs' with
      | inl hD2 => exact hConsR hD2
      | inr hG2 => exact hG2
    intro e Lrecv hGrecv
    set senderEp : Endpoint := { sid := e.sid, role := e.sender }
    set recvEp : Endpoint := { sid := e.sid, role := e.receiver }
    have hInvRecv := lookupG_append_inv (G₁:=split.G1) (G₂:=G₂') (e:=recvEp) hGrecv
    cases hInvRecv with
    | inl hRecvLeft =>
        have hSidLeft : e.sid ∈ SessionsOf split.G1 := ⟨recvEp, Lrecv, hRecvLeft, rfl⟩
        have hD2none : D₂'.find? e = none :=
          lookupD_none_of_disjointG (G₁:=split.G1) (G₂:=split.G2) (D₂:=D₂') hDisjG hSubD hSidLeft
        have hTraceEq : lookupD (D₁ ++ D₂') e = lookupD D₁ e :=
          lookupD_append_left_of_right_none (D₁:=D₁) (D₂:=D₂') (e:=e) hD2none
        have hCohEdge := hCohL e Lrecv hRecvLeft
        rcases hCohEdge with ⟨Lsender, hGsenderLeft, hConsume⟩
        have hGsenderMerged : lookupG (split.G1 ++ G₂') senderEp = some Lsender :=
          lookupG_append_left (G₁:=split.G1) (G₂:=G₂') hGsenderLeft
        refine ⟨Lsender, hGsenderMerged, ?_⟩
        simpa [hTraceEq] using hConsume
    | inr hRecvRight =>
        have hSidRight : e.sid ∈ SessionsOf G₂' := ⟨recvEp, Lrecv, hRecvRight.2, rfl⟩
        have hDisjGsym : DisjointG G₂' split.G1 := DisjointG_symm hDisjG'
        have hD1none : D₁.find? e = none :=
          lookupD_none_of_disjointG (G₁:=G₂') (G₂:=split.G1) (D₂:=D₁) hDisjGsym hConsL hSidRight
        have hTraceEq : lookupD (D₁ ++ D₂') e = lookupD D₂' e :=
          lookupD_append_right (D₁:=D₁) (D₂:=D₂') (e:=e) hD1none
        have hCohEdge := hCohR' e Lrecv hRecvRight.2
        rcases hCohEdge with ⟨Lsender, hGsenderRight, hConsume⟩
        have hNot : e.sid ∉ SessionsOf split.G1 := by
          intro hIn
          have hInter : e.sid ∈ SessionsOf split.G1 ∩ SessionsOf G₂' := ⟨hIn, hSidRight⟩
          have hEmpty : SessionsOf split.G1 ∩ SessionsOf G₂' = (∅ : Set SessionId) := hDisjG'
          have : e.sid ∈ (∅ : Set SessionId) := by
            simpa [hEmpty] using hInter
          exact this.elim
        have hG1none : lookupG split.G1 senderEp = none := lookupG_none_of_not_session hNot
        have hSenderEq := lookupG_append_right (G₁:=split.G1) (G₂:=G₂') (e:=senderEp) hG1none
        have hGsenderMerged : lookupG (split.G1 ++ G₂') senderEp = some Lsender := by
          simpa [hSenderEq] using hGsenderRight
        refine ⟨Lsender, hGsenderMerged, ?_⟩
        simpa [hTraceEq] using hConsume
  | .par_skip_left, hCoh =>
    hCoh
  | .par_skip_right, hCoh =>
    hCoh

/-! ## StoreTypedStrong Preservation -/

/- Updating a key already present in the left SEnv only affects the left side. -/
private theorem updateSEnv_append_left_of_left {S₁ S₂ : SEnv} {x : Var} {T T' : ValType}
    (hLeft : lookupSEnv S₁ x = some T') :
    updateSEnv (S₁ ++ S₂) x T = updateSEnv S₁ x T ++ S₂ := by
  induction S₁ with
  | nil =>
      simp [lookupSEnv] at hLeft
  | cons hd tl ih =>
      cases hd with
      | mk y U =>
          by_cases hxy : x = y
          · simp [updateSEnv, hxy]
          · have hLeft' : lookupSEnv tl x = some T' := by
              have hbeq : (x == y) = false := by
                exact beq_eq_false_iff_ne.mpr hxy
              simpa [lookupSEnv, List.lookup, hbeq] using hLeft
            simp [updateSEnv, hxy, ih hLeft']

private lemma lookupSEnv_update_append_neq
    {S₁ S₂ : SEnv} {x y : Var} {T : ValType} (hxy : y ≠ x) :
    lookupSEnv (updateSEnv S₁ x T ++ S₂) y = lookupSEnv (S₁ ++ S₂) y := by
  cases hL : lookupSEnv S₁ y with
  | some Ty =>
      have hL' : lookupSEnv (updateSEnv S₁ x T) y = some Ty := by
        simpa [hL] using
          (lookupSEnv_update_neq (env:=S₁) (x:=x) (y:=y) (T:=T) (Ne.symm hxy))
      have hLeft : lookupSEnv (updateSEnv S₁ x T ++ S₂) y = some Ty :=
        lookupSEnv_append_left hL'
      have hLeft' : lookupSEnv (S₁ ++ S₂) y = some Ty :=
        lookupSEnv_append_left hL
      simpa [hLeft'] using hLeft
  | none =>
      have hL' : lookupSEnv (updateSEnv S₁ x T) y = none := by
        simpa [hL] using
          (lookupSEnv_update_neq (env:=S₁) (x:=x) (y:=y) (T:=T) (Ne.symm hxy))
      have hRight : lookupSEnv (updateSEnv S₁ x T ++ S₂) y = lookupSEnv S₂ y :=
        lookupSEnv_append_right hL'
      have hRight' : lookupSEnv (S₁ ++ S₂) y = lookupSEnv S₂ y :=
        lookupSEnv_append_right hL
      simpa [hRight'] using hRight

private lemma lookupSEnv_SEnvAll_update_neq
    {Ssh Sown S₂ : SEnv} {x y : Var} {T : ValType} (hxy : y ≠ x) :
    lookupSEnv (SEnvAll Ssh (updateSEnv Sown x T ++ S₂)) y =
      lookupSEnv (SEnvAll Ssh (Sown ++ S₂)) y := by
  cases hS : lookupSEnv Ssh y with
  | some Ty =>
      have hLeft : lookupSEnv (SEnvAll Ssh (updateSEnv Sown x T ++ S₂)) y = some Ty :=
        lookupSEnv_append_left hS
      have hLeft' : lookupSEnv (SEnvAll Ssh (Sown ++ S₂)) y = some Ty :=
        lookupSEnv_append_left hS
      simpa [hLeft'] using hLeft
  | none =>
      have hRight :
          lookupSEnv (SEnvAll Ssh (updateSEnv Sown x T ++ S₂)) y =
            lookupSEnv (updateSEnv Sown x T ++ S₂) y :=
        lookupSEnv_append_right hS
      have hRight' :
          lookupSEnv (SEnvAll Ssh (Sown ++ S₂)) y =
            lookupSEnv (Sown ++ S₂) y :=
        lookupSEnv_append_right hS
      have hUpd := lookupSEnv_update_append_neq (S₁:=Sown) (S₂:=S₂) (x:=x) (y:=y) (T:=T) hxy
      simpa [hRight, hRight'] using hUpd

private lemma lookupSEnv_comm_of_disjoint {S₁ S₂ : SEnv} (hDisj : DisjointS S₁ S₂) :
    ∀ x, lookupSEnv (S₁ ++ S₂) x = lookupSEnv (S₂ ++ S₁) x := by
  intro x
  cases hLeft : lookupSEnv S₁ x with
  | some T =>
      have hNone : lookupSEnv S₂ x = none :=
        lookupSEnv_none_of_disjoint_left (S₁:=S₂) (S₂:=S₁) (x:=x) (T:=T)
          (DisjointS_symm hDisj) hLeft
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
      have hLeft :=
        lookupSEnv_append_right (S₁:=Ssh) (S₂:=((S₁ ++ S₂) ++ S₃)) (x:=x) hS
      have hRight :=
        lookupSEnv_append_right (S₁:=Ssh) (S₂:=(S₂ ++ (S₁ ++ S₃))) (x:=x) hS
      have hSwap :
          lookupSEnv ((S₁ ++ S₂) ++ S₃) x = lookupSEnv (S₂ ++ (S₁ ++ S₃)) x := by
        have hSwap' := lookupSEnv_swap_left (S₁:=S₁) (S₂:=S₂) (S₃:=S₃) hDisj x
        simpa [List.append_assoc] using hSwap'
      have hLeft' :
          lookupSEnv (Ssh ++ (S₁ ++ (S₂ ++ S₃))) x = lookupSEnv (S₁ ++ (S₂ ++ S₃)) x := by
        simpa [List.append_assoc] using hLeft
      have hSwap' :
          lookupSEnv (S₁ ++ (S₂ ++ S₃)) x = lookupSEnv (S₂ ++ (S₁ ++ S₃)) x := by
        simpa [List.append_assoc] using hSwap
      simpa [SEnvAll, hLeft', hRight, hSwap']

axiom DisjointS_preserved_TypedStep_right
    {G D Ssh S2 store bufs Q G' D' S2' store' bufs' Q' S1} :
    TypedStep G D Ssh S2 store bufs Q G' D' S2' store' bufs' Q' →
    DisjointS S1 S2 →
    DisjointS S1 S2'

private lemma StoreTyped_rewriteG {G G' : GEnv} {S : SEnv} {store : Store}
    (hMono : ∀ e L, lookupG G e = some L → lookupG G' e = some L) :
    StoreTyped G S store → StoreTyped G' S store := by
  intro hStore x v T hStr hS
  exact HasTypeVal_mono G G' v T (hStore x v T hStr hS) hMono

private lemma StoreTyped_rewriteS {G : GEnv} {S S' : SEnv} {store : Store}
    (hEq : ∀ x, lookupSEnv S x = lookupSEnv S' x) :
    StoreTyped G S store → StoreTyped G S' store := by
  intro hStore x v T hStr hS'
  have hS : lookupSEnv S x = some T := by
    simpa [hEq x] using hS'
  exact hStore x v T hStr hS

private lemma StoreTyped_weakenS {G : GEnv} {S S' : SEnv} {store : Store}
    (hMono : ∀ x T, lookupSEnv S' x = some T → lookupSEnv S x = some T) :
    StoreTyped G S store → StoreTyped G S' store := by
  intro hStore x v T hStr hS'
  exact hStore x v T hStr (hMono x T hS')

private lemma StoreTypedStrong_rewriteG {G G' : GEnv} {S : SEnv} {store : Store}
    (hEq : ∀ e, lookupG G e = lookupG G' e) :
    StoreTypedStrong G S store → StoreTypedStrong G' S store := by
  intro hStore
  refine ⟨?_, ?_⟩
  · intro x
    exact hStore.sameDomain x
  ·
    apply StoreTyped_rewriteG (G:=G) (G':=G') (S:=S)
      (hMono:=by
        intro e L hLookup
        simpa [hEq e] using hLookup)
    exact hStore.typeCorr

private lemma StoreTypedStrong_rewriteS {G : GEnv} {S S' : SEnv} {store : Store}
    (hEq : ∀ x, lookupSEnv S x = lookupSEnv S' x) :
    StoreTypedStrong G S store → StoreTypedStrong G S' store := by
  intro hStore
  refine ⟨?_, ?_⟩
  · intro x
    simpa [hEq x] using hStore.sameDomain x
  ·
    apply StoreTyped_rewriteS (G:=G) (S:=S) (S':=S') hEq
    exact hStore.typeCorr

private lemma lookupG_none_of_disjoint_early {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂)
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
          have hInter' := hInter
          simp [hEmpty] at hInter'
        exact this.elim

private lemma lookupG_comm_of_disjoint_early {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂) :
    ∀ e, lookupG (G₁ ++ G₂) e = lookupG (G₂ ++ G₁) e := by
  intro e
  cases hLeft : lookupG G₁ e with
  | some L =>
      have hNone : lookupG G₂ e = none :=
        lookupG_none_of_disjoint_early (G₁:=G₂) (G₂:=G₁) (DisjointG_symm hDisj) (e:=e) (L:=L) hLeft
      have hA := lookupG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hLeft
      have hB := lookupG_append_right (G₁:=G₂) (G₂:=G₁) (e:=e) hNone
      simpa [hA, hB, hLeft]
  | none =>
      have hA := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hLeft
      cases hRight : lookupG G₂ e with
      | some L =>
          have hB := lookupG_append_left (G₁:=G₂) (G₂:=G₁) (e:=e) (L:=L) hRight
          simpa [hA, hB, hRight]
      | none =>
          have hB := lookupG_append_right (G₁:=G₂) (G₂:=G₁) (e:=e) hRight
          simpa [hA, hB, hRight, hLeft]

private lemma lookupG_swap_left {G₁ G₂ G₃ : GEnv} (hDisj : DisjointG G₁ G₂) :
    ∀ e, lookupG ((G₁ ++ G₂) ++ G₃) e = lookupG ((G₂ ++ G₁) ++ G₃) e := by
  intro e
  cases hLeft : lookupG (G₁ ++ G₂) e with
  | some L =>
      have hA := lookupG_append_left (G₁:=G₁ ++ G₂) (G₂:=G₃) (e:=e) (L:=L) hLeft
      have hSwap := lookupG_comm_of_disjoint_early hDisj e
      have hLeft' : lookupG (G₂ ++ G₁) e = some L := by
        simpa [hSwap] using hLeft
      have hB := lookupG_append_left (G₁:=G₂ ++ G₁) (G₂:=G₃) (e:=e) (L:=L) hLeft'
      have hA' : lookupG (G₁ ++ (G₂ ++ G₃)) e = some L := by
        simpa [List.append_assoc] using hA
      have hB' : lookupG (G₂ ++ (G₁ ++ G₃)) e = some L := by
        simpa [List.append_assoc] using hB
      simpa [hA', hB']
  | none =>
      have hA := lookupG_append_right (G₁:=G₁ ++ G₂) (G₂:=G₃) (e:=e) hLeft
      have hSwap := lookupG_comm_of_disjoint_early hDisj e
      have hNone : lookupG (G₂ ++ G₁) e = none := by
        simpa [hSwap] using hLeft
      have hB := lookupG_append_right (G₁:=G₂ ++ G₁) (G₂:=G₃) (e:=e) hNone
      have hA' : lookupG (G₁ ++ (G₂ ++ G₃)) e = lookupG G₃ e := by
        simpa [List.append_assoc] using hA
      have hB' : lookupG (G₂ ++ (G₁ ++ G₃)) e = lookupG G₃ e := by
        simpa [List.append_assoc] using hB
      simpa [hA', hB']

private lemma StoreTypedStrong_swap_G_left {G₁ G₂ G₃ : GEnv} {S : SEnv} {store : Store}
    (hDisj : DisjointG G₁ G₂) :
    StoreTypedStrong ((G₁ ++ G₂) ++ G₃) S store →
    StoreTypedStrong ((G₂ ++ G₁) ++ G₃) S store := by
  intro hStore
  apply StoreTypedStrong_rewriteG (G:=((G₁ ++ G₂) ++ G₃)) (G':=((G₂ ++ G₁) ++ G₃))
    (by
      intro e
      exact lookupG_swap_left (G₁:=G₁) (G₂:=G₂) (G₃:=G₃) hDisj e)
  exact hStore

private lemma StoreTypedStrong_swap_S_left_prefix
    {Ssh S₁ S₂ S₃ : SEnv} {G : GEnv} {store : Store}
    (hDisj : DisjointS S₁ S₂) :
    StoreTypedStrong G (SEnvAll Ssh ((S₁ ++ S₂) ++ S₃)) store →
    StoreTypedStrong G (SEnvAll Ssh (S₂ ++ (S₁ ++ S₃))) store := by
  intro hStore
  apply StoreTypedStrong_rewriteS
    (S:=SEnvAll Ssh ((S₁ ++ S₂) ++ S₃))
    (S':=SEnvAll Ssh (S₂ ++ (S₁ ++ S₃)))
    (by
      intro x
      exact lookupSEnv_swap_left_prefix (Ssh:=Ssh) (S₁:=S₁) (S₂:=S₂) (S₃:=S₃) hDisj x)
  exact hStore

/-- If a disjoint update environment contains x, the right side cannot. -/
private theorem lookupSEnv_none_of_disjoint_update
    {S₁ S₂ : SEnv} {x : Var} {T : ValType}
    (hDisj : DisjointS (updateSEnv S₁ x T) S₂) :
    lookupSEnv S₂ x = none := by
  -- Otherwise disjointness is violated at x.
  by_contra hSome
  cases hS2 : lookupSEnv S₂ x with
  | none => exact (hSome hS2).elim
  | some T₂ =>
      have hS1 : lookupSEnv (updateSEnv S₁ x T) x = some T := by
        simpa using (lookupSEnv_update_eq (env:=S₁) (x:=x) (T:=T))
      exact (hDisj x T T₂ hS1 hS2).elim

/-- Same-domain is preserved by a matching SEnv/store update. -/
private theorem StoreTypedStrong_sameDomain_update
    {S : SEnv} {store : Store} {x : Var} {T : ValType} {v : Value}
    (hDom : ∀ y, (lookupSEnv S y).isSome ↔ (lookupStr store y).isSome) :
    ∀ y, (lookupSEnv (updateSEnv S x T) y).isSome ↔
      (lookupStr (updateStr store x v) y).isSome := by
  -- Update is pointwise: only x changes.
  intro y
  by_cases hEq : y = x
  · subst hEq
    simp [lookupSEnv_update_eq, lookupStr_update_eq]
  · have hS : lookupSEnv (updateSEnv S x T) y = lookupSEnv S y := by
      simpa using (lookupSEnv_update_neq (env:=S) (x:=x) (y:=y) (T:=T) (Ne.symm hEq))
    have hStr : lookupStr (updateStr store x v) y = lookupStr store y := by
      simpa using (lookupStr_update_neq store x y v (Ne.symm hEq))
    simpa [hS, hStr] using hDom y

/-- StoreTypedStrong is stable under updating G at a single endpoint. -/
private theorem StoreTypedStrong_updateG
    {G : GEnv} {S : SEnv} {store : Store} {e : Endpoint} {L : LocalType}
    (hStore : StoreTypedStrong G S store) :
    StoreTypedStrong (updateG G e L) S store := by
  -- Same-domain is unchanged; typing weakens along updateG.
  refine ⟨?_, ?_⟩
  · intro x
    simpa using hStore.sameDomain x
  ·
    have hST : StoreTyped (updateG G e L) S store :=
      StoreTyped_send_preserved (G:=G) (S:=S) (store:=store) (e:=e) (L:=L) hStore.typeCorr
    exact hST

/-- Assignment preserves StoreTypedStrong on shared+owned SEnv. -/
private theorem StoreTypedStrong_assign_update
    {G : GEnv} {Ssh Sown : SEnv} {store : Store} {x : Var} {v : Value} {T : ValType}
    (hStore : StoreTypedStrong G (SEnvAll Ssh Sown) store)
    (hNone : lookupSEnv Ssh x = none)
    (hv : HasTypeVal G v T) :
    StoreTypedStrong G (SEnvAll Ssh (updateSEnv Sown x T)) (updateStr store x v) := by
  -- Same-domain updates pointwise; typing uses StoreTyped_assign_preserved.
  refine ⟨?_, ?_⟩
  ·
    have hDom := StoreTypedStrong_sameDomain_update (S:=SEnvAll Ssh Sown) (store:=store)
      (x:=x) (T:=T) (v:=v) hStore.sameDomain
    simpa [SEnvAll, updateSEnv_append_left hNone] using hDom
  ·
    have hST : StoreTyped G (updateSEnv (SEnvAll Ssh Sown) x T) (updateStr store x v) :=
      StoreTyped_assign_preserved (G:=G) (S:=SEnvAll Ssh Sown) (store:=store) (x:=x) (v:=v) (T:=T)
        hStore.typeCorr hv
    simpa [SEnvAll, updateSEnv_append_left hNone] using hST

/-- Receive preserves StoreTypedStrong on shared+owned SEnv. -/
private theorem StoreTypedStrong_recv_update
    {G : GEnv} {Ssh Sown : SEnv} {store : Store} {e : Endpoint} {L : LocalType}
    {x : Var} {v : Value} {T : ValType}
    (hStore : StoreTypedStrong G (SEnvAll Ssh Sown) store)
    (hNone : lookupSEnv Ssh x = none)
    (hv : HasTypeVal G v T) :
    StoreTypedStrong (updateG G e L) (SEnvAll Ssh (updateSEnv Sown x T)) (updateStr store x v) := by
  -- Same-domain updates pointwise; typing uses StoreTyped_recv_preserved.
  refine ⟨?_, ?_⟩
  ·
    have hDom := StoreTypedStrong_sameDomain_update (S:=SEnvAll Ssh Sown) (store:=store)
      (x:=x) (T:=T) (v:=v) hStore.sameDomain
    simpa [SEnvAll, updateSEnv_append_left hNone] using hDom
  ·
    have hST : StoreTyped (updateG G e L) (updateSEnv (SEnvAll Ssh Sown) x T) (updateStr store x v) :=
      StoreTyped_recv_preserved (G:=G) (S:=SEnvAll Ssh Sown) (store:=store) (e:=e) (L:=L)
        (x:=x) (v:=v) (T:=T) hStore.typeCorr hv
    simpa [SEnvAll, updateSEnv_append_left hNone] using hST

/-- Frame: send updates G on the left under a right context. -/
private theorem StoreTypedStrong_frame_send
    {G G₂ : GEnv} {Ssh Sown S₂ : SEnv} {store : Store}
    {e : Endpoint} {target : Role} {T : ValType} {L : LocalType}
    (hStore : StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store)
    (hG : lookupG G e = some (.send target T L)) :
    StoreTypedStrong (updateG G e L ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store := by
  -- Update G on the left; SEnv/store unchanged.
  have hStore' :
      StoreTypedStrong (updateG (G ++ G₂) e L) (SEnvAll Ssh (Sown ++ S₂)) store :=
    StoreTypedStrong_updateG (G:=G ++ G₂) (S:=SEnvAll Ssh (Sown ++ S₂))
      (store:=store) (e:=e) (L:=L) hStore
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.send target T L) (L':=L) hG
  simpa [hGrew] using hStore'

/-- Frame: select updates G on the left under a right context. -/
private theorem StoreTypedStrong_frame_select
    {G G₂ : GEnv} {Ssh Sown S₂ : SEnv} {store : Store}
    {e : Endpoint} {target : Role} {bs : List (Label × LocalType)} {L : LocalType}
    (hStore : StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store)
    (hG : lookupG G e = some (.select target bs)) :
    StoreTypedStrong (updateG G e L ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store := by
  -- Update G on the left; SEnv/store unchanged.
  have hStore' :
      StoreTypedStrong (updateG (G ++ G₂) e L) (SEnvAll Ssh (Sown ++ S₂)) store :=
    StoreTypedStrong_updateG (G:=G ++ G₂) (S:=SEnvAll Ssh (Sown ++ S₂))
      (store:=store) (e:=e) (L:=L) hStore
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.select target bs) (L':=L) hG
  simpa [hGrew] using hStore'

/-- Frame: branch updates G on the left under a right context. -/
private theorem StoreTypedStrong_frame_branch
    {G G₂ : GEnv} {Ssh Sown S₂ : SEnv} {store : Store}
    {e : Endpoint} {source : Role} {bs : List (Label × LocalType)} {L : LocalType}
    (hStore : StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store)
    (hG : lookupG G e = some (.branch source bs)) :
    StoreTypedStrong (updateG G e L ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store := by
  -- Update G on the left; SEnv/store unchanged.
  have hStore' :
      StoreTypedStrong (updateG (G ++ G₂) e L) (SEnvAll Ssh (Sown ++ S₂)) store :=
    StoreTypedStrong_updateG (G:=G ++ G₂) (S:=SEnvAll Ssh (Sown ++ S₂))
      (store:=store) (e:=e) (L:=L) hStore
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.branch source bs) (L':=L) hG
  simpa [hGrew] using hStore'

/-- Frame: assignment updates S on the left under a right context. -/
private theorem StoreTypedStrong_frame_assign
    {G G₂ : GEnv} {Ssh Sown S₂ : SEnv} {store : Store}
    {x : Var} {v : Value} {T : ValType}
    (hStore : StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store)
    (hNone : lookupSEnv Ssh x = none)
    (hv : HasTypeVal G v T) :
    StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (updateSEnv Sown x T ++ S₂)) (updateStr store x v) := by
  -- Lift hv to the framed G, then update SEnv/store directly.
  have hv' : HasTypeVal (G ++ G₂) v T :=
    HasTypeVal_mono G (G ++ G₂) v T hv (by
      intro ep L hLookup
      exact lookupG_append_left hLookup)
  refine ⟨?_, ?_⟩
  · intro y
    by_cases hxy : y = x
    · cases hxy
      -- x is present in the updated SEnv; store update inserts v at x.
      have hS : lookupSEnv (SEnvAll Ssh (updateSEnv Sown x T ++ S₂)) x = some T := by
        have hRight :
            lookupSEnv (SEnvAll Ssh (updateSEnv Sown x T ++ S₂)) x =
              lookupSEnv (updateSEnv Sown x T ++ S₂) x :=
          lookupSEnv_append_right (S₁:=Ssh) (S₂:=updateSEnv Sown x T ++ S₂) (x:=x) hNone
        have hLeft :
            lookupSEnv (updateSEnv Sown x T ++ S₂) x = some T :=
          lookupSEnv_append_left (lookupSEnv_update_eq (env:=Sown) (x:=x) (T:=T))
        simpa [hRight, hLeft]
      have hStr : lookupStr (updateStr store x v) x = some v := by
        simp [lookupStr_update_eq]
      simp [hS, hStr]
    · -- y ≠ x: lookups are unchanged.
      have hSEnvEq :=
        lookupSEnv_SEnvAll_update_neq (Ssh:=Ssh) (Sown:=Sown) (S₂:=S₂) (x:=x) (y:=y) (T:=T) hxy
      have hStrEq : lookupStr (updateStr store x v) y = lookupStr store y := by
        simpa using (lookupStr_update_neq store x y v (Ne.symm hxy))
      simpa [hSEnvEq, hStrEq] using hStore.sameDomain y
  · intro y w Ty hStoreY hSY
    by_cases hxy : y = x
    · cases hxy
      -- Reduce to the updated value v : T.
      have hStr : w = v := by
        have hStr' : lookupStr (updateStr store x v) x = some v := by
          simp [lookupStr_update_eq]
        exact Option.some.inj (hStoreY.symm.trans hStr')
      have hTy : Ty = T := by
        have hS : lookupSEnv (SEnvAll Ssh (updateSEnv Sown x T ++ S₂)) x = some T := by
          have hRight :
              lookupSEnv (SEnvAll Ssh (updateSEnv Sown x T ++ S₂)) x =
                lookupSEnv (updateSEnv Sown x T ++ S₂) x :=
            lookupSEnv_append_right (S₁:=Ssh) (S₂:=updateSEnv Sown x T ++ S₂) (x:=x) hNone
          have hLeft :
              lookupSEnv (updateSEnv Sown x T ++ S₂) x = some T :=
            lookupSEnv_append_left (lookupSEnv_update_eq (env:=Sown) (x:=x) (T:=T))
          simpa [hRight, hLeft]
        exact Option.some.inj (hSY.symm.trans hS)
      simpa [hStr, hTy] using hv'
    · -- y ≠ x: use original typing.
      have hSEnvEq :=
        lookupSEnv_SEnvAll_update_neq (Ssh:=Ssh) (Sown:=Sown) (S₂:=S₂) (x:=x) (y:=y) (T:=T) hxy
      have hStrEq : lookupStr store y = some w := by
        -- updateStr doesn't affect y ≠ x
        have hStrEq' : lookupStr (updateStr store x v) y = lookupStr store y := by
          simpa using (lookupStr_update_neq store x y v (Ne.symm hxy))
        simpa [hStrEq'] using hStoreY
      have hSY' : lookupSEnv (SEnvAll Ssh (Sown ++ S₂)) y = some Ty := by
        simpa [hSEnvEq] using hSY
      exact hStore.typeCorr y w Ty hStrEq hSY'

/-- Frame: receive updates S and G on the left under a right context. -/
private theorem StoreTypedStrong_frame_recv
    {G G₂ : GEnv} {Ssh Sown S₂ : SEnv} {store : Store}
    {e : Endpoint} {source : Role} {L : LocalType} {x : Var} {v : Value} {T : ValType} :
    StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store →
    lookupSEnv Ssh x = none →
    HasTypeVal G v T →
    lookupG G e = some (.recv source T L) →
    StoreTypedStrong (updateG G e L ++ G₂)
      (SEnvAll Ssh (updateSEnv Sown x T ++ S₂)) (updateStr store x v) := by
  -- Lift hv to the framed G, update SEnv/store, then update G.
  intro hStore hNone hv hG
  have hStore' :
      StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (updateSEnv Sown x T ++ S₂)) (updateStr store x v) :=
    StoreTypedStrong_frame_assign (G:=G) (G₂:=G₂) (Ssh:=Ssh) (Sown:=Sown) (S₂:=S₂)
      (store:=store) (x:=x) (v:=v) (T:=T) hStore hNone hv
  have hStore'' :
      StoreTypedStrong (updateG (G ++ G₂) e L)
        (SEnvAll Ssh (updateSEnv Sown x T ++ S₂)) (updateStr store x v) :=
    StoreTypedStrong_updateG (G:=G ++ G₂) (S:=SEnvAll Ssh (updateSEnv Sown x T ++ S₂))
      (store:=updateStr store x v) (e:=e) (L:=L) hStore'
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.recv source T L) (L':=L) hG
  simpa [hGrew] using hStore''

/-- Store typing is preserved by a framed TypedStep. -/
private theorem StoreTypedStrong_preserved_frame_left
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'}
    {G₂ : GEnv} {S₂ : SEnv} {Sfin Gfin W Δ} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    StoreTypedStrong (G' ++ G₂) (SEnvAll Ssh (Sown' ++ S₂)) store' := by
  intro hTS hStore hPre
  induction hTS generalizing G₂ S₂ Sfin Gfin W Δ with
  | send =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
        hk hx hG hS hv hRecvReady hEdge hGout hDout hBufsOut
      cases hPre
      · rename_i hk hG' hx
        have hStore' :
            StoreTypedStrong (updateG (G ++ G₂) e L) (SEnvAll Ssh (Sown ++ S₂)) store :=
          StoreTypedStrong_updateG (G:=G ++ G₂) (S:=SEnvAll Ssh (Sown ++ S₂))
            (store:=store) (e:=e) (L:=L) hStore
        have hGrew :
            updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
          updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.send target T L) (L':=L) hG
        simpa [hGout, hGrew] using hStore'
  | recv =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
        hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut
      cases hPre with
      | recv_new hk hG' hNoSh hNoOwn =>
          have hStore' :=
            StoreTypedStrong_frame_recv (G:=G) (G₂:=G₂) (Ssh:=Ssh) (Sown:=Sown) (S₂:=S₂)
              (store:=store) (e:=e) (source:=source) (L:=L) (x:=x) (v:=v) (T:=T)
              hStore hNoSh hv hG
          simpa [hGout, hSout, hStoreOut] using hStore'
      | recv_old hk hG' hNoSh hOwn =>
          have hStore' :=
            StoreTypedStrong_frame_recv (G:=G) (G₂:=G₂) (Ssh:=Ssh) (Sown:=Sown) (S₂:=S₂)
              (store:=store) (e:=e) (source:=source) (L:=L) (x:=x) (v:=v) (T:=T)
              hStore hNoSh hv hG
          simpa [hGout, hSout, hStoreOut] using hStore'
  | select =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
        hk hG hFind hTargetReady hEdge hGout hDout hBufsOut
      cases hPre
      · rename_i hk hG' hFind
        have hStore' :
            StoreTypedStrong (updateG (G ++ G₂) e L) (SEnvAll Ssh (Sown ++ S₂)) store :=
          StoreTypedStrong_updateG (G:=G ++ G₂) (S:=SEnvAll Ssh (Sown ++ S₂))
            (store:=store) (e:=e) (L:=L) hStore
        have hGrew :
            updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
          updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.select target bs) (L':=L) hG
        simpa [hGout, hGrew] using hStore'
  | branch =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
        hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut
      cases hPre
      · rename_i hk hG' hLen hLbl hProcs hOut hDom
        have hStore' :
            StoreTypedStrong (updateG (G ++ G₂) e L) (SEnvAll Ssh (Sown ++ S₂)) store :=
          StoreTypedStrong_updateG (G:=G ++ G₂) (S:=SEnvAll Ssh (Sown ++ S₂))
            (store:=store) (e:=e) (L:=L) hStore
        have hGrew :
            updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
          updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.branch source bs) (L':=L) hG
        simpa [hGout, hGrew] using hStore'
  | assign =>
      rename_i G D Ssh Sown store bufs x v T S' store' hv hSout hStoreOut
      cases hPre with
      | assign_new hNoSh hNoOwn hvPre =>
          have hStore' :=
            StoreTypedStrong_frame_assign (G:=G) (G₂:=G₂) (Ssh:=Ssh) (Sown:=Sown) (S₂:=S₂)
              (store:=store) (x:=x) (v:=v) hStore hNoSh hv
          simpa [hSout, hStoreOut] using hStore'
      | assign_old hNoSh hOwn hvPre =>
          have hStore' :=
            StoreTypedStrong_frame_assign (G:=G) (G₂:=G₂) (Ssh:=Ssh) (Sown:=Sown) (S₂:=S₂)
              (store:=store) (x:=x) (v:=v) hStore hNoSh hv
          simpa [hSout, hStoreOut] using hStore'
  | seq_step hTS ih =>
      cases hPre with
      | seq hP hQ =>
          exact ih hStore hP
  | seq_skip =>
      exact hStore
  | par_left split hTS hDisjG hDisjD hDisjS hConsL hConsR ih =>
      rename_i Ssh store bufs store' bufs' P P' Q S G D₁ D₂ G₁' D₁' S₁'
      cases hPre with
      | par splitPre hSfin hGfin hW hΔ hDisjG0 hDisjS0 hDisjS_left hDisjS_right hDisjS_fin hDisjW hDisjΔ hP hQ =>
          have hsplit : split = splitPre := ParSplit.unique split splitPre
          cases hsplit
          have hStore' :
              StoreTypedStrong (split.G1 ++ (split.G2 ++ G₂))
                (SEnvAll Ssh (split.S1 ++ (split.S2 ++ S₂))) store := by
            simpa [split.hG, split.hS, SEnvAll, List.append_assoc] using hStore
          have hStore'' :=
            ih (G₂:=split.G2 ++ G₂) (S₂:=split.S2 ++ S₂) hStore' hP
          simpa [SEnvAll, List.append_assoc] using hStore''
  | par_right split hTS hDisjG hDisjD hDisjS hConsL hConsR ih =>
      rename_i Ssh store bufs store' bufs' P Q Q' S G D₁ D₂ G₂out D₂' S₂out
      cases hPre with
      | par splitPre hSfin hGfin hW hΔ hDisjG0 hDisjS0 hDisjS_left hDisjS_right hDisjS_fin hDisjW hDisjΔ hP hQ =>
          have hsplit : split = splitPre := ParSplit.unique split splitPre
          cases hsplit
          have hStore' :
              StoreTypedStrong ((split.G1 ++ split.G2) ++ G₂)
                (SEnvAll Ssh ((split.S1 ++ split.S2) ++ S₂)) store := by
            simpa [split.hG, split.hS, SEnvAll, List.append_assoc] using hStore
          have hStore'' :
              StoreTypedStrong (split.G2 ++ (split.G1 ++ G₂))
                (SEnvAll Ssh (split.S2 ++ (split.S1 ++ S₂))) store := by
            have hStoreG :=
              StoreTypedStrong_swap_G_left (G₁:=split.G1) (G₂:=split.G2) (G₃:=G₂) hDisjG hStore'
            have hStoreS :=
              StoreTypedStrong_swap_S_left_prefix (Ssh:=Ssh) (S₁:=split.S1) (S₂:=split.S2) (S₃:=S₂)
                hDisjS hStoreG
            simpa [List.append_assoc] using hStoreS
          have hStore''' :=
            ih (G₂:=split.G1 ++ G₂) (S₂:=split.S1 ++ S₂) hStore'' hQ
          have hSubG : SessionsOf G₂out ⊆ SessionsOf split.G2 := SessionsOf_subset_of_TypedStep hTS
          have hDisjG_symm : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
          have hDisjG' : DisjointG G₂out split.G1 := DisjointG_of_subset_left hSubG hDisjG_symm
          have hStoreG' :
              StoreTypedStrong ((split.G1 ++ G₂out) ++ G₂)
                (SEnvAll Ssh (S₂out ++ (split.S1 ++ S₂))) store' := by
            have hStore'''_assoc :
                StoreTypedStrong ((G₂out ++ split.G1) ++ G₂)
                  (SEnvAll Ssh (S₂out ++ (split.S1 ++ S₂))) store' := by
              simpa [List.append_assoc] using hStore'''
            have hSwap :=
              StoreTypedStrong_swap_G_left (G₁:=G₂out) (G₂:=split.G1) (G₃:=G₂) hDisjG' hStore'''_assoc
            simpa [List.append_assoc] using hSwap
          have hDisjS_out : DisjointS split.S1 S₂out :=
            DisjointS_preserved_TypedStep_right (S1:=split.S1) hTS hDisjS
          have hDisjS_symm : DisjointS S₂out split.S1 := DisjointS_symm hDisjS_out
          have hStoreS' :
              StoreTypedStrong ((split.G1 ++ G₂out) ++ G₂)
                (SEnvAll Ssh (split.S1 ++ (S₂out ++ S₂))) store' := by
            have hStoreG'_assoc :
                StoreTypedStrong ((split.G1 ++ G₂out) ++ G₂)
                  (SEnvAll Ssh ((S₂out ++ split.S1) ++ S₂)) store' := by
              simpa [SEnvAll, List.append_assoc] using hStoreG'
            have hSwap :=
              StoreTypedStrong_swap_S_left_prefix (Ssh:=Ssh) (S₁:=S₂out) (S₂:=split.S1) (S₃:=S₂)
                hDisjS_symm hStoreG'_assoc
            simpa [SEnvAll, List.append_assoc] using hSwap
          simpa [SEnvAll, List.append_assoc] using hStoreS'
  | par_skip_left =>
      exact hStore
  | par_skip_right =>
      exact hStore

/-- Store typing is preserved by TypedStep. -/
theorem StoreTypedStrong_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'}
    {Sfin Gfin W Δ} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    StoreTypedStrong G' (SEnvAll Ssh Sown') store' := by
  -- Use the frame lemma with empty right context.
  intro hTS hStore hPre
  have hStore' :
      StoreTypedStrong (G ++ ∅) (SEnvAll Ssh (Sown ++ ∅)) store := by
    simpa [SEnvAll, List.append_nil] using hStore
  simpa [SEnvAll, List.append_nil] using
    (StoreTypedStrong_preserved_frame_left (G₂:=∅) (S₂:=∅) hTS hStore' hPre)

private theorem BuffersTyped_weakenG
    {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} {bufs : Buffers} :
    BuffersTyped (G₁ ++ G₂) (D₁ ++ D₂) bufs →
    (∀ e L, lookupG (G₁ ++ G₂) e = some L → lookupG (G₁ ++ G₂) e = some L) →
    BuffersTyped (G₁ ++ G₂) (D₁ ++ D₂) bufs := by
  intro hBT _; exact hBT

private theorem BuffersTyped_rewriteD
    {G : GEnv} {D D' : DEnv} {bufs : Buffers} :
    (∀ e, lookupD D e = lookupD D' e) →
    BuffersTyped G D bufs →
    BuffersTyped G D' bufs := by
  intro hEq hBT e
  rcases hBT e with ⟨hLen, hTyping⟩
  refine ⟨?_, ?_⟩
  · simpa [hEq e] using hLen
  · intro i hi
    simpa [hEq e] using hTyping i hi

private lemma lookupG_none_of_disjoint {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂)
    {e : Endpoint} {L : LocalType} (hLookup : lookupG G₂ e = some L) :
    lookupG G₁ e = none := by
  -- Use disjoint session IDs to rule out any left lookup.
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
          have hInter' := hInter
          simp [hEmpty] at hInter'
        exact this.elim

private lemma findD_update_eq (env : DEnv) (e : Edge) (ts : List ValType) :
    (updateD env e ts).find? e = some ts := by
  have hEq : compare e e = .eq := by
    simp
  simpa [updateD] using
    (RBMap.find?_insert_of_eq (t := env.map) (k := e) (v := ts) (k' := e) hEq)

private lemma findD_update_neq (env : DEnv) (e e' : Edge) (ts : List ValType) (hne : e ≠ e') :
    (updateD env e ts).find? e' = env.find? e' := by
  have hne' : compare e' e ≠ .eq := by
    intro hEq
    exact hne ((Edge.compare_eq_iff_eq e' e).1 hEq).symm
  have h' : (env.map.insert e ts).find? e' = env.map.find? e' := by
    simpa using
      (RBMap.find?_insert_of_ne (t := env.map) (k := e) (v := ts) (k' := e') hne')
  have h'' : (updateD env e ts).find? e' = env.map.find? e' := by
    simpa [updateD] using h'
  simpa [DEnv.find?] using h''

private lemma lookupD_append_left_of_find {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType} :
    D₁.find? e = some ts →
    lookupD (D₁ ++ D₂) e = ts := by
  intro hFind
  have hLeft := findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) hFind
  simp [lookupD, hLeft]

private lemma lookupD_updateD_append_left {D D₂ : DEnv} {e e' : Edge} {ts : List ValType} :
    lookupD (updateD (D ++ D₂) e ts) e' = lookupD (updateD D e ts ++ D₂) e' := by
  by_cases hEq : e' = e
  · cases hEq
    -- Both sides update e to ts.
    have hFind : (updateD D e ts).find? e = some ts := findD_update_eq (env:=D) (e:=e) (ts:=ts)
    have hRight : lookupD (updateD D e ts ++ D₂) e = ts :=
      lookupD_append_left_of_find (D₁:=updateD D e ts) (D₂:=D₂) (e:=e) hFind
    simp [lookupD_update_eq, hRight]
  · have hLeftEq :
        lookupD (updateD (D ++ D₂) e ts) e' = lookupD (D ++ D₂) e' :=
        lookupD_update_neq (env:=D ++ D₂) (e:=e) (e':=e') (ts:=ts) (by
          intro hEq'; exact hEq hEq'.symm)
    have hfind : (updateD D e ts).find? e' = D.find? e' :=
      findD_update_neq (env:=D) (e:=e) (e':=e') (ts:=ts) (by
        intro hEq'; exact hEq hEq'.symm)
    cases hLeft : D.find? e' with
    | some ts' =>
        have hLeft' : (updateD D e ts).find? e' = some ts' := by
          simpa [hLeft] using hfind
        have hA :=
          findD_append_left (D₁:=updateD D e ts) (D₂:=D₂) (e:=e') (ts:=ts') hLeft'
        have hB :=
          findD_append_left (D₁:=D) (D₂:=D₂) (e:=e') (ts:=ts') hLeft
        have hfind_union :
            (updateD D e ts ++ D₂).find? e' = (D ++ D₂).find? e' := by
          simpa [hA, hB]
        have hRightEq : lookupD (updateD D e ts ++ D₂) e' = lookupD (D ++ D₂) e' := by
          simp [lookupD, hfind_union]
        simpa [hLeftEq, hRightEq]
    | none =>
        have hLeft' : (updateD D e ts).find? e' = none := by
          simpa [hLeft] using hfind
        have hA := findD_append_right (D₁:=updateD D e ts) (D₂:=D₂) (e:=e') hLeft'
        have hB := findD_append_right (D₁:=D) (D₂:=D₂) (e:=e') hLeft
        have hfind_union :
            (updateD D e ts ++ D₂).find? e' = (D ++ D₂).find? e' := by
          simpa [hA, hB]
        have hRightEq : lookupD (updateD D e ts ++ D₂) e' = lookupD (D ++ D₂) e' := by
          simp [lookupD, hfind_union]
        simpa [hLeftEq, hRightEq]

private lemma lookupD_updateD_append_right {D₁ D : DEnv} {e e' : Edge} {ts : List ValType}
    (hNone : D₁.find? e = none) :
    lookupD (updateD (D₁ ++ D) e ts) e' = lookupD (D₁ ++ updateD D e ts) e' := by
  by_cases hEq : e' = e
  · cases hEq
    -- Left updates e directly; right uses append-right since left has none.
    have hRight :
        lookupD (D₁ ++ updateD D e ts) e = lookupD (updateD D e ts) e :=
      lookupD_append_right (D₁:=D₁) (D₂:=updateD D e ts) (e:=e) hNone
    simp [lookupD_update_eq, hRight]
  · have hLeftEq :
        lookupD (updateD (D₁ ++ D) e ts) e' = lookupD (D₁ ++ D) e' :=
        lookupD_update_neq (env:=D₁ ++ D) (e:=e) (e':=e') (ts:=ts) (by
          intro hEq'; exact hEq hEq'.symm)
    have hfind : (updateD D e ts).find? e' = D.find? e' :=
      findD_update_neq (env:=D) (e:=e) (e':=e') (ts:=ts) (by
        intro hEq'; exact hEq hEq'.symm)
    cases hLeft : D₁.find? e' with
    | some ts' =>
        have hA := findD_append_left (D₁:=D₁) (D₂:=updateD D e ts) (e:=e') (ts:=ts') hLeft
        have hB := findD_append_left (D₁:=D₁) (D₂:=D) (e:=e') (ts:=ts') hLeft
        have hfind_union :
            (D₁ ++ updateD D e ts).find? e' = (D₁ ++ D).find? e' := by
          simpa [hA, hB]
        have hRightEq : lookupD (D₁ ++ updateD D e ts) e' = lookupD (D₁ ++ D) e' := by
          simp [lookupD, hfind_union]
        simpa [hLeftEq, hRightEq]
    | none =>
        have hA := findD_append_right (D₁:=D₁) (D₂:=updateD D e ts) (e:=e') hLeft
        have hB := findD_append_right (D₁:=D₁) (D₂:=D) (e:=e') hLeft
        have hfind_union :
            (D₁ ++ updateD D e ts).find? e' = (D₁ ++ D).find? e' := by
          -- use hfind to rewrite right find?
          simpa [hA, hB, hfind]
        have hRightEq : lookupD (D₁ ++ updateD D e ts) e' = lookupD (D₁ ++ D) e' := by
          simp [lookupD, hfind_union]
        simpa [hLeftEq, hRightEq]

private lemma lookupD_append_assoc {D₁ D₂ D₃ : DEnv} :
    ∀ e, lookupD ((D₁ ++ D₂) ++ D₃) e = lookupD (D₁ ++ (D₂ ++ D₃)) e := by
  intro e
  cases h1 : D₁.find? e with
  | some ts =>
      have h12 : (D₁ ++ D₂).find? e = some ts :=
        findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) h1
      have hLeft : ((D₁ ++ D₂) ++ D₃).find? e = some ts :=
        findD_append_left (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) (ts:=ts) h12
      have hRight : (D₁ ++ (D₂ ++ D₃)).find? e = some ts :=
        findD_append_left (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) (ts:=ts) h1
      simp [lookupD, hLeft, hRight]
  | none =>
      have h12 : (D₁ ++ D₂).find? e = D₂.find? e :=
        findD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) h1
      cases h2 : D₂.find? e with
      | some ts =>
          have h12' : (D₁ ++ D₂).find? e = some ts := by
            simpa [h2] using h12
          have hLeft : ((D₁ ++ D₂) ++ D₃).find? e = some ts :=
            findD_append_left (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) (ts:=ts) h12'
          have h23 : (D₂ ++ D₃).find? e = some ts :=
            findD_append_left (D₁:=D₂) (D₂:=D₃) (e:=e) (ts:=ts) h2
          have hRight : (D₁ ++ (D₂ ++ D₃)).find? e = some ts := by
            have hRight0 := findD_append_right (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) h1
            simpa [h23] using hRight0
          simp [lookupD, hLeft, hRight]
      | none =>
          have h12' : (D₁ ++ D₂).find? e = none := by
            simpa [h2] using h12
          have hLeft := findD_append_right (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) h12'
          have h23 : (D₂ ++ D₃).find? e = D₃.find? e :=
            findD_append_right (D₁:=D₂) (D₂:=D₃) (e:=e) h2
          have hRight : (D₁ ++ (D₂ ++ D₃)).find? e = D₃.find? e := by
            have hRight0 := findD_append_right (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) h1
            simpa [h23] using hRight0
          simp [lookupD, hLeft, hRight]

private lemma BuffersTyped_append_assoc
    {G : GEnv} {D₁ D₂ D₃ : DEnv} {bufs : Buffers} :
    BuffersTyped G ((D₁ ++ D₂) ++ D₃) bufs →
    BuffersTyped G (D₁ ++ (D₂ ++ D₃)) bufs := by
  intro hBT
  exact BuffersTyped_rewriteD (lookupD_append_assoc (D₁:=D₁) (D₂:=D₂) (D₃:=D₃)) hBT

private lemma BuffersTyped_append_assoc_symm
    {G : GEnv} {D₁ D₂ D₃ : DEnv} {bufs : Buffers} :
    BuffersTyped G (D₁ ++ (D₂ ++ D₃)) bufs →
    BuffersTyped G ((D₁ ++ D₂) ++ D₃) bufs := by
  intro hBT
  refine BuffersTyped_rewriteD ?_ hBT
  intro e
  symm
  exact lookupD_append_assoc (D₁:=D₁) (D₂:=D₂) (D₃:=D₃) e

private lemma DConsistent_append {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    DConsistent G₁ D₁ →
    DConsistent G₂ D₂ →
    DConsistent (G₁ ++ G₂) (D₁ ++ D₂) := by
  intro h1 h2 s hs
  have hs' : s ∈ SessionsOfD D₁ ∪ SessionsOfD D₂ :=
    SessionsOfD_append_subset (D₁:=D₁) (D₂:=D₂) hs
  cases hs' with
  | inl hL =>
      exact SessionsOf_append_left (G₂:=G₂) (h1 hL)
  | inr hR =>
      exact SessionsOf_append_right (G₁:=G₁) (h2 hR)

private lemma DEnv_find_none_of_disjoint_left {D₁ D₂ : DEnv} (hDisj : DisjointD D₁ D₂)
    {e : Edge} {ts : List ValType} (hFind : D₁.find? e = some ts) :
    D₂.find? e = none := by
  exact DisjointD_lookup_left (D₁:=D₁) (D₂:=D₂) hDisj hFind

private lemma findD_comm_of_disjoint {D₁ D₂ : DEnv} (hDisj : DisjointD D₁ D₂) :
    ∀ e, (D₁ ++ D₂).find? e = (D₂ ++ D₁).find? e := by
  intro e
  cases hLeft : D₁.find? e with
  | some ts =>
      have hRightNone : D₂.find? e = none :=
        DEnv_find_none_of_disjoint_left hDisj (e:=e) (ts:=ts) hLeft
      have hA := findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) hLeft
      have hB := findD_append_right (D₁:=D₂) (D₂:=D₁) (e:=e) hRightNone
      simpa [hA, hB, hLeft]
  | none =>
      have hA := findD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hLeft
      cases hRight : D₂.find? e with
      | some ts =>
          have hB := findD_append_left (D₁:=D₂) (D₂:=D₁) (e:=e) (ts:=ts) hRight
          simpa [hA, hB, hRight]
      | none =>
          have hB := findD_append_right (D₁:=D₂) (D₂:=D₁) (e:=e) hRight
          simpa [hA, hB, hRight, hLeft]

private lemma BuffersTyped_mono {G G' : GEnv} {D : DEnv} {bufs : Buffers} :
    (∀ e L, lookupG G e = some L → lookupG G' e = some L) →
    BuffersTyped G D bufs →
    BuffersTyped G' D bufs := by
  intro hMono hBT e
  rcases hBT e with ⟨hLen, hTyping⟩
  refine ⟨hLen, ?_⟩
  intro i hi
  exact HasTypeVal_mono G G' _ _ (hTyping i hi) hMono

private lemma lookupG_comm_of_disjoint {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂) :
    ∀ e, lookupG (G₁ ++ G₂) e = lookupG (G₂ ++ G₁) e := by
  intro e
  cases hLeft : lookupG G₁ e with
  | some L =>
      have hNone : lookupG G₂ e = none :=
        lookupG_none_of_disjoint (G₁:=G₂) (G₂:=G₁) (DisjointG_symm hDisj) (e:=e) (L:=L) hLeft
      have hA := lookupG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hLeft
      have hB := lookupG_append_right (G₁:=G₂) (G₂:=G₁) (e:=e) hNone
      simpa [hA, hB, hLeft]
  | none =>
      have hA := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hLeft
      cases hRight : lookupG G₂ e with
      | some L =>
          have hB := lookupG_append_left (G₁:=G₂) (G₂:=G₁) (e:=e) (L:=L) hRight
          simpa [hA, hB, hRight]
      | none =>
          have hB := lookupG_append_right (G₁:=G₂) (G₂:=G₁) (e:=e) hRight
          simpa [hA, hB, hRight, hLeft]

private lemma BuffersTyped_swap_G_left {G₁ G₂ G₃ : GEnv} {D : DEnv} {bufs : Buffers}
    (hDisj : DisjointG G₁ G₂) :
    BuffersTyped ((G₁ ++ G₂) ++ G₃) D bufs →
    BuffersTyped (G₂ ++ (G₁ ++ G₃)) D bufs := by
  intro hBT
  have hBT' : BuffersTyped ((G₂ ++ G₁) ++ G₃) D bufs := by
    apply BuffersTyped_mono (G:=((G₁ ++ G₂) ++ G₃)) (G':=((G₂ ++ G₁) ++ G₃))
    · intro ep L hLookup
      have hInv := lookupG_append_inv (G₁:=G₁ ++ G₂) (G₂:=G₃) (e:=ep) hLookup
      cases hInv with
      | inl hLeft =>
          have hSwap := lookupG_comm_of_disjoint hDisj ep
          have hLeft' : lookupG (G₂ ++ G₁) ep = some L := by
            simpa [hSwap] using hLeft
          exact lookupG_append_left (G₁:=G₂ ++ G₁) (G₂:=G₃) hLeft'
      | inr hRight =>
          have hSwap := lookupG_comm_of_disjoint hDisj ep
          have hNone : lookupG (G₂ ++ G₁) ep = none := by
            simpa [hSwap] using hRight.1
          have hRight' : lookupG (G₂ ++ (G₁ ++ G₃)) ep = lookupG G₃ ep := by
            have hRight0 :=
              lookupG_append_right (G₁:=G₂ ++ G₁) (G₂:=G₃) (e:=ep) hNone
            simpa [List.append_assoc] using hRight0
          have hRight'' : lookupG (G₂ ++ (G₁ ++ G₃)) ep = some L := by
            simpa [hRight'] using hRight.2
          have hRight''' : lookupG ((G₂ ++ G₁) ++ G₃) ep = some L := by
            simpa [List.append_assoc] using hRight''
          exact hRight'''
    · exact hBT
  simpa [List.append_assoc] using hBT'

private lemma BuffersTyped_swap_D_left {G : GEnv} {D₁ D₂ D₃ : DEnv} {bufs : Buffers}
    (hDisj : DisjointD D₁ D₂) :
    BuffersTyped G ((D₁ ++ D₂) ++ D₃) bufs →
    BuffersTyped G ((D₂ ++ D₁) ++ D₃) bufs := by
  intro hBT
  have hEq : ∀ e, lookupD ((D₁ ++ D₂) ++ D₃) e = lookupD ((D₂ ++ D₁) ++ D₃) e := by
    intro e
    have hInv := findD_comm_of_disjoint hDisj e
    cases hLeft : (D₁ ++ D₂).find? e with
    | some ts =>
        have hA := findD_append_left (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) (ts:=ts) hLeft
        have hLeft' : (D₂ ++ D₁).find? e = some ts := by
          simpa [hInv] using hLeft
        have hB := findD_append_left (D₁:=D₂ ++ D₁) (D₂:=D₃) (e:=e) (ts:=ts) hLeft'
        simp [lookupD, hA, hB]
    | none =>
        have hA := findD_append_right (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) hLeft
        have hLeft' : (D₂ ++ D₁).find? e = none := by
          simpa [hInv] using hLeft
        have hB := findD_append_right (D₁:=D₂ ++ D₁) (D₂:=D₃) (e:=e) hLeft'
        simp [lookupD, hA, hB]
  exact BuffersTyped_rewriteD hEq hBT

private lemma lookupG_swap_right {G₁ G₂ G₃ : GEnv} (hDisj : DisjointG G₂ G₃) :
    ∀ e, lookupG (G₁ ++ (G₂ ++ G₃)) e = lookupG (G₁ ++ (G₃ ++ G₂)) e := by
  intro e
  cases hLeft : lookupG G₁ e with
  | some L =>
      have hA := lookupG_append_left (G₁:=G₁) (G₂:=G₂ ++ G₃) (e:=e) (L:=L) hLeft
      have hB := lookupG_append_left (G₁:=G₁) (G₂:=G₃ ++ G₂) (e:=e) (L:=L) hLeft
      simpa [hA, hB]
  | none =>
      have hA := lookupG_append_right (G₁:=G₁) (G₂:=G₂ ++ G₃) (e:=e) hLeft
      have hB := lookupG_append_right (G₁:=G₁) (G₂:=G₃ ++ G₂) (e:=e) hLeft
      have hComm := lookupG_comm_of_disjoint hDisj e
      simpa [hA, hB, hComm]

private lemma BuffersTyped_swap_G_right {G₁ G₂ G₃ : GEnv} {D : DEnv} {bufs : Buffers}
    (hDisj : DisjointG G₂ G₃) :
    BuffersTyped (G₁ ++ (G₂ ++ G₃)) D bufs →
    BuffersTyped (G₁ ++ (G₃ ++ G₂)) D bufs := by
  intro hBT
  apply BuffersTyped_mono (G:=G₁ ++ (G₂ ++ G₃)) (G':=G₁ ++ (G₃ ++ G₂))
  · intro ep L hLookup
    have hEq := lookupG_swap_right (G₁:=G₁) (G₂:=G₂) (G₃:=G₃) hDisj ep
    simpa [hEq] using hLookup
  · exact hBT

private lemma lookupD_swap_right {D₁ D₂ D₃ : DEnv} (hDisj : DisjointD D₂ D₃) :
    ∀ e, lookupD (D₁ ++ (D₂ ++ D₃)) e = lookupD (D₁ ++ (D₃ ++ D₂)) e := by
  intro e
  cases hLeft : D₁.find? e with
  | some ts =>
      have hA := findD_append_left (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) (ts:=ts) hLeft
      have hB := findD_append_left (D₁:=D₁) (D₂:=D₃ ++ D₂) (e:=e) (ts:=ts) hLeft
      simp [lookupD, hA, hB]
  | none =>
      have hA := findD_append_right (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) hLeft
      have hB := findD_append_right (D₁:=D₁) (D₂:=D₃ ++ D₂) (e:=e) hLeft
      have hComm := findD_comm_of_disjoint hDisj e
      simp [lookupD, hA, hB, hComm]

private lemma BuffersTyped_swap_D_right {G : GEnv} {D₁ D₂ D₃ : DEnv} {bufs : Buffers}
    (hDisj : DisjointD D₂ D₃) :
    BuffersTyped G (D₁ ++ (D₂ ++ D₃)) bufs →
    BuffersTyped G (D₁ ++ (D₃ ++ D₂)) bufs := by
  intro hBT
  have hEq : ∀ e, lookupD (D₁ ++ (D₂ ++ D₃)) e = lookupD (D₁ ++ (D₃ ++ D₂)) e :=
    lookupD_swap_right (D₁:=D₁) (D₂:=D₂) (D₃:=D₃) hDisj
  exact BuffersTyped_rewriteD hEq hBT

private theorem BuffersTyped_send_frame_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} {bufs : Buffers}
    {e : Endpoint} {target : Role} {T : ValType} {L : LocalType} {v : Value}
    {sendEdge : Edge} :
    lookupG G e = some (.send target T L) →
    HasTypeVal G v T →
    sendEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    BuffersTyped (updateG G e L ++ G₂)
      (updateD (D ++ D₂) sendEdge (lookupD D sendEdge ++ [T]))
      (enqueueBuf bufs sendEdge v) := by
  intro hG hv hEdge hDisj hCons hBT
  subst hEdge
  have hv' : HasTypeVal (G ++ G₂) v T :=
    HasTypeVal_mono G (G ++ G₂) v T hv (by
      intro ep L' hLookup
      exact lookupG_append_left hLookup)
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .send target T L, hG, rfl⟩
  have hD2none : D₂.find? { sid := e.sid, sender := e.role, receiver := target } = none :=
    lookupD_none_of_disjointG (G₁:=G) (G₂:=G₂) (D₂:=D₂) hDisj hCons hSid
  have hEq :
      lookupD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target } =
        lookupD D { sid := e.sid, sender := e.role, receiver := target } :=
    lookupD_append_left_of_right_none (D₁:=D) (D₂:=D₂) (e:={ sid := e.sid, sender := e.role, receiver := target }) hD2none
  have hBT' :
      BuffersTyped (G ++ G₂)
        (updateD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target } ++ [T]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } v) :=
    BuffersTyped_enqueue (G:=G ++ G₂) (D:=D ++ D₂) (bufs:=bufs)
      (e:={ sid := e.sid, sender := e.role, receiver := target }) (v:=v) (T:=T) hBT hv'
  have hBT'' :
      BuffersTyped (G ++ G₂)
        (updateD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD D { sid := e.sid, sender := e.role, receiver := target } ++ [T]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } v) := by
    simpa [hEq] using hBT'
  have hBT''' :
      BuffersTyped (updateG (G ++ G₂) e L)
        (updateD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD D { sid := e.sid, sender := e.role, receiver := target } ++ [T]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } v) :=
    BuffersTyped_updateG_weaken (e:=e) (L:=L) hBT''
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.send target T L) (L':=L) hG
  simpa [hGrew] using hBT'''

private theorem BuffersTyped_recv_frame_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} {bufs : Buffers}
    {e : Endpoint} {source : Role} {T : ValType} {L : LocalType} {v : Value} {vs : List Value}
    {recvEdge : Edge} :
    lookupG G e = some (.recv source T L) →
    lookupBuf bufs recvEdge = v :: vs →
    (lookupD D recvEdge).head? = some T →
    recvEdge = { sid := e.sid, sender := source, receiver := e.role } →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    BuffersTyped (updateG G e L ++ G₂)
      (updateD (D ++ D₂) recvEdge (lookupD D recvEdge).tail)
      (updateBuf bufs recvEdge vs) := by
  intro hG hBuf hHead hEdge hDisj hCons hBT
  subst hEdge
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .recv source T L, hG, rfl⟩
  have hD2none : D₂.find? { sid := e.sid, sender := source, receiver := e.role } = none :=
    lookupD_none_of_disjointG (G₁:=G) (G₂:=G₂) (D₂:=D₂) hDisj hCons hSid
  have hEq :
      lookupD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role } =
        lookupD D { sid := e.sid, sender := source, receiver := e.role } :=
    lookupD_append_left_of_right_none (D₁:=D) (D₂:=D₂) (e:={ sid := e.sid, sender := source, receiver := e.role }) hD2none
  have hHead' :
      (lookupD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }).head? = some T := by
    simpa [hEq] using hHead
  have hBT' :
      BuffersTyped (G ++ G₂)
        (updateD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) :=
    BuffersTyped_dequeue (G:=G ++ G₂) (D:=D ++ D₂) (bufs:=bufs)
      (recvEdge:={ sid := e.sid, sender := source, receiver := e.role }) (v:=v) (vs:=vs) (T:=T)
      hBT hBuf hHead'
  have hBT'' :
      BuffersTyped (G ++ G₂)
        (updateD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) := by
    simpa [hEq] using hBT'
  have hBT''' :
      BuffersTyped (updateG (G ++ G₂) e L)
        (updateD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) :=
    BuffersTyped_updateG_weaken (e:=e) (L:=L) hBT''
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.recv source T L) (L':=L) hG
  simpa [hGrew] using hBT'''

private theorem BuffersTyped_select_frame_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} {bufs : Buffers}
    {e : Endpoint} {target : Role} {bs : List (String × LocalType)} {ℓ : String}
    {L : LocalType} {selectEdge : Edge} :
    lookupG G e = some (.select target bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    selectEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    BuffersTyped (updateG G e L ++ G₂)
      (updateD (D ++ D₂) selectEdge (lookupD D selectEdge ++ [.string]))
      (enqueueBuf bufs selectEdge (.string ℓ)) := by
  intro hG hFind hEdge hDisj hCons hBT
  subst hEdge
  have hv' : HasTypeVal (G ++ G₂) (.string ℓ) .string :=
    HasTypeVal_mono G (G ++ G₂) (.string ℓ) .string (HasTypeVal.string ℓ) (by
      intro ep L' hLookup
      exact lookupG_append_left hLookup)
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .select target bs, hG, rfl⟩
  have hD2none : D₂.find? { sid := e.sid, sender := e.role, receiver := target } = none :=
    lookupD_none_of_disjointG (G₁:=G) (G₂:=G₂) (D₂:=D₂) hDisj hCons hSid
  have hEq :
      lookupD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target } =
        lookupD D { sid := e.sid, sender := e.role, receiver := target } :=
    lookupD_append_left_of_right_none (D₁:=D) (D₂:=D₂) (e:={ sid := e.sid, sender := e.role, receiver := target }) hD2none
  have hBT' :
      BuffersTyped (G ++ G₂)
        (updateD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target } ++ [.string]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } (.string ℓ)) :=
    BuffersTyped_enqueue (G:=G ++ G₂) (D:=D ++ D₂) (bufs:=bufs)
      (e:={ sid := e.sid, sender := e.role, receiver := target }) (v:=.string ℓ) (T:=.string) hBT hv'
  have hBT'' :
      BuffersTyped (G ++ G₂)
        (updateD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD D { sid := e.sid, sender := e.role, receiver := target } ++ [.string]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } (.string ℓ)) := by
    simpa [hEq] using hBT'
  have hBT''' :
      BuffersTyped (updateG (G ++ G₂) e L)
        (updateD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD D { sid := e.sid, sender := e.role, receiver := target } ++ [.string]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } (.string ℓ)) :=
    BuffersTyped_updateG_weaken (e:=e) (L:=L) hBT''
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.select target bs) (L':=L) hG
  simpa [hGrew] using hBT'''

private theorem BuffersTyped_branch_frame_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} {bufs : Buffers}
    {e : Endpoint} {source : Role} {bs : List (String × LocalType)}
    {ℓ : String} {L : LocalType} {vs : List Value} {branchEdge : Edge} :
    lookupG G e = some (.branch source bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    lookupBuf bufs branchEdge = .string ℓ :: vs →
    (lookupD D branchEdge).head? = some .string →
    branchEdge = { sid := e.sid, sender := source, receiver := e.role } →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    BuffersTyped (updateG G e L ++ G₂)
      (updateD (D ++ D₂) branchEdge (lookupD D branchEdge).tail)
      (updateBuf bufs branchEdge vs) := by
  intro hG hFind hBuf hHead hEdge hDisj hCons hBT
  subst hEdge
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .branch source bs, hG, rfl⟩
  have hD2none : D₂.find? { sid := e.sid, sender := source, receiver := e.role } = none :=
    lookupD_none_of_disjointG (G₁:=G) (G₂:=G₂) (D₂:=D₂) hDisj hCons hSid
  have hEq :
      lookupD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role } =
        lookupD D { sid := e.sid, sender := source, receiver := e.role } :=
    lookupD_append_left_of_right_none (D₁:=D) (D₂:=D₂) (e:={ sid := e.sid, sender := source, receiver := e.role }) hD2none
  have hHead' :
      (lookupD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }).head? = some .string := by
    simpa [hEq] using hHead
  have hBT' :
      BuffersTyped (G ++ G₂)
        (updateD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) :=
    BuffersTyped_dequeue (G:=G ++ G₂) (D:=D ++ D₂) (bufs:=bufs)
      (recvEdge:={ sid := e.sid, sender := source, receiver := e.role }) (v:=.string ℓ) (vs:=vs) (T:=.string)
      hBT hBuf hHead'
  have hBT'' :
      BuffersTyped (G ++ G₂)
        (updateD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) := by
    simpa [hEq] using hBT'
  have hBT''' :
      BuffersTyped (updateG (G ++ G₂) e L)
        (updateD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) :=
    BuffersTyped_updateG_weaken (e:=e) (L:=L) hBT''
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.branch source bs) (L':=L) hG
  simpa [hGrew] using hBT'''

private theorem BuffersTyped_send_frame_right
    {G : GEnv} {D : DEnv} {G₁ : GEnv} {D₁ : DEnv} {bufs : Buffers}
    {e : Endpoint} {target : Role} {T : ValType} {L : LocalType} {v : Value}
    {sendEdge : Edge} :
    lookupG G e = some (.send target T L) →
    HasTypeVal G v T →
    sendEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    BuffersTyped (G₁ ++ updateG G e L)
      (updateD (D₁ ++ D) sendEdge (lookupD D sendEdge ++ [T]))
      (enqueueBuf bufs sendEdge v) := by
  intro hG hv hEdge hDisj hCons hBT
  subst hEdge
  have hv' : HasTypeVal (G₁ ++ G) v T :=
    HasTypeVal_mono G (G₁ ++ G) v T hv (by
      intro ep L' hLookup
      -- use right lookup, disjointness ensures left has none
      have hNone : lookupG G₁ ep = none := lookupG_none_of_disjoint hDisj hLookup
      have hEq := lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=ep) hNone
      simpa [hEq] using hLookup)
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .send target T L, hG, rfl⟩
  have hDisj' : DisjointG G G₁ := DisjointG_symm hDisj
  have hD1none : D₁.find? { sid := e.sid, sender := e.role, receiver := target } = none :=
    lookupD_none_of_disjointG (G₁:=G) (G₂:=G₁) (D₂:=D₁) hDisj' hCons hSid
  have hEq :
      lookupD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target } =
        lookupD D { sid := e.sid, sender := e.role, receiver := target } :=
    lookupD_append_right (D₁:=D₁) (D₂:=D) (e:={ sid := e.sid, sender := e.role, receiver := target }) hD1none
  have hBT' :
      BuffersTyped (G₁ ++ G)
        (updateD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target } ++ [T]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } v) :=
    BuffersTyped_enqueue (G:=G₁ ++ G) (D:=D₁ ++ D) (bufs:=bufs)
      (e:={ sid := e.sid, sender := e.role, receiver := target }) (v:=v) (T:=T) hBT hv'
  have hBT'' :
      BuffersTyped (G₁ ++ G)
        (updateD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD D { sid := e.sid, sender := e.role, receiver := target } ++ [T]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } v) := by
    simpa [hEq] using hBT'
  have hBT''' :
      BuffersTyped (updateG (G₁ ++ G) e L)
        (updateD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD D { sid := e.sid, sender := e.role, receiver := target } ++ [T]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } v) :=
    BuffersTyped_updateG_weaken (e:=e) (L:=L) hBT''
  have hGrew :
      updateG (G₁ ++ G) e L = G₁ ++ updateG G e L :=
    updateG_append_left (G₁:=G₁) (G₂:=G) (e:=e) (L:=L)
      (lookupG_none_of_disjoint (G₁:=G₁) (G₂:=G) hDisj hG)
  simpa [hGrew] using hBT'''

private theorem BuffersTyped_recv_frame_right
    {G : GEnv} {D : DEnv} {G₁ : GEnv} {D₁ : DEnv} {bufs : Buffers}
    {e : Endpoint} {source : Role} {T : ValType} {L : LocalType} {v : Value} {vs : List Value}
    {recvEdge : Edge} :
    lookupG G e = some (.recv source T L) →
    lookupBuf bufs recvEdge = v :: vs →
    (lookupD D recvEdge).head? = some T →
    recvEdge = { sid := e.sid, sender := source, receiver := e.role } →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    BuffersTyped (G₁ ++ updateG G e L)
      (updateD (D₁ ++ D) recvEdge (lookupD D recvEdge).tail)
      (updateBuf bufs recvEdge vs) := by
  intro hG hBuf hHead hEdge hDisj hCons hBT
  subst hEdge
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .recv source T L, hG, rfl⟩
  have hDisj' : DisjointG G G₁ := DisjointG_symm hDisj
  have hD1none : D₁.find? { sid := e.sid, sender := source, receiver := e.role } = none :=
    lookupD_none_of_disjointG (G₁:=G) (G₂:=G₁) (D₂:=D₁) hDisj' hCons hSid
  have hEq :
      lookupD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role } =
        lookupD D { sid := e.sid, sender := source, receiver := e.role } :=
    lookupD_append_right (D₁:=D₁) (D₂:=D) (e:={ sid := e.sid, sender := source, receiver := e.role }) hD1none
  have hHead' :
      (lookupD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }).head? = some T := by
    simpa [hEq] using hHead
  have hBT' :
      BuffersTyped (G₁ ++ G)
        (updateD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) :=
    BuffersTyped_dequeue (G:=G₁ ++ G) (D:=D₁ ++ D) (bufs:=bufs)
      (recvEdge:={ sid := e.sid, sender := source, receiver := e.role }) (v:=v) (vs:=vs) (T:=T)
      hBT hBuf hHead'
  have hBT'' :
      BuffersTyped (G₁ ++ G)
        (updateD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) := by
    simpa [hEq] using hBT'
  have hBT''' :
      BuffersTyped (updateG (G₁ ++ G) e L)
        (updateD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) :=
    BuffersTyped_updateG_weaken (e:=e) (L:=L) hBT''
  have hGrew :
      updateG (G₁ ++ G) e L = G₁ ++ updateG G e L :=
    updateG_append_left (G₁:=G₁) (G₂:=G) (e:=e) (L:=L)
      (lookupG_none_of_disjoint (G₁:=G₁) (G₂:=G) hDisj hG)
  simpa [hGrew] using hBT'''

private theorem BuffersTyped_select_frame_right
    {G : GEnv} {D : DEnv} {G₁ : GEnv} {D₁ : DEnv} {bufs : Buffers}
    {e : Endpoint} {target : Role} {bs : List (String × LocalType)} {ℓ : String}
    {L : LocalType} {selectEdge : Edge} :
    lookupG G e = some (.select target bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    selectEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    BuffersTyped (G₁ ++ updateG G e L)
      (updateD (D₁ ++ D) selectEdge (lookupD D selectEdge ++ [.string]))
      (enqueueBuf bufs selectEdge (.string ℓ)) := by
  intro hG hFind hEdge hDisj hCons hBT
  subst hEdge
  have hv' : HasTypeVal (G₁ ++ G) (.string ℓ) .string :=
    HasTypeVal_mono G (G₁ ++ G) (.string ℓ) .string (HasTypeVal.string ℓ) (by
      intro ep L' hLookup
      have hNone : lookupG G₁ ep = none := lookupG_none_of_disjoint hDisj hLookup
      have hEq := lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=ep) hNone
      simpa [hEq] using hLookup)
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .select target bs, hG, rfl⟩
  have hDisj' : DisjointG G G₁ := DisjointG_symm hDisj
  have hD1none : D₁.find? { sid := e.sid, sender := e.role, receiver := target } = none :=
    lookupD_none_of_disjointG (G₁:=G) (G₂:=G₁) (D₂:=D₁) hDisj' hCons hSid
  have hEq :
      lookupD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target } =
        lookupD D { sid := e.sid, sender := e.role, receiver := target } :=
    lookupD_append_right (D₁:=D₁) (D₂:=D) (e:={ sid := e.sid, sender := e.role, receiver := target }) hD1none
  have hBT' :
      BuffersTyped (G₁ ++ G)
        (updateD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target } ++ [.string]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } (.string ℓ)) :=
    BuffersTyped_enqueue (G:=G₁ ++ G) (D:=D₁ ++ D) (bufs:=bufs)
      (e:={ sid := e.sid, sender := e.role, receiver := target }) (v:=.string ℓ) (T:=.string) hBT hv'
  have hBT'' :
      BuffersTyped (G₁ ++ G)
        (updateD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD D { sid := e.sid, sender := e.role, receiver := target } ++ [.string]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } (.string ℓ)) := by
    simpa [hEq] using hBT'
  have hBT''' :
      BuffersTyped (updateG (G₁ ++ G) e L)
        (updateD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD D { sid := e.sid, sender := e.role, receiver := target } ++ [.string]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } (.string ℓ)) :=
    BuffersTyped_updateG_weaken (e:=e) (L:=L) hBT''
  have hGrew :
      updateG (G₁ ++ G) e L = G₁ ++ updateG G e L :=
    updateG_append_left (G₁:=G₁) (G₂:=G) (e:=e) (L:=L)
      (lookupG_none_of_disjoint (G₁:=G₁) (G₂:=G) hDisj hG)
  simpa [hGrew] using hBT'''

private theorem BuffersTyped_branch_frame_right
    {G : GEnv} {D : DEnv} {G₁ : GEnv} {D₁ : DEnv} {bufs : Buffers}
    {e : Endpoint} {source : Role} {bs : List (String × LocalType)} {ℓ : String}
    {L : LocalType} {vs : List Value} {branchEdge : Edge} :
    lookupG G e = some (.branch source bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    lookupBuf bufs branchEdge = .string ℓ :: vs →
    (lookupD D branchEdge).head? = some .string →
    branchEdge = { sid := e.sid, sender := source, receiver := e.role } →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    BuffersTyped (G₁ ++ updateG G e L)
      (updateD (D₁ ++ D) branchEdge (lookupD D branchEdge).tail)
      (updateBuf bufs branchEdge vs) := by
  intro hG hFind hBuf hHead hEdge hDisj hCons hBT
  subst hEdge
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .branch source bs, hG, rfl⟩
  have hDisj' : DisjointG G G₁ := DisjointG_symm hDisj
  have hD1none : D₁.find? { sid := e.sid, sender := source, receiver := e.role } = none :=
    lookupD_none_of_disjointG (G₁:=G) (G₂:=G₁) (D₂:=D₁) hDisj' hCons hSid
  have hEq :
      lookupD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role } =
        lookupD D { sid := e.sid, sender := source, receiver := e.role } :=
    lookupD_append_right (D₁:=D₁) (D₂:=D) (e:={ sid := e.sid, sender := source, receiver := e.role }) hD1none
  have hHead' :
      (lookupD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }).head? = some .string := by
    simpa [hEq] using hHead
  have hBT' :
      BuffersTyped (G₁ ++ G)
        (updateD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) :=
    BuffersTyped_dequeue (G:=G₁ ++ G) (D:=D₁ ++ D) (bufs:=bufs)
      (recvEdge:={ sid := e.sid, sender := source, receiver := e.role }) (v:=.string ℓ) (vs:=vs) (T:=.string)
      hBT hBuf hHead'
  have hBT'' :
      BuffersTyped (G₁ ++ G)
        (updateD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) := by
    simpa [hEq] using hBT'
  have hBT''' :
      BuffersTyped (updateG (G₁ ++ G) e L)
        (updateD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) :=
    BuffersTyped_updateG_weaken (e:=e) (L:=L) hBT''
  have hGrew :
      updateG (G₁ ++ G) e L = G₁ ++ updateG G e L :=
    updateG_append_left (G₁:=G₁) (G₂:=G) (e:=e) (L:=L)
      (lookupG_none_of_disjoint (G₁:=G₁) (G₂:=G) hDisj hG)
  simpa [hGrew] using hBT'''

set_option maxHeartbeats 2000000 in
private theorem BuffersTyped_preserved_frame_left
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'}
    {G₂ : GEnv} {D₂ : DEnv} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    BuffersTyped (G' ++ G₂) (D' ++ D₂) bufs' := by
  intro hTS hDisj hCons hBT
  induction hTS generalizing G₂ D₂ with
  | send =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
        hk hx hG hS hv hRecvReady hEdge hGout hDout hBufsOut
      have hBT' :=
        BuffersTyped_send_frame_left (G:=G) (D:=D) (G₂:=G₂) (D₂:=D₂)
          (e:=e) (target:=target) (T:=T) (L:=L) (v:=v) (sendEdge:=sendEdge)
          hG hv hEdge hDisj hCons hBT
      have hEq : ∀ e', lookupD (updateD (D ++ D₂) sendEdge (lookupD D sendEdge ++ [T])) e' =
        lookupD ((appendD D sendEdge T) ++ D₂) e' := by
          intro e'
          unfold appendD
          exact
            lookupD_updateD_append_left (D:=D) (D₂:=D₂) (e:=sendEdge) (e':=e')
              (ts:=lookupD D sendEdge ++ [T])
      have hBT'' := BuffersTyped_rewriteD hEq hBT'
      cases hGout
      cases hDout
      cases hBufsOut
      simpa using hBT''
  | recv =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
        hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut
      have hBT' :=
        BuffersTyped_recv_frame_left (G:=G) (D:=D) (G₂:=G₂) (D₂:=D₂)
          (e:=e) (source:=source) (T:=T) (L:=L) (v:=v) (vs:=vs) (recvEdge:=recvEdge)
          hG hBuf hTrace hEdge hDisj hCons hBT
      have hEq : ∀ e', lookupD (updateD (D ++ D₂) recvEdge (lookupD D recvEdge).tail) e' =
        lookupD (updateD D recvEdge (lookupD D recvEdge).tail ++ D₂) e' := by
          intro e'
          exact
            lookupD_updateD_append_left (D:=D) (D₂:=D₂) (e:=recvEdge) (e':=e')
              (ts:=(lookupD D recvEdge).tail)
      have hBT'' := BuffersTyped_rewriteD hEq hBT'
      cases hGout
      cases hDout
      cases hBufsOut
      simpa using hBT''
  | select =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
        hk hG hFind hTargetReady hEdge hGout hDout hBufsOut
      have hBT' :=
        BuffersTyped_select_frame_left (G:=G) (D:=D) (G₂:=G₂) (D₂:=D₂)
          (e:=e) (target:=target) (bs:=bs) (ℓ:=ℓ) (L:=L) (selectEdge:=selectEdge)
          hG hFind hEdge hDisj hCons hBT
      have hEq : ∀ e', lookupD (updateD (D ++ D₂) selectEdge (lookupD D selectEdge ++ [.string])) e' =
        lookupD ((appendD D selectEdge .string) ++ D₂) e' := by
          intro e'
          unfold appendD
          exact
            lookupD_updateD_append_left (D:=D) (D₂:=D₂) (e:=selectEdge) (e':=e')
              (ts:=lookupD D selectEdge ++ [.string])
      have hBT'' := BuffersTyped_rewriteD hEq hBT'
      cases hGout
      cases hDout
      cases hBufsOut
      simpa using hBT''
  | branch =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
        hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut
      have hBT' :=
        BuffersTyped_branch_frame_left (G:=G) (D:=D) (G₂:=G₂) (D₂:=D₂)
          (e:=e) (source:=source) (bs:=bs) (ℓ:=ℓ) (L:=L) (vs:=vs) (branchEdge:=branchEdge)
          hG hFindT hBuf hTrace hEdge hDisj hCons hBT
      have hEq : ∀ e', lookupD (updateD (D ++ D₂) branchEdge (lookupD D branchEdge).tail) e' =
        lookupD (updateD D branchEdge (lookupD D branchEdge).tail ++ D₂) e' := by
          intro e'
          exact
            lookupD_updateD_append_left (D:=D) (D₂:=D₂) (e:=branchEdge) (e':=e')
              (ts:=(lookupD D branchEdge).tail)
      have hBT'' := BuffersTyped_rewriteD hEq hBT'
      cases hGout
      cases hDout
      cases hBufsOut
      simpa using hBT''
  | assign =>
      rename_i G D Ssh Sown store bufs x v T S' store' hv hSout hStoreOut
      simpa using hBT
  | seq_step hTS ih =>
      exact ih hDisj hCons hBT
  | seq_skip =>
      simpa using hBT
  | par_left split hTS hDisjG hDisjD hDisjS hConsL hConsR ih =>
      rename_i Ssh store bufs store' bufs' P P' Q S G D₁ D₂i G₁' D₁' S₁'
      have hSub : SessionsOf split.G1 ⊆ SessionsOf G := by
        intro s hs
        simpa [split.hG] using SessionsOf_append_left (G₂:=split.G2) hs
      have hDisjOuter : DisjointG split.G1 G₂ :=
        DisjointG_of_subset_left hSub hDisj
      have hDisjOuter_symm : DisjointG G₂ split.G1 := DisjointG_symm hDisjOuter
      have hDisjG_symm : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
      have hDisjR : DisjointG (split.G2 ++ G₂) split.G1 :=
        DisjointG_append_left hDisjG_symm hDisjOuter_symm
      have hDisjL : DisjointG split.G1 (split.G2 ++ G₂) := DisjointG_symm hDisjR
      have hConsR' : DConsistent (split.G2 ++ G₂) (D₂i ++ D₂) :=
        DConsistent_append hConsR hCons
      have hBT' :
          BuffersTyped (split.G1 ++ (split.G2 ++ G₂)) (D₁ ++ D₂i ++ D₂) bufs := by
        simpa [split.hG, List.append_assoc] using hBT
      have hBT'' :=
        ih (G₂:=split.G2 ++ G₂) (D₂:=D₂i ++ D₂) hDisjL hConsR'
          (BuffersTyped_append_assoc (D₁:=D₁) (D₂:=D₂i) (D₃:=D₂) hBT')
      have hBT''_assoc :
          BuffersTyped ((G₁' ++ split.G2) ++ G₂) (D₁' ++ (D₂i ++ D₂)) bufs' := by
        simpa [List.append_assoc] using hBT''
      exact
        BuffersTyped_append_assoc_symm (D₁:=D₁') (D₂:=D₂i) (D₃:=D₂) hBT''_assoc
  | par_right split hTS hDisjG hDisjD hDisjS hConsL hConsR ih =>
      rename_i Ssh store bufs store' bufs' P Q Q' S G D₁ D₂i G₂' D₂' S₂'
      have hSub : SessionsOf split.G2 ⊆ SessionsOf G := by
        intro s hs
        simpa [split.hG] using SessionsOf_append_right (G₁:=split.G1) hs
      have hDisjOuter : DisjointG split.G2 G₂ :=
        DisjointG_of_subset_left hSub hDisj
      have hDisjOuter_symm : DisjointG G₂ split.G2 := DisjointG_symm hDisjOuter
      have hDisjG_symm : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
      have hDisjR : DisjointG (split.G1 ++ G₂) split.G2 :=
        DisjointG_append_left hDisjG hDisjOuter_symm
      have hDisjL : DisjointG split.G2 (split.G1 ++ G₂) := DisjointG_symm hDisjR
      have hConsL' : DConsistent (split.G1 ++ G₂) (D₁ ++ D₂) :=
        DConsistent_append hConsL hCons
      have hBT0 :
          BuffersTyped ((split.G1 ++ split.G2) ++ G₂) ((D₁ ++ D₂i) ++ D₂) bufs := by
        simpa [split.hG, List.append_assoc] using hBT
      have hBT1 :=
        BuffersTyped_swap_G_left (G₁:=split.G1) (G₂:=split.G2) (G₃:=G₂) hDisjG hBT0
      have hBT1' :
          BuffersTyped ((split.G2 ++ split.G1) ++ G₂) ((D₁ ++ D₂i) ++ D₂) bufs := by
        simpa [List.append_assoc] using hBT1
      have hBT2 :=
        BuffersTyped_swap_D_left (G:=((split.G2 ++ split.G1) ++ G₂))
          (D₁:=D₁) (D₂:=D₂i) (D₃:=D₂) hDisjD hBT1'
      have hBT' :
          BuffersTyped (split.G2 ++ (split.G1 ++ G₂)) (D₂i ++ (D₁ ++ D₂)) bufs := by
        have hBT2' :
            BuffersTyped (split.G2 ++ (split.G1 ++ G₂)) ((D₂i ++ D₁) ++ D₂) bufs := by
          simpa [List.append_assoc] using hBT2
        exact BuffersTyped_append_assoc (D₁:=D₂i) (D₂:=D₁) (D₃:=D₂) hBT2'
      have hBT'' :=
        ih (G₂:=split.G1 ++ G₂) (D₂:=D₁ ++ D₂) hDisjL hConsL' hBT'
      -- swap G₂' and split.G1 back into order
      have hSubG : SessionsOf G₂' ⊆ SessionsOf split.G2 := SessionsOf_subset_of_TypedStep hTS
      have hDisjG' : DisjointG G₂' split.G1 :=
        DisjointG_of_subset_left hSubG hDisjG_symm
      have hBT''_assoc :
          BuffersTyped ((G₂' ++ split.G1) ++ G₂) (D₂' ++ (D₁ ++ D₂)) bufs' := by
        simpa [List.append_assoc] using hBT''
      have hBT''' :=
        BuffersTyped_swap_G_left (G₁:=G₂') (G₂:=split.G1) (G₃:=G₂) hDisjG' hBT''_assoc
      -- swap D₂' and D₁ back into order
      have hSubD : SessionsOfD D₂' ⊆ SessionsOf split.G2 := by
        intro s hs
        have hs' : s ∈ SessionsOfD D₂i ∪ SessionsOf split.G2 :=
          SessionsOfD_subset_of_TypedStep hTS hs
        cases hs' with
        | inl hIn => exact hConsR hIn
        | inr hIn => exact hIn
      have hSubD₁ : SessionsOfD D₁ ⊆ SessionsOf split.G1 := hConsL
      have hDisjD' : DisjointD D₂' D₁ := by
        apply Set.eq_empty_iff_forall_notMem.2
        intro s hs
        have hIn1 : s ∈ SessionsOf split.G2 := hSubD hs.1
        have hIn2 : s ∈ SessionsOf split.G1 := hSubD₁ hs.2
        have hEmpty : SessionsOf split.G2 ∩ SessionsOf split.G1 = ∅ := by
          simpa [DisjointG, GEnvDisjoint, Set.inter_comm] using hDisjG
        have hInter : s ∈ SessionsOf split.G2 ∩ SessionsOf split.G1 := ⟨hIn1, hIn2⟩
        have : s ∈ (∅ : Set SessionId) := by
          simpa [hEmpty] using hInter
        exact this.elim
      have hBT'''_assocG :
          BuffersTyped ((split.G1 ++ G₂') ++ G₂) (D₂' ++ (D₁ ++ D₂)) bufs' := by
        simpa [List.append_assoc] using hBT'''
      have hBT'''_assocD :
          BuffersTyped ((split.G1 ++ G₂') ++ G₂) ((D₂' ++ D₁) ++ D₂) bufs' := by
        exact BuffersTyped_append_assoc_symm (D₁:=D₂') (D₂:=D₁) (D₃:=D₂) hBT'''_assocG
      have hBT'''' :=
        BuffersTyped_swap_D_left (G:=((split.G1 ++ G₂') ++ G₂))
          (D₁:=D₂') (D₂:=D₁) (D₃:=D₂) hDisjD' hBT'''_assocD
      simpa [List.append_assoc] using hBT''''
  | par_skip_left =>
      simpa using hBT
  | par_skip_right =>
      simpa using hBT

set_option maxHeartbeats 2000000 in
private theorem BuffersTyped_preserved_frame_right
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'}
    {G₁ : GEnv} {D₁ : DEnv} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    BuffersTyped (G₁ ++ G') (D₁ ++ D') bufs' := by
  intro hTS hDisj hCons hBT
  induction hTS generalizing G₁ D₁ with
  | send =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
        hk hx hG hS hv hRecvReady hEdge hGout hDout hBufsOut
      have hBT' :=
        BuffersTyped_send_frame_right (G:=G) (D:=D) (G₁:=G₁) (D₁:=D₁)
          (e:=e) (target:=target) (T:=T) (L:=L) (v:=v) (sendEdge:=sendEdge)
          hG hv hEdge hDisj hCons hBT
      have hSid : sendEdge.sid ∈ SessionsOf G := by
        rcases hEdge with rfl
        exact ⟨e, .send target T L, hG, rfl⟩
      have hNone : D₁.find? sendEdge = none :=
        lookupD_none_of_disjointG (G₁:=G) (G₂:=G₁) (D₂:=D₁) (DisjointG_symm hDisj) hCons
          hSid
      have hEq : ∀ e', lookupD (updateD (D₁ ++ D) sendEdge (lookupD D sendEdge ++ [T])) e' =
        lookupD (D₁ ++ appendD D sendEdge T) e' := by
          intro e'
          unfold appendD
          exact
            lookupD_updateD_append_right (D₁:=D₁) (D:=D) (e:=sendEdge) (e':=e')
              (ts:=lookupD D sendEdge ++ [T]) hNone
      have hBT'' := BuffersTyped_rewriteD hEq hBT'
      cases hGout
      cases hDout
      cases hBufsOut
      simpa using hBT''
  | recv =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
        hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut
      have hBT' :=
        BuffersTyped_recv_frame_right (G:=G) (D:=D) (G₁:=G₁) (D₁:=D₁)
          (e:=e) (source:=source) (T:=T) (L:=L) (v:=v) (vs:=vs) (recvEdge:=recvEdge)
          hG hBuf hTrace hEdge hDisj hCons hBT
      have hSid : recvEdge.sid ∈ SessionsOf G := by
        rcases hEdge with rfl
        exact ⟨e, .recv source T L, hG, rfl⟩
      have hNone : D₁.find? recvEdge = none :=
        lookupD_none_of_disjointG (G₁:=G) (G₂:=G₁) (D₂:=D₁) (DisjointG_symm hDisj) hCons
          hSid
      have hEq : ∀ e', lookupD (updateD (D₁ ++ D) recvEdge (lookupD D recvEdge).tail) e' =
        lookupD (D₁ ++ updateD D recvEdge (lookupD D recvEdge).tail) e' := by
          intro e'
          exact
            lookupD_updateD_append_right (D₁:=D₁) (D:=D) (e:=recvEdge) (e':=e')
              (ts:=(lookupD D recvEdge).tail) hNone
      have hBT'' := BuffersTyped_rewriteD hEq hBT'
      cases hGout
      cases hDout
      cases hBufsOut
      simpa using hBT''
  | select =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
        hk hG hFind hTargetReady hEdge hGout hDout hBufsOut
      have hBT' :=
        BuffersTyped_select_frame_right (G:=G) (D:=D) (G₁:=G₁) (D₁:=D₁)
          (e:=e) (target:=target) (bs:=bs) (ℓ:=ℓ) (L:=L) (selectEdge:=selectEdge)
          hG hFind hEdge hDisj hCons hBT
      have hSid : selectEdge.sid ∈ SessionsOf G := by
        rcases hEdge with rfl
        exact ⟨e, .select target bs, hG, rfl⟩
      have hNone : D₁.find? selectEdge = none :=
        lookupD_none_of_disjointG (G₁:=G) (G₂:=G₁) (D₂:=D₁) (DisjointG_symm hDisj) hCons
          hSid
      have hEq : ∀ e', lookupD (updateD (D₁ ++ D) selectEdge (lookupD D selectEdge ++ [.string])) e' =
        lookupD (D₁ ++ appendD D selectEdge .string) e' := by
          intro e'
          unfold appendD
          exact
            lookupD_updateD_append_right (D₁:=D₁) (D:=D) (e:=selectEdge) (e':=e')
              (ts:=lookupD D selectEdge ++ [.string]) hNone
      have hBT'' := BuffersTyped_rewriteD hEq hBT'
      cases hGout
      cases hDout
      cases hBufsOut
      simpa using hBT''
  | branch =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
        hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut
      have hBT' :=
        BuffersTyped_branch_frame_right (G:=G) (D:=D) (G₁:=G₁) (D₁:=D₁)
          (e:=e) (source:=source) (bs:=bs) (ℓ:=ℓ) (L:=L) (vs:=vs) (branchEdge:=branchEdge)
          hG hFindT hBuf hTrace hEdge hDisj hCons hBT
      have hSid : branchEdge.sid ∈ SessionsOf G := by
        rcases hEdge with rfl
        exact ⟨e, .branch source bs, hG, rfl⟩
      have hNone : D₁.find? branchEdge = none :=
        lookupD_none_of_disjointG (G₁:=G) (G₂:=G₁) (D₂:=D₁) (DisjointG_symm hDisj) hCons
          hSid
      have hEq : ∀ e', lookupD (updateD (D₁ ++ D) branchEdge (lookupD D branchEdge).tail) e' =
        lookupD (D₁ ++ updateD D branchEdge (lookupD D branchEdge).tail) e' := by
          intro e'
          exact
            lookupD_updateD_append_right (D₁:=D₁) (D:=D) (e:=branchEdge) (e':=e')
              (ts:=(lookupD D branchEdge).tail) hNone
      have hBT'' := BuffersTyped_rewriteD hEq hBT'
      cases hGout
      cases hDout
      cases hBufsOut
      simpa using hBT''
  | assign =>
      simpa using hBT
  | seq_step hTS ih =>
      exact ih hDisj hCons hBT
  | seq_skip =>
      simpa using hBT
  | par_left split hTS hDisjG hDisjD hDisjS hConsL hConsR ih =>
      rename_i Ssh store bufs store' bufs' P P' Q S G D₁i D₂i G₁' D₁' S₁'
      have hSub : SessionsOf split.G1 ⊆ SessionsOf G := by
        intro s hs
        simpa [split.hG] using SessionsOf_append_left (G₂:=split.G2) hs
      have hDisjOuter : DisjointG split.G1 G₁ :=
        DisjointG_of_subset_left hSub (DisjointG_symm hDisj)
      have hDisjOuter_symm : DisjointG G₁ split.G1 := DisjointG_symm hDisjOuter
      have hDisjG_symm : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
      have hDisjL : DisjointG (G₁ ++ split.G2) split.G1 :=
        DisjointG_append_left hDisjOuter_symm hDisjG_symm
      have hConsR' : DConsistent (G₁ ++ split.G2) (D₁ ++ D₂i) :=
        DConsistent_append hCons hConsR
      have hBT0 :
          BuffersTyped (G₁ ++ (split.G1 ++ split.G2)) (D₁ ++ (D₁i ++ D₂i)) bufs := by
        simpa [split.hG, List.append_assoc] using hBT
      have hBT1 :=
        BuffersTyped_swap_G_right (G₁:=G₁) (G₂:=split.G1) (G₃:=split.G2) hDisjG hBT0
      have hBT2 :=
        BuffersTyped_swap_D_right (D₁:=D₁) (D₂:=D₁i) (D₃:=D₂i) hDisjD hBT1
      have hBT' :
          BuffersTyped (G₁ ++ (split.G2 ++ split.G1)) ((D₁ ++ D₂i) ++ D₁i) bufs := by
        exact BuffersTyped_append_assoc_symm (D₁:=D₁) (D₂:=D₂i) (D₃:=D₁i) hBT2
      have hBT'' :=
        ih (G₁:=G₁ ++ split.G2) (D₁:=D₁ ++ D₂i) hDisjL hConsR'
          (by simpa [List.append_assoc] using hBT')
      -- swap split.G2 and G₁' to match output order
      have hSubG : SessionsOf G₁' ⊆ SessionsOf split.G1 := SessionsOf_subset_of_TypedStep hTS
      have hDisjG' : DisjointG G₁' split.G2 :=
        DisjointG_of_subset_left hSubG hDisjG
      have hDisjG'' : DisjointG split.G2 G₁' := DisjointG_symm hDisjG'
      have hBT''_assoc :
          BuffersTyped (G₁ ++ (split.G2 ++ G₁')) (D₁ ++ D₂i ++ D₁') bufs' := by
        simpa [List.append_assoc] using hBT''
      have hBT''' :=
        BuffersTyped_swap_G_right (G₁:=G₁) (G₂:=split.G2) (G₃:=G₁') hDisjG'' hBT''_assoc
      -- swap D₂i and D₁' to match output order
      have hSubD : SessionsOfD D₁' ⊆ SessionsOf split.G1 := by
        intro s hs
        have hs' : s ∈ SessionsOfD D₁i ∪ SessionsOf split.G1 :=
          SessionsOfD_subset_of_TypedStep hTS hs
        cases hs' with
        | inl hIn => exact hConsL hIn
        | inr hIn => exact hIn
      have hSubD₂ : SessionsOfD D₂i ⊆ SessionsOf split.G2 := hConsR
      have hDisjD' : DisjointD D₂i D₁' := by
        apply Set.eq_empty_iff_forall_notMem.2
        intro s hs
        have hIn1 : s ∈ SessionsOf split.G2 := hSubD₂ hs.1
        have hIn2 : s ∈ SessionsOf split.G1 := hSubD hs.2
        have hEmpty : SessionsOf split.G2 ∩ SessionsOf split.G1 = ∅ := by
          simpa [DisjointG, GEnvDisjoint, Set.inter_comm] using hDisjG
        have hInter : s ∈ SessionsOf split.G2 ∩ SessionsOf split.G1 := ⟨hIn1, hIn2⟩
        have : s ∈ (∅ : Set SessionId) := by
          simpa [hEmpty] using hInter
        exact this.elim
      have hBT'''_assoc :
          BuffersTyped (G₁ ++ (G₁' ++ split.G2)) (D₁ ++ (D₂i ++ D₁')) bufs' := by
        exact BuffersTyped_append_assoc (D₁:=D₁) (D₂:=D₂i) (D₃:=D₁') hBT'''
      have hBT'''' :=
        BuffersTyped_swap_D_right (D₁:=D₁) (D₂:=D₂i) (D₃:=D₁') hDisjD' hBT'''_assoc
      exact hBT''''
  | par_right split hTS hDisjG hDisjD hDisjS hConsL hConsR ih =>
      rename_i Ssh store bufs store' bufs' P Q Q' S G D₁i D₂i G₂' D₂' S₂'
      have hSub : SessionsOf split.G2 ⊆ SessionsOf G := by
        intro s hs
        simpa [split.hG] using SessionsOf_append_right (G₁:=split.G1) hs
      have hDisjOuter : DisjointG split.G2 G₁ :=
        DisjointG_of_subset_left hSub (DisjointG_symm hDisj)
      have hDisjOuter_symm : DisjointG G₁ split.G2 := DisjointG_symm hDisjOuter
      have hDisjG_symm : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
      have hDisjL : DisjointG (G₁ ++ split.G1) split.G2 :=
        DisjointG_append_left hDisjOuter_symm hDisjG
      have hConsL' : DConsistent (G₁ ++ split.G1) (D₁ ++ D₁i) :=
        DConsistent_append hCons hConsL
      have hBT0 :
          BuffersTyped ((G₁ ++ split.G1) ++ split.G2) (D₁ ++ (D₁i ++ D₂i)) bufs := by
        simpa [split.hG, List.append_assoc] using hBT
      have hBT' :
          BuffersTyped ((G₁ ++ split.G1) ++ split.G2) ((D₁ ++ D₁i) ++ D₂i) bufs := by
        exact BuffersTyped_append_assoc_symm (D₁:=D₁) (D₂:=D₁i) (D₃:=D₂i) hBT0
      have hBT'' :=
        ih (G₁:=G₁ ++ split.G1) (D₁:=D₁ ++ D₁i) hDisjL hConsL'
          (by simpa [List.append_assoc] using hBT')
      have hBT''_assoc :
          BuffersTyped (G₁ ++ (split.G1 ++ G₂')) ((D₁ ++ D₁i) ++ D₂') bufs' := by
        simpa [List.append_assoc] using hBT''
      exact BuffersTyped_append_assoc (D₁:=D₁) (D₂:=D₁i) (D₃:=D₂') hBT''_assoc
  | par_skip_left =>
      simpa using hBT
  | par_skip_right =>
      simpa using hBT

private lemma SessionsOf_empty : SessionsOf ([] : GEnv) = ∅ := by
  ext s; constructor
  · intro h
    rcases h with ⟨e, L, hLookup, hSid⟩
    simp [lookupG] at hLookup
  · intro h; cases h

private lemma SessionsOfD_empty : SessionsOfD (∅ : DEnv) = ∅ := by
  ext s; constructor
  · intro h
    rcases h with ⟨e, ts, hFind, hSid⟩
    have : (∅ : DEnv).find? e = none := by
      simp [DEnv.find?, DEnv_map_find?_empty]
    cases hFind
  · intro h; cases h

private lemma DisjointG_right_empty (G : GEnv) : DisjointG G [] := by
  simp [DisjointG, GEnvDisjoint, SessionsOf_empty]

private lemma DConsistent_empty (G : GEnv) : DConsistent G (∅ : DEnv) := by
  simp [DConsistent, SessionsOfD_empty]

theorem BuffersTyped_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    Coherent G D →
    BuffersTyped G D bufs →
    BuffersTyped G' D' bufs' := by
  intro hTS _ hBT
  have hEqD : ∀ e, lookupD (D ++ (∅ : DEnv)) e = lookupD D e := by
    intro e
    have hNone : (∅ : DEnv).find? e = none := by
      simp [DEnv.find?, DEnv_map_find?_empty]
    exact lookupD_append_left_of_right_none (D₁:=D) (D₂:=∅) (e:=e) hNone
  have hBT' :
      BuffersTyped (G ++ []) (D ++ (∅ : DEnv)) bufs := by
    have hBTD : BuffersTyped G (D ++ (∅ : DEnv)) bufs :=
      BuffersTyped_rewriteD (D:=D) (D':=D ++ (∅ : DEnv)) (by
        intro e; symm; exact hEqD e) hBT
    apply BuffersTyped_mono (G:=G) (G':=G ++ []) (D:=D ++ (∅ : DEnv)) (bufs:=bufs)
    · intro ep L hLookup
      exact lookupG_append_left (G₁:=G) (G₂:=[]) hLookup
    · exact hBTD
  have hDisj : DisjointG G ([] : GEnv) := DisjointG_right_empty G
  have hCons : DConsistent ([] : GEnv) (∅ : DEnv) := DConsistent_empty []
  have hBT'' :=
    BuffersTyped_preserved_frame_left (G₂:=[]) (D₂:=∅) hTS hDisj hCons hBT'
  have hBT''' : BuffersTyped G' (D' ++ (∅ : DEnv)) bufs' := by
    simpa [List.append_nil] using hBT''
  have hEqD' : ∀ e, lookupD (D' ++ (∅ : DEnv)) e = lookupD D' e := by
    intro e
    have hNone : (∅ : DEnv).find? e = none := by
      simp [DEnv.find?, DEnv_map_find?_empty]
    exact lookupD_append_left_of_right_none (D₁:=D') (D₂:=∅) (e:=e) hNone
  exact BuffersTyped_rewriteD (D:=D' ++ (∅ : DEnv)) (D':=D') hEqD' hBT'''
