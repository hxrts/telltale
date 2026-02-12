import Protocol.Typing.Framing
import Batteries.Data.RBMap.Lemmas

/-! # MPST Process Typing: Preservation

This module proves typing preservation under steps. -/

/-
The Problem. We need subject reduction for the process typing judgment:
if `⊢ P` and P steps to P', then `⊢ P'`. This is the core safety theorem.

Solution Structure. We prove preservation by:
1. Case analysis on the typing derivation (skip, seq, par, send, etc.)
2. Using the framing lemmas for parallel composition
3. Combining with coherence preservation for the full invariant
-/


/-! ## Key Judgments

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

section

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
  | @TypedStep.par_left Ssh Sown store bufs store' bufs' P P' Q G D₁ D₂ G₁' D₁' S₁' nS nG split
      hSlen hTS hDisjG hDisjD hDisjS, hCoh => by
    -- Full-G step rule: delegate directly to the sub-step.
    have hCohMerged : Coherent G (D₁ ++ D₂) := by
      simpa [split.hG] using hCoh
    exact typed_step_preserves_coherence hTS hCohMerged
  | @TypedStep.par_right Ssh Sown store bufs store' bufs' P Q Q' G D₁ D₂ G₂' D₂' S₂' nS nG split
      hSlen hTS hDisjG hDisjD hDisjS, hCoh => by
    -- Full-G step rule: delegate directly to the sub-step.
    have hCohMerged : Coherent G (D₁ ++ D₂) := by
      simpa [split.hG] using hCoh
    exact typed_step_preserves_coherence hTS hCohMerged
  | .par_skip_left _ _ _, hCoh =>
    hCoh
  | .par_skip_right _ _ _, hCoh =>
    hCoh

/-! ## StoreTypedStrong Preservation -/

/- Updating a key already present in the left SEnv only affects the left side. -/
theorem updateSEnv_append_left_of_left {S₁ S₂ : SEnv} {x : Var} {T T' : ValType}
    (hLeft : lookupSEnv S₁ x = some T') :
    updateSEnv (S₁ ++ S₂) x T = updateSEnv S₁ x T ++ S₂ := by
  induction S₁ with
  | nil =>
      simp [lookupSEnv] at hLeft
  | cons hd tl ih =>
      cases hd with
      | mk y U =>
          by_cases hxy : x = y
          · subst hxy
            have hLeftAll : lookupSEnv ((x, U) :: tl ++ S₂) x = some U := by
              simp [lookupSEnv]
            simp [updateSEnv]
          ·
            have hLeft' : lookupSEnv tl x = some T' := by
              have hbeq : (x == y) = false := by
                exact beq_eq_false_iff_ne.mpr hxy
              simpa [lookupSEnv, List.lookup, hbeq] using hLeft
            have hLeftAll : lookupSEnv ((y, U) :: tl ++ S₂) x = some T' := by
              have hLeftAll' : lookupSEnv (tl ++ S₂) x = some T' :=
                lookupSEnv_append_left hLeft'
              have hbeq : (x == y) = false := beq_eq_false_iff_ne.mpr hxy
              simpa [lookupSEnv, List.lookup, hbeq] using hLeftAll'
            simp [updateSEnv, hxy, ih hLeft']

lemma lookupSEnv_update_append_neq
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
      simpa [hLeft, hLeft'] 
  | none =>
      have hL' : lookupSEnv (updateSEnv S₁ x T) y = none := by
        simpa [hL] using
          (lookupSEnv_update_neq (env:=S₁) (x:=x) (y:=y) (T:=T) (Ne.symm hxy))
      have hRight : lookupSEnv (updateSEnv S₁ x T ++ S₂) y = lookupSEnv S₂ y :=
        lookupSEnv_append_right hL'
      have hRight' : lookupSEnv (S₁ ++ S₂) y = lookupSEnv S₂ y :=
        lookupSEnv_append_right hL
      simpa [hRight'] using hRight

lemma lookupSEnv_SEnvAll_update_neq
    {Ssh Sown S₂ : SEnv} {x y : Var} {T : ValType} (hxy : y ≠ x) :
    lookupSEnv (SEnvAll Ssh (updateSEnv Sown x T ++ S₂)) y =
      lookupSEnv (SEnvAll Ssh (Sown ++ S₂)) y
    := by
  simp only [SEnvAll]
  cases hSh : lookupSEnv Ssh y with
  | some Ty =>
      have hLeft :
          lookupSEnv (Ssh ++ (updateSEnv Sown x T ++ S₂)) y = some Ty :=
        lookupSEnv_append_left hSh
      have hRight : lookupSEnv (Ssh ++ (Sown ++ S₂)) y = some Ty :=
        lookupSEnv_append_left hSh
      simpa [hLeft, hRight]
  | none =>
      have hLeft :
          lookupSEnv (Ssh ++ (updateSEnv Sown x T ++ S₂)) y =
            lookupSEnv (updateSEnv Sown x T ++ S₂) y :=
        lookupSEnv_append_right hSh
      have hRight :
          lookupSEnv (Ssh ++ (Sown ++ S₂)) y = lookupSEnv (Sown ++ S₂) y :=
        lookupSEnv_append_right hSh
      have hUpd :
          lookupSEnv (updateSEnv Sown x T ++ S₂) y = lookupSEnv (Sown ++ S₂) y :=
        lookupSEnv_update_append_neq (S₁:=Sown) (S₂:=S₂) (x:=x) (y:=y) (T:=T) hxy
      simpa [hRight] using hLeft.trans hUpd

lemma DisjointS_owned_right {S₁ : SEnv} {Sown : OwnedEnv} :
    DisjointS S₁ (Sown : SEnv) →
    DisjointS S₁ Sown.right := by
  intro hDisj
  have hSub : SEnvDomSubset Sown.right (Sown : SEnv) := by
    simpa [OwnedEnv.all] using
      (SEnvDomSubset_append_left (S₁:=Sown.right) (S₂:=Sown.left))
  exact DisjointS_of_domsubset_right hSub hDisj

lemma DisjointS_owned_left {S₁ : SEnv} {Sown : OwnedEnv} :
    DisjointS S₁ (Sown : SEnv) →
    DisjointS S₁ Sown.left := by
  intro hDisj
  have hSub : SEnvDomSubset Sown.left (Sown : SEnv) := by
    simpa [OwnedEnv.all] using
      (SEnvDomSubset_append_right (S₁:=Sown.right) (S₂:=Sown.left))
  exact DisjointS_of_domsubset_right hSub hDisj

lemma DisjointS_update_right {S₁ S₂ : SEnv} {x : Var} {T : ValType}
    (hDisj : DisjointS S₁ S₂)
    (hNone : lookupSEnv S₁ x = none) :
    DisjointS S₁ (updateSEnv S₂ x T) := by
  intro y T₁ T₂ hL1 hL2
  by_cases hxy : y = x
  · subst hxy
    have : (some T₁ : Option ValType) = none := by
      simpa [hNone] using hL1
    cases this
  ·
    have hL2' : lookupSEnv S₂ y = some T₂ := by
      have hEq := lookupSEnv_update_neq (env:=S₂) (x:=x) (y:=y) (T:=T) (Ne.symm hxy)
      simpa [hEq] using hL2
    exact hDisj y T₁ T₂ hL1 hL2'

lemma lookupSEnv_erase_eq
    {S : SEnv} {x : Var} :
    lookupSEnv (eraseSEnv S x) x = none := by
  induction S with
  | nil =>
      simp [eraseSEnv, lookupSEnv]
  | cons hd tl ih =>
      cases hd with
      | mk y Ty =>
          by_cases hxy : x = y
          · subst hxy
            simpa [eraseSEnv] using ih
          · have hbeq : (x == y) = false := beq_eq_false_iff_ne.mpr hxy
            simpa [eraseSEnv, hxy, lookupSEnv, List.lookup, hbeq] using ih

lemma lookupSEnv_erase_ne
    {S : SEnv} {x y : Var} (hxy : y ≠ x) :
    lookupSEnv (eraseSEnv S x) y = lookupSEnv S y := by
  induction S generalizing x y with
  | nil =>
      simp [eraseSEnv, lookupSEnv]
  | cons hd tl ih =>
      cases hd with
      | mk z Tz =>
          by_cases hxz : x = z
          · subst hxz
            have hyx : y ≠ x := by simpa using hxy
            have hbeq : (y == x) = false := beq_eq_false_iff_ne.mpr hyx
            simpa [eraseSEnv, lookupSEnv, List.lookup, hbeq] using (ih (x:=x) (y:=y) hyx)
          · by_cases hyz : y = z
            · subst hyz
              simp [eraseSEnv, hxz, lookupSEnv, List.lookup]
            · have hbeq : (y == z) = false := beq_eq_false_iff_ne.mpr hyz
              simpa [eraseSEnv, hxz, lookupSEnv, List.lookup, hbeq] using (ih (x:=x) (y:=y) hxy)

lemma DisjointS_updateLeft {S₁ : SEnv} {Sown : OwnedEnv} {x : Var} {T : ValType}
    (hDisj : DisjointS S₁ (Sown : SEnv))
    (hNone : lookupSEnv S₁ x = none) :
    DisjointS S₁ (OwnedEnv.updateLeft Sown x T) := by
  have hRight : DisjointS S₁ Sown.right := DisjointS_owned_right hDisj
  have hLeft : DisjointS S₁ Sown.left := DisjointS_owned_left hDisj
  have hLeft' : DisjointS S₁ (updateSEnv Sown.left x T) :=
    DisjointS_update_right (S₁:=S₁) (S₂:=Sown.left) hLeft hNone
  have hRight' : DisjointS S₁ (eraseSEnv Sown.right x) := by
    intro y T₁ T₂ hL1 hL2
    by_cases hxy : y = x
    · subst hxy
      have hNoneErase : lookupSEnv (eraseSEnv Sown.right y) y = none :=
        lookupSEnv_erase_eq (S:=Sown.right) (x:=y)
      have : (some T₂ : Option ValType) = none := by simpa [hNoneErase] using hL2
      cases this
    · have hR : lookupSEnv Sown.right y = some T₂ := by
        have hEq := lookupSEnv_erase_ne (S:=Sown.right) (x:=x) (y:=y) hxy
        simpa [hEq] using hL2
      exact hRight y T₁ T₂ hL1 hR
  have hAll : DisjointS S₁ (eraseSEnv Sown.right x ++ updateSEnv Sown.left x T) :=
    DisjointS_append_right hRight' hLeft'
  simpa [OwnedEnv.updateLeft] using hAll

/-- Disjointness against an append gives disjointness against the left part. -/
lemma DisjointS_split_left {Ssh S₁ S₂ : SEnv} :
    DisjointS Ssh (S₁ ++ S₂) → DisjointS Ssh S₁ := by
  -- Project through the left-append subset.
  intro hDisj
  have hSub : SEnvDomSubset S₁ (S₁ ++ S₂) := by
    simpa using (SEnvDomSubset_append_left (S₁:=S₁) (S₂:=S₂))
  exact DisjointS_of_domsubset_right hSub hDisj

/-- Disjointness against an append gives disjointness against the right part. -/
lemma DisjointS_split_right {Ssh S₁ S₂ : SEnv} :
    DisjointS Ssh (S₁ ++ S₂) → DisjointS Ssh S₂ := by
  -- Project through the right-append subset.
  intro hDisj
  have hSub : SEnvDomSubset S₂ (S₁ ++ S₂) := by
    simpa using (SEnvDomSubset_append_right (S₁:=S₁) (S₂:=S₂))
  exact DisjointS_of_domsubset_right hSub hDisj

/-- Disjointness against an append gives disjointness against both parts. -/
lemma DisjointS_split_both {Ssh S₁ S₂ : SEnv} :
    DisjointS Ssh (S₁ ++ S₂) → DisjointS Ssh S₁ ∧ DisjointS Ssh S₂ := by
  -- Project both sides using the split lemmas.
  intro hDisj
  exact ⟨DisjointS_split_left hDisj, DisjointS_split_right hDisj⟩

/-- Extract disjointness against each split component of `Sown.left`. -/
lemma DisjointS_split_from_owned_left
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv}
    (split : ParSplit Sown.left G) :
    DisjointS Ssh (Sown : SEnv) →
    DisjointS Ssh split.S1 ∧ DisjointS Ssh split.S2 := by
  -- Rewrite Sown.left via split.hS, then project each side.
  intro hDisj
  have hLeftAll : DisjointS Ssh (split.S1 ++ split.S2) := by
    simpa [split.hS] using (DisjointS_owned_left (Sown:=Sown) hDisj)
  exact ⟨DisjointS_split_left hLeftAll, DisjointS_split_right hLeftAll⟩

/-- Repackage disjointness for an owned env with an extended right side. -/
lemma DisjointS_owned_repack
    {Ssh : SEnv} {Sright Sleft Smid : SEnv} :
    DisjointS Ssh Sright →
    DisjointS Ssh Sleft →
    DisjointS Ssh Smid →
    DisjointS Ssh ({ right := Sright ++ Smid, left := Sleft } : OwnedEnv) := by
  -- Combine right+mid+left disjointness via append.
  intro hRight hLeft hMid
  have hRight' : DisjointS Ssh (Sright ++ Smid) :=
    DisjointS_append_right hRight hMid
  have hAll : DisjointS Ssh ((Sright ++ Smid) ++ Sleft) :=
    DisjointS_append_right hRight' hLeft
  simpa [OwnedEnv.all, List.append_assoc] using hAll

/-- Finish par-left disjointness using the inner owned env. -/
lemma DisjointS_par_left_finish
    {Ssh : SEnv} {SownR S₂ S₁' : SEnv} :
    DisjointS Ssh SownR →
    DisjointS Ssh S₂ →
    DisjointS Ssh ({ right := SownR ++ S₂, left := S₁' } : OwnedEnv) →
    DisjointS Ssh ({ right := SownR, left := S₁' ++ S₂ } : OwnedEnv) := by
  -- Peel the left part and rebuild with appends.
  intro hDisjRight hDisjS2 hInnerRes
  have hDisjS1' : DisjointS Ssh S₁' :=
    DisjointS_owned_left (Sown:={ right := SownR ++ S₂, left := S₁' }) hInnerRes
  have hLeft : DisjointS Ssh (S₁' ++ S₂) := DisjointS_append_right hDisjS1' hDisjS2
  have hAll : DisjointS Ssh (SownR ++ (S₁' ++ S₂)) := DisjointS_append_right hDisjRight hLeft
  simpa [OwnedEnv.all, List.append_assoc] using hAll

/-- Finish par-right disjointness using the inner owned env. -/
lemma DisjointS_par_right_finish
    {Ssh : SEnv} {SownR S₁ S₂' : SEnv} :
    DisjointS Ssh SownR →
    DisjointS Ssh S₁ →
    DisjointS Ssh ({ right := SownR ++ S₁, left := S₂' } : OwnedEnv) →
    DisjointS Ssh ({ right := SownR, left := S₁ ++ S₂' } : OwnedEnv) := by
  -- Peel the left part and rebuild with appends.
  intro hDisjRight hDisjS1 hInnerRes
  have hDisjS2' : DisjointS Ssh S₂' :=
    DisjointS_owned_left (Sown:={ right := SownR ++ S₁, left := S₂' }) hInnerRes
  have hLeft : DisjointS Ssh (S₁ ++ S₂') := DisjointS_append_right hDisjS1 hDisjS2'
  have hAll : DisjointS Ssh (SownR ++ (S₁ ++ S₂')) := DisjointS_append_right hDisjRight hLeft
  simpa [OwnedEnv.all, List.append_assoc] using hAll

/-- Frame G on the right for a par-left subprocess. -/
lemma HasTypeProcPreOut_frame_G_right_par
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {split : ParSplit Sown.left G}
    {P : Process} {Sfin Gfin W Δ} :
    DisjointG split.G1 split.G2 →
    HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := split.S1 } split.G1 P Sfin Gfin W Δ →
    HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := split.S1 } G P Sfin (Gfin ++ split.G2) W Δ := by
  -- Frame on the right and rewrite G via split.hG.
  intro hDisjG hP
  have hP' :=
    HasTypeProcPreOut_frame_G_right (Ssh:=Ssh)
      (Sown:={ right := Sown.right ++ split.S2, left := split.S1 })
      (G:=split.G1) (Gfr:=split.G2) hDisjG hP
  simpa [split.hG] using hP'

/-- Frame G on the left for a par-right subprocess. -/
lemma HasTypeProcPreOut_frame_G_left_par
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {split : ParSplit Sown.left G}
    {Q : Process} {Sfin Gfin W Δ} :
    DisjointG split.G1 split.G2 →
    DisjointS (Sown.right ++ split.S1) split.S2 →
    HasTypeProcPreOut Ssh { right := Sown.right ++ split.S1, left := split.S2 } split.G2 Q Sfin Gfin W Δ →
    DisjointS (Sown.right ++ split.S1) Sfin.left →
    HasTypeProcPreOut Ssh { right := Sown.right ++ split.S1, left := split.S2 } G Q Sfin (split.G1 ++ Gfin) W Δ := by
  -- Frame on the left and rewrite G via split.hG.
  intro hDisjG hDisjIn hQ hDisjOut
  have hQ' :=
    HasTypeProcPreOut_frame_G_left (Ssh:=Ssh)
      (Sown:={ right := Sown.right ++ split.S1, left := split.S2 })
      (G:=split.G2) (Gfr:=split.G1) hDisjG hDisjIn hQ hDisjOut
  simpa [split.hG] using hQ'

end
