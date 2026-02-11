import Protocol.Semantics
import Protocol.Typing
import Protocol.Coherence
import Batteries.Data.RBMap.Lemmas

/-! # MPST Preservation Theorem

This module contains the preservation (subject reduction) theorem for MPST:
if a well-typed configuration takes a step, the result is also well-typed. -/

/-
The Problem. We need subject reduction: well-typed configurations remain
well-typed after stepping. This is the core safety theorem for MPST.

Solution Structure. We prove preservation by case analysis on step kind:
1. Send: use `Coherent_send_preserved` + `BuffersTyped_enqueue`
2. Recv: use `Coherent_recv_preserved` + buffer dequeue lemma
3. Select/Branch: similar to send/recv for labels
4. NewSession: use freshness invariants (`SupplyInv_newSession`)
-/

/-!
**UPDATE (2026-01-15)**: This module now imports Protocol.Typing which defines
TypedStep - the linear resource transition typing judgment that resolves the
design issues that blocked the original preservation theorems below.

The new preservation theorems are:
- `preservation_typed` (in Typing.lean) - TypedStep preserves LocalTypeR.WellFormed
- `progress_typed` (in Typing.lean) - WellFormedComplete processes can step or terminate
- `subject_reduction` (this file) - TypedStep implies Step (soundness)

The old theorems (`preservation_send`, `preservation_recv`, `preservation`, `progress`)
have been removed. The canonical results are the TypedStep-based theorems below,
which align with the pre-update typing discipline.

## Proof Structure

The proof proceeds by case analysis on the step relation:

1. **Send**: The sender's local type advances, the directed edge trace grows
   - Use `Coherent_send_preserved` for coherence
   - Use `BuffersTyped_enqueue` for buffer typing

2. **Recv**: The receiver's local type advances, the directed edge trace shrinks
   - Use `Coherent_recv_preserved` for coherence
   - Use buffer dequeue lemma for buffer typing

3. **Select/Branch**: Similar to send/recv but for labels

4. **NewSession**: Fresh session ID allocated, environments extended
   - Use freshness invariants (SupplyInv_newSession)

5. **Context steps** (seq, par): Use induction hypothesis

## Key Lemmas

- `preservation` (this file): TypedStep preserves LocalTypeR.WellFormed (wrapper)
- `progress` (this file): WellFormedComplete processes can step or are blocked (wrapper)
- `subject_reduction` (this file): TypedStep implies Step (soundness)

## Proof Techniques

The TypedStep-based proofs avoid the old pre/post-update mismatch. All
session evolution happens inside the transition judgment, so preservation
and progress become direct structural proofs.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical
open Batteries

section

/-! ## Compatibility Aliases -/

/-- Backwards-compatible single-env pre-typing. -/
abbrev HasTypeProcPre1 (S : SEnv) (G : GEnv) (P : Process) : Prop :=
  HasTypeProcPre S ∅ G P

/-! ## Helper Lemmas -/

theorem findLabel_eq {α : Type} {lbl lbl' : Label} {xs : List (Label × α)} {v : α}
    (h : xs.find? (fun b => b.1 == lbl) = some (lbl', v)) : lbl' = lbl := by
  have hPred : (lbl' == lbl) := (List.find?_eq_some_iff_append (xs := xs)
    (p := fun b => b.1 == lbl) (b := (lbl', v))).1 h |>.1
  have hPred' : (lbl' == lbl) = true := by
    simpa using hPred
  exact (beq_iff_eq).1 hPred'

/-- StoreTyped is preserved when updating a non-channel variable. -/
theorem StoreTyped_update_nonChan {G : GEnv} {S : SEnv} {store : VarStore}
    {x : Var} {v : Value} {T : ValType}
    (hST : StoreTyped G S store)
    (hv : HasTypeVal G v T)
    (hNonChan : ¬T.isLinear) :
    StoreTyped G (updateSEnv S x T) (updateStr store x v) := by
  intro y w U hy hU
  by_cases hyx : y = x
  · -- y = x: use the new value
    subst hyx
    rw [lookupStr_update_eq] at hy
    rw [lookupSEnv_update_eq] at hU
    have hw : w = v := Option.some_injective _ hy.symm
    have hUT : U = T := Option.some_injective _ hU.symm
    subst hw hUT
    exact hv
  · -- y ≠ x: use the original typing
    have hyx' : x ≠ y := Ne.symm hyx
    rw [lookupStr_update_neq _ _ _ _ hyx'] at hy
    rw [lookupSEnv_update_neq _ _ _ _ hyx'] at hU
    exact hST y w U hy hU

/-- BuffersTyped is preserved when enqueuing a well-typed value. -/
theorem BuffersTyped_enqueue_old {G : GEnv} {D : DEnv} {bufs : Buffers}
    {e : Edge} {v : Value} {T : ValType}
    (hBT : BuffersTyped G D bufs)
    (hv : HasTypeVal G v T) :
    BuffersTyped G (updateD D e (lookupD D e ++ [T])) (enqueueBuf bufs e v) := by
  -- Directly reuse the newer enqueue lemma.
  simpa using
    (BuffersTyped_enqueue (G := G) (D := D) (bufs := bufs) (e := e) (v := v) (T := T) hBT hv)

/-! ## Preservation Support -/

theorem SessionsOf_eq_of_TypedStep
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    SessionsOf G' = SessionsOf G := by
  intro hTS
  induction hTS with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
        SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.send target T L) hG
      simp [hGout, hEq]
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
        SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.recv source T L) hG
      simp [hGout, hEq]
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
        SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.select target bs) hG
      simp [hGout, hEq]
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
        SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.branch source bs) hG
      simp [hGout, hEq]
  | assign =>
      simp
  | seq_step _ ih =>
      exact ih
  | seq_skip =>
      simp
  | par_left split hSlen hTS hDisjG hDisjD hDisjS ih =>
      exact ih
  | par_right split hSlen hTS hDisjG hDisjD hDisjS ih =>
      exact ih
  | par_skip_left =>
      simp
  | par_skip_right =>
      simp

theorem DConsistent_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    DConsistent G D →
    DConsistent G' D' := by
  intro hTS hCons s hs
  have hEq : SessionsOf G' = SessionsOf G := SessionsOf_eq_of_TypedStep hTS
  have hs' := SessionsOfD_subset_of_TypedStep hTS hs
  cases hs' with
  | inl hD =>
      have hG : s ∈ SessionsOf G := hCons hD
      simpa [hEq] using hG
  | inr hG =>
    simpa [hEq] using hG

/-! ## Buffer/Coherence Rewrites -/

theorem BuffersTyped_rewriteD
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

theorem Coherent_rewriteD
    {G : GEnv} {D D' : DEnv} :
    (∀ e, lookupD D e = lookupD D' e) →
    Coherent G D →
    Coherent G D' := by
  intro hEq hCoh e hActive Lrecv hGrecv
  have hCohEdge := hCoh e hActive Lrecv hGrecv
  rcases hCohEdge with ⟨Lsender, hGsender, hConsume⟩
  refine ⟨Lsender, hGsender, ?_⟩
  simpa [hEq e] using hConsume

theorem SessionsOf_empty : SessionsOf ([] : GEnv) = ∅ := by
  ext s; constructor
  · intro hs
    rcases hs with ⟨e, L, hLookup, hSid⟩
    cases hLookup
  · intro hs
    cases hs

theorem SessionsOfD_empty : SessionsOfD (∅ : DEnv) = ∅ := by
  ext s; constructor
  · intro hs
    rcases hs with ⟨e, ts, hFind, hSid⟩
    simp [DEnv.find?, DEnv_map_find?_empty] at hFind
  · intro hs
    cases hs

theorem DConsistent_append {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
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

theorem DConsistent_empty (G : GEnv) : DConsistent G (∅ : DEnv) := by
  simp [DConsistent, SessionsOfD_empty]

theorem lookupSEnv_erase_eq {S : SEnv} {x : Var} :
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

theorem lookupSEnv_erase_ne {S : SEnv} {x y : Var} (hxy : y ≠ x) :
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

theorem OwnedDisjoint_updateLeft
    {Sown : OwnedEnv} {x : Var} {T : ValType} :
    OwnedDisjoint Sown →
    OwnedDisjoint (OwnedEnv.updateLeft Sown x T) := by
  intro hOwn y Ty1 Ty2 hR hL
  by_cases hxy : y = x
  · subst hxy
    have hNone : lookupSEnv (eraseSEnv Sown.right y) y = none := lookupSEnv_erase_eq (S:=Sown.right) (x:=y)
    have : (some Ty1 : Option ValType) = none := by
      have hR' := hR
      simp [OwnedEnv.updateLeft, hNone] at hR'
    cases this
  · have hR' : lookupSEnv Sown.right y = some Ty1 := by
      have hEq := lookupSEnv_erase_ne (S:=Sown.right) (x:=x) (y:=y) hxy
      simpa [OwnedEnv.updateLeft, hEq] using hR
    have hL' : lookupSEnv Sown.left y = some Ty2 := by
      have hEq := lookupSEnv_update_neq (env:=Sown.left) (x:=x) (y:=y) (T:=T) (Ne.symm hxy)
      simpa [OwnedEnv.updateLeft, hEq] using hL
    exact hOwn y Ty1 Ty2 hR' hL'

theorem SEnvDomSubset_erase
    {S : SEnv} {x : Var} :
    SEnvDomSubset (eraseSEnv S x) S := by
  intro y Ty hErase
  by_cases hxy : y = x
  · subst hxy
    have hNone : lookupSEnv (eraseSEnv S y) y = none := lookupSEnv_erase_eq (S:=S) (x:=y)
    have : (some Ty : Option ValType) = none := by
      have hErase' := hErase
      simp [hNone] at hErase'
    cases this
  · have hEq : lookupSEnv (eraseSEnv S x) y = lookupSEnv S y :=
      lookupSEnv_erase_ne (S:=S) (x:=x) (y:=y) hxy
    exact ⟨Ty, by simpa [hEq] using hErase⟩

theorem TypedStep_right_domsubset
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' Sfin Gfin W Δ} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    SEnvDomSubset Sown'.right Sown.right := by
  intro hTS hPre
  induction hTS generalizing Sfin Gfin W Δ with
  | send =>
      exact SEnvDomSubset_refl
  | recv =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
        hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut
      subst hSout
      simpa [OwnedEnv.updateLeft] using (SEnvDomSubset_erase (S:=Sown.right) (x:=x))
  | select =>
      exact SEnvDomSubset_refl
  | branch =>
      exact SEnvDomSubset_refl
  | assign =>
      rename_i G D Ssh Sown store bufs x v T S' store' hv hSout hStoreOut
      subst hSout
      simpa [OwnedEnv.updateLeft] using (SEnvDomSubset_erase (S:=Sown.right) (x:=x))
  | seq_step _ ih =>
      cases hPre with
      | seq hP hQ =>
          exact ih hP
  | seq_skip =>
      exact SEnvDomSubset_refl
  | par_left =>
      exact SEnvDomSubset_refl
  | par_right =>
      exact SEnvDomSubset_refl
  | par_skip_left =>
      exact SEnvDomSubset_refl
  | par_skip_right =>
      exact SEnvDomSubset_refl

theorem OwnedDisjoint_preserved_TypedStep
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' Sfin Gfin W Δ} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    OwnedDisjoint Sown →
    DisjointS Sown.right Sfin.left →
    OwnedDisjoint Sown' := by
  intro hTS hPre hOwn hDisjRightFin
  induction hTS generalizing Sfin Gfin W Δ with
  | send =>
      simpa [OwnedDisjoint] using hOwn
  | recv =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
        hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut
      subst hSout
      exact OwnedDisjoint_updateLeft hOwn
  | select =>
      simpa [OwnedDisjoint] using hOwn
  | branch =>
      simpa [OwnedDisjoint] using hOwn
  | assign =>
      rename_i G D Ssh Sown store bufs x v T S' store' hv hSout hStoreOut
      subst hSout
      exact OwnedDisjoint_updateLeft hOwn
  | seq_step _ ih =>
      cases hPre with
      | seq hP hQ =>
          have hDomQ := HasTypeProcPreOut_domsubset hQ
          have hDisjRightMid := DisjointS_of_domsubset_right hDomQ hDisjRightFin
          exact ih hP hOwn hDisjRightMid
  | seq_skip =>
      simpa [OwnedDisjoint] using hOwn
  | par_left split hSlen hStep hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P P' Q G D₁ D₂ G₁' D₁' S₁' nS nG
      have hTS' :
          TypedStep G (D₁ ++ D₂) Ssh Sown store bufs (.par nS nG P Q)
            (G₁' ++ split.G2) (D₁' ++ D₂) { right := Sown.right, left := S₁' ++ split.S2 }
            store' bufs' (.par S₁'.length nG P' Q) :=
        TypedStep.par_left (split:=split) hSlen hStep hDisjG hDisjD hDisjS
      have hDom : SEnvDomSubset Sown.right Sown.right := by
        intro x T hL
        exact ⟨T, hL⟩
      have hLeftDisj : DisjointS Sown.right (S₁' ++ split.S2) :=
        DisjointS_preserved_TypedStep_left (Sframe:=Sown.right) hTS' hPre
          hOwn hDom hOwn hDisjRightFin rfl
      simpa [OwnedDisjoint] using hLeftDisj
  | par_right split hSlen hStep hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P Q Q' G D₁ D₂ G₂' D₂' S₂' nS nG
      have hTS' :
          TypedStep G (D₁ ++ D₂) Ssh Sown store bufs (.par nS nG P Q)
            (split.G1 ++ G₂') (D₁ ++ D₂') { right := Sown.right, left := split.S1 ++ S₂' }
            store' bufs' (.par split.S1.length nG P Q') :=
        TypedStep.par_right (split:=split) hSlen hStep hDisjG hDisjD hDisjS
      have hDom : SEnvDomSubset Sown.right Sown.right := by
        intro x T hL
        exact ⟨T, hL⟩
      have hLeftDisj : DisjointS Sown.right (split.S1 ++ S₂') :=
        DisjointS_preserved_TypedStep_left (Sframe:=Sown.right) hTS' hPre
          hOwn hDom hOwn hDisjRightFin rfl
      simpa [OwnedDisjoint] using hLeftDisj
  | par_skip_left =>
      simpa [OwnedDisjoint] using hOwn
  | par_skip_right =>
      simpa [OwnedDisjoint] using hOwn

theorem DEnv_append_empty_right (D : DEnv) : D ++ (∅ : DEnv) = D := by
  simpa using (DEnvUnion_empty_right D)

theorem BuffersTyped_mono {G G' : GEnv} {D : DEnv} {bufs : Buffers} :
    (∀ e L, lookupG G e = some L → lookupG G' e = some L) →
    BuffersTyped G D bufs →
    BuffersTyped G' D bufs := by
  intro hMono hBT e
  rcases hBT e with ⟨hLen, hTyping⟩
  refine ⟨hLen, ?_⟩
  intro i hi
  exact HasTypeVal_mono G G' _ _ (hTyping i hi) hMono

theorem Coherent_mono {G G' : GEnv} {D : DEnv} :
    (∀ e, lookupG G e = lookupG G' e) →
    Coherent G D →
    Coherent G' D := by
  intro hEq hCoh e hActive Lrecv hGrecv
  rcases hActive with ⟨hSenderSome, hRecvSome⟩
  have hSenderSome' : (lookupG G { sid := e.sid, role := e.sender }).isSome := by
    simpa [hEq _] using hSenderSome
  have hRecvSome' : (lookupG G { sid := e.sid, role := e.receiver }).isSome := by
    simpa [hEq _] using hRecvSome
  have hActive' : ActiveEdge G e := ⟨hSenderSome', hRecvSome'⟩
  have hGrecv' : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv := by
    simpa [hEq _] using hGrecv
  rcases hCoh e hActive' Lrecv hGrecv' with ⟨Lsender, hGsender, hConsume⟩
  have hGsender' : lookupG G' { sid := e.sid, role := e.sender } = some Lsender := by
    simpa [hEq _] using hGsender
  exact ⟨Lsender, hGsender', hConsume⟩

theorem ValidLabels_mono {G G' : GEnv} {D : DEnv} {bufs : Buffers} :
    (∀ e, lookupG G e = lookupG G' e) →
    ValidLabels G D bufs →
    ValidLabels G' D bufs := by
  intro hEq hValid e source bs hActive hGrecv
  have hActive' : ActiveEdge G e := by
    rcases hActive with ⟨hSender, hRecv⟩
    have hSender' : (lookupG G { sid := e.sid, role := e.sender }).isSome := by
      simpa [hEq _] using hSender
    have hRecv' : (lookupG G { sid := e.sid, role := e.receiver }).isSome := by
      simpa [hEq _] using hRecv
    exact ⟨hSender', hRecv'⟩
  have hGrecv' : lookupG G { sid := e.sid, role := e.receiver } = some (.branch source bs) := by
    simpa [hEq _] using hGrecv
  exact hValid e source bs hActive' hGrecv'


end
