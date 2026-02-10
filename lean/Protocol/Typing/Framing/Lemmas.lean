import Protocol.Environments.Core
import Protocol.Typing.StepLemmas
import Protocol.Typing.MergeLemmas
import Protocol.Typing.Framing.GEnvFrameHelpers

/-! # MPST Framing Lemmas

Small framing lemmas for lookup, disjointness, and typing judgments. -/

/-
The Problem. Establish small framing lemmas for lookup, disjointness, and
pre/pre-out typing so later preservation proofs can be assembled compositionally.

Solution Structure. First, prove lookup and disjointness transport lemmas for
owned environments and concatenated G/S environments. Then, lift typing
judgments through left/right frames and package constructor-specific helpers.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

private theorem lookupSEnv_all_frame_prefix_ofLeft
    {Ssh S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    DisjointS S₁ S₂ →
    lookupSEnv (SEnvAll Ssh (S₂ : OwnedEnv)) x = some T →
    lookupSEnv (SEnvAll Ssh { right := S₁, left := S₂ }) x = some T := by
  intro hDisj hLookup
  have hLookup' : lookupSEnv (Ssh ++ S₂) x = some T := by
    simpa [SEnvAll_ofLeft] using hLookup
  have hFrame := lookupSEnv_all_frame_left (Ssh:=Ssh) (S₁:=S₁) (S₂:=S₂) hDisj hLookup'
  simpa [SEnvAll, List.append_assoc] using hFrame

private theorem lookupSEnv_all_frame_left_owned
    {Ssh : SEnv} {Sown : OwnedEnv} {Sframe : SEnv} {x : Var} {T : ValType} :
    DisjointS Sframe Sown.left →
    lookupSEnv (SEnvAll Ssh Sown) x = some T →
    lookupSEnv (SEnvAll Ssh { right := Sown.right, left := Sframe ++ Sown.left }) x = some T := by
  intro hDisj hLookup
  have hLookup' : lookupSEnv ((Ssh ++ Sown.right) ++ Sown.left) x = some T := by
    have hEq := lookupSEnv_append_assoc (S₁:=Ssh) (S₂:=Sown.right) (S₃:=Sown.left) (x:=x)
    simpa [SEnvAll, hEq] using hLookup
  have hFrame :=
    lookupSEnv_all_frame_left (Ssh:=Ssh ++ Sown.right) (S₁:=Sframe) (S₂:=Sown.left) hDisj hLookup'
  have hEq' := lookupSEnv_append_assoc (S₁:=Ssh) (S₂:=Sown.right) (S₃:=Sframe ++ Sown.left) (x:=x)
  simpa [SEnvAll, hEq', List.append_assoc] using hFrame

private theorem lookupSEnv_all_frame_right_owned
    {Ssh : SEnv} {Sown : OwnedEnv} {Sframe : SEnv} {x : Var} {T : ValType} :
    lookupSEnv (SEnvAll Ssh Sown) x = some T →
    lookupSEnv (SEnvAll Ssh { right := Sown.right, left := Sown.left ++ Sframe }) x = some T := by
  intro hLookup
  have hLookup' : lookupSEnv (Ssh ++ (Sown.right ++ Sown.left)) x = some T := by
    simpa [SEnvAll] using hLookup
  have hLeft :=
    lookupSEnv_append_left (S₁:=Ssh ++ (Sown.right ++ Sown.left)) (S₂:=Sframe) (x:=x) (T:=T) hLookup'
  simpa [SEnvAll, List.append_assoc] using hLeft

private theorem lookupSEnv_all_frame_right_prefix
    {Ssh : SEnv} {Sown : OwnedEnv} {Sframe : SEnv} {x : Var} {T : ValType} :
    DisjointS Sframe Sown.right →
    DisjointS Sframe Sown.left →
    lookupSEnv (SEnvAll Ssh Sown) x = some T →
    lookupSEnv (SEnvAll Ssh { right := Sframe ++ Sown.right, left := Sown.left }) x = some T := by
  intro hDisjR hDisjL hLookup
  have hDisj : DisjointS Sframe (Sown.right ++ Sown.left) := by
    intro x T₁ T₂ hL1 hL12
    cases hLr : lookupSEnv Sown.right x with
    | some T₁' =>
        have hEq : T₁' = T₂ := by
          have hLeft := lookupSEnv_append_left (S₁:=Sown.right) (S₂:=Sown.left) (x:=x) (T:=T₁') hLr
          exact Option.some.inj (by simpa [hLeft] using hL12)
        exact hDisjR x T₁ T₁' hL1 (by simpa [hEq] using hLr)
    | none =>
        have hRight := lookupSEnv_append_right (S₁:=Sown.right) (S₂:=Sown.left) (x:=x) hLr
        have hL2 : lookupSEnv Sown.left x = some T₂ := by
          simpa [hRight] using hL12
        exact hDisjL x T₁ T₂ hL1 hL2
  have hLookup' : lookupSEnv (Ssh ++ (Sown.right ++ Sown.left)) x = some T := by
    simpa [SEnvAll] using hLookup
  have hFrame := lookupSEnv_all_frame_left (Ssh:=Ssh) (S₁:=Sframe) (S₂:=Sown.right ++ Sown.left) hDisj hLookup'
  simpa [SEnvAll, List.append_assoc] using hFrame

private lemma lookupSEnv_comm_of_disjoint {S₁ S₂ : SEnv} (hDisj : DisjointS S₁ S₂) :
    ∀ x, lookupSEnv (S₁ ++ S₂) x = lookupSEnv (S₂ ++ S₁) x := by
  intro x
  cases hLeft : lookupSEnv S₁ x with
  | some T₁ =>
      have hRight : lookupSEnv S₂ x = none :=
        lookupSEnv_none_of_disjoint_left (S₁:=S₂) (S₂:=S₁) (x:=x) (T:=T₁) (DisjointS_symm hDisj) hLeft
      have hA := lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T₁) hLeft
      have hB := lookupSEnv_append_right (S₁:=S₂) (S₂:=S₁) (x:=x) hRight
      simpa [hA, hB, hLeft]
  | none =>
      have hA := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hLeft
      cases hRight : lookupSEnv S₂ x with
      | some T₂ =>
          have hB := lookupSEnv_append_left (S₁:=S₂) (S₂:=S₁) (x:=x) (T:=T₂) hRight
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

lemma lookupSEnv_swap_left_prefix {Ssh S₁ S₂ S₃ : SEnv} (hDisj : DisjointS S₁ S₂) :
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

/-! ### Framing Lemmas -/

/-- HasTypeVal is stable under framing on the left of G. -/
theorem HasTypeVal_frame_left {G₁ G₂ : GEnv} {v : Value} {T : ValType} :
    DisjointG G₁ G₂ →
    HasTypeVal G₂ v T →
    HasTypeVal (G₁ ++ G₂) v T := by
  intro hDisj hv
  cases hv with
  | unit => exact HasTypeVal.unit
  | bool b => exact HasTypeVal.bool b
  | nat n => exact HasTypeVal.nat n
  | string s => exact HasTypeVal.string s
  | prod h₁ h₂ =>
      exact HasTypeVal.prod (HasTypeVal_frame_left hDisj h₁) (HasTypeVal_frame_left hDisj h₂)
  | chan h =>
      rename_i e L
      have hDisjSym := DisjointG_symm hDisj
      have hNone : lookupG G₁ e = none :=
        DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym h
      have hLookup : lookupG (G₁ ++ G₂) e = some L := by
        simpa [lookupG_append_right hNone] using h
      exact HasTypeVal.chan hLookup

/-- Pre-update typing is stable under framing on the left of G (no S changes). -/
private theorem HasTypeProcPre_frame_G_branch
    {Ssh : SEnv} {Sown : OwnedEnv} {G₁ G : GEnv} {k : Var} {procs : List (Label × Process)}
    {e : Endpoint} {p : Role} {bs : List (Label × LocalType)} :
    DisjointG G₁ G →
    lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e.sid e.role) →
    lookupG G e = some (.branch p bs) →
    bs.length = procs.length →
    (∀ i (hi : i < bs.length) (hip : i < procs.length),
        (procs.get ⟨i, hip⟩).1 = (bs.get ⟨i, hi⟩).1) →
    (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown (updateG G e (bs.get ⟨i, hi⟩).2) (procs.get ⟨i, hip⟩).2) →
    (∀ i (hi : i < bs.length) (hip : i < procs.length) {G₁' : GEnv},
        DisjointG G₁' (updateG G e (bs.get ⟨i, hi⟩).2) →
          HasTypeProcPre Ssh Sown
            (G₁' ++ updateG G e (bs.get ⟨i, hi⟩).2)
            (procs.get ⟨i, hip⟩).2) →
    HasTypeProcPre Ssh Sown (G₁ ++ G) (.branch k procs) := by
  intro hDisj hk hG hLen hLbl hProcs ih
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .branch p bs, hG, rfl⟩
  have hNot : e.sid ∉ SessionsOf G₁ := by
    intro hIn
    have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G := ⟨hIn, hSid⟩
    have hEmpty : SessionsOf G₁ ∩ SessionsOf G = (∅ : Set SessionId) := by
      simpa [DisjointG, GEnvDisjoint] using hDisj
    have : e.sid ∈ (∅ : Set SessionId) := by
      simpa [hEmpty] using hInter
    exact this.elim
  have hNone : lookupG G₁ e = none := lookupG_none_of_not_session (G:=G₁) hNot
  have hG' : lookupG (G₁ ++ G) e = some (.branch p bs) := by
    simpa [lookupG_append_right hNone] using hG
  have hProcs' :
      ∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown
          (updateG (G₁ ++ G) e (bs.get ⟨i, hi⟩).2)
          (procs.get ⟨i, hip⟩).2 := by
    intro i hi hip
    have hSub : SessionsOf (updateG G e (bs.get ⟨i, hi⟩).2) ⊆ SessionsOf G := by
      intro s hs
      rcases hs with ⟨e', L', hLookup, hSid'⟩
      by_cases hEq : e' = e
      · subst hEq
        simpa [hSid'] using hSid
      · have hLookup' : lookupG G e' = some L' := by
          have h :=
            lookupG_update_neq (env:=G) (e:=e) (e':=e') (L:= (bs.get ⟨i, hi⟩).2) (Ne.symm hEq)
          rw [h] at hLookup
          exact hLookup
        exact ⟨e', L', hLookup', hSid'⟩
    have hDisj' : DisjointG G₁ (updateG G e (bs.get ⟨i, hi⟩).2) := by
      have hDisjSym := DisjointG_symm hDisj
      have hDisj'' :=
        DisjointG_of_subset_left (G₁:=G) (G₁':=updateG G e (bs.get ⟨i, hi⟩).2)
          (G₂:=G₁) hSub hDisjSym
      exact DisjointG_symm hDisj''
    have hPre' := ih i hi hip (G₁':=G₁) hDisj'
    have hUpd :
        updateG (G₁ ++ G) e (bs.get ⟨i, hi⟩).2 =
          G₁ ++ updateG G e (bs.get ⟨i, hi⟩).2 :=
      updateG_append_left (G₁:=G₁) (G₂:=G) (e:=e) (L:= (bs.get ⟨i, hi⟩).2) hNone
    rw [hUpd.symm] at hPre'
    exact hPre'
  exact HasTypeProcPre.branch hk hG' hLen hLbl hProcs'

theorem HasTypeProcPre_frame_G {Ssh : SEnv} {Sown : OwnedEnv} {G₁ G₂ : GEnv} {P : Process} :
    DisjointG G₁ G₂ →
    HasTypeProcPre Ssh Sown G₂ P →
    HasTypeProcPre Ssh Sown (G₁ ++ G₂) P := by
  intro hDisj hPre
  induction hPre generalizing G₁ with
  | skip =>
      rename_i Sown G
      simpa using (HasTypeProcPre.skip (Ssh:=Ssh) (Sown:=Sown) (G:=G₁ ++ G))
  | send hk hG hx =>
      rename_i Sown G k x e q T L
      have hNone : lookupG G₁ e = none :=
        DisjointG_lookup_left (G₁:=G) (G₂:=G₁) (DisjointG_symm hDisj) hG
      have hG' : lookupG (G₁ ++ G) e = some (.send q T L) := by
        simpa [lookupG_append_right hNone] using hG
      exact HasTypeProcPre.send hk hG' hx
  | recv hk hG hNoSh =>
      rename_i Sown G k x e p T L
      have hNone : lookupG G₁ e = none :=
        DisjointG_lookup_left (G₁:=G) (G₂:=G₁) (DisjointG_symm hDisj) hG
      have hG' : lookupG (G₁ ++ G) e = some (.recv p T L) := by
        simpa [lookupG_append_right hNone] using hG
      exact HasTypeProcPre.recv hk hG' hNoSh
  | select hk hG hbs =>
      rename_i Sown G k l e q bs L
      have hNone : lookupG G₁ e = none :=
        DisjointG_lookup_left (G₁:=G) (G₂:=G₁) (DisjointG_symm hDisj) hG
      have hG' : lookupG (G₁ ++ G) e = some (.select q bs) := by
        simpa [lookupG_append_right hNone] using hG
      exact HasTypeProcPre.select hk hG' hbs
  | branch hk hG hLen hLbl hProcs ih =>
      rename_i Sown G k procs e p bs
      exact HasTypeProcPre_frame_G_branch (G₁:=G₁) (G:=G) (k:=k) (procs:=procs)
        (e:=e) (p:=p) (bs:=bs)
        hDisj hk hG hLen hLbl hProcs
        (by
          intro i hi hip G₁' hDisj'
          exact ih i hi hip hDisj')
  | seq hP hQ ihP ihQ =>
      exact HasTypeProcPre.seq (ihP hDisj) (ihQ hDisj)
  | par hDisjS hSplit hP hQ ihP ihQ =>
      exact HasTypeProcPre.par hDisjS hSplit (ihP hDisj) (ihQ hDisj)
  | assign hNoSh hv =>
      exact HasTypeProcPre.assign hNoSh (HasTypeVal_frame_left hDisj hv)

/-- Frame a disjoint GEnv on the left of pre-typing. -/
lemma HasTypeProcPre_frame_G_left {Ssh : SEnv} {Sown : OwnedEnv} {Gfr G : GEnv} {P : Process} :
    DisjointG Gfr G →
    HasTypeProcPre Ssh Sown G P →
    HasTypeProcPre Ssh Sown (Gfr ++ G) P :=
  HasTypeProcPre_frame_G

/-- Any SEnv is domain-included in its right-framed extension. -/
theorem SEnvDomSubset_into_right_frame {Sbase Sframe : SEnv} :
    SEnvDomSubset Sbase (Sbase ++ Sframe) := by
  intro x T hLookup
  exact ⟨T, lookupSEnv_append_left (S₁:=Sbase) (S₂:=Sframe) (x:=x) (T:=T) hLookup⟩

/-- Dom-subset transports lookup absence from a right frame back to the source. -/
theorem lookupSEnv_none_of_domsubset_right
    {Sframe Sright : SEnv} {x : Var} :
    SEnvDomSubset Sframe Sright →
    lookupSEnv Sright x = none →
    lookupSEnv Sframe x = none := by
  intro hSub hNo
  by_cases hNone : lookupSEnv Sframe x = none
  · exact hNone
  · cases hL : lookupSEnv Sframe x with
    | none => exact (hNone hL).elim
    | some T =>
        obtain ⟨T', hRight⟩ := hSub hL
        simpa [hNo] using hRight

/-- Disjointness with an appended SEnv implies disjointness with the left side. -/
private theorem DisjointS_of_append_left {S₁ S₂ S₃ : SEnv} :
    DisjointS S₁ (S₂ ++ S₃) → DisjointS S₁ S₂ := by
  -- Shrink the right side using domain subset.
  intro hDisj
  have hDom : SEnvDomSubset S₂ (S₂ ++ S₃) := SEnvDomSubset_append_left (S₁:=S₂) (S₂:=S₃)
  exact DisjointS_of_domsubset_right hDom hDisj

/-- Disjointness with an appended SEnv implies disjointness with the right side. -/
private theorem DisjointS_of_append_right {S₁ S₂ S₃ : SEnv} :
    DisjointS S₁ (S₂ ++ S₃) → DisjointS S₁ S₃ := by
  -- Shrink the right side using domain subset.
  intro hDisj
  have hDom : SEnvDomSubset S₃ (S₂ ++ S₃) := SEnvDomSubset_append_right (S₁:=S₂) (S₂:=S₃)
  exact DisjointS_of_domsubset_right hDom hDisj

/-- Disjointness distributes over right appends. -/
private theorem DisjointS_append_right
    {Ssh S₁ S₂ : SEnv} :
    DisjointS Ssh S₁ →
    DisjointS Ssh S₂ →
    DisjointS Ssh (S₁ ++ S₂) := by
  -- Route the append lookup to the appropriate side.
  intro hDisj1 hDisj2 x T₁ T₂ hLsh hL12
  cases hL1 : lookupSEnv S₁ x with
  | some T₁' =>
      have hEq : T₁' = T₂ := by
        have hLeft := lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T₁') hL1
        exact Option.some.inj (by simpa [hLeft] using hL12)
      exact hDisj1 x T₁ T₁' hLsh (by simpa [hEq] using hL1)
  | none =>
      have hRight := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hL1
      have hL2 : lookupSEnv S₂ x = some T₂ := by
        simpa [hRight] using hL12
      exact hDisj2 x T₁ T₂ hLsh hL2

/-- DisjointG distributes over right appends. -/
theorem DisjointG_append_right {G₁ G₂ G₃ : GEnv} :
    DisjointG G₁ G₂ →
    DisjointG G₁ G₃ →
    DisjointG G₁ (G₂ ++ G₃) := by
  intro hDisj12 hDisj13
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro s hs
  rcases hs with ⟨h1, h23⟩
  have h23' : s ∈ SessionsOf G₂ ∪ SessionsOf G₃ :=
    SessionsOf_append_subset (G₁:=G₂) (G₂:=G₃) h23
  cases h23' with
  | inl h2 =>
      have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := hDisj12
      have hInter : s ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨h1, h2⟩
      have : s ∈ (∅ : Set SessionId) := by
        simpa [hEmpty] using hInter
      exact this.elim
  | inr h3 =>
      have hEmpty : SessionsOf G₁ ∩ SessionsOf G₃ = (∅ : Set SessionId) := hDisj13
      have hInter : s ∈ SessionsOf G₁ ∩ SessionsOf G₃ := ⟨h1, h3⟩
      have : s ∈ (∅ : Set SessionId) := by
        simpa [hEmpty] using hInter
      exact this.elim

private lemma SessionsOf_empty : SessionsOf ([] : GEnv) = (∅ : Set SessionId) := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro s hs
  rcases hs with ⟨e, L, hLookup, _⟩
  have : False := by
    simpa [lookupG] using hLookup
  exact this.elim

lemma DisjointG_right_empty (G : GEnv) : DisjointG G ([] : GEnv) := by
  simp [DisjointG, GEnvDisjoint, SessionsOf_empty]

/-- DisjointG with an appended GEnv implies disjointness with the left side. -/
private theorem DisjointG_of_append_left {G₁ G₂ G₃ : GEnv} :
    DisjointG G₁ (G₂ ++ G₃) → DisjointG G₁ G₂ := by
  -- Shrink the right side using session subset.
  intro hDisj
  have hDisjSym := DisjointG_symm hDisj
  have hSub : SessionsOf G₂ ⊆ SessionsOf (G₂ ++ G₃) := SessionsOf_append_left (G₁:=G₂) (G₂:=G₃)
  have hDisj' := DisjointG_of_subset_left hSub hDisjSym
  exact DisjointG_symm hDisj'

/-- DisjointG with an appended GEnv implies disjointness with the right side. -/
private theorem DisjointG_of_append_right {G₁ G₂ G₃ : GEnv} :
    DisjointG G₁ (G₂ ++ G₃) → DisjointG G₁ G₃ := by
  -- Shrink the right side using session subset.
  intro hDisj
  have hDisjSym := DisjointG_symm hDisj
  have hSub : SessionsOf G₃ ⊆ SessionsOf (G₂ ++ G₃) := SessionsOf_append_right (G₁:=G₂) (G₂:=G₃)
  have hDisj' := DisjointG_of_subset_left hSub hDisjSym
  exact DisjointG_symm hDisj'

/-- Lift a GEnv lookup across a left frame using disjointness. -/
private theorem lookupG_frame_left {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType} :
    DisjointG G₁ G₂ →
    lookupG G₂ e = some L →
    lookupG (G₁ ++ G₂) e = some L := by
  intro hDisj hLookup
  have hDisjSym := DisjointG_symm hDisj
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hLookup
  simpa [lookupG_append_right hNone] using hLookup

/-- GEnv disjointness is preserved when updating an existing endpoint on the right. -/
private theorem DisjointG_updateG_left
    {G₁ G₂ : GEnv} {e : Endpoint} {L L' : LocalType} :
    DisjointG G₁ G₂ →
    lookupG G₂ e = some L →
    DisjointG G₁ (updateG G₂ e L') := by
  -- Updating an existing endpoint does not add new session ids.
  intro hDisj hLookup
  have hSub : SessionsOf (updateG G₂ e L') ⊆ SessionsOf G₂ := by
    intro s hs
    rcases hs with ⟨e', L'', hLookup', hSid⟩
    by_cases hEq : e' = e
    · have hLookup'' : lookupG G₂ e' = some L := by
        simpa [hEq] using hLookup
      exact ⟨e', L, hLookup'', hSid⟩
    · have hLookup'' : lookupG G₂ e' = some L'' := by
        have h := lookupG_update_neq (env:=G₂) (e:=e) (e':=e') (L:=L') (Ne.symm hEq)
        simpa [h] using hLookup'
      exact ⟨e', L'', hLookup'', hSid⟩
  have hDisjSym := DisjointG_symm hDisj
  have hDisj' :=
    DisjointG_of_subset_left (G₁:=G₂) (G₁':=updateG G₂ e L') (G₂:=G₁) hSub hDisjSym
  exact DisjointG_symm hDisj'

lemma lookupG_none_of_disjoint {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂)
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

-- NOTE: We intentionally avoid general G-framing lemmas here to keep full-G
-- reasoning explicit under the par-step rule.

/-- Pre-update typing is stable under framing on the left of S/G. -/
theorem HasTypeProcPre_frame_left
    {Ssh : SEnv} {Sown : OwnedEnv} {Sframe : SEnv} {G₁ G₂ : GEnv} {P : Process} :
    DisjointS Sframe Sown.right →
    DisjointS Sframe Sown.left →
    DisjointG G₁ G₂ →
    HasTypeProcPre Ssh Sown G₂ P →
    HasTypeProcPre Ssh { right := Sframe ++ Sown.right, left := Sown.left } (G₁ ++ G₂) P := by
  intro hDisjR hDisjL hDisjG hPre
  induction hPre generalizing G₁ Sframe with
  | skip =>
      rename_i Sown G
      simpa using
        (HasTypeProcPre.skip
          (Ssh:=Ssh)
          (Sown:={ right := Sframe ++ Sown.right, left := Sown.left })
          (G:=G₁ ++ G))
  | send hk hG hx =>
      rename_i Sown G k x e q T L
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := Sframe ++ Sown.right, left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible, List.append_assoc] using hk
      have hG' := lookupG_frame_left hDisjG hG
      have hx' :
          lookupSEnv (SEnvVisible Ssh { right := Sframe ++ Sown.right, left := Sown.left }) x = some T := by
        simpa [SEnvVisible, List.append_assoc] using hx
      exact HasTypeProcPre.send hk' hG' hx'
  | recv hk hG hNoSh =>
      rename_i Sown G k x e p T L
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := Sframe ++ Sown.right, left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible, List.append_assoc] using hk
      have hG' := lookupG_frame_left hDisjG hG
      exact HasTypeProcPre.recv hk' hG' hNoSh
  | select hk hG hFind =>
      rename_i Sown G k l e q bs L
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := Sframe ++ Sown.right, left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible, List.append_assoc] using hk
      have hG' := lookupG_frame_left hDisjG hG
      exact HasTypeProcPre.select hk' hG' hFind
  | branch hk hG hLen hLbl hProcs ih =>
      rename_i Sown G k procs e p bs
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := Sframe ++ Sown.right, left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible, List.append_assoc] using hk
      have hG' := lookupG_frame_left hDisjG hG
      have hDisjSym := DisjointG_symm hDisjG
      have hNone : lookupG G₁ e = none :=
        DisjointG_lookup_left (G₁:=G) (G₂:=G₁) hDisjSym hG
      have hProcs' :
          ∀ i (hi : i < bs.length) (hip : i < procs.length),
            HasTypeProcPre Ssh { right := Sframe ++ Sown.right, left := Sown.left }
              (updateG (G₁ ++ G) e (bs.get ⟨i, hi⟩).2) (procs.get ⟨i, hip⟩).2 := by
        intro i hi hip
        have hDisj' : DisjointG G₁ (updateG G e (bs.get ⟨i, hi⟩).2) :=
          DisjointG_updateG_left (G₁:=G₁) (G₂:=G) (e:=e)
            (L:=.branch p bs) (L':=(bs.get ⟨i, hi⟩).2) hDisjG hG
        have hBody := ih i hi hip hDisjR hDisjL hDisj'
        have hUpd := updateG_append_left (G₁:=G₁) (G₂:=G) (e:=e)
          (L:=(bs.get ⟨i, hi⟩).2) hNone
        have hBody' := hBody
        rw [← hUpd] at hBody'
        exact hBody'
      exact HasTypeProcPre.branch hk' hG' hLen hLbl hProcs'
  | seq hP hQ ihP ihQ =>
      exact HasTypeProcPre.seq (ihP hDisjR hDisjL hDisjG) (ihQ hDisjR hDisjL hDisjG)
  | par hDisjS hS hP hQ ihP ihQ =>
      rename_i Sown G P Q S₁ S₂ nS nG
      have hDisjS1 : DisjointS Sframe S₁ := by
        have hDisjL' : DisjointS Sframe (S₁ ++ S₂) := by simpa [hS] using hDisjL
        exact DisjointS_of_append_left hDisjL'
      have hDisjS2 : DisjointS Sframe S₂ := by
        have hDisjL' : DisjointS Sframe (S₁ ++ S₂) := by simpa [hS] using hDisjL
        exact DisjointS_of_append_right hDisjL'
      have hDisjRP : DisjointS Sframe (Sown.right ++ S₂) :=
        DisjointS_append_right hDisjR hDisjS2
      have hDisjRQ : DisjointS Sframe (Sown.right ++ S₁) :=
        DisjointS_append_right hDisjR hDisjS1
      have hP' := ihP hDisjRP hDisjS1 hDisjG
      have hQ' := ihQ hDisjRQ hDisjS2 hDisjG
      exact HasTypeProcPre.par hDisjS (by simpa [hS] using hS)
        (by simpa [List.append_assoc] using hP')
        (by simpa [List.append_assoc] using hQ')
  | assign hNoSh hv =>
      exact HasTypeProcPre.assign hNoSh (HasTypeVal_frame_left hDisjG hv)

/-- Pre-typing is invariant under right-gauge reframe of the owned environment. -/
theorem HasTypeProcPre_reframe_right
    {Ssh : SEnv} {Sown Sown' : OwnedEnv} {G : GEnv} {P : Process} :
    Sown'.left = Sown.left →
    HasTypeProcPre Ssh Sown G P →
    HasTypeProcPre Ssh Sown' G P := by
  intro hLeft h
  induction h generalizing Sown' with
  | skip =>
      exact HasTypeProcPre.skip
  | send hk hG hx =>
      rename_i Sown G k x e q T L
      have hk' :
          lookupSEnv (SEnvVisible Ssh Sown') k = some (.chan e.sid e.role) := by
        simpa [SEnvVisible, hLeft] using hk
      have hx' :
          lookupSEnv (SEnvVisible Ssh Sown') x = some T := by
        simpa [SEnvVisible, hLeft] using hx
      exact HasTypeProcPre.send hk' hG hx'
  | recv hk hG hNoSh =>
      rename_i Sown G k x e p T L
      have hk' :
          lookupSEnv (SEnvVisible Ssh Sown') k = some (.chan e.sid e.role) := by
        simpa [SEnvVisible, hLeft] using hk
      exact HasTypeProcPre.recv hk' hG hNoSh
  | select hk hG hFind =>
      rename_i Sown G k l e q bs L
      have hk' :
          lookupSEnv (SEnvVisible Ssh Sown') k = some (.chan e.sid e.role) := by
        simpa [SEnvVisible, hLeft] using hk
      exact HasTypeProcPre.select hk' hG hFind
  | branch hk hG hLen hLbl hProcs ih =>
      rename_i Sown G k procs e p bs
      have hk' :
          lookupSEnv (SEnvVisible Ssh Sown') k = some (.chan e.sid e.role) := by
        simpa [SEnvVisible, hLeft] using hk
      have hProcs' :
          ∀ i (hi : i < bs.length) (hip : i < procs.length),
            HasTypeProcPre Ssh Sown' (updateG G e (bs.get ⟨i, hi⟩).2) (procs.get ⟨i, hip⟩).2 := by
        intro i hi hip
        exact ih i hi hip (Sown':=Sown') hLeft
      exact HasTypeProcPre.branch hk' hG hLen hLbl hProcs'
  | seq hP hQ ihP ihQ =>
      exact HasTypeProcPre.seq (ihP (Sown':=Sown') hLeft) (ihQ (Sown':=Sown') hLeft)
  | par hDisjS hS hP hQ ihP ihQ =>
      rename_i Sown G P Q S₁ S₂ nS nG
      have hS' : Sown'.left = S₁ ++ S₂ := by
        simpa [hS] using hLeft
      have hP' :
          HasTypeProcPre Ssh { right := Sown'.right ++ S₂, left := S₁ } G P := by
        exact ihP (Sown':={ right := Sown'.right ++ S₂, left := S₁ }) rfl
      have hQ' :
          HasTypeProcPre Ssh { right := Sown'.right ++ S₁, left := S₂ } G Q := by
        exact ihQ (Sown':={ right := Sown'.right ++ S₁, left := S₂ }) rfl
      exact HasTypeProcPre.par hDisjS hS' hP' hQ'
  | assign hNoSh hv =>
      exact HasTypeProcPre.assign hNoSh hv

/-- Sessions only shrink under pre-out typing (no new sessions introduced). -/
private theorem SessionsOf_subset_update_send
    {G : GEnv} {e : Endpoint} {q : Role} {T : ValType} {L : LocalType} :
    lookupG G e = some (.send q T L) →
    SessionsOf (updateG G e L) ⊆ SessionsOf G := by
  intro hG s hs
  have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
    SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.send q T L) hG
  simpa [hEq] using hs

private theorem SessionsOf_subset_update_recv
    {G : GEnv} {e : Endpoint} {p : Role} {T : ValType} {L : LocalType} :
    lookupG G e = some (.recv p T L) →
    SessionsOf (updateG G e L) ⊆ SessionsOf G := by
  intro hG s hs
  have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
    SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.recv p T L) hG
  simpa [hEq] using hs

private theorem SessionsOf_subset_update_select
    {G : GEnv} {e : Endpoint} {q : Role} {bs : List (Label × LocalType)} {L : LocalType} :
    lookupG G e = some (.select q bs) →
    SessionsOf (updateG G e L) ⊆ SessionsOf G := by
  intro hG s hs
  have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
    SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.select q bs) hG
  simpa [hEq] using hs

theorem SessionsOf_subset_of_HasTypeProcPreOut
    {Ssh Sown G P Sown' G' W Δ} :
    HasTypeProcPreOut Ssh Sown G P Sown' G' W Δ →
    SessionsOf G' ⊆ SessionsOf G := by
  intro h
  induction h with
  | skip =>
      intro s hs
      simpa using hs
  | send hk hG hx =>
      exact SessionsOf_subset_update_send hG
  | recv_new hk hG hNoSh hNoOwnL =>
      exact SessionsOf_subset_update_recv hG
  | recv_old hk hG hNoSh hOwn =>
      exact SessionsOf_subset_update_recv hG
  | select hk hG hFind =>
      exact SessionsOf_subset_update_select hG
  | branch _ _ _ _ _ _ hSess _ =>
      exact hSess
  | seq hP hQ ihP ihQ =>
      intro s hs
      exact ihP (ihQ hs)
  | par split hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
      hDisjW hDisjΔ hP hQ ihP ihQ =>
      intro s hs
      cases hGfin
      have hs' := SessionsOf_append_subset hs
      cases hs' with
      | inl hsL =>
          simpa [split.hG] using (SessionsOf_append_left (G₂:=split.G2) (ihP hsL))
      | inr hsR =>
          simpa [split.hG] using (SessionsOf_append_right (G₁:=split.G1) (ihQ hsR))
  | assign_new =>
      intro s hs
      simpa using hs
  | assign_old =>
      intro s hs
      simpa using hs

/-- Lift SEnvAll lookups across a right frame (left-biased). -/
private theorem lookupSEnv_all_frame_right
    {Ssh S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    lookupSEnv (SEnvAll Ssh S₁) x = some T →
    lookupSEnv (SEnvAll Ssh (S₁ ++ S₂)) x = some T := by
  -- Appending on the right preserves existing left-biased lookups.
  intro hLookup
  have hLeft :=
    lookupSEnv_append_left (S₁:=Ssh ++ S₁) (S₂:=S₂) (x:=x) (T:=T) (by
      simpa [SEnvAll_ofLeft] using hLookup)
  have hEq := lookupSEnv_append_assoc (S₁:=Ssh) (S₂:=S₁) (S₃:=S₂) (x:=x)
  simpa [SEnvAll_ofLeft, SEnvAll, hEq] using hLeft

/-- Right framing preserves HasTypeVal without extra disjointness. -/
theorem HasTypeVal_frame_right {G₁ G₂ : GEnv} {v : Value} {T : ValType} :
    HasTypeVal G₁ v T →
    HasTypeVal (G₁ ++ G₂) v T := by
  -- The left environment dominates lookups.
  intro hv
  induction hv with
  | unit => exact HasTypeVal.unit
  | bool b => exact HasTypeVal.bool b
  | nat n => exact HasTypeVal.nat n
  | string s => exact HasTypeVal.string s
  | prod h₁ h₂ ih₁ ih₂ => exact HasTypeVal.prod ih₁ ih₂
  | chan h =>
      exact HasTypeVal.chan (lookupG_append_left h)

/-- If the right frame is disjoint from a lookup on the left, the right lookup is none. -/
private theorem lookupSEnv_none_of_disjoint_right {S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    DisjointS S₂ S₁ →
    lookupSEnv S₁ x = some T →
    lookupSEnv S₂ x = none := by
  -- Disjointness forbids any binding for x on the right.
  intro hDisj hLeft
  by_cases hNone : lookupSEnv S₂ x = none
  · exact hNone
  · cases hRight : lookupSEnv S₂ x with
    | none => exact (hNone hRight).elim
    | some T₂ => exact (hDisj x T₂ T hRight hLeft).elim

/-- Empty SEnv is disjoint from any environment. -/
theorem DisjointS_left_empty (S : SEnv) : DisjointS (∅ : SEnv) S := by
  -- Empty lookup is never `some`, so disjointness is trivial.
  intro x T₁ T₂ hLeft hRight
  cases hLeft

/-- Appending the empty SEnv on the right is a no-op. -/
private theorem SEnv_append_empty_right (S : SEnv) : S ++ (∅ : SEnv) = S := by
  simpa using (List.append_nil S)

/-- When x is in S₁, update distributes over append.
    NOTE: This was previously an unsound assumption. The theorem requires x ∈ S₁.
    Uses Core.updateSEnv_append_left_of_mem. -/
private theorem updateSEnv_append_left' {S₁ S₂ : SEnv} {x : Var} {T : ValType}
    (h : ∃ T', lookupSEnv S₁ x = some T') :
    updateSEnv (S₁ ++ S₂) x T = updateSEnv S₁ x T ++ S₂ :=
  updateSEnv_append_left_of_mem h

/-- Shorthand for left-framing on pre-out typing. -/
private abbrev FrameLeft (Ssh S₁ S₂ : SEnv) (G₁ G₂ : GEnv) (P : Process) : Prop :=
  -- Expand the left framing goal as a reusable predicate.
  ∀ {S₂' G₂' W Δ}, DisjointS S₁ S₂ → DisjointS S₁ S₂' → DisjointG G₁ G₂ →
    HasTypeProcPreOut Ssh S₂ G₂ P S₂' G₂' W Δ →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) P (S₁ ++ S₂') (G₁ ++ G₂') W Δ

/-- Shorthand for right-framing on pre-out typing. -/
private abbrev FrameRight (Ssh S₁ S₂ : SEnv) (G₁ G₂ : GEnv) (P : Process) : Prop :=
  -- Expand the right framing goal as a reusable predicate.
  ∀ {S₁' G₁' W Δ}, DisjointS S₂ S₁ → DisjointS S₂ S₁' → DisjointG G₁ G₂ →
    HasTypeProcPreOut Ssh S₁ G₁ P S₁' G₁' W Δ →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) P (S₁' ++ S₂) (G₁' ++ G₂) W Δ


/-- Left framing for skip. -/
private theorem frame_left_skip {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} :
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) .skip
      { right := S₁, left := S₂ } (G₁ ++ G₂) [] ∅ := by
  -- Skip leaves environments unchanged.
  simpa using
    (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ }) (G:=G₁ ++ G₂))

/-- Left framing for send. -/
private theorem frame_left_send
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k x : Var} {e : Endpoint} {q : Role}
    {T : ValType} {L : LocalType} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupSEnv (SEnvVisible Ssh (S₂ : OwnedEnv)) k = some (.chan e.sid e.role) →
    lookupG G₂ e = some (.send q T L) →
    lookupSEnv (SEnvVisible Ssh (S₂ : OwnedEnv)) x = some T →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.send k x)
      { right := S₁, left := S₂ } (G₁ ++ updateG G₂ e L) [] ∅ := by
  -- Lift lookups and push update into the right GEnv.
  intro hDisjS hDisjG hk hG hx
  have hk' :
      lookupSEnv (SEnvVisible Ssh { right := S₁, left := S₂ }) k = some (.chan e.sid e.role) := by
    simpa [SEnvVisible] using hk
  have hx' :
      lookupSEnv (SEnvVisible Ssh { right := S₁, left := S₂ }) x = some T := by
    simpa [SEnvVisible] using hx
  have hG' := lookupG_frame_left hDisjG hG
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpd := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  simpa [hUpd] using
    (HasTypeProcPreOut.send (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ }) (G:=G₁ ++ G₂) hk' hG' hx')

/-- Left framing for recv_new. -/
private theorem frame_left_recv_new
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k x : Var} {e : Endpoint} {p : Role}
    {T : ValType} {L : LocalType} :
    DisjointS S₁ S₂ →
    DisjointS S₁ (updateSEnv S₂ x T) →
    DisjointG G₁ G₂ →
    lookupSEnv (SEnvVisible Ssh (S₂ : OwnedEnv)) k = some (.chan e.sid e.role) →
    lookupG G₂ e = some (.recv p T L) →
    lookupSEnv Ssh x = none →
    lookupSEnv S₂ x = none →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.recv k x)
      { right := S₁, left := updateSEnv S₂ x T } (G₁ ++ updateG G₂ e L) [x] (updateSEnv ∅ x T) := by
  -- Use disjointness to show x is not in the left frame.
  intro hDisjS hDisjS' hDisjG hk hG hSsh hSown
  have hk' :
      lookupSEnv (SEnvVisible Ssh { right := S₁, left := S₂ }) k = some (.chan e.sid e.role) := by
    simpa [SEnvVisible] using hk
  have hG' := lookupG_frame_left hDisjG hG
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpdG := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  have hRight : lookupSEnv S₁ x = none := by
    have hx2 : lookupSEnv (updateSEnv S₂ x T) x = some T := by simp [lookupSEnv_update_eq]
    exact lookupSEnv_none_of_disjoint_left hDisjS' hx2
  have hErase : eraseSEnv S₁ x = S₁ := eraseSEnv_of_lookup_none hRight
  have hLeft : lookupSEnv S₂ x = none := hSown
  simpa [OwnedEnv.updateLeft, hErase, hUpdG] using
    (HasTypeProcPreOut.recv_new (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ })
      (G:=G₁ ++ G₂) hk' hG' hSsh hLeft)

/-- Left framing for recv_old. -/
private theorem frame_left_recv_old
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k x : Var} {e : Endpoint} {p : Role}
    {T : ValType} {L : LocalType} {T' : ValType} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupSEnv (SEnvVisible Ssh (S₂ : OwnedEnv)) k = some (.chan e.sid e.role) →
    lookupG G₂ e = some (.recv p T L) →
    lookupSEnv Ssh x = none →
    lookupSEnv S₂ x = some T' →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.recv k x)
      { right := S₁, left := updateSEnv S₂ x T } (G₁ ++ updateG G₂ e L) [x] ∅ := by
  -- Old recv: x already in S₂, so not in S₁ by disjointness.
  intro hDisjS hDisjG hk hG hSsh hSown
  have hk' :
      lookupSEnv (SEnvVisible Ssh { right := S₁, left := S₂ }) k = some (.chan e.sid e.role) := by
    simpa [SEnvVisible] using hk
  have hG' := lookupG_frame_left hDisjG hG
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpdG := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  have hRight : lookupSEnv S₁ x = none := lookupSEnv_none_of_disjoint_left hDisjS hSown
  have hErase : eraseSEnv S₁ x = S₁ := eraseSEnv_of_lookup_none hRight
  have hLeft : lookupSEnv S₂ x = some T' := hSown
  simpa [OwnedEnv.updateLeft, hErase, hUpdG] using
    (HasTypeProcPreOut.recv_old (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ })
      (G:=G₁ ++ G₂) hk' hG' hSsh hLeft)

/-- Left framing for select. -/
private theorem frame_left_select
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k : Var} {l : Label} {e : Endpoint}
    {q : Role} {bs : List (Label × LocalType)} {L : LocalType} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupSEnv (SEnvVisible Ssh (S₂ : OwnedEnv)) k = some (.chan e.sid e.role) →
    lookupG G₂ e = some (.select q bs) →
    bs.find? (fun b => b.1 == l) = some (l, L) →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.select k l)
      { right := S₁, left := S₂ } (G₁ ++ updateG G₂ e L) [] ∅ := by
  -- Lift lookups and push update into the right GEnv.
  intro hDisjS hDisjG hk hG hFind
  have hk' :
      lookupSEnv (SEnvVisible Ssh { right := S₁, left := S₂ }) k = some (.chan e.sid e.role) := by
    simpa [SEnvVisible] using hk
  have hG' := lookupG_frame_left hDisjG hG
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpd := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  simpa [hUpd] using
    (HasTypeProcPreOut.select (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ })
      (G:=G₁ ++ G₂) hk' hG' hFind)

/-- Frame-left helper for branch pre-typing. -/
private theorem frame_left_pre_updateG
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {e : Endpoint} {L L0 : LocalType} {P : Process} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupG G₂ e = some L0 →
    HasTypeProcPre Ssh S₂ (updateG G₂ e L) P →
    HasTypeProcPre Ssh { right := S₁, left := S₂ } (updateG (G₁ ++ G₂) e L) P := by
  -- Frame pre-typing and rewrite the update on G.
  intro hDisjS hDisjG hG hPre
  have hDisjG' : DisjointG G₁ (updateG G₂ e L) :=
    DisjointG_updateG_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L0) (L':=L) hDisjG hG
  have hDisjR : DisjointS S₁ ([] : SEnv) := by
    simpa using (DisjointS_symm (DisjointS_left_empty S₁))
  have hPre' := HasTypeProcPre_frame_left (Sframe:=S₁) (Sown:=(S₂ : OwnedEnv))
    (G₁:=G₁) (G₂:=updateG G₂ e L) hDisjR hDisjS hDisjG' hPre
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpd := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  simpa [hUpd] using hPre'

/-- Left framing for branch. -/
private theorem frame_left_branch
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k : Var} {procs : List (Label × Process)}
    {e : Endpoint} {p : Role} {bs : List (Label × LocalType)}
    {S₂' : SEnv} {G₂' : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointS S₁ S₂ →
    DisjointS S₁ S₂' →
    DisjointG G₁ G₂ →
    lookupSEnv (SEnvVisible Ssh (S₂ : OwnedEnv)) k = some (.chan e.sid e.role) →
    lookupG G₂ e = some (.branch p bs) →
    bs.length = procs.length →
    (∀ j (hj : j < bs.length) (hjp : j < procs.length),
      (procs.get ⟨j, hjp⟩).1 = (bs.get ⟨j, hj⟩).1) →
    (∀ j (hj : j < bs.length) (hjp : j < procs.length),
      HasTypeProcPre Ssh S₂ (updateG G₂ e (bs.get ⟨j, hj⟩).2) (procs.get ⟨j, hjp⟩).2) →
    (∀ lbl P L,
      procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
      bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
      HasTypeProcPreOut Ssh S₂ (updateG G₂ e L) P S₂' G₂' W Δ) →
    SessionsOf G₂' ⊆ SessionsOf G₂ →
    SEnvDomSubset S₂ S₂' →
    (∀ lbl P L,
      procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
      bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
      DisjointS S₁ S₂ →
      DisjointS S₁ S₂' →
      DisjointG G₁ (updateG G₂ e L) →
      HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ updateG G₂ e L) P
        { right := S₁, left := S₂' } (G₁ ++ G₂') W Δ) →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.branch k procs)
      { right := S₁, left := S₂' } (G₁ ++ G₂') W Δ := by
  -- Frame each branch using the provided IH and rebuild the constructor.
  intro hDisjS hDisjS' hDisjG hk hG hLen hLbl hProcs hOut hSess hDom ih
  have hk' :
      lookupSEnv (SEnvVisible Ssh { right := S₁, left := S₂ }) k = some (.chan e.sid e.role) := by
    simpa [SEnvVisible] using hk
  have hG' := lookupG_frame_left hDisjG hG
  have hProcs' :
      ∀ j (hj : j < bs.length) (hjp : j < procs.length),
        HasTypeProcPre Ssh { right := S₁, left := S₂ }
          (updateG (G₁ ++ G₂) e (bs.get ⟨j, hj⟩).2)
          (procs.get ⟨j, hjp⟩).2 := by
    intro j hj hjp
    exact frame_left_pre_updateG hDisjS hDisjG hG (hProcs j hj hjp)
  have hOut' :
      ∀ lbl P L,
        procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
        bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
        HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (updateG (G₁ ++ G₂) e L)
          P { right := S₁, left := S₂' } (G₁ ++ G₂') W Δ := by
    intro lbl P L hP hB
    have hDisjG' : DisjointG G₁ (updateG G₂ e L) :=
      DisjointG_updateG_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=.branch p bs) (L':=L) hDisjG hG
    have hPre' := ih lbl P L hP hB hDisjS hDisjS' hDisjG'
    have hDisjSym := DisjointG_symm hDisjG
    have hNone : lookupG G₁ e = none :=
      DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
    have hUpd := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
    simpa [hUpd] using hPre'
  have hSess' : SessionsOf (G₁ ++ G₂') ⊆ SessionsOf (G₁ ++ G₂) := by
    intro s hs
    have hs' := SessionsOf_append_subset (G₁:=G₁) (G₂:=G₂') hs
    cases hs' with
    | inl hsL =>
        exact SessionsOf_append_left (G₂:=G₂) hsL
    | inr hsR =>
        exact SessionsOf_append_right (G₁:=G₁) (hSess hsR)
  exact HasTypeProcPreOut.branch hk' hG' hLen hLbl hProcs' hOut' hSess' hDom rfl

/-- Left framing for assign_new. -/
private theorem frame_left_assign_new
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {x : Var} {v : Value} {T : ValType} :
    DisjointS S₁ (updateSEnv S₂ x T) →
    DisjointG G₁ G₂ →
    lookupSEnv Ssh x = none →
    lookupSEnv S₂ x = none →
    HasTypeVal G₂ v T →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.assign x v)
      { right := S₁, left := updateSEnv S₂ x T } (G₁ ++ G₂) [x] (updateSEnv ∅ x T) := by
  -- Use disjointness to keep x absent from the left frame.
  intro hDisjS' hDisjG hSsh hSown hv
  have hx2 : lookupSEnv (updateSEnv S₂ x T) x = some T := by
    simp [lookupSEnv_update_eq]
  have hx1 : lookupSEnv S₁ x = none := lookupSEnv_none_of_disjoint_left hDisjS' hx2
  have hv' := HasTypeVal_frame_left (G₁:=G₁) (G₂:=G₂) hDisjG hv
  have hRight : lookupSEnv S₁ x = none := hx1
  have hErase : eraseSEnv S₁ x = S₁ := eraseSEnv_of_lookup_none hRight
  have hLeft : lookupSEnv S₂ x = none := hSown
  simpa [OwnedEnv.updateLeft, hErase] using
    (HasTypeProcPreOut.assign_new (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ })
      (G:=G₁ ++ G₂) hSsh hLeft hv')

/-- Left framing for assign_old. -/
private theorem frame_left_assign_old
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {x : Var} {v : Value} {T T' : ValType} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupSEnv Ssh x = none →
    lookupSEnv S₂ x = some T' →
    HasTypeVal G₂ v T →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.assign x v)
      { right := S₁, left := updateSEnv S₂ x T } (G₁ ++ G₂) [x] ∅ := by
  -- Old assignment: x is in S₂, so not in S₁ by disjointness.
  intro hDisjS hDisjG hSsh hSown hv
  have hx1 : lookupSEnv S₁ x = none := lookupSEnv_none_of_disjoint_left hDisjS hSown
  have hv' := HasTypeVal_frame_left (G₁:=G₁) (G₂:=G₂) hDisjG hv
  have hRight : lookupSEnv S₁ x = none := hx1
  have hErase : eraseSEnv S₁ x = S₁ := eraseSEnv_of_lookup_none hRight
  have hLeft : lookupSEnv S₂ x = some T' := hSown
  simpa [OwnedEnv.updateLeft, hErase] using
    (HasTypeProcPreOut.assign_old (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ })
      (G:=G₁ ++ G₂) hSsh hLeft hv')

private theorem HasTypeProcPreOut_reframe_right_general
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {P : Process}
    {Sfin : OwnedEnv} {G' : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh Sown G P Sfin G' W Δ →
    ∀ {R' : SEnv},
      DisjointS R' Sown.left →
      DisjointS R' Sfin.left →
      HasTypeProcPreOut Ssh { right := R', left := Sown.left } G P
        { right := R', left := Sfin.left } G' W Δ := by
  intro h
  induction h with
  | skip =>
      intro R' hDisjIn hDisjOut
      exact HasTypeProcPreOut.skip
  | send hk hG hx =>
      rename_i Sown G k x e q T L
      intro R' hDisjIn hDisjOut
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := R', left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible] using hk
      have hx' :
          lookupSEnv (SEnvVisible Ssh { right := R', left := Sown.left }) x = some T := by
        simpa [SEnvVisible] using hx
      exact HasTypeProcPreOut.send hk' hG hx'
  | recv_new hk hG hNoSh hNoOwnL =>
      rename_i Sown G k x e p T L
      intro R' hDisjIn hDisjOut
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := R', left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible] using hk
      have hDisjOut' : DisjointS R' (updateSEnv Sown.left x T) := by
        simpa [OwnedEnv.updateLeft] using hDisjOut
      have hxOut : lookupSEnv (updateSEnv Sown.left x T) x = some T := by
        simpa using (lookupSEnv_update_eq (env:=Sown.left) (x:=x) (T:=T))
      have hNoOwnR' : lookupSEnv R' x = none :=
        lookupSEnv_none_of_disjoint_left hDisjOut' hxOut
      have hErase : eraseSEnv R' x = R' := eraseSEnv_of_lookup_none hNoOwnR'
      simpa [OwnedEnv.updateLeft, hErase] using
        (HasTypeProcPreOut.recv_new (Ssh:=Ssh) (Sown:={ right := R', left := Sown.left })
          (G:=G) hk' hG hNoSh hNoOwnL)
  | recv_old hk hG hNoSh hOwn =>
      rename_i Sown G k x e p T L T'
      intro R' hDisjIn hDisjOut
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := R', left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible] using hk
      have hDisjOut' : DisjointS R' (updateSEnv Sown.left x T) := by
        simpa [OwnedEnv.updateLeft] using hDisjOut
      have hxOut : lookupSEnv (updateSEnv Sown.left x T) x = some T := by
        simpa using (lookupSEnv_update_eq (env:=Sown.left) (x:=x) (T:=T))
      have hNoOwnR' : lookupSEnv R' x = none :=
        lookupSEnv_none_of_disjoint_left hDisjOut' hxOut
      have hErase : eraseSEnv R' x = R' := eraseSEnv_of_lookup_none hNoOwnR'
      simpa [OwnedEnv.updateLeft, hErase] using
        (HasTypeProcPreOut.recv_old (Ssh:=Ssh) (Sown:={ right := R', left := Sown.left })
          (G:=G) hk' hG hNoSh hOwn)
  | select hk hG hFind =>
      rename_i Sown G k l e q bs L
      intro R' hDisjIn hDisjOut
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := R', left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible] using hk
      exact HasTypeProcPreOut.select hk' hG hFind
  | branch hk hG hLen hLbl hPre hOutLbl hSess hDom hRight ihOutLbl =>
      rename_i Sown G k procs e p bs S' G' W Δ
      intro R' hDisjIn hDisjOut
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := R', left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible] using hk
      have hOutLbl' :
          ∀ lbl P Lx,
            procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
            bs.find? (fun b => b.1 == lbl) = some (lbl, Lx) →
            HasTypeProcPreOut Ssh { right := R', left := Sown.left } (updateG G e Lx) P
              { right := R', left := S'.left } G' W Δ := by
        intro lbl P Lx hFindP hFindB
        exact ihOutLbl lbl P Lx hFindP hFindB (R':=R') hDisjIn hDisjOut
      have hPre' :
          ∀ j (hj : j < bs.length) (hjp : j < procs.length),
            HasTypeProcPre Ssh { right := R', left := Sown.left }
              (updateG G e (bs.get ⟨j, hj⟩).2)
              (procs.get ⟨j, hjp⟩).2 := by
        intro j hj hjp
        exact HasTypeProcPre_reframe_right
          (Sown:=Sown) (Sown':={ right := R', left := Sown.left }) rfl
          (hPre j hj hjp)
      exact HasTypeProcPreOut.branch hk' hG hLen hLbl hPre' hOutLbl' hSess hDom rfl
  | seq hP hQ ihP ihQ =>
      rename_i Sown G P Q S₁ G₁ S₂ G₂ W₁ W₂ Δ₁ Δ₂
      intro R' hDisjIn hDisjOut
      have hDomQ : SEnvDomSubset S₁.left S₂.left := HasTypeProcPreOut_domsubset hQ
      have hDisjMid : DisjointS R' S₁.left :=
        DisjointS_of_domsubset_right hDomQ hDisjOut
      exact HasTypeProcPreOut.seq
        (ihP (R':=R') hDisjIn hDisjMid)
        (ihQ (R':=R') hDisjMid hDisjOut)
  | par split hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
      hDisjW hDisjΔ hP hQ ihP ihQ =>
      rename_i Sown G P Q Sfin Gfin Wfin Δfin S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂ nS nG
      intro R' hDisjIn hDisjOut
      have hDisjInSplit : DisjointS R' (split.S1 ++ split.S2) := by
        simpa [split.hS] using hDisjIn
      have hDisjIn1 : DisjointS R' split.S1 := DisjointS_of_append_left hDisjInSplit
      have hDisjIn2 : DisjointS R' split.S2 := DisjointS_of_append_right hDisjInSplit
      have hDisjOutSplit : DisjointS R' (S₁' ++ S₂') := by
        simpa [hSfin] using hDisjOut
      have hDisjOut1 : DisjointS R' S₁' := DisjointS_of_append_left hDisjOutSplit
      have hDisjOut2 : DisjointS R' S₂' := DisjointS_of_append_right hDisjOutSplit
      have hDisjInP : DisjointS (R' ++ split.S2) split.S1 :=
        DisjointS_append_left hDisjIn1 (DisjointS_symm hDisjS)
      have hDisjOutP : DisjointS (R' ++ split.S2) S₁' :=
        DisjointS_append_left hDisjOut1 (DisjointS_symm hDisjS_left)
      have hDisjInQ : DisjointS (R' ++ split.S1) split.S2 :=
        DisjointS_append_left hDisjIn2 hDisjS
      have hDisjOutQ : DisjointS (R' ++ split.S1) S₂' :=
        DisjointS_append_left hDisjOut2 hDisjS_right
      have hP' :
          HasTypeProcPreOut Ssh { right := R' ++ split.S2, left := split.S1 } split.G1 P
            { right := R' ++ split.S2, left := S₁' } G₁' W₁ Δ₁ :=
        ihP (R':=R' ++ split.S2) hDisjInP hDisjOutP
      have hQ' :
          HasTypeProcPreOut Ssh { right := R' ++ split.S1, left := split.S2 } split.G2 Q
            { right := R' ++ split.S1, left := S₂' } G₂' W₂ Δ₂ :=
        ihQ (R':=R' ++ split.S1) hDisjInQ hDisjOutQ
      have hPar' :
          HasTypeProcPreOut Ssh { right := R', left := Sown.left } G (.par nS nG P Q)
            { right := R', left := S₁' ++ S₂' } (G₁' ++ G₂') (W₁ ++ W₂) (Δ₁ ++ Δ₂) :=
        HasTypeProcPreOut.par split hSlen rfl rfl rfl rfl
          hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hP' hQ'
      simpa [hSfin, hGfin, hW, hΔ] using hPar'
  | assign_new hNoSh hNoOwnL hv =>
      rename_i Sown G x v T
      intro R' hDisjIn hDisjOut
      have hDisjOut' : DisjointS R' (updateSEnv Sown.left x T) := by
        simpa [OwnedEnv.updateLeft] using hDisjOut
      have hxOut : lookupSEnv (updateSEnv Sown.left x T) x = some T := by
        simpa using (lookupSEnv_update_eq (env:=Sown.left) (x:=x) (T:=T))
      have hNoOwnR' : lookupSEnv R' x = none :=
        lookupSEnv_none_of_disjoint_left hDisjOut' hxOut
      have hErase : eraseSEnv R' x = R' := eraseSEnv_of_lookup_none hNoOwnR'
      have hNoOwnL' : lookupSEnv ({ right := R', left := Sown.left } : OwnedEnv).left x = none := by
        simpa using hNoOwnL
      simpa [OwnedEnv.updateLeft, hErase] using
        (HasTypeProcPreOut.assign_new (Ssh:=Ssh) (Sown:={ right := R', left := Sown.left })
          (G:=G) hNoSh hNoOwnL' hv)
  | assign_old hNoSh hOwn hv =>
      rename_i Sown G x v T T'
      intro R' hDisjIn hDisjOut
      have hDisjOut' : DisjointS R' (updateSEnv Sown.left x T) := by
        simpa [OwnedEnv.updateLeft] using hDisjOut
      have hxOut : lookupSEnv (updateSEnv Sown.left x T) x = some T := by
        simpa using (lookupSEnv_update_eq (env:=Sown.left) (x:=x) (T:=T))
      have hNoOwnR' : lookupSEnv R' x = none :=
        lookupSEnv_none_of_disjoint_left hDisjOut' hxOut
      have hErase : eraseSEnv R' x = R' := eraseSEnv_of_lookup_none hNoOwnR'
      have hOwn' : lookupSEnv ({ right := R', left := Sown.left } : OwnedEnv).left x = some T' := by
        simpa using hOwn
      simpa [OwnedEnv.updateLeft, hErase] using
        (HasTypeProcPreOut.assign_old (Ssh:=Ssh) (Sown:={ right := R', left := Sown.left })
          (G:=G) hNoSh hOwn' hv)

theorem HasTypeProcPreOut_reframe_right
    {Ssh R R' L : SEnv} {G : GEnv} {P : Process}
    {L' : SEnv} {G' : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointS R' L →
    DisjointS R' L' →
    HasTypeProcPreOut Ssh { right := R, left := L } G P { right := R, left := L' } G' W Δ →
    HasTypeProcPreOut Ssh { right := R', left := L } G P { right := R', left := L' } G' W Δ := by
  intro hDisjIn hDisjOut h
  simpa using
    (HasTypeProcPreOut_reframe_right_general
      (Ssh:=Ssh) (Sown:={ right := R, left := L }) (G:=G) (P:=P)
      (Sfin:={ right := R, left := L' }) (G':=G') (W:=W) (Δ:=Δ)
      h (R':=R') hDisjIn hDisjOut)

/-- Left framing for par: frame only the left component. -/
theorem frame_left_par
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {P Q : Process} {nS nG : Nat}
    {Sfin Gfin Wfin Δfin S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂}
    (split : ParSplit S₂ G₂)
    (hSlen : split.S1.length = nS)
    (hSfin : Sfin = S₁' ++ S₂')
    (hGfin : Gfin = G₁' ++ G₂')
    (hW : Wfin = W₁ ++ W₂)
    (hΔ : Δfin = Δ₁ ++ Δ₂)
    (hDisjG : DisjointG split.G1 split.G2)
    (hDisjS : DisjointS split.S1 split.S2)
    (hDisjS_left : DisjointS S₁' split.S2)
    (hDisjS_right : DisjointS split.S1 S₂')
    (hDisjS' : DisjointS S₁' S₂')
    (hDisjW : DisjointW W₁ W₂)
    (hDisjΔ : DisjointS Δ₁ Δ₂)
    (hQ : HasTypeProcPreOut Ssh split.S2 split.G2 Q S₂' G₂' W₂ Δ₂)
    (hDisjS_frame : DisjointS S₁ S₂)
    (hDisjS_frame' : DisjointS S₁ Sfin)
    (hDisjG_frame : DisjointG G₁ G₂)
    (ihP : DisjointS S₁ split.S1 → DisjointS S₁ S₁' → DisjointG G₁ split.G1 →
      HasTypeProcPreOut Ssh { right := S₁, left := split.S1 } (G₁ ++ split.G1) P
        { right := S₁, left := S₁' } (G₁ ++ G₁') W₁ Δ₁) :
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.par nS nG P Q)
      { right := S₁, left := Sfin } (G₁ ++ Gfin) Wfin Δfin := by
  have hSubSplit1 : SEnvDomSubset split.S1 S₂ := by
    simpa [split.hS] using (SEnvDomSubset_append_left (S₁:=split.S1) (S₂:=split.S2))
  have hSubSplit2 : SEnvDomSubset split.S2 S₂ := by
    simpa [split.hS] using (SEnvDomSubset_append_right (S₁:=split.S1) (S₂:=split.S2))
  have hSubSfin1 : SEnvDomSubset S₁' Sfin := by
    simpa [hSfin] using (SEnvDomSubset_append_left (S₁:=S₁') (S₂:=S₂'))
  have hSubSfin2 : SEnvDomSubset S₂' Sfin := by
    simpa [hSfin] using (SEnvDomSubset_append_right (S₁:=S₁') (S₂:=S₂'))
  have hDisjS_frame_1 : DisjointS S₁ split.S1 :=
    DisjointS_of_domsubset_right hSubSplit1 hDisjS_frame
  have hDisjS_frame_2 : DisjointS S₁ split.S2 :=
    DisjointS_of_domsubset_right hSubSplit2 hDisjS_frame
  have hDisjS_frame_1' : DisjointS S₁ S₁' :=
    DisjointS_of_domsubset_right hSubSfin1 hDisjS_frame'
  have hDisjS_frame_2' : DisjointS S₁ S₂' :=
    DisjointS_of_domsubset_right hSubSfin2 hDisjS_frame'
  have hSubG1 : SessionsOf split.G1 ⊆ SessionsOf G₂ := by
    simpa [split.hG] using (SessionsOf_append_left (G₁:=split.G1) (G₂:=split.G2))
  have hSubG2 : SessionsOf split.G2 ⊆ SessionsOf G₂ := by
    simpa [split.hG] using (SessionsOf_append_right (G₁:=split.G1) (G₂:=split.G2))
  have hDisjGsym : DisjointG G₂ G₁ := DisjointG_symm hDisjG_frame
  have hDisjG_frame_1 : DisjointG G₁ split.G1 := by
    exact DisjointG_symm (DisjointG_of_subset_left hSubG1 hDisjGsym)
  have hDisjG_frame_2 : DisjointG G₁ split.G2 := by
    exact DisjointG_symm (DisjointG_of_subset_left hSubG2 hDisjGsym)
  have hP0 :
      HasTypeProcPreOut Ssh { right := S₁, left := split.S1 } (G₁ ++ split.G1) P
        { right := S₁, left := S₁' } (G₁ ++ G₁') W₁ Δ₁ :=
    ihP hDisjS_frame_1 hDisjS_frame_1' hDisjG_frame_1
  have hDisjInP : DisjointS (S₁ ++ split.S2) split.S1 :=
    DisjointS_append_left hDisjS_frame_1 (DisjointS_symm hDisjS)
  have hDisjOutP : DisjointS (S₁ ++ split.S2) S₁' :=
    DisjointS_append_left hDisjS_frame_1' (DisjointS_symm hDisjS_left)
  have hP :
      HasTypeProcPreOut Ssh { right := S₁ ++ split.S2, left := split.S1 } (G₁ ++ split.G1) P
        { right := S₁ ++ split.S2, left := S₁' } (G₁ ++ G₁') W₁ Δ₁ :=
    HasTypeProcPreOut_reframe_right
      (R:=S₁) (R':=S₁ ++ split.S2) (L:=split.S1) (L':=S₁')
      (G:=G₁ ++ split.G1) (P:=P) hDisjInP hDisjOutP hP0
  have hQ0 :
      HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := split.S2 } split.G2 Q
        { right := (∅ : SEnv), left := S₂' } G₂' W₂ Δ₂ := by
    simpa using hQ
  have hDisjInQ : DisjointS (S₁ ++ split.S1) split.S2 :=
    DisjointS_append_left hDisjS_frame_2 hDisjS
  have hDisjOutQ : DisjointS (S₁ ++ split.S1) S₂' :=
    DisjointS_append_left hDisjS_frame_2' hDisjS_right
  have hQ' :
      HasTypeProcPreOut Ssh { right := S₁ ++ split.S1, left := split.S2 } split.G2 Q
        { right := S₁ ++ split.S1, left := S₂' } G₂' W₂ Δ₂ :=
    HasTypeProcPreOut_reframe_right
      (R:=(∅ : SEnv)) (R':=S₁ ++ split.S1) (L:=split.S2) (L':=S₂')
      (G:=split.G2) (P:=Q) hDisjInQ hDisjOutQ hQ0
  have hDisjG_out : DisjointG (G₁ ++ split.G1) split.G2 :=
    DisjointG_append_left hDisjG_frame_2 hDisjG
  let splitOut : ParSplit S₂ (G₁ ++ G₂) :=
    { S1 := split.S1
      S2 := split.S2
      G1 := G₁ ++ split.G1
      G2 := split.G2
      hS := split.hS
      hG := by simpa [List.append_assoc, split.hG] }
  have hPar :
      HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.par nS nG P Q)
        { right := S₁, left := S₁' ++ S₂' } ((G₁ ++ G₁') ++ G₂') (W₁ ++ W₂) (Δ₁ ++ Δ₂) :=
    HasTypeProcPreOut.par splitOut hSlen rfl rfl rfl rfl
      hDisjG_out hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hP hQ'
  simpa [hSfin, hGfin, hW, hΔ, List.append_assoc] using hPar

/-! ## Local G-Frame Transport (Right) -/

/-- Helper: extend branch bodies under a right frame (pre-typing). -/
private lemma pre_frame_right_branch_bodies_local
    {Ssh : SEnv} {Sown : OwnedEnv} {G Gfr : GEnv} {e : Endpoint} {p : Role}
    {bs : List (Label × LocalType)} {procs : List (Label × Process)} :
    lookupG G e = some (.branch p bs) →
    (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown
          (updateG G e (bs.get ⟨i, hi⟩).2 ++ Gfr)
          (procs.get ⟨i, hip⟩).2) →
    (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown
          (updateG (G ++ Gfr) e (bs.get ⟨i, hi⟩).2)
          (procs.get ⟨i, hip⟩).2) := by
  intro hG ihBodies i hi hip
  have hBody' := ihBodies i hi hip
  have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
    (L:=.branch p bs) (L':=(bs.get ⟨i, hi⟩).2) hG
  rw [hUpd]
  exact hBody'

/-- Local right-frame transport for `HasTypeProcPre`. -/
private lemma HasTypeProcPre_frame_G_right_local
    {Ssh : SEnv} {Sown : OwnedEnv} {G Gfr : GEnv} {P : Process} :
    HasTypeProcPre Ssh Sown G P →
    HasTypeProcPre Ssh Sown (G ++ Gfr) P := by
  intro h
  induction h with
  | skip =>
      rename_i Sown G
      simpa using (HasTypeProcPre.skip (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr))
  | send hk hG hx =>
      rename_i Sown G k x e q T L
      exact HasTypeProcPre.send hk (lookupG_append_left (G₂:=Gfr) hG) hx
  | recv hk hG hNoSh =>
      rename_i Sown G k x e p T L
      exact HasTypeProcPre.recv hk (lookupG_append_left (G₂:=Gfr) hG) hNoSh
  | select hk hG hbs =>
      rename_i Sown G k l e q bs L
      exact HasTypeProcPre.select hk (lookupG_append_left (G₂:=Gfr) hG) hbs
  | branch hk hG hLen hLabels hBodies ihBodies =>
      rename_i Sown G k procs e p bs
      have hBodies' := pre_frame_right_branch_bodies_local (G:=G) (Gfr:=Gfr) hG ihBodies
      exact HasTypeProcPre.branch hk (lookupG_append_left (G₂:=Gfr) hG) hLen hLabels hBodies'
  | seq hP hQ ihP ihQ =>
      exact HasTypeProcPre.seq ihP ihQ
  | par hDisjS hSsplit hP hQ ihP ihQ =>
      exact HasTypeProcPre.par hDisjS hSsplit ihP ihQ
  | assign hNoSh hv =>
      rename_i Sown G x v T
      exact HasTypeProcPre.assign hNoSh (HasTypeVal_frame_right (G₁:=G) (G₂:=Gfr) hv)

/-- Helper: extend branch bodies under a right G-frame (pre-out typing). -/
private lemma frame_right_branch_bodies_local
    {Ssh : SEnv} {Sown : OwnedEnv} {G Gfr : GEnv} {e : Endpoint} {p : Role}
    {bs : List (Label × LocalType)} {procs : List (Label × Process)} :
    lookupG G e = some (.branch p bs) →
    (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown
          (updateG G e (bs.get ⟨i, hi⟩).2)
          (procs.get ⟨i, hip⟩).2) →
    (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown
          (updateG (G ++ Gfr) e (bs.get ⟨i, hi⟩).2)
          (procs.get ⟨i, hip⟩).2) := by
  intro hG hBodies i hi hip
  have hBody := hBodies i hi hip
  have hBody' := HasTypeProcPre_frame_G_right_local (Gfr:=Gfr) hBody
  have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
    (L:=.branch p bs) (L':=(bs.get ⟨i, hi⟩).2) hG
  rw [hUpd]
  exact hBody'

/-- Helper: extend branch continuations under a right G-frame (pre-out typing). -/
private lemma frame_right_branch_out_local
    {Ssh : SEnv} {Sown : OwnedEnv} {G Gfr : GEnv} {e : Endpoint} {p : Role}
    {bs : List (Label × LocalType)} {procs : List (Label × Process)}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    lookupG G e = some (.branch p bs) →
    (∀ lbl P L,
        procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
        bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
        DisjointG (updateG G e L) Gfr →
        HasTypeProcPreOut Ssh Sown (updateG G e L ++ Gfr) P Sfin (Gfin ++ Gfr) W Δ) →
    DisjointG G Gfr →
    (∀ lbl P L,
        procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
        bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
        HasTypeProcPreOut Ssh Sown (updateG (G ++ Gfr) e L) P Sfin (Gfin ++ Gfr) W Δ) := by
  intro hG ihOutLbl hDisj lbl P L hFindP hFindB
  have hDisj' : DisjointG (updateG G e L) Gfr :=
    disjointG_updateG_left (e:=e) (L:=L) (L0:=.branch p bs) hG hDisj
  have hOut' := ihOutLbl lbl P L hFindP hFindB hDisj'
  have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e) (L:=.branch p bs) (L':=L) hG
  simpa [hUpd] using hOut'

/-- Helper: par case for right-frame pre-out transport. -/
private lemma frame_pre_out_right_par_local
    {Ssh : SEnv} {Sown : OwnedEnv} {G Gfr : GEnv} {P Q : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv}
    {S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂} {nS nG : Nat}
    (split : ParSplit Sown.left G) :
    DisjointG G Gfr →
    split.S1.length = nS →
    Sfin = { right := Sown.right, left := S₁' ++ S₂' } →
    Gfin = G₁' ++ G₂' →
    W = W₁ ++ W₂ →
    Δ = Δ₁ ++ Δ₂ →
    DisjointG split.G1 split.G2 →
    DisjointS split.S1 split.S2 →
    DisjointS S₁' split.S2 →
    DisjointS split.S1 S₂' →
    DisjointS S₁' S₂' →
    DisjointW W₁ W₂ →
    DisjointS Δ₁ Δ₂ →
    HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := split.S1 } split.G1 P
      { right := Sown.right ++ split.S2, left := S₁' } G₁' W₁ Δ₁ →
    HasTypeProcPreOut Ssh { right := Sown.right ++ split.S1, left := split.S2 } split.G2 Q
      { right := Sown.right ++ split.S1, left := S₂' } G₂' W₂ Δ₂ →
    (DisjointG split.G2 Gfr →
      HasTypeProcPreOut Ssh { right := Sown.right ++ split.S1, left := split.S2 } (split.G2 ++ Gfr) Q
        { right := Sown.right ++ split.S1, left := S₂' } (G₂' ++ Gfr) W₂ Δ₂) →
    HasTypeProcPreOut Ssh Sown (G ++ Gfr) (.par nS nG P Q) Sfin (Gfin ++ Gfr) W Δ := by
  intro hDisj hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
    hDisjW hDisjΔ hP hQ ihQ
  let splitOut : ParSplit Sown.left (G ++ Gfr) :=
    { S1 := split.S1
      S2 := split.S2
      G1 := split.G1
      G2 := split.G2 ++ Gfr
      hS := by simpa using split.hS
      hG := by simpa [split.hG, List.append_assoc] }
  have hDisjG1fr : DisjointG split.G1 Gfr :=
    (disjointG_split_frame_right (split:=split) hDisj).1
  have hDisjG2fr : DisjointG split.G2 Gfr :=
    (disjointG_split_frame_right (split:=split) hDisj).2
  have hDisjGOut : DisjointG splitOut.G1 splitOut.G2 := by
    have hDisjG' : DisjointG (split.G2 ++ Gfr) split.G1 :=
      DisjointG_append_left (DisjointG_symm hDisjG) (DisjointG_symm hDisjG1fr)
    exact DisjointG_symm (by simpa [splitOut] using hDisjG')
  have hQ' := ihQ hDisjG2fr
  have hGfin' : (G₁' ++ G₂') ++ Gfr = G₁' ++ (G₂' ++ Gfr) := by
    simp [List.append_assoc]
  refine HasTypeProcPreOut.par (G₂':=G₂' ++ Gfr) splitOut ?_ ?_ ?_ ?_ ?_ hDisjGOut hDisjS
    hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hP ?_
  · simpa [splitOut] using hSlen
  · simpa [hSfin] using rfl
  · simpa [hGfin, hGfin', splitOut] using rfl
  · simpa [hW] using rfl
  · simpa [hΔ] using rfl
  · simpa [splitOut] using hQ'

/-- Local right-frame transport for `HasTypeProcPreOut`. -/
private lemma HasTypeProcPreOut_frame_G_right_local
    {Ssh : SEnv} {Sown : OwnedEnv} {G Gfr : GEnv} {P : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointG G Gfr →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    HasTypeProcPreOut Ssh Sown (G ++ Gfr) P Sfin (Gfin ++ Gfr) W Δ := by
  intro hDisj h
  induction h with
  | skip =>
      rename_i Sown G
      simpa using (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr))
  | send hk hG hx =>
      rename_i Sown G k x e q T L
      have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
        (L:=.send q T L) (L':=L) hG
      simpa [hUpd] using
        (HasTypeProcPreOut.send (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr)
          hk (lookupG_append_left (G₂:=Gfr) hG) hx)
  | recv_new hk hG hNoSh hNoOwnL =>
      rename_i Sown G k x e p T L
      have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
        (L:=.recv p T L) (L':=L) hG
      simpa [hUpd] using
        (HasTypeProcPreOut.recv_new (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr)
          hk (lookupG_append_left (G₂:=Gfr) hG) hNoSh hNoOwnL)
  | recv_old hk hG hNoSh hOwn =>
      rename_i Sown G k x e p T L T'
      have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
        (L:=.recv p T L) (L':=L) hG
      simpa [hUpd] using
        (HasTypeProcPreOut.recv_old (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr)
          hk (lookupG_append_left (G₂:=Gfr) hG) hNoSh hOwn)
  | select hk hG hbs =>
      rename_i Sown G k l e q bs L
      have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
        (L:=.select q bs) (L':=L) hG
      simpa [hUpd] using
        (HasTypeProcPreOut.select (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr)
          hk (lookupG_append_left (G₂:=Gfr) hG) hbs)
  | branch hk hG hLen hLabels hBodies hOutLbl hSess hDom hRight ihOutLbl =>
      rename_i Sown G k procs e p bs Sfin Gfin W Δ
      have hBodies' := frame_right_branch_bodies_local (G:=G) (Gfr:=Gfr) hG hBodies
      have hOutLbl' := frame_right_branch_out_local (G:=G) (Gfr:=Gfr) hG ihOutLbl hDisj
      have hSess' : SessionsOf (Gfin ++ Gfr) ⊆ SessionsOf (G ++ Gfr) := by
        intro s hs
        have hs' := SessionsOf_append_subset (G₁:=Gfin) (G₂:=Gfr) hs
        cases hs' with
        | inl hsL =>
            exact SessionsOf_append_left (G₂:=Gfr) (hSess hsL)
        | inr hsR =>
            exact SessionsOf_append_right (G₁:=G) hsR
      exact HasTypeProcPreOut.branch (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr)
        hk (lookupG_append_left (G₂:=Gfr) hG) hLen hLabels hBodies' hOutLbl' hSess' hDom hRight
  | seq hP hQ ihP ihQ =>
      rename_i Sown G P Q S₁ G₁ S₂ G₂ W₁ W₂ Δ₁ Δ₂
      have hP' := ihP hDisj
      have hSubG1 : SessionsOf G₁ ⊆ SessionsOf G := SessionsOf_subset_of_HasTypeProcPreOut hP
      have hDisjG1fr : DisjointG G₁ Gfr := DisjointG_of_subset_left hSubG1 hDisj
      exact HasTypeProcPreOut.seq hP' (ihQ hDisjG1fr)
  | par split hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
      hDisjW hDisjΔ hP hQ ihP ihQ =>
      rename_i Sown G P Q Sfin Gfin W Δ S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂ nS nG
      exact frame_pre_out_right_par_local (split:=split)
        hDisj hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
        hDisjW hDisjΔ hP hQ ihQ
  | assign_new hNoSh hNoOwnL hv =>
      rename_i Sown G x v T
      exact HasTypeProcPreOut.assign_new hNoSh hNoOwnL (HasTypeVal_frame_right (G₁:=G) (G₂:=Gfr) hv)
  | assign_old hNoSh hOwn hv =>
      rename_i Sown G x v T T'
      exact HasTypeProcPreOut.assign_old hNoSh hOwn (HasTypeVal_frame_right (G₁:=G) (G₂:=Gfr) hv)

/-! ## Local G-Frame Transport (Left) -/

/-- Erasing a binding cannot introduce new domain elements. -/
private lemma eraseSEnv_domsubset_local {S : SEnv} {x : Var} :
    SEnvDomSubset (eraseSEnv S x) S := by
  intro y T hLookup
  induction S with
  | nil =>
      simp [eraseSEnv, lookupSEnv] at hLookup
  | cons hd tl ih =>
      cases hd with
      | mk z U =>
          by_cases hzx : x = z
          · subst hzx
            simp [eraseSEnv] at hLookup
            obtain ⟨T', hT'⟩ := ih hLookup
            by_cases hyx : y = x
            · subst hyx
              exact ⟨U, by simp [lookupSEnv, List.lookup]⟩
            · have hbeq : (y == x) = false := by
                exact beq_eq_false_iff_ne.mpr hyx
              exact ⟨T', by simpa [lookupSEnv, List.lookup, hbeq] using hT'⟩
          · by_cases hyz : y = z
            · subst hyz
              exact ⟨U, by simp [lookupSEnv, List.lookup]⟩
            · have hbeq : (y == z) = false := by
                exact beq_eq_false_iff_ne.mpr hyz
              simp [eraseSEnv, hzx, lookupSEnv, List.lookup, hbeq] at hLookup
              obtain ⟨T', hT'⟩ := ih hLookup
              exact ⟨T', by simpa [lookupSEnv, List.lookup, hbeq] using hT'⟩

/-- Pre-out typing only preserves or erases right-owned bindings. -/
private lemma HasTypeProcPreOut_right_domsubset_local
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {P : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    SEnvDomSubset Sfin.right Sown.right := by
  intro h
  induction h with
  | skip =>
      exact SEnvDomSubset_refl
  | send =>
      exact SEnvDomSubset_refl
  | recv_new _ _ _ _ =>
      simpa [OwnedEnv.updateLeft] using
        (eraseSEnv_domsubset_local : SEnvDomSubset (eraseSEnv _ _) _)
  | recv_old _ _ _ _ =>
      simpa [OwnedEnv.updateLeft] using
        (eraseSEnv_domsubset_local : SEnvDomSubset (eraseSEnv _ _) _)
  | select =>
      exact SEnvDomSubset_refl
  | branch _ _ _ _ _ _ _ hDom hRight _ =>
      simpa [hRight] using (SEnvDomSubset_refl : SEnvDomSubset _ _)
  | seq hP hQ ihP ihQ =>
      exact SEnvDomSubset_trans ihQ ihP
  | par _ _ hSfin _ _ _ _ _ _ _ _ _ _ _ _ =>
      simpa [hSfin] using (SEnvDomSubset_refl : SEnvDomSubset _ _)
  | assign_new _ _ _ =>
      simpa [OwnedEnv.updateLeft] using
        (eraseSEnv_domsubset_local : SEnvDomSubset (eraseSEnv _ _) _)
  | assign_old _ _ _ =>
      simpa [OwnedEnv.updateLeft] using
        (eraseSEnv_domsubset_local : SEnvDomSubset (eraseSEnv _ _) _)

/-- Helper: reframe the left-par pre-out typing across an empty right frame. -/
private lemma frame_left_par_reframe_local
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfr Gleft Gleft' G₂ G₂' : GEnv} {P Q : Process}
    {S₁ S₂ S₁' S₂' : SEnv} {W₁ W₂ : Footprint} {Δ₁ Δ₂ : DeltaSEnv} :
    HasTypeProcPreOut Ssh { right := Sown.right ++ S₂, left := S₁ } (Gfr ++ Gleft) P
      { right := Sown.right ++ S₂, left := S₁' } (Gfr ++ Gleft') W₁ Δ₁ →
    HasTypeProcPreOut Ssh { right := Sown.right ++ S₁, left := S₂ } G₂ Q
      { right := Sown.right ++ S₁, left := S₂' } G₂' W₂ Δ₂ →
    HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := S₁ } (Gfr ++ Gleft) P
      { right := (∅ : SEnv), left := S₁' } (Gfr ++ Gleft') W₁ Δ₁ ∧
    HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := S₂ } G₂ Q
      { right := (∅ : SEnv), left := S₂' } G₂' W₂ Δ₂ := by
  intro hP hQ
  have hP0 :=
    HasTypeProcPreOut_reframe_right
      (R:=Sown.right ++ S₂) (R':=(∅ : SEnv)) (L:=S₁) (L':=S₁')
      (G:=Gfr ++ Gleft) (P:=P)
      (DisjointS_left_empty S₁) (DisjointS_left_empty S₁') hP
  have hQ0 :=
    HasTypeProcPreOut_reframe_right
      (R:=Sown.right ++ S₁) (R':=(∅ : SEnv)) (L:=S₂) (L':=S₂')
      (G:=G₂) (P:=Q)
      (DisjointS_left_empty S₂) (DisjointS_left_empty S₂') hQ
  exact ⟨hP0, hQ0⟩

/-- Helper: assemble the par case with empty right frame. -/
private lemma frame_left_par_apply_local
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfr G : GEnv} {P Q : Process} {nS nG : Nat}
    {Sfin : OwnedEnv} {Gfin : GEnv} {Wfin : Footprint} {Δfin : DeltaSEnv}
    {S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂}
    (split : ParSplit Sown.left G) :
    split.S1.length = nS →
    Sfin = { right := Sown.right, left := S₁' ++ S₂' } →
    Gfin = (G₁' ++ G₂') →
    Wfin = (W₁ ++ W₂) →
    Δfin = (Δ₁ ++ Δ₂) →
    DisjointG split.G1 split.G2 →
    DisjointS split.S1 split.S2 →
    DisjointS S₁' split.S2 →
    DisjointS split.S1 S₂' →
    DisjointS S₁' S₂' →
    DisjointW W₁ W₂ →
    DisjointS Δ₁ Δ₂ →
    HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := split.S1 } (Gfr ++ split.G1) P
      { right := (∅ : SEnv), left := S₁' } (Gfr ++ G₁') W₁ Δ₁ →
    HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := split.S2 } split.G2 Q
      { right := (∅ : SEnv), left := S₂' } G₂' W₂ Δ₂ →
    DisjointG Gfr G →
    HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := Sown.left } (Gfr ++ G)
      (.par nS nG P Q) { right := (∅ : SEnv), left := S₁' ++ S₂' } (Gfr ++ Gfin) Wfin Δfin := by
  intro hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
    hDisjW hDisjΔ hP hQ hDisjGfrG
  have hDisjEmpty_left : DisjointS (∅ : SEnv) Sown.left := by
    exact DisjointS_left_empty Sown.left
  have hDisjEmpty_fin : DisjointS (∅ : SEnv) (S₁' ++ S₂') := by
    exact DisjointS_left_empty (S₁' ++ S₂')
  have ihP :
      DisjointS (∅ : SEnv) split.S1 →
      DisjointS (∅ : SEnv) S₁' →
      DisjointG Gfr split.G1 →
      HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := split.S1 } (Gfr ++ split.G1) P
        { right := (∅ : SEnv), left := S₁' } (Gfr ++ G₁') W₁ Δ₁ := by
    intro _ _ _
    exact hP
  exact frame_left_par (split:=split)
    (hSlen:=hSlen) (hSfin:=rfl) (hGfin:=hGfin) (hW:=hW) (hΔ:=hΔ)
    hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ
    hQ hDisjEmpty_left hDisjEmpty_fin hDisjGfrG ihP

/-- Helper: restore the right-owned frame after a par step. -/
private lemma frame_left_par_restore_local
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfr G : GEnv} {P Q : Process} {nS nG : Nat}
    {S₁' S₂' : SEnv} {Gfin : GEnv} {Wfin : Footprint} {Δfin : DeltaSEnv} :
    DisjointS Sown.right Sown.left →
    DisjointS Sown.right (S₁' ++ S₂') →
    HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := Sown.left } (Gfr ++ G)
      (.par nS nG P Q) { right := (∅ : SEnv), left := S₁' ++ S₂' } (Gfr ++ Gfin) Wfin Δfin →
    HasTypeProcPreOut Ssh { right := Sown.right, left := Sown.left } (Gfr ++ G)
      (.par nS nG P Q) { right := Sown.right, left := S₁' ++ S₂' } (Gfr ++ Gfin) Wfin Δfin := by
  intro hDisjIn hDisjOut hPar0
  exact HasTypeProcPreOut_reframe_right
    (R:=(∅ : SEnv)) (R':=Sown.right) (L:=Sown.left) (L':=S₁' ++ S₂')
    (G:=Gfr ++ G) (P:=.par nS nG P Q) hDisjIn hDisjOut hPar0

/-- Local constructive par case for left-G framing. -/
private lemma HasTypeProcPreOut_frame_G_left_par_local
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfr G : GEnv} {P Q : Process} {nS nG : Nat}
    {Sfin : OwnedEnv} {Gfin : GEnv} {Wfin : Footprint} {Δfin : DeltaSEnv}
    {S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂}
    (split : ParSplit Sown.left G) :
    split.S1.length = nS →
    Sfin = { right := Sown.right, left := S₁' ++ S₂' } →
    Gfin = (G₁' ++ G₂') →
    Wfin = (W₁ ++ W₂) →
    Δfin = (Δ₁ ++ Δ₂) →
    DisjointG split.G1 split.G2 →
    DisjointS split.S1 split.S2 →
    DisjointS S₁' split.S2 →
    DisjointS split.S1 S₂' →
    DisjointS S₁' S₂' →
    DisjointS Sown.right Sown.left →
    DisjointS Sown.right (S₁' ++ S₂') →
    DisjointW W₁ W₂ →
    DisjointS Δ₁ Δ₂ →
    HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := split.S1 } (Gfr ++ split.G1) P
      { right := Sown.right ++ split.S2, left := S₁' } (Gfr ++ G₁') W₁ Δ₁ →
    HasTypeProcPreOut Ssh { right := Sown.right ++ split.S1, left := split.S2 } split.G2 Q
      { right := Sown.right ++ split.S1, left := S₂' } G₂' W₂ Δ₂ →
    DisjointG Gfr split.G1 →
    DisjointG Gfr split.G2 →
    HasTypeProcPreOut Ssh Sown (Gfr ++ G) (.par nS nG P Q) Sfin (Gfr ++ Gfin) Wfin Δfin := by
  intro hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
    hDisjRightIn hDisjRightOut hDisjW hDisjΔ hP hQ hDisjGfrG1 hDisjGfrG2
  have hDisjGfrG : DisjointG Gfr G := by
    have hDisjGfrG' : DisjointG Gfr (split.G1 ++ split.G2) :=
      DisjointG_append_right (G₁:=Gfr) (G₂:=split.G1) (G₃:=split.G2) hDisjGfrG1 hDisjGfrG2
    simpa [split.hG] using hDisjGfrG'
  obtain ⟨hP0, hQ0⟩ := frame_left_par_reframe_local (Sown:=Sown) (Gfr:=Gfr) hP hQ
  have hPar0 :=
    frame_left_par_apply_local (split:=split) (nG:=nG)
      hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
      hDisjW hDisjΔ hP0 hQ0 hDisjGfrG
  have hPar1 := frame_left_par_restore_local (Sown:=Sown) (Gfr:=Gfr) (G:=G)
    hDisjRightIn hDisjRightOut hPar0
  simpa [hSfin] using hPar1

/-- Local left-frame transport for `HasTypeProcPreOut`. -/
private lemma HasTypeProcPreOut_frame_G_left_local
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfr G : GEnv} {P : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointG Gfr G →
    DisjointS Sown.right Sown.left →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    DisjointS Sown.right Sfin.left →
    HasTypeProcPreOut Ssh Sown (Gfr ++ G) P Sfin (Gfr ++ Gfin) W Δ := by
  intro hDisj hDisjRightIn h hDisjRightOut
  induction h with
  | skip =>
      rename_i Sown G
      simpa using (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G))
  | send hk hG hx =>
      rename_i Sown G k x e q T L
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
      have hSend :
          HasTypeProcPreOut Ssh Sown (Gfr ++ G) (.send k x) Sown
            (updateG (Gfr ++ G) e L) [] ∅ :=
        HasTypeProcPreOut.send (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G)
          hk (by simpa [hG] using lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone) hx
      rw [hUpd] at hSend
      exact hSend
  | recv_new hk hG hNoSh hNoOwnL =>
      rename_i Sown G k x e p T L
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
      have hRecv :
          HasTypeProcPreOut Ssh Sown (Gfr ++ G) (.recv k x) (OwnedEnv.updateLeft Sown x T)
            (updateG (Gfr ++ G) e L) [x] (updateSEnv ∅ x T) :=
        HasTypeProcPreOut.recv_new (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G)
          hk (by simpa [hG] using lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone)
          hNoSh hNoOwnL
      rw [hUpd] at hRecv
      exact hRecv
  | recv_old hk hG hNoSh hOwn =>
      rename_i Sown G k x e p T L T'
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
      have hRecv :
          HasTypeProcPreOut Ssh Sown (Gfr ++ G) (.recv k x) (OwnedEnv.updateLeft Sown x T)
            (updateG (Gfr ++ G) e L) [x] ∅ :=
        HasTypeProcPreOut.recv_old (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G)
          hk (by simpa [hG] using lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone)
          hNoSh hOwn
      rw [hUpd] at hRecv
      exact hRecv
  | select hk hG hbs =>
      rename_i Sown G k l e q bs L
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
      have hSel :
          HasTypeProcPreOut Ssh Sown (Gfr ++ G) (.select k l) Sown
            (updateG (Gfr ++ G) e L) [] ∅ :=
        HasTypeProcPreOut.select (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G)
          hk (by simpa [hG] using lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone) hbs
      rw [hUpd] at hSel
      exact hSel
  | branch hk hG hLen hLabels hBodies hOutLbl hSess hDom hRight ihOutLbl =>
      rename_i Sown G k procs e p bs Sfin Gfin W Δ
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hBodies' :
          ∀ i (hi : i < bs.length) (hip : i < procs.length),
            HasTypeProcPre Ssh Sown
              (updateG (Gfr ++ G) e (bs.get ⟨i, hi⟩).2)
              (procs.get ⟨i, hip⟩).2 := by
        intro i hi hip
        have hBody := hBodies i hi hip
        have hDisj' : DisjointG Gfr (updateG G e (bs.get ⟨i, hi⟩).2) := by
          have hDisj'0 :
              DisjointG (updateG G e (bs.get ⟨i, hi⟩).2) Gfr :=
            disjointG_updateG_left (e:=e) (L:=(bs.get ⟨i, hi⟩).2) (L0:=.branch p bs)
              hG (DisjointG_symm hDisj)
          exact DisjointG_symm hDisj'0
        have hBody' := HasTypeProcPre_frame_G (G₁:=Gfr)
          (G₂:=updateG G e (bs.get ⟨i, hi⟩).2) hDisj' hBody
        have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e)
          (L:=(bs.get ⟨i, hi⟩).2) hNone
        have hBody'' := hBody'
        rw [hUpd.symm] at hBody''
        exact hBody''
      have hOutLbl' : ∀ lbl P L,
          procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
          bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
          HasTypeProcPreOut Ssh Sown (updateG (Gfr ++ G) e L) P Sfin (Gfr ++ Gfin) W Δ := by
        intro lbl P L hFindP hFindB
        have hDisj' : DisjointG Gfr (updateG G e L) := by
          have hDisj'0 : DisjointG (updateG G e L) Gfr :=
            disjointG_updateG_left (e:=e) (L:=L) (L0:=.branch p bs) hG (DisjointG_symm hDisj)
          exact DisjointG_symm hDisj'0
        have hOut' := ihOutLbl lbl P L hFindP hFindB hDisj' hDisjRightIn
          (by simpa [hRight] using hDisjRightOut)
        have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
        simpa [hUpd] using hOut'
      have hSess' : SessionsOf (Gfr ++ Gfin) ⊆ SessionsOf (Gfr ++ G) := by
        intro s hs
        have hs' := SessionsOf_append_subset (G₁:=Gfr) (G₂:=Gfin) hs
        cases hs' with
        | inl hsL =>
            exact SessionsOf_append_left (G₂:=G) hsL
        | inr hsR =>
            exact SessionsOf_append_right (G₁:=Gfr) (hSess hsR)
      exact HasTypeProcPreOut.branch (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G)
        hk (by simpa [hG] using lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone)
        hLen hLabels hBodies' hOutLbl' hSess' hDom hRight
  | seq hP hQ ihP ihQ =>
      rename_i Sown G P Q S₁ G₁ S₂ G₂ W₁ W₂ Δ₁ Δ₂
      have hDomQ : SEnvDomSubset S₁.left S₂.left := HasTypeProcPreOut_domsubset hQ
      have hDisjRightMid : DisjointS Sown.right S₁.left :=
        DisjointS_of_domsubset_right hDomQ hDisjRightOut
      have hP' := ihP hDisj hDisjRightIn hDisjRightMid
      have hSubRightMid : SEnvDomSubset S₁.right Sown.right :=
        HasTypeProcPreOut_right_domsubset_local hP
      have hDisjMidIn : DisjointS S₁.right S₁.left :=
        DisjointS_of_domsubset_left hSubRightMid hDisjRightMid
      have hDisjMidOut : DisjointS S₁.right S₂.left :=
        DisjointS_of_domsubset_left hSubRightMid hDisjRightOut
      have hSubG1 : SessionsOf G₁ ⊆ SessionsOf G :=
        SessionsOf_subset_of_HasTypeProcPreOut hP
      have hDisjG1fr : DisjointG Gfr G₁ := by
        have hDisj' : DisjointG G₁ Gfr := DisjointG_of_subset_left hSubG1 (DisjointG_symm hDisj)
        exact DisjointG_symm hDisj'
      exact HasTypeProcPreOut.seq hP' (ihQ hDisjG1fr hDisjMidIn hDisjMidOut)
  | par split hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
      hDisjW hDisjΔ hP hQ ihP ihQ =>
      rename_i Sown G P Q Sfin Gfin W Δ S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂ nS nG
      have hDisjG1fr : DisjointG split.G1 Gfr :=
        (disjointG_split_frame_right (split:=split) (DisjointG_symm hDisj)).1
      have hDisjG2fr : DisjointG split.G2 Gfr :=
        (disjointG_split_frame_right (split:=split) (DisjointG_symm hDisj)).2
      have hDisjGfrG1 : DisjointG Gfr split.G1 := DisjointG_symm hDisjG1fr
      have hDisjGfrG2 : DisjointG Gfr split.G2 := DisjointG_symm hDisjG2fr
      have hDisjRightS1 : DisjointS Sown.right split.S1 := by
        have hSubS1 : SEnvDomSubset split.S1 Sown.left := by
          simpa [split.hS] using (SEnvDomSubset_append_left (S₁:=split.S1) (S₂:=split.S2))
        exact DisjointS_of_domsubset_right hSubS1 hDisjRightIn
      have hDisjRightS2 : DisjointS Sown.right split.S2 := by
        have hSubS2 : SEnvDomSubset split.S2 Sown.left := by
          simpa [split.hS] using (SEnvDomSubset_append_right (S₁:=split.S1) (S₂:=split.S2))
        exact DisjointS_of_domsubset_right hSubS2 hDisjRightIn
      have hDisjRightOut' : DisjointS Sown.right (S₁' ++ S₂') := by
        simpa [hSfin] using hDisjRightOut
      have hDisjRightS1' : DisjointS Sown.right S₁' := by
        have hSubS1' : SEnvDomSubset S₁' (S₁' ++ S₂') := by
          simpa using (SEnvDomSubset_append_left (S₁:=S₁') (S₂:=S₂'))
        exact DisjointS_of_domsubset_right hSubS1' hDisjRightOut'
      have hDisjPIn : DisjointS (Sown.right ++ split.S2) split.S1 :=
        DisjointS_append_left hDisjRightS1 (DisjointS_symm hDisjS)
      have hDisjPOut : DisjointS (Sown.right ++ split.S2) S₁' :=
        DisjointS_append_left hDisjRightS1' (DisjointS_symm hDisjS_left)
      have hP' := ihP hDisjGfrG1 hDisjPIn hDisjPOut
      exact HasTypeProcPreOut_frame_G_left_par_local (Ssh:=Ssh) (Gfr:=Gfr) (split:=split)
        hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
        hDisjRightIn hDisjRightOut' hDisjW hDisjΔ hP' hQ hDisjGfrG1 hDisjGfrG2
  | assign_new hNoSh hNoOwnL hv =>
      rename_i Sown G x v T
      exact HasTypeProcPreOut.assign_new hNoSh hNoOwnL (HasTypeVal_frame_left (G₁:=Gfr) (G₂:=G) hDisj hv)
  | assign_old hNoSh hOwn hv =>
      rename_i Sown G x v T T'
      exact HasTypeProcPreOut.assign_old hNoSh hOwn (HasTypeVal_frame_left (G₁:=Gfr) (G₂:=G) hDisj hv)

/-!
  Full-G step rule: preserve pre-out typing when stepping in the middle of a G-frame.
  This is kept as an explicit proposition so downstream proofs can thread it
  as a hypothesis while the constructive proof is being migrated.
-/
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
private def MiddleFrameGoal
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

private lemma length_updateG_hit {G : GEnv} {e : Endpoint} {L L' : LocalType} :
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

private lemma SessionsOf_left_subset_of_update
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

private lemma SessionsOf_right_subset_of_update
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
private lemma middle_send_lookup_of_pre
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
private lemma middle_recv_lookup_of_pre
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
private lemma middle_select_lookup_of_pre
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
private lemma middle_branch_lookup_of_pre
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
private lemma middle_send_update_decompose
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
private lemma preserved_sub_middle_send
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

/-- Constructive middle-frame preservation for a `select` step. -/
private lemma preserved_sub_middle_select
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

/-- Constructive middle-frame preservation for a `recv` step. -/
private lemma preserved_sub_middle_recv
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

/-- Constructive middle-frame preservation for a `branch` step. -/
private lemma preserved_sub_middle_branch
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
          have hSubSess : SessionsOf Gmid' ⊆ SessionsOf Gmid := by
            rw [hMid']
            exact SessionsOf_subset_middle_update (Gmid:=Gmid) (e:=e)
              (L0:=.branch p bsMid) (L:=L) hMid
          refine ⟨Gmid', W, Δ, hEqG', hSubSess, ?_, FootprintSubset_refl, SEnvDomSubset_refl⟩
          have hGmidEq : Gmid' = updateG Gmid eMid L := by
            simpa [hEqE] using hMid'
          simpa [hGmidEq] using hPre'

/-- Constructive middle-frame preservation for an `assign` step. -/
private lemma preserved_sub_middle_assign
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

/-- Constructive middle-frame preservation for `seq_skip`. -/
private lemma preserved_sub_middle_seq_skip
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

/-- Constructive middle-frame preservation for `seq_step`, assuming recursive middle preservation. -/
private lemma preserved_sub_middle_seq_step
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

private lemma ParSplit.sides_eq_of_len
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

private lemma StoreTyped_par_left_inner
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

theorem HasTypeProcPreOut_preserved_sub_middle_frame :
    HasTypeProcPreOut_preserved_sub_middle_frame_spec := by
  intro Gstore Gleft Gmid Gright G D Ssh Sown store bufs P
    G' D' Sown' store' bufs' P' Sfin Gfin W Δ
    hStore hDisjShAll hOwn hDisjLM hDisjLR hDisjMR hEqG hTS hDisjRightFin hPre
  induction hTS generalizing Gstore Gleft Gmid Gright Sfin Gfin W Δ with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      exact preserved_sub_middle_send
        (Gstore:=Gstore) (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
        (G:=G) (D:=D) (D':=D')
        (Ssh:=Ssh) (Sown:=Sown) (store:=store) (bufs:=bufs) (bufs':=bufs')
        (k:=k) (x:=x) (e:=e) (target:=target) (T:=T) (L:=L) (G':=G')
        (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ)
        hStore hOwn hDisjLM hEqG hk hG hGout
        (TypedStep.send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut)
        hPre
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      exact preserved_sub_middle_recv
        (Gstore:=Gstore) (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
        (G:=G) (D:=D) (D':=D')
        (Ssh:=Ssh) (Sown:=Sown) (Sown':=Sown')
        (store:=store) (store':=store') (bufs:=bufs) (bufs':=bufs')
        (k:=k) (x:=x) (e:=e) (source:=source) (T:=T) (L:=L) (G':=G')
        (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ)
        hStore hOwn hDisjLM hEqG hk hG hGout hSout
        (TypedStep.recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut)
        hPre
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      exact preserved_sub_middle_select
        (Gstore:=Gstore) (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
        (G:=G) (D:=D) (D':=D')
        (Ssh:=Ssh) (Sown:=Sown) (store:=store) (bufs:=bufs) (bufs':=bufs')
        (k:=k) (ℓ:=ℓ) (e:=e) (target:=target) (bs:=bs) (L:=L) (G':=G')
        (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ)
        hStore hOwn hDisjLM hEqG hk hG hFind hGout
        (TypedStep.select hk hG hFind hReady hEdge hGout hDout hBufsOut)
        hPre
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      exact preserved_sub_middle_branch
        (Gstore:=Gstore) (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
        (G:=G) (D:=D) (D':=D')
        (Ssh:=Ssh) (Sown:=Sown) (store:=store) (bufs:=bufs) (bufs':=bufs')
        (k:=k) (procs:=procs) (e:=e) (source:=source) (bs:=bs) (ℓ:=ℓ)
        (P:=P) (L:=L) (G':=G')
        (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ)
        hStore hOwn hDisjLM hEqG hk hG hFindP hFindT hGout
        (TypedStep.branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut)
        hPre
  | assign hv hSout hStoreOut =>
      rename_i G D Ssh Sown store bufs x v Tstep Sown' store'
      exact preserved_sub_middle_assign
        (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
        (G:=G) (G':=G) (D:=D)
        (Ssh:=Ssh) (Sown:=Sown) (Sown':=Sown')
        (store:=store) (store':=store') (bufs:=bufs)
        (x:=x) (v:=v) (Tstep:=Tstep)
        (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ)
        hDisjLM hEqG rfl hSout hv
        (TypedStep.assign hv hSout hStoreOut)
        hPre
  | seq_step hStep ih =>
      rename_i G D Ssh Sown G' D' Sown' store bufs store' bufs' P P' Q
      have hMiddle : MiddleFrameGoal (hTS := hStep) := by
        intro Gstore0 Gleft0 Gmid0 Gright0 Sfin0 Gfin0 W0 Δ0
          hStore0 hDisjSh0 hOwn0 hDisjLM0 hDisjLR0 hDisjMR0 hEqG0 hDisjRight0 hPre0
        exact ih hStore0 hDisjSh0 hOwn0 hDisjLM0 hDisjLR0 hDisjMR0 hEqG0 hDisjRight0 hPre0
      exact preserved_sub_middle_seq_step
        (Gstore:=Gstore) (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
        (G:=G) (G':=G') (D:=D) (D':=D')
        (Ssh:=Ssh) (Sown:=Sown) (Sown':=Sown')
        (store:=store) (store':=store') (bufs:=bufs) (bufs':=bufs')
        (P:=P) (P':=P') (Q:=Q)
        (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ)
        hStore hDisjShAll hOwn hDisjLM hDisjLR hDisjMR hEqG hStep hMiddle hDisjRightFin hPre
  | seq_skip =>
      rename_i G D Ssh Sown store bufs Q
      exact preserved_sub_middle_seq_skip
        (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright) (G:=G) (D:=D)
        (Ssh:=Ssh) (Sown:=Sown) (store:=store) (bufs:=bufs)
        (Q:=Q) (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ)
        hEqG TypedStep.seq_skip hPre
  | par_left split hSlen hTS hDisjG hDisjD hDisjS ih =>
      rename_i Ssh0 Sown0 store0 bufs0 store0' bufs0' P0 P0' Q0
        G0 D₁0 D₂0 G₁_step D₁_step S₁_step nS0 nG0
      obtain ⟨pw, S₁_fin, S₂_fin, G₁_fin, G₂_fin, W₁, W₂, Δ₁, Δ₂,
          hSfin, hGfin, hW, hΔ, hDisjG_mid, hDisjS_mid, hDisjS_left_mid, hDisjS_right_mid,
          hDisjS_fin, hDisjW, hDisjΔ, hP_pre, hQ_pre⟩ :=
        HasTypeProcPreOut_par_inv_witness hPre
      let splitMid : ParSplit Sown0.left Gmid := pw.split
      have hSlenEq : split.S1.length = splitMid.S1.length := by
        calc
          split.S1.length = nS0 := hSlen
          _ = splitMid.S1.length := by simpa [splitMid] using pw.hSlen.symm
      have hSidesEq := ParSplit.sides_eq_of_len (split₁:=split) (split₂:=splitMid) hSlenEq
      have hS1Eq : split.S1 = splitMid.S1 := hSidesEq.1
      have hS2Eq : split.S2 = splitMid.S2 := hSidesEq.2
      have hStoreInner :
          StoreTyped Gstore (SEnvAll Ssh0 { right := Sown0.right ++ split.S2, left := split.S1 }) store0 :=
        StoreTyped_par_left_inner (split:=split) hDisjS hStore
      have hShAll :
          DisjointS Ssh0 (Sown0.right ++ (split.S1 ++ split.S2)) := by
        simpa [OwnedEnv.all, split.hS, List.append_assoc] using hDisjShAll
      have hShR : DisjointS Ssh0 Sown0.right := DisjointS_of_append_left hShAll
      have hSh12 : DisjointS Ssh0 (split.S1 ++ split.S2) := DisjointS_of_append_right hShAll
      have hShS1 : DisjointS Ssh0 split.S1 := DisjointS_of_append_left hSh12
      have hShS2 : DisjointS Ssh0 split.S2 := DisjointS_of_append_right hSh12
      have hDisjShInner :
          DisjointS Ssh0 ({ right := Sown0.right ++ split.S2, left := split.S1 } : OwnedEnv) := by
        have hTmp : DisjointS Ssh0 ((Sown0.right ++ split.S2) ++ split.S1) :=
          DisjointS_append_right (DisjointS_append_right hShR hShS2) hShS1
        simpa [OwnedEnv.all, List.append_assoc] using hTmp
      have hOwnAll : DisjointS Sown0.right (split.S1 ++ split.S2) := by
        simpa [OwnedDisjoint, split.hS] using hOwn
      have hDisjRightS1 : DisjointS Sown0.right split.S1 := DisjointS_of_append_left hOwnAll
      have hDisjRightS2 : DisjointS Sown0.right split.S2 := DisjointS_of_append_right hOwnAll
      have hOwnInner :
          OwnedDisjoint ({ right := Sown0.right ++ split.S2, left := split.S1 } : OwnedEnv) :=
        DisjointS_append_left hDisjRightS1 (DisjointS_symm hDisjS)
      have hSubG1 : SessionsOf splitMid.G1 ⊆ SessionsOf Gmid := by
        intro s hs
        simpa [splitMid, splitMid.hG] using
          (SessionsOf_append_left (G₁:=splitMid.G1) (G₂:=splitMid.G2) hs)
      have hSubG2 : SessionsOf splitMid.G2 ⊆ SessionsOf Gmid := by
        intro s hs
        simpa [splitMid, splitMid.hG] using
          (SessionsOf_append_right (G₁:=splitMid.G1) (G₂:=splitMid.G2) hs)
      have hDisjLeftG1 : DisjointG Gleft splitMid.G1 := by
        have hSym : DisjointG Gmid Gleft := DisjointG_symm hDisjLM
        have hTmp : DisjointG splitMid.G1 Gleft := DisjointG_of_subset_left hSubG1 hSym
        exact DisjointG_symm hTmp
      have hDisjLeftG2 : DisjointG Gleft splitMid.G2 := by
        have hSym : DisjointG Gmid Gleft := DisjointG_symm hDisjLM
        have hTmp : DisjointG splitMid.G2 Gleft := DisjointG_of_subset_left hSubG2 hSym
        exact DisjointG_symm hTmp
      have hDisjG1Right : DisjointG splitMid.G1 Gright := DisjointG_of_subset_left hSubG1 hDisjMR
      have hDisjLeftRightInner : DisjointG Gleft (splitMid.G2 ++ Gright) :=
        DisjointG_append_right hDisjLeftG2 hDisjLR
      have hDisjMidRightInner : DisjointG splitMid.G1 (splitMid.G2 ++ Gright) :=
        DisjointG_append_right hDisjG_mid hDisjG1Right
      have hEqInner : G0 = Gleft ++ splitMid.G1 ++ (splitMid.G2 ++ Gright) := by
        calc
          G0 = Gleft ++ Gmid ++ Gright := hEqG
          _ = Gleft ++ (splitMid.G1 ++ splitMid.G2) ++ Gright := by
                simpa [splitMid, splitMid.hG]
          _ = Gleft ++ splitMid.G1 ++ (splitMid.G2 ++ Gright) := by
                simp [List.append_assoc]
      have hDisjS_left : DisjointS S₁_fin split.S2 := by
        simpa [splitMid, hS2Eq] using hDisjS_left_mid
      have hDisjRightFinAll : DisjointS Sown0.right (S₁_fin ++ S₂_fin) := by
        simpa [hSfin] using hDisjRightFin
      have hDisjRightS1Fin : DisjointS Sown0.right S₁_fin :=
        DisjointS_of_append_left hDisjRightFinAll
      have hDisjOutP : DisjointS (Sown0.right ++ split.S2) S₁_fin :=
        DisjointS_append_left hDisjRightS1Fin (DisjointS_symm hDisjS_left)
      have hP0 :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ split.S2, left := split.S1 } splitMid.G1 P0
            { right := Sown0.right ++ split.S2, left := S₁_fin } G₁_fin W₁ Δ₁ := by
        simpa [splitMid, hS1Eq, hS2Eq] using hP_pre
      obtain ⟨G₁_mid', W₁', Δ₁', hEqShape, hSubSess1, hP', hSubW1, hSubΔ1⟩ :=
        ih (Gstore:=Gstore) (Gleft:=Gleft) (Gmid:=splitMid.G1) (Gright:=splitMid.G2 ++ Gright)
          (Sfin:={ right := Sown0.right ++ split.S2, left := S₁_fin })
          (Gfin:=G₁_fin) (W:=W₁) (Δ:=Δ₁)
          hStoreInner hDisjShInner hOwnInner hDisjLeftG1 hDisjLeftRightInner hDisjMidRightInner
          hEqInner hDisjOutP hP0
      have hDomStep : SEnvDomSubset S₁_step S₁_fin := by
        simpa using (HasTypeProcPreOut_domsubset hP')
      have hStepS2 : DisjointS S₁_step split.S2 := by
        have hTmp : DisjointS split.S2 S₁_step :=
          DisjointS_of_domsubset_right hDomStep (DisjointS_symm hDisjS_left)
        exact DisjointS_symm hTmp
      have hStepS2fin : DisjointS S₁_step S₂_fin := by
        have hTmp : DisjointS S₂_fin S₁_step :=
          DisjointS_of_domsubset_right hDomStep (DisjointS_symm hDisjS_fin)
        exact DisjointS_symm hTmp
      have hDisjRightS2Fin : DisjointS Sown0.right S₂_fin :=
        DisjointS_of_append_right hDisjRightFinAll
      have hDisjInQNew : DisjointS (Sown0.right ++ S₁_step) split.S2 :=
        DisjointS_append_left hDisjRightS2 hStepS2
      have hDisjOutQNew : DisjointS (Sown0.right ++ S₁_step) S₂_fin :=
        DisjointS_append_left hDisjRightS2Fin hStepS2fin
      have hQ0 :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ split.S1, left := split.S2 } splitMid.G2 Q0
            { right := Sown0.right ++ split.S1, left := S₂_fin } G₂_fin W₂ Δ₂ := by
        simpa [splitMid, hS1Eq, hS2Eq] using hQ_pre
      have hQ1 :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ S₁_step, left := splitMid.S2 } splitMid.G2 Q0
            { right := Sown0.right ++ S₁_step, left := S₂_fin } G₂_fin W₂ Δ₂ := by
        have hTmp :
            HasTypeProcPreOut Ssh0 { right := Sown0.right ++ S₁_step, left := split.S2 } splitMid.G2 Q0
              { right := Sown0.right ++ S₁_step, left := S₂_fin } G₂_fin W₂ Δ₂ :=
          HasTypeProcPreOut_reframe_right
            (R:=Sown0.right ++ split.S1) (R':=Sown0.right ++ S₁_step)
            (L:=split.S2) (L':=S₂_fin) (G:=splitMid.G2) (P:=Q0)
            hDisjInQNew hDisjOutQNew hQ0
        simpa [splitMid, hS2Eq] using hTmp
      have hP1 :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ splitMid.S2, left := S₁_step } G₁_mid' P0'
            { right := Sown0.right ++ splitMid.S2, left := S₁_fin } G₁_fin W₁' Δ₁' := by
        simpa [splitMid, hS2Eq] using hP'
      have hDisjGFinal : DisjointG G₁_mid' splitMid.G2 :=
        DisjointG_of_subset_left hSubSess1 hDisjG_mid
      have hStepS2mid : DisjointS S₁_step splitMid.S2 := by
        simpa [splitMid, hS2Eq] using hStepS2
      have hDisjS1FinS2 : DisjointS S₁_fin splitMid.S2 := by
        simpa [splitMid] using hDisjS_left_mid
      have hDisjW' : DisjointW W₁' W₂ := DisjointW_of_subset_left hSubW1 hDisjW
      have hDisjΔ' : DisjointS Δ₁' Δ₂ := DisjointS_of_domsubset_left hSubΔ1 hDisjΔ
      let splitOut : ParSplit ({ right := Sown0.right, left := S₁_step ++ splitMid.S2 } : OwnedEnv).left
          (G₁_mid' ++ splitMid.G2) :=
        { S1 := S₁_step
          S2 := splitMid.S2
          G1 := G₁_mid'
          G2 := splitMid.G2
          hS := rfl
          hG := rfl }
      have hParMid :
          HasTypeProcPreOut Ssh0 { right := Sown0.right, left := S₁_step ++ splitMid.S2 }
            (G₁_mid' ++ splitMid.G2) (.par S₁_step.length nG0 P0' Q0)
            Sfin Gfin (W₁' ++ W₂) (Δ₁' ++ Δ₂) :=
        HasTypeProcPreOut.par splitOut rfl hSfin hGfin rfl rfl
          hDisjGFinal hStepS2mid hDisjS1FinS2 hStepS2fin hDisjS_fin hDisjW' hDisjΔ'
          hP1 hQ1
      have hEqGFinal : G₁_step ++ split.G2 = Gleft ++ (G₁_mid' ++ splitMid.G2) ++ Gright := by
        simpa [List.append_assoc] using hEqShape
      have hSubSessFinal : SessionsOf (G₁_mid' ++ splitMid.G2) ⊆ SessionsOf Gmid := by
        intro s hs
        have hs' := SessionsOf_append_subset (G₁:=G₁_mid') (G₂:=splitMid.G2) hs
        cases hs' with
        | inl hsL =>
            have hsMid1 : s ∈ SessionsOf splitMid.G1 := hSubSess1 hsL
            simpa [splitMid, splitMid.hG] using
              (SessionsOf_append_left (G₁:=splitMid.G1) (G₂:=splitMid.G2) hsMid1)
        | inr hsR =>
            simpa [splitMid, splitMid.hG] using
              (SessionsOf_append_right (G₁:=splitMid.G1) (G₂:=splitMid.G2) hsR)
      have hSubWFinal : FootprintSubset (W₁' ++ W₂) W := by
        have hSubW12 : FootprintSubset (W₁' ++ W₂) (W₁ ++ W₂) :=
          FootprintSubset_append_left hSubW1
        simpa [hW] using hSubW12
      have hSubΔFinal : SEnvDomSubset (Δ₁' ++ Δ₂) Δ := by
        have hSubΔ12 : SEnvDomSubset (Δ₁' ++ Δ₂) (Δ₁ ++ Δ₂) :=
          SEnvDomSubset_append_left_of_domsubset hSubΔ1
        simpa [hΔ] using hSubΔ12
      refine ⟨G₁_mid' ++ splitMid.G2, W₁' ++ W₂, Δ₁' ++ Δ₂, ?_, hSubSessFinal, ?_, hSubWFinal, hSubΔFinal⟩
      · simpa [hEqGFinal]
      · simpa [splitMid, hS2Eq, List.append_assoc] using hParMid
  | par_right split hSlen hTS hDisjG hDisjD hDisjS ih =>
      rename_i Ssh0 Sown0 store0 bufs0 store0' bufs0' P0 Q0 Q0'
        G0 D₁0 D₂0 G₂_step D₂_step S₂_step nS0 nG0
      obtain ⟨pw, S₁_fin, S₂_fin, G₁_fin, G₂_fin, W₁, W₂, Δ₁, Δ₂,
          hSfin, hGfin, hW, hΔ, hDisjG_mid, hDisjS_mid, hDisjS_left_mid, hDisjS_right_mid,
          hDisjS_fin, hDisjW, hDisjΔ, hP_pre, hQ_pre⟩ :=
        HasTypeProcPreOut_par_inv_witness hPre
      let splitMid : ParSplit Sown0.left Gmid := pw.split
      have hSlenEq : split.S1.length = splitMid.S1.length := by
        calc
          split.S1.length = nS0 := hSlen
          _ = splitMid.S1.length := by simpa [splitMid] using pw.hSlen.symm
      have hSidesEq := ParSplit.sides_eq_of_len (split₁:=split) (split₂:=splitMid) hSlenEq
      have hS1Eq : split.S1 = splitMid.S1 := hSidesEq.1
      have hS2Eq : split.S2 = splitMid.S2 := hSidesEq.2
      have hStoreInner :
          StoreTyped Gstore (SEnvAll Ssh0 { right := Sown0.right ++ split.S1, left := split.S2 }) store0 := by
        simpa [SEnvAll, split.hS, List.append_assoc] using hStore
      have hShAll :
          DisjointS Ssh0 (Sown0.right ++ (split.S1 ++ split.S2)) := by
        simpa [OwnedEnv.all, split.hS, List.append_assoc] using hDisjShAll
      have hDisjShInner :
          DisjointS Ssh0 ({ right := Sown0.right ++ split.S1, left := split.S2 } : OwnedEnv) := by
        simpa [OwnedEnv.all, List.append_assoc] using hShAll
      have hOwnAll : DisjointS Sown0.right (split.S1 ++ split.S2) := by
        simpa [OwnedDisjoint, split.hS] using hOwn
      have hDisjRightS1 : DisjointS Sown0.right split.S1 := DisjointS_of_append_left hOwnAll
      have hDisjRightS2 : DisjointS Sown0.right split.S2 := DisjointS_of_append_right hOwnAll
      have hOwnInner :
          OwnedDisjoint ({ right := Sown0.right ++ split.S1, left := split.S2 } : OwnedEnv) :=
        DisjointS_append_left hDisjRightS2 hDisjS
      have hSubG1 : SessionsOf splitMid.G1 ⊆ SessionsOf Gmid := by
        intro s hs
        simpa [splitMid, splitMid.hG] using
          (SessionsOf_append_left (G₁:=splitMid.G1) (G₂:=splitMid.G2) hs)
      have hSubG2 : SessionsOf splitMid.G2 ⊆ SessionsOf Gmid := by
        intro s hs
        simpa [splitMid, splitMid.hG] using
          (SessionsOf_append_right (G₁:=splitMid.G1) (G₂:=splitMid.G2) hs)
      have hDisjLeftG1 : DisjointG Gleft splitMid.G1 := by
        have hSym : DisjointG Gmid Gleft := DisjointG_symm hDisjLM
        have hTmp : DisjointG splitMid.G1 Gleft := DisjointG_of_subset_left hSubG1 hSym
        exact DisjointG_symm hTmp
      have hDisjLeftG2 : DisjointG Gleft splitMid.G2 := by
        have hSym : DisjointG Gmid Gleft := DisjointG_symm hDisjLM
        have hTmp : DisjointG splitMid.G2 Gleft := DisjointG_of_subset_left hSubG2 hSym
        exact DisjointG_symm hTmp
      have hDisjG1Right : DisjointG splitMid.G1 Gright := DisjointG_of_subset_left hSubG1 hDisjMR
      have hDisjG2Right : DisjointG splitMid.G2 Gright := DisjointG_of_subset_left hSubG2 hDisjMR
      have hDisjLeftMidInner : DisjointG (Gleft ++ splitMid.G1) splitMid.G2 :=
        DisjointG_append_left hDisjLeftG2 hDisjG_mid
      have hDisjLeftRightInner : DisjointG (Gleft ++ splitMid.G1) Gright :=
        DisjointG_append_left hDisjLR hDisjG1Right
      have hEqInner : G0 = (Gleft ++ splitMid.G1) ++ splitMid.G2 ++ Gright := by
        calc
          G0 = Gleft ++ Gmid ++ Gright := hEqG
          _ = Gleft ++ (splitMid.G1 ++ splitMid.G2) ++ Gright := by
                simpa [splitMid, splitMid.hG]
          _ = (Gleft ++ splitMid.G1) ++ splitMid.G2 ++ Gright := by
                simp [List.append_assoc]
      have hDisjS_right : DisjointS split.S1 S₂_fin := by
        simpa [splitMid, hS1Eq] using hDisjS_right_mid
      have hDisjRightFinAll : DisjointS Sown0.right (S₁_fin ++ S₂_fin) := by
        simpa [hSfin] using hDisjRightFin
      have hDisjRightS2Fin : DisjointS Sown0.right S₂_fin :=
        DisjointS_of_append_right hDisjRightFinAll
      have hDisjOutQ : DisjointS (Sown0.right ++ split.S1) S₂_fin :=
        DisjointS_append_left hDisjRightS2Fin hDisjS_right
      have hQ0 :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ split.S1, left := split.S2 } splitMid.G2 Q0
            { right := Sown0.right ++ split.S1, left := S₂_fin } G₂_fin W₂ Δ₂ := by
        simpa [splitMid, hS1Eq, hS2Eq] using hQ_pre
      obtain ⟨G₂_mid', W₂', Δ₂', hEqShape, hSubSess2, hQ', hSubW2, hSubΔ2⟩ :=
        ih (Gstore:=Gstore) (Gleft:=Gleft ++ splitMid.G1) (Gmid:=splitMid.G2) (Gright:=Gright)
          (Sfin:={ right := Sown0.right ++ split.S1, left := S₂_fin })
          (Gfin:=G₂_fin) (W:=W₂) (Δ:=Δ₂)
          hStoreInner hDisjShInner hOwnInner hDisjLeftMidInner hDisjLeftRightInner hDisjG2Right
          hEqInner hDisjOutQ hQ0
      have hDomStep : SEnvDomSubset S₂_step S₂_fin := by
        simpa using (HasTypeProcPreOut_domsubset hQ')
      have hStepS1 : DisjointS S₂_step split.S1 := by
        have hTmp : DisjointS split.S1 S₂_step :=
          DisjointS_of_domsubset_right hDomStep hDisjS_right
        exact DisjointS_symm hTmp
      have hStepS1fin : DisjointS S₂_step S₁_fin := by
        have hTmp : DisjointS S₁_fin S₂_step :=
          DisjointS_of_domsubset_right hDomStep hDisjS_fin
        exact DisjointS_symm hTmp
      have hDisjRightS1Fin : DisjointS Sown0.right S₁_fin :=
        DisjointS_of_append_left hDisjRightFinAll
      have hDisjInPNew : DisjointS (Sown0.right ++ S₂_step) split.S1 :=
        DisjointS_append_left hDisjRightS1 hStepS1
      have hDisjOutPNew : DisjointS (Sown0.right ++ S₂_step) S₁_fin :=
        DisjointS_append_left hDisjRightS1Fin hStepS1fin
      have hP0 :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ split.S2, left := split.S1 } splitMid.G1 P0
            { right := Sown0.right ++ split.S2, left := S₁_fin } G₁_fin W₁ Δ₁ := by
        simpa [splitMid, hS1Eq, hS2Eq] using hP_pre
      have hP1 :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ S₂_step, left := splitMid.S1 } splitMid.G1 P0
            { right := Sown0.right ++ S₂_step, left := S₁_fin } G₁_fin W₁ Δ₁ := by
        have hTmp :
            HasTypeProcPreOut Ssh0 { right := Sown0.right ++ S₂_step, left := split.S1 } splitMid.G1 P0
              { right := Sown0.right ++ S₂_step, left := S₁_fin } G₁_fin W₁ Δ₁ :=
          HasTypeProcPreOut_reframe_right
            (R:=Sown0.right ++ split.S2) (R':=Sown0.right ++ S₂_step)
            (L:=split.S1) (L':=S₁_fin) (G:=splitMid.G1) (P:=P0)
            hDisjInPNew hDisjOutPNew hP0
        simpa [splitMid, hS1Eq] using hTmp
      have hQ1 :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ splitMid.S1, left := S₂_step } G₂_mid' Q0'
            { right := Sown0.right ++ splitMid.S1, left := S₂_fin } G₂_fin W₂' Δ₂' := by
        simpa [splitMid, hS1Eq] using hQ'
      have hDisjGFinal : DisjointG splitMid.G1 G₂_mid' := by
        have hTmp : DisjointG G₂_mid' splitMid.G1 :=
          DisjointG_of_subset_left hSubSess2 (DisjointG_symm hDisjG_mid)
        exact DisjointG_symm hTmp
      have hStepS1mid : DisjointS splitMid.S1 S₂_step := by
        simpa [splitMid, hS1Eq] using (DisjointS_symm hStepS1)
      have hDisjS1FinStep : DisjointS S₁_fin S₂_step := by
        simpa using (DisjointS_symm hStepS1fin)
      have hDisjW' : DisjointW W₁ W₂' := DisjointW_of_subset_right hSubW2 hDisjW
      have hDisjΔ' : DisjointS Δ₁ Δ₂' := DisjointS_of_domsubset_right hSubΔ2 hDisjΔ
      let splitOut : ParSplit ({ right := Sown0.right, left := splitMid.S1 ++ S₂_step } : OwnedEnv).left
          (splitMid.G1 ++ G₂_mid') :=
        { S1 := splitMid.S1
          S2 := S₂_step
          G1 := splitMid.G1
          G2 := G₂_mid'
          hS := rfl
          hG := rfl }
      have hParMid :
          HasTypeProcPreOut Ssh0 { right := Sown0.right, left := splitMid.S1 ++ S₂_step }
            (splitMid.G1 ++ G₂_mid') (.par splitMid.S1.length nG0 P0 Q0')
            Sfin Gfin (W₁ ++ W₂') (Δ₁ ++ Δ₂') :=
        HasTypeProcPreOut.par splitOut rfl hSfin hGfin rfl rfl
          hDisjGFinal hStepS1mid hDisjS1FinStep hDisjS_right_mid hDisjS_fin hDisjW' hDisjΔ'
          hP1 hQ1
      have hEqGFinal : split.G1 ++ G₂_step = Gleft ++ (splitMid.G1 ++ G₂_mid') ++ Gright := by
        simpa [List.append_assoc] using hEqShape
      have hSubSessFinal : SessionsOf (splitMid.G1 ++ G₂_mid') ⊆ SessionsOf Gmid := by
        intro s hs
        have hs' := SessionsOf_append_subset (G₁:=splitMid.G1) (G₂:=G₂_mid') hs
        cases hs' with
        | inl hsL =>
            simpa [splitMid, splitMid.hG] using
              (SessionsOf_append_left (G₁:=splitMid.G1) (G₂:=splitMid.G2) hsL)
        | inr hsR =>
            have hsMid2 : s ∈ SessionsOf splitMid.G2 := hSubSess2 hsR
            simpa [splitMid, splitMid.hG] using
              (SessionsOf_append_right (G₁:=splitMid.G1) (G₂:=splitMid.G2) hsMid2)
      have hSubWFinal : FootprintSubset (W₁ ++ W₂') W := by
        have hSubW12 : FootprintSubset (W₁ ++ W₂') (W₁ ++ W₂) :=
          FootprintSubset_append_right_of_subset hSubW2
        simpa [hW] using hSubW12
      have hSubΔFinal : SEnvDomSubset (Δ₁ ++ Δ₂') Δ := by
        have hSubΔ12 : SEnvDomSubset (Δ₁ ++ Δ₂') (Δ₁ ++ Δ₂) :=
          SEnvDomSubset_append_right_of_domsubset hSubΔ2
        simpa [hΔ] using hSubΔ12
      refine ⟨splitMid.G1 ++ G₂_mid', W₁ ++ W₂', Δ₁ ++ Δ₂', ?_, hSubSessFinal, ?_, hSubWFinal, hSubΔFinal⟩
      · simpa [hEqGFinal]
      · simpa [splitMid, hS1Eq, List.append_assoc] using hParMid
  | par_skip_left split hSlen hS1Nil =>
      rename_i G0 D0 Ssh0 Sown0 store0 bufs0 Q0 nS0 nG0
      obtain ⟨pw, S₁_fin, S₂_fin, G₁_fin, G₂_fin, W₁, W₂, Δ₁, Δ₂,
          hSfin, hGfin, hW, hΔ, hDisjG_mid, hDisjS_mid, hDisjS_left_mid, hDisjS_right_mid,
          hDisjS_fin, hDisjW, hDisjΔ, hP_pre, hQ_pre⟩ :=
        HasTypeProcPreOut_par_inv_witness hPre
      let splitMid : ParSplit Sown0.left Gmid := pw.split
      have hSlenEq : split.S1.length = splitMid.S1.length := by
        calc
          split.S1.length = nS0 := hSlen
          _ = splitMid.S1.length := by simpa [splitMid] using pw.hSlen.symm
      have hSidesEq := ParSplit.sides_eq_of_len (split₁:=split) (split₂:=splitMid) hSlenEq
      have hS1Eq : split.S1 = splitMid.S1 := hSidesEq.1
      have hS2Eq : split.S2 = splitMid.S2 := hSidesEq.2
      have hS1MidNil : splitMid.S1 = ([] : SEnv) := by
        simpa [hS1Eq] using hS1Nil
      have hSownLeftEq : Sown0.left = splitMid.S2 := by
        have hSownSplit : Sown0.left = splitMid.S1 ++ splitMid.S2 := by
          simpa [splitMid] using splitMid.hS
        simpa [hS1MidNil] using hSownSplit
      cases hP_pre
      simp at hS1MidNil
      have hQ0 :
          HasTypeProcPreOut Ssh0 Sown0 splitMid.G2 Q0
            { right := Sown0.right, left := S₂_fin } G₂_fin W₂ Δ₂ := by
        cases Sown0 with
        | mk R L =>
            simp at hSownLeftEq
            simpa [splitMid, hSownLeftEq, hS1MidNil, List.nil_append] using hQ_pre
      have hDisjRightIn0 : DisjointS Sown0.right Sown0.left := by
        simpa [OwnedDisjoint] using hOwn
      have hDisjRightOut0 : DisjointS Sown0.right S₂_fin := by
        have hTmp : DisjointS Sown0.right (splitMid.S1 ++ S₂_fin) := by
          simpa [hSfin] using hDisjRightFin
        simpa [hS1MidNil] using hTmp
      have hQfull :
          HasTypeProcPreOut Ssh0 Sown0 Gmid Q0
            { right := Sown0.right, left := S₂_fin } (splitMid.G1 ++ G₂_fin) W₂ Δ₂ := by
        have hTmp :=
          HasTypeProcPreOut_frame_G_left_local
            (Ssh:=Ssh0) (Sown:=Sown0) (Gfr:=splitMid.G1) (G:=splitMid.G2)
            (P:=Q0) (Sfin:={ right := Sown0.right, left := S₂_fin }) (Gfin:=G₂_fin)
            (W:=W₂) (Δ:=Δ₂) hDisjG_mid hDisjRightIn0 hQ0 hDisjRightOut0
        simpa [splitMid, splitMid.hG, List.append_assoc] using hTmp
      have hSfinQ : Sfin = { right := Sown0.right, left := S₂_fin } := by
        calc
          Sfin = { right := Sown0.right, left := splitMid.S1 ++ S₂_fin } := by
            simpa [splitMid] using hSfin
          _ = { right := Sown0.right, left := S₂_fin } := by
            simp [hS1MidNil]
      have hGfinQ : Gfin = splitMid.G1 ++ G₂_fin := by
        simpa [splitMid] using hGfin
      have hWQ : W = W₂ := by
        simpa using hW
      have hΔQ : Δ = Δ₂ := by
        simpa using hΔ
      refine ⟨Gmid, W₂, Δ₂, hEqG, ?_, ?_, ?_, ?_⟩
      · intro s hs
        exact hs
      · simpa [hSfinQ, hGfinQ] using hQfull
      · simpa [hWQ] using (FootprintSubset_refl (W:=W₂))
      · simpa [hΔQ] using (SEnvDomSubset_refl (S:=Δ₂))
  | par_skip_right split hSlen hS2Nil =>
      rename_i G0 D0 Ssh0 Sown0 store0 bufs0 P0 nS0 nG0
      obtain ⟨pw, S₁_fin, S₂_fin, G₁_fin, G₂_fin, W₁, W₂, Δ₁, Δ₂,
          hSfin, hGfin, hW, hΔ, hDisjG_mid, hDisjS_mid, hDisjS_left_mid, hDisjS_right_mid,
          hDisjS_fin, hDisjW, hDisjΔ, hP_pre, hQ_pre⟩ :=
        HasTypeProcPreOut_par_inv_witness hPre
      let splitMid : ParSplit Sown0.left Gmid := pw.split
      have hSlenEq : split.S1.length = splitMid.S1.length := by
        calc
          split.S1.length = nS0 := hSlen
          _ = splitMid.S1.length := by simpa [splitMid] using pw.hSlen.symm
      have hSidesEq := ParSplit.sides_eq_of_len (split₁:=split) (split₂:=splitMid) hSlenEq
      have hS1Eq : split.S1 = splitMid.S1 := hSidesEq.1
      have hS2Eq : split.S2 = splitMid.S2 := hSidesEq.2
      have hS2MidNil : splitMid.S2 = ([] : SEnv) := by
        simpa [hS2Eq] using hS2Nil
      have hSownLeftEq : Sown0.left = splitMid.S1 := by
        have hSownSplit : Sown0.left = splitMid.S1 ++ splitMid.S2 := by
          simpa [splitMid] using splitMid.hS
        simpa [hS2MidNil] using hSownSplit
      cases hQ_pre
      simp at hS2MidNil
      have hP0 :
          HasTypeProcPreOut Ssh0 Sown0 splitMid.G1 P0
            { right := Sown0.right, left := S₁_fin } G₁_fin W₁ Δ₁ := by
        cases Sown0 with
        | mk R L =>
            simp at hSownLeftEq
            simpa [splitMid, hSownLeftEq, hS2MidNil, List.append_nil] using hP_pre
      have hPfull :
          HasTypeProcPreOut Ssh0 Sown0 Gmid P0
            { right := Sown0.right, left := S₁_fin } (G₁_fin ++ splitMid.G2) W₁ Δ₁ := by
        have hTmp :=
          HasTypeProcPreOut_frame_G_right_local
            (Ssh:=Ssh0) (Sown:=Sown0) (G:=splitMid.G1) (Gfr:=splitMid.G2)
            (P:=P0) (Sfin:={ right := Sown0.right, left := S₁_fin }) (Gfin:=G₁_fin)
            (W:=W₁) (Δ:=Δ₁) hDisjG_mid hP0
        simpa [splitMid, splitMid.hG, List.append_assoc] using hTmp
      have hSfinP : Sfin = { right := Sown0.right, left := S₁_fin } := by
        calc
          Sfin = { right := Sown0.right, left := S₁_fin ++ splitMid.S2 } := by
            simpa [splitMid] using hSfin
          _ = { right := Sown0.right, left := S₁_fin } := by
            simp [hS2MidNil]
      have hGfinP : Gfin = G₁_fin ++ splitMid.G2 := by
        simpa [splitMid] using hGfin
      have hWP : W = W₁ := by
        simpa using hW
      have hΔP : Δ = Δ₁ := by
        simpa using hΔ
      refine ⟨Gmid, W₁, Δ₁, hEqG, ?_, ?_, ?_, ?_⟩
      · intro s hs
        exact hs
      · simpa [hSfinP, hGfinP] using hPfull
      · simpa [hWP] using (FootprintSubset_refl (W:=W₁))
      · simpa [hΔP] using (SEnvDomSubset_refl (S:=Δ₁))

theorem SessionsOf_subset_of_TypedStep_left_frame
    {G₁ G₂ G G' D Ssh Sown store bufs P G₁' D' Sown' store' bufs' P'} :
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G' = G₁' ++ G₂ →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    SessionsOf G₁' ⊆ SessionsOf G₁ := by
  intro hDisj hEq hEq' hTS
  induction hTS with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      have hLookup : lookupG (G₁ ++ G₂) e = some (.send target T L) := by
        simpa [hEq] using hG
      have hUpd : updateG (G₁ ++ G₂) e L = G₁' ++ G₂ := by
        simpa [hEq, hEq'] using hGout.symm
      exact SessionsOf_left_subset_of_update hLookup hUpd
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      have hLookup : lookupG (G₁ ++ G₂) e = some (.recv source T L) := by
        simpa [hEq] using hG
      have hUpd : updateG (G₁ ++ G₂) e L = G₁' ++ G₂ := by
        simpa [hEq, hEq'] using hGout.symm
      exact SessionsOf_left_subset_of_update hLookup hUpd
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      have hLookup : lookupG (G₁ ++ G₂) e = some (.select target bs) := by
        simpa [hEq] using hG
      have hUpd : updateG (G₁ ++ G₂) e L = G₁' ++ G₂ := by
        simpa [hEq, hEq'] using hGout.symm
      exact SessionsOf_left_subset_of_update hLookup hUpd
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      have hLookup : lookupG (G₁ ++ G₂) e = some (.branch source bs) := by
        simpa [hEq] using hG
      have hUpd : updateG (G₁ ++ G₂) e L = G₁' ++ G₂ := by
        simpa [hEq, hEq'] using hGout.symm
      exact SessionsOf_left_subset_of_update hLookup hUpd
  | assign =>
      intro s hs
      have hEqG : G₁' ++ G₂ = G₁ ++ G₂ :=
        hEq'.symm.trans hEq
      have hG₁' : G₁' = G₁ := append_left_eq_of_eq hEqG
      simpa [hG₁'] using hs
  | seq_step _ ih =>
      exact ih hEq hEq'
  | seq_skip =>
      intro s hs
      have hEqG : G₁' ++ G₂ = G₁ ++ G₂ :=
        hEq'.symm.trans hEq
      have hG₁' : G₁' = G₁ := append_left_eq_of_eq hEqG
      simpa [hG₁'] using hs
  | par_left split hSlen hTS hDisjG hDisjD hDisjS ih =>
      -- Right frame unchanged; reuse IH on the inner step.
      exact ih hEq hEq'
  | par_right split hSlen hTS hDisjG hDisjD hDisjS ih =>
      exact ih hEq hEq'
  | par_skip_left =>
      intro s hs
      have hEqG : G₁' ++ G₂ = G₁ ++ G₂ :=
        hEq'.symm.trans hEq
      have hG₁' : G₁' = G₁ := append_left_eq_of_eq hEqG
      simpa [hG₁'] using hs
  | par_skip_right =>
      intro s hs
      have hEqG : G₁' ++ G₂ = G₁ ++ G₂ :=
        hEq'.symm.trans hEq
      have hG₁' : G₁' = G₁ := append_left_eq_of_eq hEqG
      simpa [hG₁'] using hs

theorem SessionsOf_subset_of_TypedStep_right_frame
    {G₁ G₂ G G' D Ssh Sown store bufs P G₂' D' Sown' store' bufs' P'} :
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G' = G₁ ++ G₂' →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    SessionsOf G₂' ⊆ SessionsOf G₂ := by
  intro hDisj hEq hEq' hTS
  induction hTS with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      have hLookup : lookupG (G₁ ++ G₂) e = some (.send target T L) := by
        simpa [hEq] using hG
      have hUpd : updateG (G₁ ++ G₂) e L = G₁ ++ G₂' := by
        simpa [hEq, hEq'] using hGout.symm
      exact SessionsOf_right_subset_of_update hLookup hUpd
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      have hLookup : lookupG (G₁ ++ G₂) e = some (.recv source T L) := by
        simpa [hEq] using hG
      have hUpd : updateG (G₁ ++ G₂) e L = G₁ ++ G₂' := by
        simpa [hEq, hEq'] using hGout.symm
      exact SessionsOf_right_subset_of_update hLookup hUpd
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      have hLookup : lookupG (G₁ ++ G₂) e = some (.select target bs) := by
        simpa [hEq] using hG
      have hUpd : updateG (G₁ ++ G₂) e L = G₁ ++ G₂' := by
        simpa [hEq, hEq'] using hGout.symm
      exact SessionsOf_right_subset_of_update hLookup hUpd
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      have hLookup : lookupG (G₁ ++ G₂) e = some (.branch source bs) := by
        simpa [hEq] using hG
      have hUpd : updateG (G₁ ++ G₂) e L = G₁ ++ G₂' := by
        simpa [hEq, hEq'] using hGout.symm
      exact SessionsOf_right_subset_of_update hLookup hUpd
  | assign =>
      intro s hs
      have hEqG : G₁ ++ G₂' = G₁ ++ G₂ :=
        hEq'.symm.trans hEq
      have hG₂' : G₂' = G₂ := append_right_eq_of_eq hEqG
      simpa [hG₂'] using hs
  | seq_step _ ih =>
      exact ih hEq hEq'
  | seq_skip =>
      intro s hs
      have hEqG : G₁ ++ G₂' = G₁ ++ G₂ :=
        hEq'.symm.trans hEq
      have hG₂' : G₂' = G₂ := append_right_eq_of_eq hEqG
      simpa [hG₂'] using hs
  | par_left split hSlen hTS hDisjG hDisjD hDisjS ih =>
      exact ih hEq hEq'
  | par_right split hSlen hTS hDisjG hDisjD hDisjS ih =>
      exact ih hEq hEq'
  | par_skip_left =>
      intro s hs
      have hEqG : G₁ ++ G₂' = G₁ ++ G₂ :=
        hEq'.symm.trans hEq
      have hG₂' : G₂' = G₂ := append_right_eq_of_eq hEqG
      simpa [hG₂'] using hs
  | par_skip_right =>
      intro s hs
      have hEqG : G₁ ++ G₂' = G₁ ++ G₂ :=
        hEq'.symm.trans hEq
      have hG₂' : G₂' = G₂ := append_right_eq_of_eq hEqG
      simpa [hG₂'] using hs


end
