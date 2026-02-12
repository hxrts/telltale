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

/-! ## SEnv Lookup Framing -/

theorem lookupSEnv_all_frame_prefix_ofLeft
    {Ssh S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    DisjointS S₁ S₂ →
    lookupSEnv (SEnvAll Ssh (S₂ : OwnedEnv)) x = some T →
    lookupSEnv (SEnvAll Ssh { right := S₁, left := S₂ }) x = some T := by
  intro hDisj hLookup
  have hLookup' : lookupSEnv (Ssh ++ S₂) x = some T := by
    simpa [SEnvAll_ofLeft] using hLookup
  have hFrame := lookupSEnv_all_frame_left (Ssh:=Ssh) (S₁:=S₁) (S₂:=S₂) hDisj hLookup'
  simpa [SEnvAll, List.append_assoc] using hFrame

theorem lookupSEnv_all_frame_left_owned
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

theorem lookupSEnv_all_frame_right_owned
    {Ssh : SEnv} {Sown : OwnedEnv} {Sframe : SEnv} {x : Var} {T : ValType} :
    lookupSEnv (SEnvAll Ssh Sown) x = some T →
    lookupSEnv (SEnvAll Ssh { right := Sown.right, left := Sown.left ++ Sframe }) x = some T := by
  intro hLookup
  have hLookup' : lookupSEnv (Ssh ++ (Sown.right ++ Sown.left)) x = some T := by
    simpa [SEnvAll] using hLookup
  have hLeft :=
    lookupSEnv_append_left (S₁:=Ssh ++ (Sown.right ++ Sown.left)) (S₂:=Sframe) (x:=x) (T:=T) hLookup'
  simpa [SEnvAll, List.append_assoc] using hLeft

theorem lookupSEnv_all_frame_right_prefix
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

lemma lookupSEnv_comm_of_disjoint {S₁ S₂ : SEnv} (hDisj : DisjointS S₁ S₂) :
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

lemma lookupSEnv_swap_left {S₁ S₂ S₃ : SEnv} (hDisj : DisjointS S₁ S₂) :
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

end
