import Protocol.Environments.Core
import Protocol.Typing.Framing.Lemmas


/-! # Protocol.Typing.Framing.SideCasesCore

Shared side-parameterized cores for mirrored left/right framing case lemmas.

These lemmas factor out identical post-processing patterns (skip continuations,
branch continuation passthrough, and assign update alignment) so side-specific
files only need to discharge side-dependent lookup/update equalities.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

/-- Common post-state constructor for step cases that end in `skip` after
updating a single endpoint in the framed global environment. -/
lemma preserved_sub_frame_skip_after_update
    {Ssh : SEnv} {Sown : OwnedEnv} {G G' : GEnv} {e : Endpoint} {L : LocalType}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    G' = updateG G e L →
    Sfin = Sown →
    Gfin = updateG G e L →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown G' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hG' hSfin hGfin
  refine ⟨[], ∅, ?_, ?_, ?_⟩
  · simpa [hSfin, hGfin, hG'] using
      (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sfin) (G:=Gfin))
  · intro x hx; cases hx
  · intro x T hx; cases hx

/-- Common post-state constructor for branch cases where the selected branch
continuation is already typed in the updated framed environment. -/
lemma preserved_sub_frame_branch_cont
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {P : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown G P Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro h
  exact ⟨W, Δ, h, FootprintSubset_refl, SEnvDomSubset_refl⟩

/-- Shared assign-case core for left-framed environments (`G = Gbase ++ Gframe`). -/
lemma preserved_sub_frame_assign_left_core
    {Ssh : SEnv} {Sown Sown' : OwnedEnv}
    {Gbase Gframe G Gbase' : GEnv}
    {x : Var} {v : Value} {Tstep Tpre : ValType}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    G = Gbase ++ Gframe →
    G = Gbase' ++ Gframe →
    HasTypeVal G v Tstep →
    HasTypeVal G v Tpre →
    Sown' = OwnedEnv.updateLeft Sown x Tstep →
    Sfin = OwnedEnv.updateLeft Sown x Tpre →
    Gfin = Gbase →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' Gbase' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hEq hEq' hv hvPre hSout hSfin hGfin
  have hT := HasTypeVal_unique hvPre hv
  cases hT
  have hEqG : Gbase' ++ Gframe = Gbase ++ Gframe := by
    have hEq0 : Gbase' ++ Gframe = G := by simpa using hEq'.symm
    simpa [hEq] using hEq0
  have hBase' : Gbase' = Gbase := append_left_eq_of_eq hEqG
  refine ⟨[], ∅, ?_, ?_, ?_⟩
  · subst hSout
    simpa [hBase', hSfin, hGfin] using
      (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown.updateLeft x Tstep) (G:=Gbase))
  · intro y hy; cases hy
  · intro y Ty hy; cases hy

/-- Shared assign-case core for right-framed environments (`G = Gframe ++ Gbase`). -/
lemma preserved_sub_frame_assign_right_core
    {Ssh : SEnv} {Sown Sown' : OwnedEnv}
    {Gframe Gbase G Gbase' : GEnv}
    {x : Var} {v : Value} {Tstep Tpre : ValType}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    G = Gframe ++ Gbase →
    G = Gframe ++ Gbase' →
    HasTypeVal G v Tstep →
    HasTypeVal G v Tpre →
    Sown' = OwnedEnv.updateLeft Sown x Tstep →
    Sfin = OwnedEnv.updateLeft Sown x Tpre →
    Gfin = Gbase →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' Gbase' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hEq hEq' hv hvPre hSout hSfin hGfin
  have hT := HasTypeVal_unique hvPre hv
  cases hT
  have hEqG : Gframe ++ Gbase' = Gframe ++ Gbase := by
    have hEq0 : Gframe ++ Gbase' = G := by simpa using hEq'.symm
    simpa [hEq] using hEq0
  have hBase' : Gbase' = Gbase := append_right_eq_of_eq hEqG
  refine ⟨[], ∅, ?_, ?_, ?_⟩
  · subst hSout
    simpa [hBase', hSfin, hGfin] using
      (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown.updateLeft x Tstep) (G:=Gbase))
  · intro y hy; cases hy
  · intro y Ty hy; cases hy

end
