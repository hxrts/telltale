import Protocol.Environments.Core
import Protocol.Typing.StepLemmas
import Protocol.Typing.MergeLemmas
import Protocol.Typing.Framing.Lemmas

/-
The Problem. Show that pre-typing is stable under framing a disjoint GEnv on the
right, so we can extend a global environment without re-typing processes.

Solution Structure. Prove each constructor case directly and re-use the branch
body lemma for the only non-trivial recursive step.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Pre Framing (Right) -/

/-- Helper: extend branch bodies under a right frame. -/
private lemma pre_frame_right_branch_bodies
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
  -- Reframe each branch body by rewriting the update across the right frame.
  intro hG ihBodies i hi hip
  have hBody' := ihBodies i hi hip
  have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
    (L:=.branch p bs) (L':=(bs.get ⟨i, hi⟩).2) hG
  rw [hUpd]
  exact hBody'

/-! ## Pre Framing (Right): Main Theorem -/

/-- Frame a disjoint GEnv on the right of pre-typing. -/
lemma HasTypeProcPre_frame_G_right
    {Ssh : SEnv} {Sown : OwnedEnv} {G Gfr : GEnv} {P : Process} :
    HasTypeProcPre Ssh Sown G P →
    HasTypeProcPre Ssh Sown (G ++ Gfr) P := by
  -- Dispatch by constructor, extending lookups across the right frame.
  intro h
  induction h with
  | skip =>
      rename_i Sown G
      simpa using (HasTypeProcPre.skip (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr))
  | send hk hG hx =>
      rename_i Sown G k x e q T L
      have hG' := lookupG_append_left (G₂:=Gfr) hG
      exact HasTypeProcPre.send hk hG' hx
  | recv hk hG hNoSh =>
      rename_i Sown G k x e p T L
      have hG' := lookupG_append_left (G₂:=Gfr) hG
      exact HasTypeProcPre.recv hk hG' hNoSh
  | select hk hG hbs =>
      rename_i Sown G k l e q bs L
      have hG' := lookupG_append_left (G₂:=Gfr) hG
      exact HasTypeProcPre.select hk hG' hbs
  | branch hk hG hLen hLabels hBodies ihBodies =>
      rename_i Sown G k procs e p bs
      have hG' := lookupG_append_left (G₂:=Gfr) hG
      have hBodies' := pre_frame_right_branch_bodies (G:=G) (Gfr:=Gfr) hG ihBodies
      exact HasTypeProcPre.branch hk hG' hLen hLabels hBodies'
  | seq hP hQ ihP ihQ =>
      exact HasTypeProcPre.seq ihP ihQ
  | par hDisjS hSsplit hP hQ ihP ihQ =>
      exact HasTypeProcPre.par hDisjS hSsplit ihP ihQ
  | assign hNoSh hv =>
      rename_i Sown G x v T
      have hv' := HasTypeVal_frame_right (G₁:=G) (G₂:=Gfr) hv
      exact HasTypeProcPre.assign hNoSh hv'
