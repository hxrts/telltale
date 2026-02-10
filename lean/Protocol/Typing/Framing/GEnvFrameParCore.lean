import Protocol.Typing.Framing.Lemmas

/-! # Protocol.Typing.Framing.GEnvFrameParCore

Shared helper for par-index irrelevance after framing.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

section

/-- Shared core: par typing is independent of the ambient `nG` index once the
framed typing judgment is established. -/
lemma frame_par_nG_irrel_core
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {P Q : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv}
    {nS nG nG' : Nat} :
    HasTypeProcPreOut Ssh Sown G (.par nS nG P Q) Sfin Gfin W Δ →
    HasTypeProcPreOut Ssh Sown G (.par nS nG' P Q) Sfin Gfin W Δ := by
  intro hPar
  exact HasTypeProcPreOut_par_nG_irrel hPar

end

