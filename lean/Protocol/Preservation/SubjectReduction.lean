import Protocol.Preservation.FrameLeft
set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical
open Batteries

section
theorem subject_reduction {n : SessionId}
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    Step
      { proc := P, store := store, bufs := bufs, G := G, D := D, nextSid := n }
      { proc := P', store := store', bufs := bufs', G := G', D := D', nextSid := n } := by
  intro hTS
  induction hTS with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      -- Rewrite to match sendStep.
      subst hEdge hGout hDout hBufsOut
      let C : Config :=
        { proc := .send k x, store := store, bufs := bufs, G := G, D := D, nextSid := n }
      have hStep : StepBase C (sendStep C e { sid := e.sid, sender := e.role, receiver := target } v T L) :=
        StepBase.send rfl hk hx hG
      simpa [C] using (Step.base hStep)
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      subst hEdge hGout hDout hSout hStoreOut hBufsOut
      let C : Config :=
        { proc := .recv k x, store := store, bufs := bufs, G := G, D := D, nextSid := n }
      have hStep : StepBase C (recvStep C e { sid := e.sid, sender := source, receiver := e.role } x v L) :=
        StepBase.recv rfl hk hG hBuf
      simpa [C, recvStep, dequeueBuf, hBuf] using (Step.base hStep)
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      subst hEdge hGout hDout hBufsOut
      let C : Config :=
        { proc := .select k ℓ, store := store, bufs := bufs, G := G, D := D, nextSid := n }
      have hStep : StepBase C (sendStep C e { sid := e.sid, sender := e.role, receiver := target } (.string ℓ) .string L) :=
        StepBase.select rfl hk hG hFind
      simpa [C] using (Step.base hStep)
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      subst hEdge hGout hDout hBufsOut
      -- StepBase.branch uses dequeueBuf; use the existence of a head to rewrite.
      -- The dequeueBuf in StepBase.branch is discharged by the definition in Semantics.
      have hDeq : dequeueBuf bufs { sid := e.sid, sender := source, receiver := e.role } = some (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs, .string ℓ) := by
        -- unfold dequeueBuf with the known head.
        simp [dequeueBuf, hBuf]
      let C : Config :=
        { proc := .branch k procs, store := store, bufs := bufs, G := G, D := D, nextSid := n }
      have hStep : StepBase C
          { C with proc := P,
                   bufs := updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs,
                   G := updateG G e L,
                   D := updateD D { sid := e.sid, sender := source, receiver := e.role } (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail } :=
        StepBase.branch rfl hk hG hBuf hFindP hFindT hDeq
      simpa [C] using (Step.base hStep)
  | assign hv hS hStore =>
      rename_i G D Ssh Sown store bufs x v T S' store'
      refine Step.base ?_
      subst hS hStore
      exact StepBase.assign rfl
  | seq_step hStep ih =>
      rename_i G D Ssh Sown G' D' Sown' store bufs store' bufs' P P' Q
      let C : Config :=
        { proc := .seq P Q, store := store, bufs := bufs, G := G, D := D, nextSid := n }
      let C' : Config :=
        { proc := P', store := store', bufs := bufs', G := G', D := D', nextSid := n }
      have hSub : Step { C with proc := P } C' := by
        simpa [C, C'] using ih
      have hProc : C.proc = .seq P Q := rfl
      simpa [C, C'] using (Step.seq_left hProc hSub)
  | seq_skip =>
      refine Step.base ?_
      exact StepBase.seq2 rfl
  | par_left split hSlen hStep hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P P' Q G D₁ D₂ G₁' D₁' S₁' nS nG
      let C0 : Config :=
        { proc := P, store := store, bufs := bufs, G := G, D := D₁ ++ D₂, nextSid := n }
      let C0' : Config :=
        { proc := P', store := store', bufs := bufs', G := G₁' ++ split.G2, D := D₁' ++ D₂, nextSid := n }
      have hSub : Step C0 C0' := by
        simpa [C0, C0'] using ih
      let C : Config :=
        { proc := .par nS nG P Q, store := store, bufs := bufs, G := G, D := D₁ ++ D₂, nextSid := n }
      have hSub' : Step { C with proc := P } C0' := by
        simpa [C, C0] using hSub
      have hProc : C.proc = .par nS nG P Q := rfl
      simpa [C, C0'] using
        (Step.par_left (nS':=S₁'.length) (nG':=nG) hProc hSub')
  | par_right split hSlen hStep hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P Q Q' G D₁ D₂ G₂' D₂' S₂' nS nG
      let C0 : Config :=
        { proc := Q, store := store, bufs := bufs, G := G, D := D₁ ++ D₂, nextSid := n }
      let C0' : Config :=
        { proc := Q', store := store', bufs := bufs', G := split.G1 ++ G₂', D := D₁ ++ D₂', nextSid := n }
      have hSub : Step C0 C0' := by
        simpa [C0, C0'] using ih
      let C : Config :=
        { proc := .par nS nG P Q, store := store, bufs := bufs, G := G, D := D₁ ++ D₂, nextSid := n }
      have hSub' : Step { C with proc := Q } C0' := by
        simpa [C, C0] using hSub
      have hProc : C.proc = .par nS nG P Q := rfl
      simpa [C, C0'] using
        (Step.par_right (nS':=split.S1.length) (nG':=nG) hProc hSub')
  | par_skip_left =>
      refine Step.base ?_
      exact StepBase.par_skip_left rfl
  | par_skip_right =>
      refine Step.base ?_

end
