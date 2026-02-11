import Protocol.Preservation.PreservationProgressWrappers

/-! # Progress Lemmas

Progress theorems for individual process forms (send, recv, select,
branch), showing well-typed processes can always step unless blocked
on an empty buffer. -/

/-
The Problem. Type safety requires progress: well-typed configurations
either step or are in a recognized blocked state. We need per-constructor
progress lemmas for send, recv, select, and branch.

Solution Structure. Define `BlockedRecv` predicate for the blocked-recv
case. Prove `progress_send`, `progress_recv`, `progress_select`,
`progress_branch` showing typed processes step or are blocked.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical
open Batteries

section

/-! ## Progress Lemmas for Individual Process Forms

These lemmas are currently axiomatized to keep the development building while
TypedStep-based proofs are refactored.
-/

/-- Blocked recv predicate: recv/branch is waiting on an empty buffer. -/
def BlockedRecv (C : Config) : Prop :=
  (∃ k x source T L, ∃ e : Endpoint,
    C.proc = .recv k x ∧
    lookupStr C.store k = some (.chan e) ∧
    lookupG C.G e = some (.recv source T L) ∧
    lookupBuf C.bufs ⟨e.sid, source, e.role⟩ = []) ∨
  (∃ k procs source bs, ∃ e : Endpoint,
    C.proc = .branch k procs ∧
    lookupStr C.store k = some (.chan e) ∧
    lookupG C.G e = some (.branch source bs) ∧
    lookupBuf C.bufs ⟨e.sid, source, e.role⟩ = [])

/-- Progress for send: send always steps (it just enqueues to buffer). -/
theorem progress_send {C : Config} {Ssh Sown : SEnv} {k x : Var}
    (hEq : C.proc = .send k x)
    (hProc : HasTypeProcPre Ssh Sown C.G (.send k x))
    (hStore : StoreTypedStrong C.G (SEnvAll Ssh Sown) C.store) :
    ∃ C', Step C C' := by
  rcases inversion_send hProc with ⟨e, q, T, L, hk, hG, hx⟩
  have hkAll : lookupSEnv (SEnvAll Ssh (Sown : OwnedEnv)) k = some (.chan e.sid e.role) := by
    simpa [SEnvVisible_ofLeft] using hk
  obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hkAll
  have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
  subst hkChan
  have hxAll : lookupSEnv (SEnvAll Ssh (Sown : OwnedEnv)) x = some T := by
    simpa [SEnvVisible_ofLeft] using hx
  obtain ⟨v, hxStr, _hv⟩ := store_lookup_of_senv_lookup hStore hxAll
  let sendEdge : Edge := { sid := e.sid, sender := e.role, receiver := q }
  refine ⟨sendStep C e sendEdge v T L, Step.base ?_⟩
  exact StepBase.send hEq hkStr hxStr hG

/-- Progress for recv: recv steps if buffer non-empty, otherwise blocked. -/
theorem progress_recv {C : Config} {Ssh Sown : SEnv} {k x : Var}
    (hEq : C.proc = .recv k x)
    (hProc : HasTypeProcPre Ssh Sown C.G (.recv k x))
    (hStore : StoreTypedStrong C.G (SEnvAll Ssh Sown) C.store) :
    (∃ C', Step C C') ∨ BlockedRecv C := by
  rcases inversion_recv hProc with ⟨e, p, T, L, hk, hG, _hNoSh⟩
  have hkAll : lookupSEnv (SEnvAll Ssh (Sown : OwnedEnv)) k = some (.chan e.sid e.role) := by
    simpa [SEnvVisible_ofLeft] using hk
  obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hkAll
  have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
  subst hkChan
  set recvEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
  cases hBuf : lookupBuf C.bufs recvEdge with
  | nil =>
      right
      left
      refine ⟨k, x, p, T, L, e, ?_⟩
      refine ⟨hEq, hkStr, hG, ?_⟩
      simpa [recvEdge] using hBuf
  | cons v vs =>
      left
      refine ⟨recvStep C e recvEdge x v L, Step.base ?_⟩
      have hBuf' : lookupBuf C.bufs { sid := e.sid, sender := p, receiver := e.role } = v :: vs := by
        simpa [recvEdge] using hBuf
      exact StepBase.recv hEq hkStr hG hBuf'

/-- Progress for select: select always steps (it just enqueues label to buffer). -/
theorem progress_select {C : Config} {Ssh Sown : SEnv} {k : Var} {l : Label}
    (hEq : C.proc = .select k l)
    (hProc : HasTypeProcPre Ssh Sown C.G (.select k l))
    (hStore : StoreTypedStrong C.G (SEnvAll Ssh Sown) C.store) :
    ∃ C', Step C C' := by
  rcases inversion_select hProc with ⟨e, q, bs, L, hk, hG, hFind⟩
  have hkAll : lookupSEnv (SEnvAll Ssh (Sown : OwnedEnv)) k = some (.chan e.sid e.role) := by
    simpa [SEnvVisible_ofLeft] using hk
  obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hkAll
  have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
  subst hkChan
  let selectEdge : Edge := { sid := e.sid, sender := e.role, receiver := q }
  refine ⟨sendStep C e selectEdge (.string l) .string L, Step.base ?_⟩
  exact StepBase.select hEq hkStr hG hFind

/-- Progress for branch: branch steps if buffer non-empty, otherwise blocked. -/
theorem progress_branch {C : Config} {Ssh Sown : SEnv} {k : Var} {procs : List (Label × Process)}
    (hEq : C.proc = .branch k procs)
    (hProc : HasTypeProcPre Ssh Sown C.G (.branch k procs))
    (hStore : StoreTypedStrong C.G (SEnvAll Ssh Sown) C.store)
    (hBufs : BuffersTyped C.G C.D C.bufs)
    (hHead : HeadCoherent C.G C.D)
    (hValid : ValidLabels C.G C.D C.bufs)
    (hComplete : RoleComplete C.G) :
    (∃ C', Step C C') ∨ BlockedRecv C := by
  rcases inversion_branch hProc with ⟨e, p, bs, hk, hG, hLen, hLabels, hBodies⟩
  have hkAll : lookupSEnv (SEnvAll Ssh (Sown : OwnedEnv)) k = some (.chan e.sid e.role) := by
    simpa [SEnvVisible_ofLeft] using hk
  obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hkAll
  have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
  subst hkChan
  set branchEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
  have hActiveBranch : ActiveEdge C.G branchEdge := by
    have hGrecv :
        lookupG C.G { sid := branchEdge.sid, role := branchEdge.receiver } = some (.branch p bs) := by
      simpa [branchEdge] using hG
    rcases RoleComplete_branch hComplete hG with ⟨Lsender, hGsender⟩
    exact ActiveEdge_of_endpoints (e:=branchEdge) hGsender hGrecv
  cases hBuf : lookupBuf C.bufs branchEdge with
  | nil =>
      right
      right
      refine ⟨k, procs, p, bs, e, ?_⟩
      refine ⟨hEq, hkStr, hG, ?_⟩
      simpa [branchEdge] using hBuf
  | cons v vs =>
      left
      have hTypedEdge := hBufs branchEdge
      rcases hTypedEdge with ⟨hLenBuf, hTyping⟩
      have h0buf : 0 < (lookupBuf C.bufs branchEdge).length := by
        simp [hBuf]
      have h0trace : 0 < (lookupD C.D branchEdge).length := by
        simpa [hLenBuf] using h0buf
      have hTyped0 := hTyping 0 h0buf
      have hv' : HasTypeVal C.G v ((lookupD C.D branchEdge).get ⟨0, h0trace⟩) := by
        simpa [hBuf, hLenBuf] using hTyped0
      cases hTrace : lookupD C.D branchEdge with
      | nil =>
          simp [hTrace] at h0trace
      | cons T' ts =>
          have hHeadEdge := hHead branchEdge hActiveBranch
          have hEqT : T' = .string := by
            simpa [HeadCoherent, hG, branchEdge, hTrace] using hHeadEdge
          have hv : HasTypeVal C.G v .string := by
            simpa [hTrace, hEqT] using hv'
          rcases HasTypeVal_string_inv hv with ⟨lbl, rfl⟩
          have hValidEdge := hValid branchEdge p bs hActiveBranch
            (by simpa [branchEdge] using hG)
          have hBsSome : (bs.find? (fun b => b.1 == lbl)).isSome := by
            simpa [hBuf] using hValidEdge
          rcases (Option.isSome_iff_exists).1 hBsSome with ⟨b, hFindBs⟩
          cases b with
          | mk lbl' L =>
              have hLbl : lbl' = lbl :=
                findLabel_eq (xs := bs) (lbl := lbl) (lbl' := lbl') (v := L) hFindBs
              have hFindBs' : bs.find? (fun b => b.1 == lbl') = some (lbl', L) := by
                simpa [hLbl] using hFindBs
              have hMemBs : (lbl', L) ∈ bs := List.mem_of_find?_eq_some hFindBs'
              rcases (List.mem_iff_getElem).1 hMemBs with ⟨i, hi, hGetBs⟩
              have hip : i < procs.length := by
                simpa [hLen] using hi
              have hLabelAt : (procs.get ⟨i, hip⟩).1 = lbl' := by
                have hLblEq := hLabels i hi hip
                simpa [hGetBs] using hLblEq
              have hPred : (fun b => b.1 == lbl') (procs.get ⟨i, hip⟩) := by
                exact (beq_iff_eq).2 hLabelAt
              have hFindPIsSome : (procs.find? (fun b => b.1 == lbl')).isSome := by
                cases hFindP : procs.find? (fun b => b.1 == lbl') with
                | none =>
                    have hNo : ∀ x ∈ procs, ¬ (fun b => b.1 == lbl') x := by
                      simpa [List.find?_eq_none] using hFindP
                    have hMemP : procs.get ⟨i, hip⟩ ∈ procs := List.get_mem procs ⟨i, hip⟩
                    have hContra : False := (hNo _ hMemP) hPred
                    exact (False.elim hContra)
                | some _ =>
                    simp
              rcases (Option.isSome_iff_exists).1 hFindPIsSome with ⟨bP, hFindP⟩
              cases bP with
              | mk lblP P =>
                  have hLblP : lblP = lbl' :=
                    findLabel_eq (xs := procs) (lbl := lbl') (lbl' := lblP) (v := P) hFindP
                  have hLblP' : lblP = lbl := hLblP.trans hLbl
                  have hFindP' : procs.find? (fun b => b.1 == lbl) = some (lbl, P) := by
                    simpa [hLbl, hLblP'] using hFindP
                  have hDeq :
                      dequeueBuf C.bufs branchEdge =
                        some (updateBuf C.bufs branchEdge vs, .string lbl) := by
                    simp [dequeueBuf, hBuf]
                  have hFindBs'' : bs.find? (fun b => b.1 == lbl) = some (lbl, L) := by
                    simpa [hLbl] using hFindBs
                  refine ⟨{ C with
                              proc := P,
                              bufs := updateBuf C.bufs branchEdge vs,
                              G := updateG C.G e L,
                              D := updateD C.D branchEdge (lookupD C.D branchEdge).tail },
                          Step.base ?_⟩
                  exact StepBase.branch hEq hkStr hG hBuf hFindP' hFindBs'' hDeq


end
