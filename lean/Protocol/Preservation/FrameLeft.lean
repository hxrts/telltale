import Protocol.Preservation.FrameRight

/-! # Left Frame Preservation

Proves that execution steps are preserved under left-framing: adding
a disjoint environment fragment on the left of a configuration. -/

/-
The Problem. Frame lemmas allow compositional reasoning about protocol
configurations by showing steps in a sub-configuration lift to framed
configurations. Left-framing adds `Gfr ++ G` and `Dfr ++ D` where the
frame is on the left.

Solution Structure. Prove `step_frame_left` by induction on `Step`.
For each base step (send, recv, select, branch), show the frame is
untouched by update operations and lookup results are preserved.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical
open Batteries

section

/-! ## Left Frame Lemma -/

lemma step_frame_left {C C' : Config} {Gfr : GEnv} {Dfr : DEnv} :
    DisjointG Gfr C.G →
    DConsistent Gfr Dfr →
    Step C C' →
    Step (frameConfigLeft C Gfr Dfr) (frameConfigLeft C' Gfr Dfr) := by
  intro hDisj hCons hStep
  induction hStep with
  | base hBase =>
      cases hBase with
      | send hProc hk hx hG =>
          rename_i Ccfg k x e v target T L
          set sendEdge : Edge := { sid := e.sid, sender := e.role, receiver := target }
          have hSid : e.sid ∈ SessionsOf Ccfg.G := ⟨e, .send target T L, hG, rfl⟩
          have hDfrNone : Dfr.find? sendEdge = none :=
            lookupD_none_of_disjointG (G₁:=Ccfg.G) (G₂:=Gfr) (D₂:=Dfr) (DisjointG_symm hDisj) hCons hSid
          have hLookupD :
              lookupD (Dfr ++ Ccfg.D) sendEdge = lookupD Ccfg.D sendEdge :=
            lookupD_append_right (D₁:=Dfr) (D₂:=Ccfg.D) (e:=sendEdge) hDfrNone
          have hGfrNone : lookupG Gfr e = none :=
            lookupG_none_of_disjoint (G₁:=Gfr) (G₂:=Ccfg.G) hDisj (e:=e) (L:=.send target T L) hG
          have hLookupG :
              lookupG (Gfr ++ Ccfg.G) e = some (.send target T L) := by
            simpa [lookupG_append_right (G₁:=Gfr) (G₂:=Ccfg.G) (e:=e) hGfrNone] using hG
          have hUpdG : updateG (Gfr ++ Ccfg.G) e L = Gfr ++ updateG Ccfg.G e L :=
            updateG_append_right_hit hGfrNone
          have hUpdD :
              updateD (Dfr ++ Ccfg.D) sendEdge (lookupD Ccfg.D sendEdge ++ [T]) =
                Dfr ++ updateD Ccfg.D sendEdge (lookupD Ccfg.D sendEdge ++ [T]) := by
            exact updateD_append_right (D₁:=Dfr) (D:=Ccfg.D) (e:=sendEdge)
              (ts:=lookupD Ccfg.D sendEdge ++ [T]) hDfrNone
          have hStep' :
              StepBase (frameConfigLeft Ccfg Gfr Dfr)
                (sendStep (frameConfigLeft Ccfg Gfr Dfr) e sendEdge v T L) := by
            refine StepBase.send (C:=frameConfigLeft Ccfg Gfr Dfr) (k:=k) (x:=x) (e:=e)
              (v:=v) (target:=target) (T:=T) (L:=L) ?_ ?_ ?_ ?_
            · simpa [frameConfigLeft] using hProc
            · simpa [frameConfigLeft] using hk
            · simpa [frameConfigLeft] using hx
            · exact hLookupG
          have hEq :
              sendStep (frameConfigLeft Ccfg Gfr Dfr) e sendEdge v T L =
                frameConfigLeft (sendStep Ccfg e sendEdge v T L) Gfr Dfr := by
            simp [frameConfigLeft, sendStep, hUpdG, hUpdD, hLookupD]
          simpa [hEq] using (Step.base hStep')
      | recv hProc hk hG hBuf =>
          rename_i Ccfg vs k x e v source T L
          set recvEdge : Edge := { sid := e.sid, sender := source, receiver := e.role }
          have hSid : e.sid ∈ SessionsOf Ccfg.G := ⟨e, .recv source T L, hG, rfl⟩
          have hDfrNone : Dfr.find? recvEdge = none :=
            lookupD_none_of_disjointG (G₁:=Ccfg.G) (G₂:=Gfr) (D₂:=Dfr) (DisjointG_symm hDisj) hCons hSid
          have hLookupD :
              lookupD (Dfr ++ Ccfg.D) recvEdge = lookupD Ccfg.D recvEdge :=
            lookupD_append_right (D₁:=Dfr) (D₂:=Ccfg.D) (e:=recvEdge) hDfrNone
          have hGfrNone : lookupG Gfr e = none :=
            lookupG_none_of_disjoint (G₁:=Gfr) (G₂:=Ccfg.G) hDisj (e:=e) (L:=.recv source T L) hG
          have hLookupG :
              lookupG (Gfr ++ Ccfg.G) e = some (.recv source T L) := by
            simpa [lookupG_append_right (G₁:=Gfr) (G₂:=Ccfg.G) (e:=e) hGfrNone] using hG
          have hUpdG : updateG (Gfr ++ Ccfg.G) e L = Gfr ++ updateG Ccfg.G e L :=
            updateG_append_right_hit hGfrNone
          have hUpdD :
              updateD (Dfr ++ Ccfg.D) recvEdge (lookupD Ccfg.D recvEdge).tail =
                Dfr ++ updateD Ccfg.D recvEdge (lookupD Ccfg.D recvEdge).tail := by
            exact updateD_append_right (D₁:=Dfr) (D:=Ccfg.D) (e:=recvEdge)
              (ts:=(lookupD Ccfg.D recvEdge).tail) hDfrNone
          have hStep' :
              StepBase (frameConfigLeft Ccfg Gfr Dfr)
                (recvStep (frameConfigLeft Ccfg Gfr Dfr) e recvEdge x v L) := by
            refine (@StepBase.recv vs (frameConfigLeft Ccfg Gfr Dfr) k x e v source T L ?_ ?_ ?_ ?_)
            · simpa [frameConfigLeft] using hProc
            · simpa [frameConfigLeft] using hk
            · exact hLookupG
            · simpa [frameConfigLeft] using hBuf
          have hEq :
              recvStep (frameConfigLeft Ccfg Gfr Dfr) e recvEdge x v L =
                frameConfigLeft (recvStep Ccfg e recvEdge x v L) Gfr Dfr := by
            simp [frameConfigLeft, recvStep, dequeueBuf, hBuf, hUpdG, hUpdD, hLookupD]
          simpa [hEq] using (Step.base hStep')
      | select hProc hk hG hFind =>
          rename_i Ccfg k e ℓ target branches L
          set selEdge : Edge := { sid := e.sid, sender := e.role, receiver := target }
          have hSid : e.sid ∈ SessionsOf Ccfg.G := ⟨e, .select target branches, hG, rfl⟩
          have hDfrNone : Dfr.find? selEdge = none :=
            lookupD_none_of_disjointG (G₁:=Ccfg.G) (G₂:=Gfr) (D₂:=Dfr) (DisjointG_symm hDisj) hCons hSid
          have hLookupD :
              lookupD (Dfr ++ Ccfg.D) selEdge = lookupD Ccfg.D selEdge :=
            lookupD_append_right (D₁:=Dfr) (D₂:=Ccfg.D) (e:=selEdge) hDfrNone
          have hGfrNone : lookupG Gfr e = none :=
            lookupG_none_of_disjoint (G₁:=Gfr) (G₂:=Ccfg.G) hDisj (e:=e) (L:=.select target branches) hG
          have hLookupG :
              lookupG (Gfr ++ Ccfg.G) e = some (.select target branches) := by
            simpa [lookupG_append_right (G₁:=Gfr) (G₂:=Ccfg.G) (e:=e) hGfrNone] using hG
          have hUpdG : updateG (Gfr ++ Ccfg.G) e L = Gfr ++ updateG Ccfg.G e L :=
            updateG_append_right_hit hGfrNone
          have hUpdD :
              updateD (Dfr ++ Ccfg.D) selEdge (lookupD Ccfg.D selEdge ++ [.string]) =
                Dfr ++ updateD Ccfg.D selEdge (lookupD Ccfg.D selEdge ++ [.string]) := by
            exact updateD_append_right (D₁:=Dfr) (D:=Ccfg.D) (e:=selEdge)
              (ts:=lookupD Ccfg.D selEdge ++ [.string]) hDfrNone
          have hStep' :
              StepBase (frameConfigLeft Ccfg Gfr Dfr)
                (sendStep (frameConfigLeft Ccfg Gfr Dfr) e selEdge (.string ℓ) .string L) := by
            refine StepBase.select (C:=frameConfigLeft Ccfg Gfr Dfr) (k:=k) (e:=e) (ℓ:=ℓ)
              (target:=target) (branches:=branches) (L:=L) ?_ ?_ ?_ ?_
            · simpa [frameConfigLeft] using hProc
            · simpa [frameConfigLeft] using hk
            · exact hLookupG
            · simpa using hFind
          have hEq :
              sendStep (frameConfigLeft Ccfg Gfr Dfr) e selEdge (.string ℓ) .string L =
                frameConfigLeft (sendStep Ccfg e selEdge (.string ℓ) .string L) Gfr Dfr := by
            simp [frameConfigLeft, sendStep, hUpdG, hUpdD, hLookupD]
          simpa [hEq] using (Step.base hStep')
      | branch hProc hk hG hBuf hFindP hFindT hDeq =>
          rename_i Ccfg vs vOut k e ℓ source procBranches typeBranches P L bufs'
          set brEdge : Edge := { sid := e.sid, sender := source, receiver := e.role }
          have hSid : e.sid ∈ SessionsOf Ccfg.G := ⟨e, .branch source typeBranches, hG, rfl⟩
          have hDfrNone : Dfr.find? brEdge = none :=
            lookupD_none_of_disjointG (G₁:=Ccfg.G) (G₂:=Gfr) (D₂:=Dfr) (DisjointG_symm hDisj) hCons hSid
          have hLookupD :
              lookupD (Dfr ++ Ccfg.D) brEdge = lookupD Ccfg.D brEdge :=
            lookupD_append_right (D₁:=Dfr) (D₂:=Ccfg.D) (e:=brEdge) hDfrNone
          have hGfrNone : lookupG Gfr e = none :=
            lookupG_none_of_disjoint (G₁:=Gfr) (G₂:=Ccfg.G) hDisj (e:=e) (L:=.branch source typeBranches) hG
          have hLookupG :
              lookupG (Gfr ++ Ccfg.G) e = some (.branch source typeBranches) := by
            simpa [lookupG_append_right (G₁:=Gfr) (G₂:=Ccfg.G) (e:=e) hGfrNone] using hG
          have hUpdG : updateG (Gfr ++ Ccfg.G) e L = Gfr ++ updateG Ccfg.G e L :=
            updateG_append_right_hit hGfrNone
          have hUpdD :
              updateD (Dfr ++ Ccfg.D) brEdge (lookupD Ccfg.D brEdge).tail =
                Dfr ++ updateD Ccfg.D brEdge (lookupD Ccfg.D brEdge).tail := by
            exact updateD_append_right (D₁:=Dfr) (D:=Ccfg.D) (e:=brEdge)
              (ts:=(lookupD Ccfg.D brEdge).tail) hDfrNone
          have hStep' :
              StepBase (frameConfigLeft Ccfg Gfr Dfr)
                { frameConfigLeft Ccfg Gfr Dfr with
                    proc := P,
                    bufs := bufs',
                    G := updateG (frameConfigLeft Ccfg Gfr Dfr).G e L,
                    D := updateD (frameConfigLeft Ccfg Gfr Dfr).D brEdge
                          (lookupD (frameConfigLeft Ccfg Gfr Dfr).D brEdge).tail } := by
            refine (@StepBase.branch vs vOut (frameConfigLeft Ccfg Gfr Dfr)
              k e ℓ source procBranches typeBranches P L bufs' ?_ ?_ ?_ ?_ ?_ ?_ ?_)
            · simpa [frameConfigLeft] using hProc
            · simpa [frameConfigLeft] using hk
            · exact hLookupG
            · simpa [frameConfigLeft] using hBuf
            · simpa using hFindP
            · simpa using hFindT
            · simpa [frameConfigLeft] using hDeq
          have hEq :
              { frameConfigLeft Ccfg Gfr Dfr with
                  proc := P,
                  bufs := bufs',
                  G := updateG (frameConfigLeft Ccfg Gfr Dfr).G e L,
                  D := updateD (frameConfigLeft Ccfg Gfr Dfr).D brEdge
                        (lookupD (frameConfigLeft Ccfg Gfr Dfr).D brEdge).tail } =
                frameConfigLeft
                  { Ccfg with
                      proc := P,
                      bufs := bufs',
                      G := updateG Ccfg.G e L,
                      D := updateD Ccfg.D brEdge (lookupD Ccfg.D brEdge).tail } Gfr Dfr := by
            simp [frameConfigLeft, hUpdG, hUpdD, hLookupD]
          simpa [hEq] using (Step.base hStep')
      | newSession hProc =>
          rename_i Ccfg roles f P
          have hStep' : StepBase (frameConfigLeft Ccfg Gfr Dfr)
              { (newSessionStep (frameConfigLeft Ccfg Gfr Dfr) roles f) with proc := P } :=
            StepBase.newSession (C:=frameConfigLeft Ccfg Gfr Dfr) (roles:=roles) (f:=f) (P:=P)
              (by simpa [frameConfigLeft] using hProc)
          have hEq :
              { (newSessionStep (frameConfigLeft Ccfg Gfr Dfr) roles f) with proc := P } =
                frameConfigLeft { (newSessionStep Ccfg roles f) with proc := P } Gfr Dfr := by
            simp [frameConfigLeft, newSessionStep]
          simpa [hEq] using (Step.base hStep')
      | assign hProc =>
          rename_i Ccfg x v
          have hStep' : StepBase (frameConfigLeft Ccfg Gfr Dfr)
              { frameConfigLeft Ccfg Gfr Dfr with
                  proc := .skip,
                  store := updateStr (frameConfigLeft Ccfg Gfr Dfr).store x v } :=
            StepBase.assign (C:=frameConfigLeft Ccfg Gfr Dfr) (x:=x) (v:=v)
              (by simpa [frameConfigLeft] using hProc)
          have hEq :
              { frameConfigLeft Ccfg Gfr Dfr with
                  proc := .skip,
                  store := updateStr (frameConfigLeft Ccfg Gfr Dfr).store x v } =
                frameConfigLeft
                  { Ccfg with proc := .skip, store := updateStr Ccfg.store x v } Gfr Dfr := by
            simp [frameConfigLeft]
          simpa [hEq] using (Step.base hStep')
      | seq2 hProc =>
          rename_i Ccfg Q
          have hStep' : StepBase (frameConfigLeft Ccfg Gfr Dfr)
              { frameConfigLeft Ccfg Gfr Dfr with proc := Q } :=
            StepBase.seq2 (C:=frameConfigLeft Ccfg Gfr Dfr) (Q:=Q) (by simpa [frameConfigLeft] using hProc)
          have hEq :
              { frameConfigLeft Ccfg Gfr Dfr with proc := Q } =
                frameConfigLeft { Ccfg with proc := Q } Gfr Dfr := by
            simp [frameConfigLeft]
          simpa [hEq] using (Step.base hStep')
      | par_skip_left hProc =>
          rename_i Ccfg Q nS nG
          have hStep' : StepBase (frameConfigLeft Ccfg Gfr Dfr)
              { frameConfigLeft Ccfg Gfr Dfr with proc := Q } :=
            StepBase.par_skip_left (C:=frameConfigLeft Ccfg Gfr Dfr) (Q:=Q)
              (by simpa [frameConfigLeft] using hProc)
          have hEq :
              { frameConfigLeft Ccfg Gfr Dfr with proc := Q } =
                frameConfigLeft { Ccfg with proc := Q } Gfr Dfr := by
            simp [frameConfigLeft]
          simpa [hEq] using (Step.base hStep')
      | par_skip_right hProc =>
          rename_i Ccfg P nS nG
          have hStep' : StepBase (frameConfigLeft Ccfg Gfr Dfr)
              { frameConfigLeft Ccfg Gfr Dfr with proc := P } :=
            StepBase.par_skip_right (C:=frameConfigLeft Ccfg Gfr Dfr) (P:=P)
              (by simpa [frameConfigLeft] using hProc)
          have hEq :
              { frameConfigLeft Ccfg Gfr Dfr with proc := P } =
                frameConfigLeft { Ccfg with proc := P } Gfr Dfr := by
            simp [frameConfigLeft]
          simpa [hEq] using (Step.base hStep')
  | seq_left hProc hSub ih =>
      rename_i Ccfg Ccfg' P Q
      have hProc' : (frameConfigLeft Ccfg Gfr Dfr).proc = .seq P Q := by
        simpa [frameConfigLeft] using hProc
      have hDisj' : DisjointG Gfr { Ccfg with proc := P }.G := by
        simpa using hDisj
      have hSub' := ih hDisj'
      simpa [frameConfigLeft] using (Step.seq_left hProc' hSub')
  | par_left hProc hSub ih =>
      rename_i Ccfg Ccfg' P Q nS nG nS' nG'
      have hProc' : (frameConfigLeft Ccfg Gfr Dfr).proc = .par nS nG P Q := by
        simpa [frameConfigLeft] using hProc
      have hDisj' : DisjointG Gfr { Ccfg with proc := P }.G := by
        simpa using hDisj
      have hSub' := ih hDisj'
      simpa [frameConfigLeft] using (Step.par_left hProc' hSub')
  | par_right hProc hSub ih =>
      rename_i Ccfg Ccfg' P Q nS nG nS' nG'
      have hProc' : (frameConfigLeft Ccfg Gfr Dfr).proc = .par nS nG P Q := by
        simpa [frameConfigLeft] using hProc
      have hDisj' : DisjointG Gfr { Ccfg with proc := Q }.G := by
        simpa using hDisj
      have hSub' := ih hDisj'
      simpa [frameConfigLeft] using (Step.par_right hProc' hSub')

/-! ## Subject Reduction -/

end
