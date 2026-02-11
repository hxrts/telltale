import Protocol.Preservation.ProgressLemmas

/-! # Right Frame Preservation

Proves that execution steps are preserved under right-framing: adding
a disjoint environment fragment on the right of a configuration. -/

/-
The Problem. Frame lemmas allow compositional reasoning about protocol
configurations. Right-framing adds `G ++ Gfr` and `D ++ Dfr` where the
frame is on the right. We need to show steps in the unframed config
lift to the framed config.

Solution Structure. Define `frameConfigRight` and `frameConfigLeft`
configuration constructors. Prove `step_frame_right` by induction on
`Step`, showing update operations stay within the original portion.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical
open Batteries

section

/-! ## Frame Configuration Constructors -/

def frameConfigRight (C : Config) (Gfr : GEnv) (Dfr : DEnv) : Config :=
  { C with G := C.G ++ Gfr, D := C.D ++ Dfr }

def frameConfigLeft (C : Config) (Gfr : GEnv) (Dfr : DEnv) : Config :=
  { C with G := Gfr ++ C.G, D := Dfr ++ C.D }

lemma step_frame_right {C C' : Config} {Gfr : GEnv} {Dfr : DEnv} :
    DisjointG C.G Gfr →
    DConsistent Gfr Dfr →
    Step C C' →
    Step (frameConfigRight C Gfr Dfr) (frameConfigRight C' Gfr Dfr) := by
  intro hDisj hCons hStep
  induction hStep with
  | base hBase =>
      cases hBase with
      | send hProc hk hx hG =>
          rename_i Ccfg k x e v target T L
          set sendEdge : Edge := { sid := e.sid, sender := e.role, receiver := target }
          have hSid : e.sid ∈ SessionsOf Ccfg.G := ⟨e, .send target T L, hG, rfl⟩
          have hDfrNone : Dfr.find? sendEdge = none :=
            lookupD_none_of_disjointG (G₁:=Ccfg.G) (G₂:=Gfr) (D₂:=Dfr) hDisj hCons hSid
          have hLookupD :
              lookupD (Ccfg.D ++ Dfr) sendEdge = lookupD Ccfg.D sendEdge :=
            lookupD_append_left_of_right_none (D₁:=Ccfg.D) (D₂:=Dfr) (e:=sendEdge) hDfrNone
          have hUpdG : updateG (Ccfg.G ++ Gfr) e L = updateG Ccfg.G e L ++ Gfr :=
            updateG_append_left_hit hG
          have hUpdD :
              updateD (Ccfg.D ++ Dfr) sendEdge (lookupD Ccfg.D sendEdge ++ [T]) =
                updateD Ccfg.D sendEdge (lookupD Ccfg.D sendEdge ++ [T]) ++ Dfr := by
            exact updateD_append_left (D:=Ccfg.D) (D₂:=Dfr) (e:=sendEdge)
              (ts:=lookupD Ccfg.D sendEdge ++ [T])
          have hStep' :
              StepBase (frameConfigRight Ccfg Gfr Dfr)
                (sendStep (frameConfigRight Ccfg Gfr Dfr) e sendEdge v T L) := by
            refine StepBase.send (C:=frameConfigRight Ccfg Gfr Dfr) (k:=k) (x:=x) (e:=e)
              (v:=v) (target:=target) (T:=T) (L:=L) ?_ ?_ ?_ ?_
            · simpa [frameConfigRight] using hProc
            · simpa [frameConfigRight] using hk
            · simpa [frameConfigRight] using hx
            · exact lookupG_append_left hG
          have hEq :
              sendStep (frameConfigRight Ccfg Gfr Dfr) e sendEdge v T L =
                frameConfigRight (sendStep Ccfg e sendEdge v T L) Gfr Dfr := by
            simp [frameConfigRight, sendStep, hUpdG, hUpdD, hLookupD]
          simpa [hEq] using (Step.base hStep')
      | recv hProc hk hG hBuf =>
          rename_i Ccfg vs k x e v source T L
          set recvEdge : Edge := { sid := e.sid, sender := source, receiver := e.role }
          have hSid : e.sid ∈ SessionsOf Ccfg.G := ⟨e, .recv source T L, hG, rfl⟩
          have hDfrNone : Dfr.find? recvEdge = none :=
            lookupD_none_of_disjointG (G₁:=Ccfg.G) (G₂:=Gfr) (D₂:=Dfr) hDisj hCons hSid
          have hLookupD :
              lookupD (Ccfg.D ++ Dfr) recvEdge = lookupD Ccfg.D recvEdge :=
            lookupD_append_left_of_right_none (D₁:=Ccfg.D) (D₂:=Dfr) (e:=recvEdge) hDfrNone
          have hUpdG : updateG (Ccfg.G ++ Gfr) e L = updateG Ccfg.G e L ++ Gfr :=
            updateG_append_left_hit hG
          have hUpdD :
              updateD (Ccfg.D ++ Dfr) recvEdge (lookupD Ccfg.D recvEdge).tail =
                updateD Ccfg.D recvEdge (lookupD Ccfg.D recvEdge).tail ++ Dfr := by
            exact updateD_append_left (D:=Ccfg.D) (D₂:=Dfr) (e:=recvEdge)
              (ts:=(lookupD Ccfg.D recvEdge).tail)
          have hStep' :
              StepBase (frameConfigRight Ccfg Gfr Dfr)
                (recvStep (frameConfigRight Ccfg Gfr Dfr) e recvEdge x v L) := by
            refine (@StepBase.recv vs (frameConfigRight Ccfg Gfr Dfr) k x e v source T L ?_ ?_ ?_ ?_)
            · simpa [frameConfigRight] using hProc
            · simpa [frameConfigRight] using hk
            · exact lookupG_append_left hG
            · simpa [frameConfigRight] using hBuf
          have hEq :
              recvStep (frameConfigRight Ccfg Gfr Dfr) e recvEdge x v L =
                frameConfigRight (recvStep Ccfg e recvEdge x v L) Gfr Dfr := by
            simp [frameConfigRight, recvStep, dequeueBuf, hBuf, hUpdG, hUpdD, hLookupD]
          simpa [hEq] using (Step.base hStep')
      | select hProc hk hG hFind =>
          rename_i Ccfg k e ℓ target branches L
          set selEdge : Edge := { sid := e.sid, sender := e.role, receiver := target }
          have hSid : e.sid ∈ SessionsOf Ccfg.G := ⟨e, .select target branches, hG, rfl⟩
          have hDfrNone : Dfr.find? selEdge = none :=
            lookupD_none_of_disjointG (G₁:=Ccfg.G) (G₂:=Gfr) (D₂:=Dfr) hDisj hCons hSid
          have hLookupD :
              lookupD (Ccfg.D ++ Dfr) selEdge = lookupD Ccfg.D selEdge :=
            lookupD_append_left_of_right_none (D₁:=Ccfg.D) (D₂:=Dfr) (e:=selEdge) hDfrNone
          have hUpdG : updateG (Ccfg.G ++ Gfr) e L = updateG Ccfg.G e L ++ Gfr :=
            updateG_append_left_hit hG
          have hUpdD :
              updateD (Ccfg.D ++ Dfr) selEdge (lookupD Ccfg.D selEdge ++ [.string]) =
                updateD Ccfg.D selEdge (lookupD Ccfg.D selEdge ++ [.string]) ++ Dfr := by
            exact updateD_append_left (D:=Ccfg.D) (D₂:=Dfr) (e:=selEdge)
              (ts:=lookupD Ccfg.D selEdge ++ [.string])
          have hStep' :
              StepBase (frameConfigRight Ccfg Gfr Dfr)
                (sendStep (frameConfigRight Ccfg Gfr Dfr) e selEdge (.string ℓ) .string L) := by
            refine StepBase.select (C:=frameConfigRight Ccfg Gfr Dfr) (k:=k) (e:=e) (ℓ:=ℓ)
              (target:=target) (branches:=branches) (L:=L) ?_ ?_ ?_ ?_
            · simpa [frameConfigRight] using hProc
            · simpa [frameConfigRight] using hk
            · exact lookupG_append_left hG
            · simpa using hFind
          have hEq :
              sendStep (frameConfigRight Ccfg Gfr Dfr) e selEdge (.string ℓ) .string L =
                frameConfigRight (sendStep Ccfg e selEdge (.string ℓ) .string L) Gfr Dfr := by
            simp [frameConfigRight, sendStep, hUpdG, hUpdD, hLookupD]
          simpa [hEq] using (Step.base hStep')
      | branch hProc hk hG hBuf hFindP hFindT hDeq =>
          rename_i Ccfg vs vOut k e ℓ source procBranches typeBranches P L bufs'
          set brEdge : Edge := { sid := e.sid, sender := source, receiver := e.role }
          have hSid : e.sid ∈ SessionsOf Ccfg.G := ⟨e, .branch source typeBranches, hG, rfl⟩
          have hDfrNone : Dfr.find? brEdge = none :=
            lookupD_none_of_disjointG (G₁:=Ccfg.G) (G₂:=Gfr) (D₂:=Dfr) hDisj hCons hSid
          have hLookupD :
              lookupD (Ccfg.D ++ Dfr) brEdge = lookupD Ccfg.D brEdge :=
            lookupD_append_left_of_right_none (D₁:=Ccfg.D) (D₂:=Dfr) (e:=brEdge) hDfrNone
          have hUpdG : updateG (Ccfg.G ++ Gfr) e L = updateG Ccfg.G e L ++ Gfr :=
            updateG_append_left_hit hG
          have hUpdD :
              updateD (Ccfg.D ++ Dfr) brEdge (lookupD Ccfg.D brEdge).tail =
                updateD Ccfg.D brEdge (lookupD Ccfg.D brEdge).tail ++ Dfr := by
            exact updateD_append_left (D:=Ccfg.D) (D₂:=Dfr) (e:=brEdge)
              (ts:=(lookupD Ccfg.D brEdge).tail)
          have hStep' :
              StepBase (frameConfigRight Ccfg Gfr Dfr)
                { frameConfigRight Ccfg Gfr Dfr with
                    proc := P,
                    bufs := bufs',
                    G := updateG (frameConfigRight Ccfg Gfr Dfr).G e L,
                    D := updateD (frameConfigRight Ccfg Gfr Dfr).D brEdge
                          (lookupD (frameConfigRight Ccfg Gfr Dfr).D brEdge).tail } := by
            refine (@StepBase.branch vs vOut (frameConfigRight Ccfg Gfr Dfr)
              k e ℓ source procBranches typeBranches P L bufs' ?_ ?_ ?_ ?_ ?_ ?_ ?_)
            · simpa [frameConfigRight] using hProc
            · simpa [frameConfigRight] using hk
            · exact lookupG_append_left hG
            · simpa [frameConfigRight] using hBuf
            · simpa using hFindP
            · simpa using hFindT
            · simpa [frameConfigRight] using hDeq
          have hEq :
              { frameConfigRight Ccfg Gfr Dfr with
                  proc := P,
                  bufs := bufs',
                  G := updateG (frameConfigRight Ccfg Gfr Dfr).G e L,
                  D := updateD (frameConfigRight Ccfg Gfr Dfr).D brEdge
                        (lookupD (frameConfigRight Ccfg Gfr Dfr).D brEdge).tail } =
                frameConfigRight
                  { Ccfg with
                      proc := P,
                      bufs := bufs',
                      G := updateG Ccfg.G e L,
                      D := updateD Ccfg.D brEdge (lookupD Ccfg.D brEdge).tail } Gfr Dfr := by
            simp [frameConfigRight, hUpdG, hUpdD, hLookupD]
          simpa [hEq] using (Step.base hStep')
      | newSession hProc =>
          rename_i Ccfg roles f P
          have hStep' : StepBase (frameConfigRight Ccfg Gfr Dfr)
              { (newSessionStep (frameConfigRight Ccfg Gfr Dfr) roles f) with proc := P } :=
            StepBase.newSession (C:=frameConfigRight Ccfg Gfr Dfr) (roles:=roles) (f:=f) (P:=P)
              (by simpa [frameConfigRight] using hProc)
          have hEq :
              { (newSessionStep (frameConfigRight Ccfg Gfr Dfr) roles f) with proc := P } =
                frameConfigRight { (newSessionStep Ccfg roles f) with proc := P } Gfr Dfr := by
            simp [frameConfigRight, newSessionStep]
          simpa [hEq] using (Step.base hStep')
      | assign hProc =>
          rename_i Ccfg x v
          have hStep' : StepBase (frameConfigRight Ccfg Gfr Dfr)
              { frameConfigRight Ccfg Gfr Dfr with
                  proc := .skip,
                  store := updateStr (frameConfigRight Ccfg Gfr Dfr).store x v } :=
            StepBase.assign (C:=frameConfigRight Ccfg Gfr Dfr) (x:=x) (v:=v)
              (by simpa [frameConfigRight] using hProc)
          have hEq :
              { frameConfigRight Ccfg Gfr Dfr with
                  proc := .skip,
                  store := updateStr (frameConfigRight Ccfg Gfr Dfr).store x v } =
                frameConfigRight
                  { Ccfg with proc := .skip, store := updateStr Ccfg.store x v } Gfr Dfr := by
            simp [frameConfigRight]
          simpa [hEq] using (Step.base hStep')
      | seq2 hProc =>
          rename_i Ccfg Q
          have hStep' : StepBase (frameConfigRight Ccfg Gfr Dfr)
              { frameConfigRight Ccfg Gfr Dfr with proc := Q } :=
            StepBase.seq2 (C:=frameConfigRight Ccfg Gfr Dfr) (Q:=Q) (by simpa [frameConfigRight] using hProc)
          have hEq :
              { frameConfigRight Ccfg Gfr Dfr with proc := Q } =
                frameConfigRight { Ccfg with proc := Q } Gfr Dfr := by
            simp [frameConfigRight]
          simpa [hEq] using (Step.base hStep')
      | par_skip_left hProc =>
          rename_i Ccfg Q nS nG
          have hStep' : StepBase (frameConfigRight Ccfg Gfr Dfr)
              { frameConfigRight Ccfg Gfr Dfr with proc := Q } :=
            StepBase.par_skip_left (C:=frameConfigRight Ccfg Gfr Dfr) (Q:=Q)
              (by simpa [frameConfigRight] using hProc)
          have hEq :
              { frameConfigRight Ccfg Gfr Dfr with proc := Q } =
                frameConfigRight { Ccfg with proc := Q } Gfr Dfr := by
            simp [frameConfigRight]
          simpa [hEq] using (Step.base hStep')
      | par_skip_right hProc =>
          rename_i Ccfg P nS nG
          have hStep' : StepBase (frameConfigRight Ccfg Gfr Dfr)
              { frameConfigRight Ccfg Gfr Dfr with proc := P } :=
            StepBase.par_skip_right (C:=frameConfigRight Ccfg Gfr Dfr) (P:=P)
              (by simpa [frameConfigRight] using hProc)
          have hEq :
              { frameConfigRight Ccfg Gfr Dfr with proc := P } =
                frameConfigRight { Ccfg with proc := P } Gfr Dfr := by
            simp [frameConfigRight]
          simpa [hEq] using (Step.base hStep')
  | seq_left hProc hSub ih =>
      rename_i Ccfg Ccfg' P Q
      have hProc' : (frameConfigRight Ccfg Gfr Dfr).proc = .seq P Q := by
        simpa [frameConfigRight] using hProc
      have hDisj' : DisjointG { Ccfg with proc := P }.G Gfr := by
        simpa using hDisj
      have hSub' := ih hDisj'
      simpa [frameConfigRight] using (Step.seq_left hProc' hSub')
  | par_left hProc hSub ih =>
      rename_i Ccfg Ccfg' P Q nS nG nS' nG'
      have hProc' : (frameConfigRight Ccfg Gfr Dfr).proc = .par nS nG P Q := by
        simpa [frameConfigRight] using hProc
      have hDisj' : DisjointG { Ccfg with proc := P }.G Gfr := by
        simpa using hDisj
      have hSub' := ih hDisj'
      simpa [frameConfigRight] using (Step.par_left hProc' hSub')
  | par_right hProc hSub ih =>
      rename_i Ccfg Ccfg' P Q nS nG nS' nG'
      have hProc' : (frameConfigRight Ccfg Gfr Dfr).proc = .par nS nG P Q := by
        simpa [frameConfigRight] using hProc
      have hDisj' : DisjointG { Ccfg with proc := Q }.G Gfr := by
        simpa using hDisj
      have hSub' := ih hDisj'
      simpa [frameConfigRight] using (Step.par_right hProc' hSub')


end
