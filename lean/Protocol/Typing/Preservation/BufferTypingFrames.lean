
import Protocol.Typing.Preservation.BufferTypingRewrites

/-! # Buffer Typing Frame Lemmas

Buffer typing preservation under framing operations for send, recv,
select, and branch steps with left-appended environments. -/

/-
The Problem. When proving buffer preservation for framed configurations,
we need to show `BuffersTyped (G ++ G₂) (D ++ D₂) bufs` lifts through
send/recv operations that modify only the left portion.

Solution Structure. Prove `BuffersTyped_send_frame_left`, etc. by
combining lookup localization (send edge is in left portion) with
the underlying buffer update lemmas.
-/

/- ## Structured Block 1 -/
set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical
open Batteries

section

-- Send Frame Lemma

theorem BuffersTyped_send_frame_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} {bufs : Buffers}
    {e : Endpoint} {target : Role} {T : ValType} {L : LocalType} {v : Value}
    {sendEdge : Edge} :
    lookupG G e = some (.send target T L) →
    HasTypeVal G v T →
    sendEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    BuffersTyped (updateG G e L ++ G₂)
      (updateD (D ++ D₂) sendEdge (lookupD D sendEdge ++ [T]))
      (enqueueBuf bufs sendEdge v) := by
  intro hG hv hEdge hDisj hCons hBT
  subst hEdge
  have hv' : HasTypeVal (G ++ G₂) v T :=
    HasTypeVal_mono G (G ++ G₂) v T hv (by
      intro ep L' hLookup
      exact lookupG_append_left hLookup)
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .send target T L, hG, rfl⟩
  have hD2none : D₂.find? { sid := e.sid, sender := e.role, receiver := target } = none :=
    lookupD_none_of_disjointG (G₁:=G) (G₂:=G₂) (D₂:=D₂) hDisj hCons hSid
  have hEq :
      lookupD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target } =
        lookupD D { sid := e.sid, sender := e.role, receiver := target } :=
    lookupD_append_left_of_right_none (D₁:=D) (D₂:=D₂) (e:={ sid := e.sid, sender := e.role, receiver := target }) hD2none
  have hBT' :
      BuffersTyped (G ++ G₂)
        (updateD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target } ++ [T]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } v) :=
    BuffersTyped_enqueue (G:=G ++ G₂) (D:=D ++ D₂) (bufs:=bufs)
      (e:={ sid := e.sid, sender := e.role, receiver := target }) (v:=v) (T:=T) hBT hv'
  have hBT'' :
      BuffersTyped (G ++ G₂)
        (updateD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD D { sid := e.sid, sender := e.role, receiver := target } ++ [T]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } v) := by
    simpa [hEq] using hBT'
  have hBT''' :
      BuffersTyped (updateG (G ++ G₂) e L)
        (updateD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD D { sid := e.sid, sender := e.role, receiver := target } ++ [T]))
/- ## Structured Block 2 -/
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } v) :=
    BuffersTyped_updateG_weaken (e:=e) (L:=L) hBT''
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.send target T L) (L':=L) hG
  simpa [hGrew] using hBT'''

-- Recv Frame Lemma (Left Append)

theorem BuffersTyped_recv_frame_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} {bufs : Buffers}
    {e : Endpoint} {source : Role} {T : ValType} {L : LocalType} {v : Value} {vs : List Value}
    {recvEdge : Edge} :
    lookupG G e = some (.recv source T L) →
    lookupBuf bufs recvEdge = v :: vs →
    (lookupD D recvEdge).head? = some T →
    recvEdge = { sid := e.sid, sender := source, receiver := e.role } →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    BuffersTyped (updateG G e L ++ G₂)
      (updateD (D ++ D₂) recvEdge (lookupD D recvEdge).tail)
      (updateBuf bufs recvEdge vs) := by
  intro hG hBuf hHead hEdge hDisj hCons hBT
  subst hEdge
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .recv source T L, hG, rfl⟩
  have hD2none : D₂.find? { sid := e.sid, sender := source, receiver := e.role } = none :=
    lookupD_none_of_disjointG (G₁:=G) (G₂:=G₂) (D₂:=D₂) hDisj hCons hSid
  have hEq :
      lookupD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role } =
        lookupD D { sid := e.sid, sender := source, receiver := e.role } :=
    lookupD_append_left_of_right_none (D₁:=D) (D₂:=D₂) (e:={ sid := e.sid, sender := source, receiver := e.role }) hD2none
  have hHead' :
      (lookupD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }).head? = some T := by
    simpa [hEq] using hHead
  have hBT' :
      BuffersTyped (G ++ G₂)
        (updateD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) :=
    BuffersTyped_dequeue (G:=G ++ G₂) (D:=D ++ D₂) (bufs:=bufs)
      (recvEdge:={ sid := e.sid, sender := source, receiver := e.role }) (v:=v) (vs:=vs) (T:=T)
      hBT hBuf hHead'
  have hBT'' :
      BuffersTyped (G ++ G₂)
        (updateD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) := by
    simpa [hEq] using hBT'
  -- # Lift Along `updateG` and Reassociate
  have hBT''' :
      BuffersTyped (updateG (G ++ G₂) e L)
        (updateD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail)
/- ## Structured Block 3 -/
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) :=
    BuffersTyped_updateG_weaken (e:=e) (L:=L) hBT''
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.recv source T L) (L':=L) hG
  simpa [hGrew] using hBT'''

-- Select Frame Lemma (Left Append)

theorem BuffersTyped_select_frame_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} {bufs : Buffers}
    {e : Endpoint} {target : Role} {bs : List (String × LocalType)} {ℓ : String}
    {L : LocalType} {selectEdge : Edge} :
    lookupG G e = some (.select target bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    selectEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    BuffersTyped (updateG G e L ++ G₂)
      (updateD (D ++ D₂) selectEdge (lookupD D selectEdge ++ [.string]))
      (enqueueBuf bufs selectEdge (.string ℓ)) := by
  intro hG hFind hEdge hDisj hCons hBT
  subst hEdge
  have hv' : HasTypeVal (G ++ G₂) (.string ℓ) .string :=
    HasTypeVal_mono G (G ++ G₂) (.string ℓ) .string (HasTypeVal.string ℓ) (by
      intro ep L' hLookup
      exact lookupG_append_left hLookup)
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .select target bs, hG, rfl⟩
  have hD2none : D₂.find? { sid := e.sid, sender := e.role, receiver := target } = none :=
    lookupD_none_of_disjointG (G₁:=G) (G₂:=G₂) (D₂:=D₂) hDisj hCons hSid
  have hEq :
      lookupD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target } =
        lookupD D { sid := e.sid, sender := e.role, receiver := target } :=
    lookupD_append_left_of_right_none (D₁:=D) (D₂:=D₂) (e:={ sid := e.sid, sender := e.role, receiver := target }) hD2none
  have hBT' :
      BuffersTyped (G ++ G₂)
        (updateD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target } ++ [.string]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } (.string ℓ)) :=
    BuffersTyped_enqueue (G:=G ++ G₂) (D:=D ++ D₂) (bufs:=bufs)
      (e:={ sid := e.sid, sender := e.role, receiver := target }) (v:=.string ℓ) (T:=.string) hBT hv'
  have hBT'' :
      BuffersTyped (G ++ G₂)
        (updateD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD D { sid := e.sid, sender := e.role, receiver := target } ++ [.string]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } (.string ℓ)) := by
    simpa [hEq] using hBT'
  have hBT''' :
      BuffersTyped (updateG (G ++ G₂) e L)
        (updateD (D ++ D₂) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD D { sid := e.sid, sender := e.role, receiver := target } ++ [.string]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } (.string ℓ)) :=
/- ## Structured Block 4 -/
    BuffersTyped_updateG_weaken (e:=e) (L:=L) hBT''
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.select target bs) (L':=L) hG
  simpa [hGrew] using hBT'''

-- Branch Frame Lemma (Left Append)

theorem BuffersTyped_branch_frame_left
    {G : GEnv} {D : DEnv} {G₂ : GEnv} {D₂ : DEnv} {bufs : Buffers}
    {e : Endpoint} {source : Role} {bs : List (String × LocalType)}
    {ℓ : String} {L : LocalType} {vs : List Value} {branchEdge : Edge} :
    lookupG G e = some (.branch source bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    lookupBuf bufs branchEdge = .string ℓ :: vs →
    (lookupD D branchEdge).head? = some .string →
    branchEdge = { sid := e.sid, sender := source, receiver := e.role } →
    DisjointG G G₂ →
    DConsistent G₂ D₂ →
    BuffersTyped (G ++ G₂) (D ++ D₂) bufs →
    BuffersTyped (updateG G e L ++ G₂)
      (updateD (D ++ D₂) branchEdge (lookupD D branchEdge).tail)
      (updateBuf bufs branchEdge vs) := by
  intro hG hFind hBuf hHead hEdge hDisj hCons hBT
  subst hEdge
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .branch source bs, hG, rfl⟩
  have hD2none : D₂.find? { sid := e.sid, sender := source, receiver := e.role } = none :=
    lookupD_none_of_disjointG (G₁:=G) (G₂:=G₂) (D₂:=D₂) hDisj hCons hSid
  have hEq :
      lookupD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role } =
        lookupD D { sid := e.sid, sender := source, receiver := e.role } :=
    lookupD_append_left_of_right_none (D₁:=D) (D₂:=D₂) (e:={ sid := e.sid, sender := source, receiver := e.role }) hD2none
  -- # Normalize Lookup Head Premise Through Rewritten DEnv
  have hHead' :
      (lookupD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }).head? = some .string := by
    simpa [hEq] using hHead
  have hBT' :
      BuffersTyped (G ++ G₂)
        (updateD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) :=
    BuffersTyped_dequeue (G:=G ++ G₂) (D:=D ++ D₂) (bufs:=bufs)
      (recvEdge:={ sid := e.sid, sender := source, receiver := e.role }) (v:=.string ℓ) (vs:=vs) (T:=.string)
      hBT hBuf hHead'
  have hBT'' :
      BuffersTyped (G ++ G₂)
        (updateD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) := by
    simpa [hEq] using hBT'
  have hBT''' :
      BuffersTyped (updateG (G ++ G₂) e L)
        (updateD (D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail)
/- ## Structured Block 5 -/
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) :=
    BuffersTyped_updateG_weaken (e:=e) (L:=L) hBT''
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.branch source bs) (L':=L) hG
  simpa [hGrew] using hBT'''

-- Send Frame Lemma (Right Append)

theorem BuffersTyped_send_frame_right
    {G : GEnv} {D : DEnv} {G₁ : GEnv} {D₁ : DEnv} {bufs : Buffers}
    {e : Endpoint} {target : Role} {T : ValType} {L : LocalType} {v : Value}
    {sendEdge : Edge} :
    lookupG G e = some (.send target T L) →
    HasTypeVal G v T →
    sendEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    BuffersTyped (G₁ ++ updateG G e L)
      (updateD (D₁ ++ D) sendEdge (lookupD D sendEdge ++ [T]))
      (enqueueBuf bufs sendEdge v) := by
  intro hG hv hEdge hDisj hCons hBT
  subst hEdge
  have hv' : HasTypeVal (G₁ ++ G) v T :=
    HasTypeVal_mono G (G₁ ++ G) v T hv (by
      intro ep L' hLookup
      -- use right lookup, disjointness ensures left has none
      have hNone : lookupG G₁ ep = none := lookupG_none_of_disjoint hDisj hLookup
      have hEq := lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=ep) hNone
      simpa [hEq] using hLookup)
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .send target T L, hG, rfl⟩
  have hDisj' : DisjointG G G₁ := DisjointG_symm hDisj
  have hD1none : D₁.find? { sid := e.sid, sender := e.role, receiver := target } = none :=
    lookupD_none_of_disjointG (G₁:=G) (G₂:=G₁) (D₂:=D₁) hDisj' hCons hSid
  have hEq :
      lookupD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target } =
        lookupD D { sid := e.sid, sender := e.role, receiver := target } :=
    lookupD_append_right (D₁:=D₁) (D₂:=D) (e:={ sid := e.sid, sender := e.role, receiver := target }) hD1none
  have hBT' :
      BuffersTyped (G₁ ++ G)
        (updateD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target } ++ [T]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } v) :=
    BuffersTyped_enqueue (G:=G₁ ++ G) (D:=D₁ ++ D) (bufs:=bufs)
      (e:={ sid := e.sid, sender := e.role, receiver := target }) (v:=v) (T:=T) hBT hv'
  have hBT'' :
      BuffersTyped (G₁ ++ G)
        (updateD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD D { sid := e.sid, sender := e.role, receiver := target } ++ [T]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } v) := by
    simpa [hEq] using hBT'
  -- # Lift Along `updateG` and Reassociate
  have hBT''' :
      BuffersTyped (updateG (G₁ ++ G) e L)
/- ## Structured Block 6 -/
        (updateD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD D { sid := e.sid, sender := e.role, receiver := target } ++ [T]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } v) :=
    BuffersTyped_updateG_weaken (e:=e) (L:=L) hBT''
  have hGrew :
      updateG (G₁ ++ G) e L = G₁ ++ updateG G e L :=
    updateG_append_left (G₁:=G₁) (G₂:=G) (e:=e) (L:=L)
      (lookupG_none_of_disjoint (G₁:=G₁) (G₂:=G) hDisj hG)
  simpa [hGrew] using hBT'''

-- Recv Frame Lemma (Right Append)

theorem BuffersTyped_recv_frame_right
    {G : GEnv} {D : DEnv} {G₁ : GEnv} {D₁ : DEnv} {bufs : Buffers}
    {e : Endpoint} {source : Role} {T : ValType} {L : LocalType} {v : Value} {vs : List Value}
    {recvEdge : Edge} :
    lookupG G e = some (.recv source T L) →
    lookupBuf bufs recvEdge = v :: vs →
    (lookupD D recvEdge).head? = some T →
    recvEdge = { sid := e.sid, sender := source, receiver := e.role } →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    BuffersTyped (G₁ ++ updateG G e L)
      (updateD (D₁ ++ D) recvEdge (lookupD D recvEdge).tail)
      (updateBuf bufs recvEdge vs) := by
  intro hG hBuf hHead hEdge hDisj hCons hBT
  subst hEdge
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .recv source T L, hG, rfl⟩
  have hDisj' : DisjointG G G₁ := DisjointG_symm hDisj
  have hD1none : D₁.find? { sid := e.sid, sender := source, receiver := e.role } = none :=
    lookupD_none_of_disjointG (G₁:=G) (G₂:=G₁) (D₂:=D₁) hDisj' hCons hSid
  have hEq :
      lookupD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role } =
        lookupD D { sid := e.sid, sender := source, receiver := e.role } :=
    lookupD_append_right (D₁:=D₁) (D₂:=D) (e:={ sid := e.sid, sender := source, receiver := e.role }) hD1none
  have hHead' :
      (lookupD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }).head? = some T := by
    simpa [hEq] using hHead
  have hBT' :
      BuffersTyped (G₁ ++ G)
        (updateD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) :=
    BuffersTyped_dequeue (G:=G₁ ++ G) (D:=D₁ ++ D) (bufs:=bufs)
      (recvEdge:={ sid := e.sid, sender := source, receiver := e.role }) (v:=v) (vs:=vs) (T:=T)
      hBT hBuf hHead'
  have hBT'' :
      BuffersTyped (G₁ ++ G)
        (updateD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) := by
    simpa [hEq] using hBT'
  -- # Lift Along `updateG` and Reassociate
/- ## Structured Block 7 -/
  have hBT''' :
      BuffersTyped (updateG (G₁ ++ G) e L)
        (updateD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) :=
    BuffersTyped_updateG_weaken (e:=e) (L:=L) hBT''
  have hGrew :
      updateG (G₁ ++ G) e L = G₁ ++ updateG G e L :=
    updateG_append_left (G₁:=G₁) (G₂:=G) (e:=e) (L:=L)
      (lookupG_none_of_disjoint (G₁:=G₁) (G₂:=G) hDisj hG)
  simpa [hGrew] using hBT'''

-- Select Frame Lemma (Right Append)

theorem BuffersTyped_select_frame_right
    {G : GEnv} {D : DEnv} {G₁ : GEnv} {D₁ : DEnv} {bufs : Buffers}
    {e : Endpoint} {target : Role} {bs : List (String × LocalType)} {ℓ : String}
    {L : LocalType} {selectEdge : Edge} :
    lookupG G e = some (.select target bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    selectEdge = { sid := e.sid, sender := e.role, receiver := target } →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    BuffersTyped (G₁ ++ updateG G e L)
      (updateD (D₁ ++ D) selectEdge (lookupD D selectEdge ++ [.string]))
      (enqueueBuf bufs selectEdge (.string ℓ)) := by
  intro hG hFind hEdge hDisj hCons hBT
  subst hEdge
  have hv' : HasTypeVal (G₁ ++ G) (.string ℓ) .string :=
    HasTypeVal_mono G (G₁ ++ G) (.string ℓ) .string (HasTypeVal.string ℓ) (by
      intro ep L' hLookup
      have hNone : lookupG G₁ ep = none := lookupG_none_of_disjoint hDisj hLookup
      have hEq := lookupG_append_right (G₁:=G₁) (G₂:=G) (e:=ep) hNone
      simpa [hEq] using hLookup)
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .select target bs, hG, rfl⟩
  have hDisj' : DisjointG G G₁ := DisjointG_symm hDisj
  have hD1none : D₁.find? { sid := e.sid, sender := e.role, receiver := target } = none :=
    lookupD_none_of_disjointG (G₁:=G) (G₂:=G₁) (D₂:=D₁) hDisj' hCons hSid
  have hEq :
      lookupD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target } =
        lookupD D { sid := e.sid, sender := e.role, receiver := target } :=
    lookupD_append_right (D₁:=D₁) (D₂:=D) (e:={ sid := e.sid, sender := e.role, receiver := target }) hD1none
  have hBT' :
      BuffersTyped (G₁ ++ G)
        (updateD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target } ++ [.string]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } (.string ℓ)) :=
    BuffersTyped_enqueue (G:=G₁ ++ G) (D:=D₁ ++ D) (bufs:=bufs)
      (e:={ sid := e.sid, sender := e.role, receiver := target }) (v:=.string ℓ) (T:=.string) hBT hv'
  have hBT'' :
      BuffersTyped (G₁ ++ G)
        (updateD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target }
/- ## Structured Block 8 -/
          (lookupD D { sid := e.sid, sender := e.role, receiver := target } ++ [.string]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } (.string ℓ)) := by
    simpa [hEq] using hBT'
  -- # Lift Along `updateG` and Reassociate
  have hBT''' :
      BuffersTyped (updateG (G₁ ++ G) e L)
        (updateD (D₁ ++ D) { sid := e.sid, sender := e.role, receiver := target }
          (lookupD D { sid := e.sid, sender := e.role, receiver := target } ++ [.string]))
        (enqueueBuf bufs { sid := e.sid, sender := e.role, receiver := target } (.string ℓ)) :=
    BuffersTyped_updateG_weaken (e:=e) (L:=L) hBT''
  have hGrew :
      updateG (G₁ ++ G) e L = G₁ ++ updateG G e L :=
    updateG_append_left (G₁:=G₁) (G₂:=G) (e:=e) (L:=L)
      (lookupG_none_of_disjoint (G₁:=G₁) (G₂:=G) hDisj hG)
  simpa [hGrew] using hBT'''

-- Branch Frame Lemma (Right Append)

theorem BuffersTyped_branch_frame_right
    {G : GEnv} {D : DEnv} {G₁ : GEnv} {D₁ : DEnv} {bufs : Buffers}
    {e : Endpoint} {source : Role} {bs : List (String × LocalType)} {ℓ : String}
    {L : LocalType} {vs : List Value} {branchEdge : Edge} :
    lookupG G e = some (.branch source bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    lookupBuf bufs branchEdge = .string ℓ :: vs →
    (lookupD D branchEdge).head? = some .string →
    branchEdge = { sid := e.sid, sender := source, receiver := e.role } →
    DisjointG G₁ G →
    DConsistent G₁ D₁ →
    BuffersTyped (G₁ ++ G) (D₁ ++ D) bufs →
    BuffersTyped (G₁ ++ updateG G e L)
      (updateD (D₁ ++ D) branchEdge (lookupD D branchEdge).tail)
      (updateBuf bufs branchEdge vs) := by
  intro hG hFind hBuf hHead hEdge hDisj hCons hBT
  subst hEdge
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .branch source bs, hG, rfl⟩
  have hDisj' : DisjointG G G₁ := DisjointG_symm hDisj
  have hD1none : D₁.find? { sid := e.sid, sender := source, receiver := e.role } = none :=
    lookupD_none_of_disjointG (G₁:=G) (G₂:=G₁) (D₂:=D₁) hDisj' hCons hSid
  have hEq :
      lookupD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role } =
        lookupD D { sid := e.sid, sender := source, receiver := e.role } :=
    lookupD_append_right (D₁:=D₁) (D₂:=D) (e:={ sid := e.sid, sender := source, receiver := e.role }) hD1none
  have hHead' :
      (lookupD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }).head? = some .string := by
    simpa [hEq] using hHead
  have hBT' :
      BuffersTyped (G₁ ++ G)
        (updateD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) :=
    BuffersTyped_dequeue (G:=G₁ ++ G) (D:=D₁ ++ D) (bufs:=bufs)
      (recvEdge:={ sid := e.sid, sender := source, receiver := e.role }) (v:=.string ℓ) (vs:=vs) (T:=.string)
      hBT hBuf hHead'
/- ## Structured Block 9 -/
  have hBT'' :
      BuffersTyped (G₁ ++ G)
        (updateD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) := by
    simpa [hEq] using hBT'
  -- # Lift Along `updateG` and Reassociate
  have hBT''' :
      BuffersTyped (updateG (G₁ ++ G) e L)
        (updateD (D₁ ++ D) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail)
        (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs) :=
    BuffersTyped_updateG_weaken (e:=e) (L:=L) hBT''
  have hGrew :
      updateG (G₁ ++ G) e L = G₁ ++ updateG G e L :=
    updateG_append_left (G₁:=G₁) (G₂:=G) (e:=e) (L:=L)
      (lookupG_none_of_disjoint (G₁:=G₁) (G₂:=G) hDisj hG)
  simpa [hGrew] using hBT'''

set_option maxHeartbeats 2000000 in

end
