import Protocol.Typing.Compatibility

/-! # Protocol.Typing.MergeLemmas

Merge lemmas and branch processing for typing.
-/

/-! ## Merge Lemmas -/

/-- DisjointG: endpoints from the right are absent on the left. -/
private theorem lookupG_none_of_disjoint {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂)
    {e : Endpoint} {L : LocalType} (hLookup : lookupG G₂ e = some L) :
    lookupG G₁ e = none := by
  -- Use disjoint session IDs to rule out any left lookup.
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
          have hInter' := hInter
          simp [hEmpty] at hInter'
        exact this.elim

/-- DisjointG: a session in the left is not in the right. -/
private theorem sid_not_in_right_of_left {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂)
    {s : SessionId} (hIn : s ∈ SessionsOf G₁) : s ∉ SessionsOf G₂ := by
  -- Turn disjointness into a contradiction on the intersection.
  intro hIn2
  have hInter : s ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn, hIn2⟩
  have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = ∅ := hDisj
  have : s ∈ (∅ : Set SessionId) := by
    have hInter' := hInter
    simp [hEmpty] at hInter'
  exact this.elim

/-- DConsistent: a missing session in G implies no edge entry in D. -/
private theorem DEnv_find_none_of_notin_sessions {G : GEnv} {D : DEnv} (hCons : DConsistent G D)
    {e : Edge} (hNot : e.sid ∉ SessionsOf G) : D.find? e = none := by
  -- If there were an entry, it would witness membership in SessionsOfD.
  by_cases hNone : D.find? e = none
  · exact hNone
  · cases hSome : D.find? e with
    | none => exact (hNone hSome).elim
    | some ts =>
        have hSid : e.sid ∈ SessionsOfD D := ⟨e, ts, hSome, rfl⟩
        have hSidG : e.sid ∈ SessionsOf G := hCons hSid
        exact (hNot hSidG).elim

/-- DisjointD: a left edge entry forbids a right entry at the same edge. -/
private theorem DEnv_find_none_of_disjoint_left {D₁ D₂ : DEnv} (hDisj : DisjointD D₁ D₂)
    {e : Edge} {ts : List ValType} (hFind : D₁.find? e = some ts) : D₂.find? e = none := by
  -- Use disjoint session IDs to rule out any right entry.
  have hSid : e.sid ∈ SessionsOfD D₁ := ⟨e, ts, hFind, rfl⟩
  have hNot : e.sid ∉ SessionsOfD D₂ := by
    intro hIn2
    have hInter : e.sid ∈ SessionsOfD D₁ ∩ SessionsOfD D₂ := ⟨hSid, hIn2⟩
    have hEmpty : SessionsOfD D₁ ∩ SessionsOfD D₂ = ∅ := hDisj
    have : e.sid ∈ (∅ : Set SessionId) := by
      have hInter' := hInter
      simp [hEmpty] at hInter'
    exact this.elim
  by_cases hNone : D₂.find? e = none
  · exact hNone
  · cases hSome : D₂.find? e with
    | none => exact (hNone hSome).elim
    | some ts₂ =>
        have hSid₂ : e.sid ∈ SessionsOfD D₂ := ⟨e, ts₂, hSome, rfl⟩
        exact (hNot hSid₂).elim

/-- BufferTyped is preserved when extending GEnv with compatible endpoints. -/
private theorem BufferTyped_weakenG {G G' : GEnv} {D : DEnv} {bufs : Buffers} {e : Edge} :
    BufferTyped G D bufs e →
    (∀ ep L, lookupG G ep = some L → lookupG G' ep = some L) →
    BufferTyped G' D bufs e := by
  -- Lift each value typing using HasTypeVal_mono.
  intro hBT hMono
  rcases hBT with ⟨hLen, hTyping⟩
  refine ⟨hLen, ?_⟩
  intro i hi
  exact HasTypeVal_mono G G' _ _ (hTyping i hi) hMono

/-- BufferTyped is stable under rewriting the trace at a fixed edge. -/
private theorem BufferTyped_rewriteD {G : GEnv} {D D' : DEnv} {bufs : Buffers} {e : Edge} :
    lookupD D' e = lookupD D e →
    BufferTyped G D bufs e →
    BufferTyped G D' bufs e := by
  -- Rewrite the trace in the length/typing witnesses.
  intro hEq hBT
  rcases hBT with ⟨hLen, hTyping⟩
  refine ⟨?_, ?_⟩
  · simpa [hEq] using hLen
  · intro i hi
    simpa [hEq] using hTyping i hi

/-- BufferTyped lifts from the left GEnv into the merged environment. -/
private theorem BufferTyped_lift_left {G₁ G₂ : GEnv} {D : DEnv} {bufs : Buffers} {e : Edge} :
    BufferTyped G₁ D bufs e →
    BufferTyped (G₁ ++ G₂) D bufs e := by
  -- Use lookupG_append_left to lift HasTypeVal.
  intro hBT
  apply BufferTyped_weakenG hBT
  intro ep L hLookup
  exact lookupG_append_left (G₁:=G₁) (G₂:=G₂) hLookup

/-- BufferTyped lifts from the right GEnv into the merged environment. -/
private theorem BufferTyped_lift_right {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂)
    {D : DEnv} {bufs : Buffers} {e : Edge} :
    BufferTyped G₂ D bufs e →
    BufferTyped (G₁ ++ G₂) D bufs e := by
  -- Use disjointness to route lookups through the right.
  intro hBT
  apply BufferTyped_weakenG hBT
  intro ep L hLookup
  have hNone : lookupG G₁ ep = none := lookupG_none_of_disjoint hDisj hLookup
  have hEq := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=ep) hNone
  simpa [hEq] using hLookup

/-- StoreTyped merges when SEnv is split and endpoints are disjoint. -/
theorem StoreTyped_merge {G₁ G₂ : GEnv} {S₁ S₂ : SEnv} {store : VarStore}
    (hDisj : DisjointG G₁ G₂) :
    StoreTyped G₁ S₁ store →
    StoreTyped G₂ S₂ store →
    StoreTyped (G₁ ++ G₂) (S₁ ++ S₂) store := by
  -- Split on where the variable is stored, then lift HasTypeVal.
  intro hST1 hST2 x v T hStore hLookup
  by_cases hLeft : lookupSEnv S₁ x = none
  · have hLookup' : lookupSEnv S₂ x = some T := by
      simpa [lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hLeft] using hLookup
    have hVal : HasTypeVal G₂ v T := hST2 x v T hStore hLookup'
    exact HasTypeVal_prepend G₁ G₂ v T hVal (by
      intro ep L hLookup
      have hNone := lookupG_none_of_disjoint (G₁:=G₁) (G₂:=G₂) hDisj hLookup
      simpa [lookupG] using hNone)
  · cases hSome : lookupSEnv S₁ x with
    | none => exact (hLeft hSome).elim
    | some T₁ =>
        have hEq : T₁ = T := by
          have hLeft' : lookupSEnv (S₁ ++ S₂) x = some T₁ :=
            lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) hSome
          have : some T₁ = some T := by simpa [hLeft'] using hLookup
          exact Option.some.inj this
        have hVal : HasTypeVal G₁ v T := by
          simpa [hEq] using (hST1 x v T₁ hStore hSome)
        exact HasTypeVal_mono G₁ (G₁ ++ G₂) v T hVal (by
          intro ep L hL; exact lookupG_append_left (G₁:=G₁) (G₂:=G₂) hL)

/-- BuffersTyped merges when traces are disjoint by session. -/
theorem BuffersTyped_merge {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} {bufs : Buffers}
    (hDisjG : DisjointG G₁ G₂) (hDisjD : DisjointD D₁ D₂) :
    BuffersTyped G₁ D₁ bufs →
    BuffersTyped G₂ D₂ bufs →
    BuffersTyped (G₁ ++ G₂) (D₁ ++ D₂) bufs := by
  -- Split on whether the left environment provides the trace.
  intro hBT1 hBT2 e
  by_cases hNone : D₁.find? e = none
  · have hEq : lookupD (D₁ ++ D₂) e = lookupD D₂ e :=
      lookupD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hNone
    have hBT2' : BufferTyped (G₁ ++ G₂) D₂ bufs e := BufferTyped_lift_right hDisjG (hBT2 e)
    exact BufferTyped_rewriteD hEq hBT2'
  · cases hSome : D₁.find? e with
    | none => exact (hNone hSome).elim
    | some ts =>
        have hD2none : D₂.find? e = none := DEnv_find_none_of_disjoint_left hDisjD hSome
        have hEq : lookupD (D₁ ++ D₂) e = lookupD D₁ e :=
          lookupD_append_left_of_right_none (D₁:=D₁) (D₂:=D₂) (e:=e) hD2none
        have hBT1' : BufferTyped (G₁ ++ G₂) D₁ bufs e := BufferTyped_lift_left (hBT1 e)
        exact BufferTyped_rewriteD hEq hBT1'

/-- EdgeCoherent: receiver from the left implies left coherence is enough. -/
private theorem EdgeCoherent_merge_left {G₁ G₂ : GEnv} {D₁ D₂ : DEnv}
    (hC₁ : Coherent G₁ D₁) (hDisjG : DisjointG G₁ G₂) (hCons₂ : DConsistent G₂ D₂)
    {e : Edge} {Lrecv : LocalType}
    (hGrecvL : lookupG G₁ { sid := e.sid, role := e.receiver } = some Lrecv) :
    ∃ Lsender,
      lookupG (G₁ ++ G₂) { sid := e.sid, role := e.sender } = some Lsender ∧
      (Consume e.sender Lrecv (lookupD (D₁ ++ D₂) e)).isSome := by
  -- Use left coherence and lift lookups/trace into the merged environment.
  let senderEp : Endpoint := { sid := e.sid, role := e.sender }
  have hCoh := hC₁ e Lrecv hGrecvL
  rcases hCoh with ⟨Lsender, hGsender, hConsume⟩
  have hSid : e.sid ∈ SessionsOf G₁ := ⟨senderEp, Lsender, hGsender, rfl⟩
  have hNot : e.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisjG hSid
  have hD2none : D₂.find? e = none := DEnv_find_none_of_notin_sessions (G:=G₂) (D:=D₂) hCons₂ hNot
  have hEq : lookupD (D₁ ++ D₂) e = lookupD D₁ e :=
    lookupD_append_left_of_right_none (D₁:=D₁) (D₂:=D₂) (e:=e) hD2none
  have hGsender' : lookupG (G₁ ++ G₂) senderEp = some Lsender :=
    lookupG_append_left (G₁:=G₁) (G₂:=G₂) hGsender
  refine ⟨Lsender, hGsender', ?_⟩
  simpa [hEq] using hConsume

/-- EdgeCoherent: receiver from the right implies right coherence is enough. -/
private theorem EdgeCoherent_merge_right {G₁ G₂ : GEnv} {D₁ D₂ : DEnv}
    (hC₂ : Coherent G₂ D₂) (hDisjG : DisjointG G₁ G₂) (hCons₁ : DConsistent G₁ D₁)
    {e : Edge} {Lrecv : LocalType}
    (hGrecvR : lookupG G₂ { sid := e.sid, role := e.receiver } = some Lrecv) :
    ∃ Lsender,
      lookupG (G₁ ++ G₂) { sid := e.sid, role := e.sender } = some Lsender ∧
      (Consume e.sender Lrecv (lookupD (D₁ ++ D₂) e)).isSome := by
  -- Use right coherence and lift lookups/trace into the merged environment.
  let senderEp : Endpoint := { sid := e.sid, role := e.sender }
  have hCoh := hC₂ e Lrecv hGrecvR
  rcases hCoh with ⟨Lsender, hGsender, hConsume⟩
  have hSid : e.sid ∈ SessionsOf G₂ := ⟨senderEp, Lsender, hGsender, rfl⟩
  have hDisjG' : DisjointG G₂ G₁ := DisjointG_symm hDisjG
  have hNot : e.sid ∉ SessionsOf G₁ := sid_not_in_right_of_left hDisjG' hSid
  have hD1none : D₁.find? e = none := DEnv_find_none_of_notin_sessions (G:=G₁) (D:=D₁) hCons₁ hNot
  have hEq : lookupD (D₁ ++ D₂) e = lookupD D₂ e :=
    lookupD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hD1none
  have hNoneSender : lookupG G₁ senderEp = none := lookupG_none_of_disjoint hDisjG hGsender
  have hEqSender := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=senderEp) hNoneSender
  have hGsender' : lookupG (G₁ ++ G₂) senderEp = some Lsender := by
    simpa [hEqSender] using hGsender
  refine ⟨Lsender, hGsender', ?_⟩
  simpa [hEq] using hConsume

/-- Coherence merges when sessions are disjoint and traces follow their owners. -/
theorem Coherent_merge {G₁ G₂ : GEnv} {D₁ D₂ : DEnv}
    (hC₁ : Coherent G₁ D₁) (hC₂ : Coherent G₂ D₂)
    (hDisjG : DisjointG G₁ G₂) (hCons₁ : DConsistent G₁ D₁) (hCons₂ : DConsistent G₂ D₂) :
    Coherent (G₁ ++ G₂) (D₁ ++ D₂) := by
  -- Split on which side provides the receiver endpoint.
  intro e Lrecv hGrecv
  have hInv := lookupG_append_inv (G₁:=G₁) (G₂:=G₂)
    (e:={ sid := e.sid, role := e.receiver }) hGrecv
  cases hInv with
  | inl hLeft =>
      exact EdgeCoherent_merge_left hC₁ hDisjG hCons₂ hLeft
  | inr hRight =>
      exact EdgeCoherent_merge_right hC₂ hDisjG hCons₁ hRight.2

/-- Updating an existing endpoint preserves the set of sessions. -/
theorem SessionsOf_updateG_eq {G : GEnv} {e : Endpoint} {L L' : LocalType}
    (hLookup : lookupG G e = some L') :
    SessionsOf (updateG G e L) = SessionsOf G := by
  ext s; constructor
  · intro hs
    rcases hs with ⟨e', L'', hLookup', hSid⟩
    by_cases heq : e' = e
    · cases heq
      exact ⟨e, L', hLookup, hSid⟩
    · have hLookup'' : lookupG G e' = some L'' := by
        simpa [lookupG_update_neq _ _ _ _ (Ne.symm heq)] using hLookup'
      exact ⟨e', L'', hLookup'', hSid⟩
  · intro hs
    rcases hs with ⟨e', L'', hLookup', hSid⟩
    by_cases heq : e' = e
    · cases heq
      exact ⟨e, L, by simpa using (lookupG_update_eq G e L), hSid⟩
    · have hLookup'' : lookupG (updateG G e L) e' = some L'' := by
        simpa [lookupG_update_neq _ _ _ _ (Ne.symm heq)] using hLookup'
      exact ⟨e', L'', hLookup'', hSid⟩

/-- Sessions only shrink under TypedStep (no new sessions introduced). -/
theorem SessionsOf_subset_of_TypedStep {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    SessionsOf G' ⊆ SessionsOf G := by
  intro hTS
  induction hTS with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
        SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.send target T L) hG
      simp [hGout, hEq]
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
        SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.recv source T L) hG
      simp [hGout, hEq]
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
        SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.select target bs) hG
      simp [hGout, hEq]
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
        SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.branch source bs) hG
      simp [hGout, hEq]
  | assign =>
      simp
  | seq_step _ ih =>
      exact ih
  | seq_skip =>
      simp
  | par_left split hSlen hGlen hTS hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P P' Q G D₁ D₂ G₁' D₁' S₁' nS nG
      intro s hs
      have hIn : s ∈ SessionsOf G := ih hs
      simpa [split.hG] using hIn
  | par_right split hSlen hGlen hTS hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P Q Q' G D₁ D₂ G₂' D₂' S₂' nS nG
      intro s hs
      have hIn : s ∈ SessionsOf G := ih hs
      simpa [split.hG] using hIn
  | par_skip_left =>
      simp
  | par_skip_right =>
      simp

/- D sessions remain within original sessions plus the current G sessions. -/
