import Protocol.Typing.Compatibility

/-!
# MPST Process Typing

This module defines the typing rules for MPST processes.

## Key Judgments

- `HasTypeProcN n S G D P`: Process P is well-typed under environments S, G, D
  with maximum session ID n
- `WTConfigN n S G D C`: Configuration C is well-typed

## Typing Rules

- **Skip**: `⊢ skip` (always well-typed)
- **Seq**: `⊢ P` and `⊢ Q` implies `⊢ seq P Q`
- **Par**: `⊢ P` and `⊢ Q` with split contexts implies `⊢ par P Q`
- **Send**: If `S[k] = chan (sid, r)` and `G[sid,r] = !q(T).L` and `S[x] = T`,
            then `⊢ send k x` and G[sid,r] ↦ L
- **Recv**: If `S[k] = chan (sid, r)` and `G[sid,r] = ?p(T).L`,
            then `⊢ recv k x` and G[sid,r] ↦ L, S[x] ↦ T
- **Select**: If `S[k] = chan (sid, r)` and `G[sid,r] = ⊕q{ℓᵢ: Lᵢ}`,
              then `⊢ select k ℓⱼ` and G[sid,r] ↦ Lⱼ
- **Branch**: If `S[k] = chan (sid, r)` and `G[sid,r] = &p{ℓᵢ: Lᵢ}`,
              then `⊢ branch k [(ℓᵢ, Pᵢ)]` if each Pᵢ is typed under Lᵢ
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 5000000

open scoped Classical

section

theorem SessionsOfD_subset_of_TypedStep {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    SessionsOfD D' ⊆ SessionsOfD D ∪ SessionsOf G := by
  intro hTS
  induction hTS with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      intro s hs
      have hs' : s ∈ SessionsOfD (appendD D sendEdge T) := by
        simpa [hDout] using hs
      have hSub := SessionsOfD_updateD_subset (D:=D) (e:=sendEdge)
        (ts:=lookupD D sendEdge ++ [T]) hs'
      cases hSub with
      | inl hIn => exact Or.inl hIn
      | inr hIn =>
          have hSidE : e.sid ∈ SessionsOf G := ⟨e, .send target T L, hG, rfl⟩
          have hSid : sendEdge.sid ∈ SessionsOf G := by
            simpa [hEdge] using hSidE
          have hEq : s = sendEdge.sid := by
            simpa using hIn
          exact Or.inr (by simpa [hEq] using hSid)
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      intro s hs
      have hs' : s ∈ SessionsOfD (updateD D recvEdge (lookupD D recvEdge).tail) := by
        simpa [hDout] using hs
      have hSub := SessionsOfD_updateD_subset (D:=D) (e:=recvEdge)
        (ts:=(lookupD D recvEdge).tail) hs'
      cases hSub with
      | inl hIn => exact Or.inl hIn
      | inr hIn =>
          have hSidE : e.sid ∈ SessionsOf G := ⟨e, .recv source T L, hG, rfl⟩
          have hSid : recvEdge.sid ∈ SessionsOf G := by
            simpa [hEdge] using hSidE
          have hEq : s = recvEdge.sid := by
            simpa using hIn
          exact Or.inr (by simpa [hEq] using hSid)
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      intro s hs
      have hs' : s ∈ SessionsOfD (appendD D selectEdge .string) := by
        simpa [hDout] using hs
      have hSub := SessionsOfD_updateD_subset (D:=D) (e:=selectEdge)
        (ts:=lookupD D selectEdge ++ [.string]) hs'
      cases hSub with
      | inl hIn => exact Or.inl hIn
      | inr hIn =>
          have hSidE : e.sid ∈ SessionsOf G := ⟨e, .select target bs, hG, rfl⟩
          have hSid : selectEdge.sid ∈ SessionsOf G := by
            simpa [hEdge] using hSidE
          have hEq : s = selectEdge.sid := by
            simpa using hIn
          exact Or.inr (by simpa [hEq] using hSid)
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      intro s hs
      have hs' : s ∈ SessionsOfD (updateD D branchEdge (lookupD D branchEdge).tail) := by
        simpa [hDout] using hs
      have hSub := SessionsOfD_updateD_subset (D:=D) (e:=branchEdge)
        (ts:=(lookupD D branchEdge).tail) hs'
      cases hSub with
      | inl hIn => exact Or.inl hIn
      | inr hIn =>
          have hSidE : e.sid ∈ SessionsOf G := ⟨e, .branch source bs, hG, rfl⟩
          have hSid : branchEdge.sid ∈ SessionsOf G := by
            simpa [hEdge] using hSidE
          have hEq : s = branchEdge.sid := by
            simpa using hIn
          exact Or.inr (by simpa [hEq] using hSid)
  | assign =>
      simp
  | seq_step _ ih =>
      exact ih
  | seq_skip =>
      simp
  | par_left split hSlen hGlen hTS hDisjG hDisjD hDisjS ih =>
      exact ih
  | par_right split hSlen hGlen hTS hDisjG hDisjD hDisjS ih =>
      exact ih
  | par_skip_left =>
      simp
  | par_skip_right =>
      simp

theorem lookupD_none_of_disjointG {G₁ G₂ : GEnv} {D₂ : DEnv} {e : Edge} :
    DisjointG G₁ G₂ →
    DConsistent G₂ D₂ →
    e.sid ∈ SessionsOf G₁ →
    D₂.find? e = none := by
  intro hDisj hCons hIn1
  by_contra hSome
  cases hFind : D₂.find? e with
  | none =>
      exact (hSome hFind)
  | some ts =>
      have hSid : e.sid ∈ SessionsOfD D₂ := ⟨e, ts, hFind, rfl⟩
      have hSid2 : e.sid ∈ SessionsOf G₂ := hCons hSid
      have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn1, hSid2⟩
      have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := hDisj
      have : e.sid ∈ (∅ : Set SessionId) := by
        simpa [hEmpty] using hInter
      exact this.elim

/-- Coherence splits to the right portion of G/D when sessions are disjoint. -/
theorem Coherent_split_right {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    Coherent (G₁ ++ G₂) (D₁ ++ D₂) →
    DisjointG G₁ G₂ →
    DConsistent G₁ D₁ →
    Coherent G₂ D₂ := by
  intro hCoh hDisj hCons e hActive Lrecv hGrecv
  -- endpoints are in G₂; ensure G₁ has none for this session
  have hSid : e.sid ∈ SessionsOf G₂ := ⟨{ sid := e.sid, role := e.receiver }, Lrecv, hGrecv, rfl⟩
  have hG1none_sender : lookupG G₁ { sid := e.sid, role := e.sender } = none := by
    apply lookupG_none_of_not_session
    intro hIn
    have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn, hSid⟩
    have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := hDisj
    have hContra : e.sid ∈ (∅ : Set SessionId) := by
      simpa [hEmpty] using hInter
    exact hContra.elim
  have hG1none_recv : lookupG G₁ { sid := e.sid, role := e.receiver } = none := by
    apply lookupG_none_of_not_session
    intro hIn
    have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn, hSid⟩
    have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := hDisj
    have hContra : e.sid ∈ (∅ : Set SessionId) := by
      simpa [hEmpty] using hInter
    exact hContra.elim
  have hGrecv' : lookupG (G₁ ++ G₂) { sid := e.sid, role := e.receiver } = some Lrecv := by
    simpa [lookupG_append_right hG1none_recv] using hGrecv
  -- D₁ has no entries for this session
  have hDisjSym : DisjointG G₂ G₁ := by
    unfold DisjointG at *
    unfold GEnvDisjoint at hDisj
    unfold GEnvDisjoint
    simpa [Set.inter_comm] using hDisj
  have hD1none : D₁.find? e = none :=
    lookupD_none_of_disjointG (G₁:=G₂) (G₂:=G₁) (D₂:=D₁) hDisjSym hCons hSid
  have hTraceEq : lookupD (D₁ ++ D₂) e = lookupD D₂ e :=
    lookupD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hD1none
  have hActive' : ActiveEdge (G₁ ++ G₂) e := by
    have hSenderMerged : (lookupG (G₁ ++ G₂) { sid := e.sid, role := e.sender }).isSome = true := by
      cases hActive with
      | intro hSender _ =>
          simpa [lookupG_append_right hG1none_sender] using hSender
    have hRecvMerged : (lookupG (G₁ ++ G₂) { sid := e.sid, role := e.receiver }).isSome = true := by
      simp [hGrecv']
    exact ⟨hSenderMerged, hRecvMerged⟩
  have hCohEdge := hCoh e hActive' Lrecv hGrecv'
  rcases hCohEdge with ⟨Lsender, hGsenderMerged, hConsume⟩
  have hSenderEq := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:={ sid := e.sid, role := e.sender }) hG1none_sender
  have hGsenderG2 : lookupG G₂ { sid := e.sid, role := e.sender } = some Lsender := by
    simpa [hSenderEq] using hGsenderMerged
  refine ⟨Lsender, hGsenderG2, ?_⟩
  simpa [hTraceEq] using hConsume

/-- HasTypeVal weakening: values typed in empty environment are typed in any environment. -/
theorem HasTypeVal_weaken {v : Value} {T : ValType} {G : GEnv} :
    HasTypeVal ∅ v T → HasTypeVal G v T := by
  intro hv
  cases hv with
  | unit => exact HasTypeVal.unit
  | bool b => exact HasTypeVal.bool b
  | nat n => exact HasTypeVal.nat n
  | string s => exact HasTypeVal.string s
  | prod h₁ h₂ =>
    exact HasTypeVal.prod (HasTypeVal_weaken h₁) (HasTypeVal_weaken h₂)
  | chan h =>
    -- Channel in empty environment is impossible
    simp [lookupG] at h

/-- HasTypeVal weakening for updateG: if the value doesn't depend on the updated endpoint.
    For non-channel values, this is always true. For channel values, we need the channel
    to be a different endpoint. -/
theorem HasTypeVal_updateG_weaken {G : GEnv} {e : Endpoint} {L : LocalType} {v : Value} {T : ValType} :
    HasTypeVal G v T →
    HasTypeVal (updateG G e L) v T := by
  intro hv
  cases hv with
  | unit => exact HasTypeVal.unit
  | bool b => exact HasTypeVal.bool b
  | nat n => exact HasTypeVal.nat n
  | string s => exact HasTypeVal.string s
  | prod h₁ h₂ =>
    exact HasTypeVal.prod (HasTypeVal_updateG_weaken h₁) (HasTypeVal_updateG_weaken h₂)
  | chan h =>
    -- Channel case: need to show lookupG (updateG G e L) e' = some L''
    -- e' and L' are implicit arguments from the chan constructor
    rename_i e' L'
    by_cases heq : e' = e
    · -- e' = e: the channel endpoint was updated
      -- After update, lookupG (updateG G e L) e = some L
      rw [heq]
      apply HasTypeVal.chan
      apply lookupG_update_eq
    · -- e' ≠ e: use update_neq lemma
      apply HasTypeVal.chan
      rw [lookupG_update_neq G e e' L (Ne.symm heq)]
      exact h

/-- For the send case: StoreTyped is trivially preserved because store is unchanged.
    We just need to weaken G, which works for all values (with caveat for sent channel). -/
theorem StoreTyped_send_preserved {G : GEnv} {S : SEnv} {store : VarStore} {e : Endpoint} {L : LocalType} :
    StoreTyped G S store →
    StoreTyped (updateG G e L) S store := by
  intro hST
  unfold StoreTyped at hST ⊢
  intro x v T hStore hS
  have hVal := hST x v T hStore hS
  exact HasTypeVal_updateG_weaken hVal

/-- For the assign case: StoreTyped with updated S and updated store.
    The value v has type T in G (from TypedStep.assign premise). After update,
    store[x] = v and S[x] = T match. -/
theorem StoreTyped_assign_preserved {G : GEnv} {S : SEnv} {store : VarStore} {x : Var} {v : Value} {T : ValType} :
    StoreTyped G S store →
    HasTypeVal G v T →
    StoreTyped G (updateSEnv S x T) (updateStr store x v) := by
  intro hST hv
  unfold StoreTyped at hST ⊢
  intro y w T' hStoreY hSY
  by_cases heq : y = x
  · -- y = x case: use the new typing
    subst heq
    rw [lookupSEnv_update_eq] at hSY
    simp at hSY
    cases hSY
    rw [lookupStr_update_eq] at hStoreY
    simp at hStoreY
    cases hStoreY
    exact hv
  · -- y ≠ x case: use original typing from unchanged variables
    rw [lookupSEnv_update_neq S x y T (Ne.symm heq)] at hSY
    rw [lookupStr_update_neq store x y v (Ne.symm heq)] at hStoreY
    exact hST y w T' hStoreY hSY

/-- BuffersTyped is preserved when updating G: all values in buffers remain well-typed
    because HasTypeVal_updateG_weaken preserves typing for all values. -/
theorem BuffersTyped_updateG_weaken {G : GEnv} {D : DEnv} {bufs : Buffers} {e : Endpoint} {L : LocalType} :
    BuffersTyped G D bufs →
    BuffersTyped (updateG G e L) D bufs := by
  intro hBT edge
  have hOrig := hBT edge
  unfold BufferTyped at hOrig ⊢
  obtain ⟨hLen, hTyping⟩ := hOrig
  refine ⟨hLen, ?_⟩
  intro i hi
  have hVal := hTyping i hi
  exact HasTypeVal_updateG_weaken hVal

/-- For the recv case: StoreTyped is preserved when receiving a value into the store.
    The received value has type T in G, so it has type T in (updateG G e L) by weakening. -/
theorem StoreTyped_recv_preserved {G : GEnv} {S : SEnv} {store : VarStore} {e : Endpoint} {L : LocalType}
    {x : Var} {v : Value} {T : ValType} :
    StoreTyped G S store →
    HasTypeVal G v T →
    StoreTyped (updateG G e L) (updateSEnv S x T) (updateStr store x v) := by
  intro hST hv
  unfold StoreTyped at hST ⊢
  intro y w T' hStoreY hSY
  by_cases heq : y = x
  · -- y = x case: use the received value's typing
    subst heq
    rw [lookupSEnv_update_eq] at hSY
    simp at hSY
    cases hSY
    rw [lookupStr_update_eq] at hStoreY
    simp at hStoreY
    cases hStoreY
    exact HasTypeVal_updateG_weaken hv
  · -- y ≠ x case: use original typing with G weakening
    rw [lookupSEnv_update_neq S x y T (Ne.symm heq)] at hSY
    rw [lookupStr_update_neq store x y v (Ne.symm heq)] at hStoreY
    have hValOrig := hST y w T' hStoreY hSY
    exact HasTypeVal_updateG_weaken hValOrig

/-- BuffersTyped is preserved when enqueuing a well-typed value.

    NOTE: This lemma is proven in Protocol.Preservation. It's duplicated here to avoid
    circular dependencies, but should be moved to a shared module. -/
theorem BuffersTyped_enqueue {G : GEnv} {D : DEnv} {bufs : Buffers}
    {e : Edge} {v : Value} {T : ValType}
    (hBT : BuffersTyped G D bufs)
    (hv : HasTypeVal G v T) :
    BuffersTyped G (updateD D e (lookupD D e ++ [T])) (enqueueBuf bufs e v) := by
  intro a
  unfold BufferTyped
  by_cases ha : a = e
  · -- a = e: the edge we're enqueuing on
    have hOrig := hBT e
    unfold BufferTyped at hOrig
    obtain ⟨hLen, hTyping⟩ := hOrig
    subst ha
    -- The buffer becomes: lookupBuf bufs a ++ [v]
    -- The trace becomes: lookupD D a ++ [T]
    simp only [enqueueBuf, lookupBuf_update_eq, lookupD_update_eq]
    have hBufUpdate :
        lookupBuf (updateBuf bufs a (lookupBuf bufs a ++ [v])) a = (lookupBuf bufs a ++ [v]) := by
      simp
    have hTraceUpdate :
        lookupD (updateD D a (lookupD D a ++ [T])) a = (lookupD D a ++ [T]) := by
      simp [lookupD_update_eq]
    -- New lengths are equal
    have hNewLen : (lookupBuf bufs a ++ [v]).length = (lookupD D a ++ [T]).length := by
      simp [List.length_append]
      omega
    refine ⟨hNewLen, ?_⟩
    intro i hi
    -- Case split: is i < original length or i = original length?
    by_cases hOld : i < (lookupBuf bufs a).length
    · -- i < old length: use original typing
      have hTrace : i < (lookupD D a).length := hLen ▸ hOld
      have hiTrace : i < (lookupD D a ++ [T]).length := by
        simpa [hNewLen] using hi
      have hBufGet : (lookupBuf bufs a ++ [v])[i] = (lookupBuf bufs a)[i] := by
        exact List.getElem_append_left (as := lookupBuf bufs a) (bs := [v]) hOld (h' := hi)
      have hTraceGet : (lookupD D a ++ [T])[i] = (lookupD D a)[i] := by
        exact List.getElem_append_left (as := lookupD D a) (bs := [T]) hTrace (h' := hiTrace)
      have hGoal : HasTypeVal G (lookupBuf bufs a)[i] (lookupD D a)[i] := by
        convert hTyping i hOld using 2
      have hGoal' : HasTypeVal G (lookupBuf bufs a ++ [v])[i] (lookupD D a ++ [T])[i] := by
        simpa [hBufGet, hTraceGet] using hGoal
      simpa [hBufUpdate, hTraceUpdate] using hGoal'
    · -- i >= old length: must be the newly added element
      have hLe : (lookupBuf bufs a).length ≤ i := Nat.le_of_not_lt hOld
      have hLe' : i ≤ (lookupBuf bufs a).length := by
        have hi' : i < (lookupBuf bufs a).length + 1 := by
          have hi' := hi
          simp [List.length_append] at hi'
          exact hi'
        exact Nat.le_of_lt_succ hi'
      have hEq : i = (lookupBuf bufs a).length := Nat.le_antisymm hLe' hLe
      have hTraceEq : i = (lookupD D a).length := hLen ▸ hEq
      have hiTrace : i < (lookupD D a ++ [T]).length := by
        simpa [hNewLen] using hi
      have hBufGet : (lookupBuf bufs a ++ [v])[i] = v := by
        have hLe : (lookupBuf bufs a).length ≤ i := by simpa [hEq]
        -- i = length, so right side index is 0 in [v]
        simpa [hEq] using
          (List.getElem_append_right (as := lookupBuf bufs a) (bs := [v]) (i := i) hLe (h₂ := hi))
      have hTraceGet : (lookupD D a ++ [T])[i] = T := by
        have hLe : (lookupD D a).length ≤ i := by simpa [hTraceEq]
        simpa [hTraceEq] using
          (List.getElem_append_right (as := lookupD D a) (bs := [T]) (i := i) hLe (h₂ := hiTrace))
      have hGoal' : HasTypeVal G (lookupBuf bufs a ++ [v])[i] (lookupD D a ++ [T])[i] := by
        simpa [hBufGet, hTraceGet] using hv
      simpa [hBufUpdate, hTraceUpdate] using hGoal'
  · -- a ≠ e: unaffected edge
    have hOrig := hBT a
    have hBufEq : lookupBuf (updateBuf bufs e (lookupBuf bufs e ++ [v])) a = lookupBuf bufs a := by
      exact lookupBuf_update_neq _ _ _ _ (Ne.symm ha)
    have hTraceEq : lookupD (updateD D e (lookupD D e ++ [T])) a = lookupD D a := by
      exact lookupD_update_neq _ _ _ _ (Ne.symm ha)
    simpa [BufferTyped, hBufEq, hTraceEq, enqueueBuf] using hOrig

/-- BuffersTyped is preserved when dequeuing a buffer: removing the head preserves typing
    for the remaining elements (which shift down by one index).

    NOTE: This lemma needs to be proven. Similar to BuffersTyped_enqueue, this should be
    moved to a shared module to avoid circular dependencies. -/
theorem BuffersTyped_dequeue {G : GEnv} {D : DEnv} {bufs : Buffers}
    {recvEdge : Edge} {v : Value} {vs : List Value} {T : ValType} :
    BuffersTyped G D bufs →
    lookupBuf bufs recvEdge = v :: vs →
    (lookupD D recvEdge).head? = some T →
    BuffersTyped G (updateD D recvEdge (lookupD D recvEdge).tail) (updateBuf bufs recvEdge vs) := by
  intro hBT hBuf hHead a
  unfold BufferTyped
  by_cases ha : a = recvEdge
  · subst a
    have hOrig := hBT recvEdge
    unfold BufferTyped at hOrig
    obtain ⟨hLen, hTyping⟩ := hOrig
    -- Decompose the trace using head?
    cases hTrace : lookupD D recvEdge with
    | nil =>
        -- head? = some T is impossible on empty trace
        simp [hTrace] at hHead
    | cons t ts =>
        have hT : t = T := by
          -- head? = some T implies t = T
          simpa [hTrace] using hHead
        -- Lengths: v :: vs and t :: ts
        have hLen' : vs.length = ts.length := by
          -- From length equality on cons lists
          simpa [hBuf, hTrace] using hLen
        -- Updated buffer/trace
        have hBufEq : lookupBuf (updateBuf bufs recvEdge vs) recvEdge = vs := by
          exact lookupBuf_update_eq _ _ _
        have hTraceEq :
            lookupD (updateD D recvEdge (lookupD D recvEdge).tail) recvEdge = ts := by
          simp [lookupD_update_eq, hTrace]
        refine ⟨?_, ?_⟩
        · -- length equality
          -- Simplify lookups on the updated environments
          simp [lookupD_update_eq, hLen']
        · intro i hi
          -- Use original typing at index i+1
          have hi' : i < vs.length := by
            -- hi refers to the updated buffer length
            simpa [hBufEq] using hi
          have hi_succ : i + 1 < (lookupBuf bufs recvEdge).length := by
            have h' : i + 1 < vs.length + 1 := Nat.succ_lt_succ hi'
            simpa [hBuf, List.length_cons] using h'
          have hTypedIdx := hTyping (i + 1) hi_succ
          -- Simplify gets on cons lists
          -- Also use hTrace for trace structure
          have hTypedIdx' : HasTypeVal G vs[i] ts[i] := by
            simpa [List.get_eq_getElem, hBuf, hTrace, List.getElem_cons_succ] using hTypedIdx
          -- Now rewrite indices in updated envs
          simpa [hBufEq, lookupD_update_eq] using hTypedIdx'
  · -- a ≠ recvEdge: unaffected edge
    have hOrig := hBT a
    have hBufEq : lookupBuf (updateBuf bufs recvEdge vs) a = lookupBuf bufs a := by
      exact lookupBuf_update_neq _ _ _ _ (Ne.symm ha)
    have hTraceEq :
        lookupD (updateD D recvEdge (lookupD D recvEdge).tail) a = lookupD D a := by
      exact lookupD_update_neq _ _ _ _ (Ne.symm ha)
    simpa [BufferTyped, hBufEq, hTraceEq] using hOrig


end
