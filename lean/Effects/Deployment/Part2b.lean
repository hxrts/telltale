import Effects.Deployment.Part2a
import Effects.Typing.Part3a
import Effects.Coherence.Part9

/-! # Effects.Deployment.Part2b

Linking theorems and composition preservation results.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Linking Theorems -/

/-! ### Helper Lemmas for Merge Operations -/

/-- BufferTyped is stable under GEnv extension. -/
private theorem BufferTyped_weakenG {G G' : GEnv} {D : DEnv} {bufs : Buffers} {e : Edge}
    (hBT : BufferTyped G D bufs e)
    (hMono : ∀ ep L, lookupG G ep = some L → lookupG G' ep = some L) :
    BufferTyped G' D bufs e := by
  -- Lift each HasTypeVal witness through the lookup monotonicity.
  rcases hBT with ⟨hLen, hTyping⟩
  refine ⟨hLen, ?_⟩
  intro i hi
  exact HasTypeVal_mono G G' _ _ (hTyping i hi) hMono

/-- BufferTyped lifts from the left GEnv into the merged environment. -/
private theorem BufferTyped_lift_left {G₁ G₂ : GEnv} {D : DEnv} {bufs : Buffers} {e : Edge}
    (hBT : BufferTyped G₁ D bufs e) :
    BufferTyped (mergeGEnv G₁ G₂) D bufs e := by
  -- Use lookupG_append_left to lift left lookups.
  apply BufferTyped_weakenG hBT
  intro ep L hLookup
  exact lookupG_append_left (G₁:=G₁) (G₂:=G₂) hLookup

/-- BufferTyped lifts from the right GEnv into the merged environment. -/
private theorem BufferTyped_lift_right {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂)
    {D : DEnv} {bufs : Buffers} {e : Edge}
    (hBT : BufferTyped G₂ D bufs e) :
    BufferTyped (mergeGEnv G₁ G₂) D bufs e := by
  -- Route G lookups through the right using disjointness.
  apply BufferTyped_weakenG hBT
  intro ep L hLookup
  have hDisj' : DisjointG G₂ G₁ := DisjointG_symm hDisj
  have hNone : lookupG G₁ ep = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisj' hLookup
  have hNone' : G₁.lookup ep = none := by
    simpa [lookupG] using hNone
  have hEq : lookupG (mergeGEnv G₁ G₂) ep = lookupG G₂ ep := by
    simp [mergeGEnv, lookupG, List.lookup_append, hNone']
  simpa [hEq] using hLookup

/-- Merge typing when the left buffer is absent. -/
private theorem mergeBufs_typed_right_case
    {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} {B₁ B₂ : Buffers} {e : Edge}
    (hTyped₂ : BuffersTyped G₂ D₂ B₂)
    (hDisjG : DisjointG G₁ G₂)
    (hDom₁ : BufsDom B₁ D₁)
    (hLeft : B₁.lookup e = none) :
    BufferTyped (mergeGEnv G₁ G₂) (mergeDEnv D₁ D₂) (mergeBufs B₁ B₂) e := by
  -- Use the right buffer/trace and lift typing into merged G.
  have hD1 : D₁.find? e = none := hDom₁ e hLeft
  have hBuf : lookupBuf (mergeBufs B₁ B₂) e = lookupBuf B₂ e :=
    MergeBufs_Right B₁ B₂ e hLeft
  have hD : lookupD (mergeDEnv D₁ D₂) e = lookupD D₂ e :=
    lookupD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hD1
  have hBT := BufferTyped_lift_right hDisjG (hTyped₂ e)
  simpa [BufferTyped, hBuf, hD] using hBT

/-- Merge typing when the left buffer is present. -/
private theorem mergeBufs_typed_left_case
    {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} {B₁ B₂ : Buffers} {e : Edge} {buf : Buffer}
    (hTyped₁ : BuffersTyped G₁ D₁ B₁)
    (hDisjG : DisjointG G₁ G₂)
    (hConsB₁ : BConsistent G₁ B₁)
    (hConsD₂ : DConsistent G₂ D₂)
    (hLeft : B₁.lookup e = some buf) :
    BufferTyped (mergeGEnv G₁ G₂) (mergeDEnv D₁ D₂) (mergeBufs B₁ B₂) e := by
  -- Use the left buffer and show the right DEnv is absent for this session.
  have hSid : e.sid ∈ SessionsOf G₁ := hConsB₁ e buf hLeft
  have hNot : e.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisjG hSid
  have hD2 : D₂.find? e = none :=
    DEnv_find_none_of_notin_sessions (G:=G₂) (D:=D₂) hConsD₂ hNot
  have hBuf : lookupBuf (mergeBufs B₁ B₂) e = lookupBuf B₁ e := by
    -- Left entry wins in buffer merge.
    simp [lookupBuf, mergeBufs, List.lookup_append, hLeft]
  have hD : lookupD (mergeDEnv D₁ D₂) e = lookupD D₁ e :=
    lookupD_append_left_of_right_none (D₁:=D₁) (D₂:=D₂) (e:=e) hD2
  have hBT := BufferTyped_lift_left (G₂:=G₂) (hTyped₁ e)
  simpa [BufferTyped, hBuf, hD] using hBT

/-- Merged buffers preserve typing when sessions are disjoint. -/
theorem mergeBufs_typed (G₁ G₂ : GEnv) (D₁ D₂ : DEnv) (B₁ B₂ : Buffers)
    (hTyped₁ : BuffersTyped G₁ D₁ B₁)
    (hTyped₂ : BuffersTyped G₂ D₂ B₂)
    (hDisjG : DisjointG G₁ G₂)
    (hConsD₂ : DConsistent G₂ D₂)
    (hConsB₁ : BConsistent G₁ B₁)
    (hDom₁ : BufsDom B₁ D₁) :
    BuffersTyped (mergeGEnv G₁ G₂) (mergeDEnv D₁ D₂) (mergeBufs B₁ B₂) := by
  -- Split on whether the left buffer provides an entry.
  intro e
  cases hLeft : B₁.lookup e with
  | none =>
      exact mergeBufs_typed_right_case hTyped₂ hDisjG hDom₁ hLeft
  | some buf =>
      exact mergeBufs_typed_left_case hTyped₁ hDisjG hConsB₁ hConsD₂ hLeft

/-- Merged linear context is valid when GEnvs are disjoint. -/
theorem mergeLin_valid (G₁ G₂ : GEnv) (L₁ L₂ : LinCtx)
    (hValid₁ : ∀ e S, (e, S) ∈ L₁ → lookupG G₁ e = some S)
    (hValid₂ : ∀ e S, (e, S) ∈ L₂ → lookupG G₂ e = some S)
    (hDisjointG : DisjointG G₁ G₂) :
    ∀ e S, (e, S) ∈ mergeLin L₁ L₂ → lookupG (mergeGEnv G₁ G₂) e = some S := by
  -- Split membership between the left and right linear contexts.
  intro e S hMem
  simp only [mergeLin, List.mem_append] at hMem
  cases hMem with
  | inl h₁ =>
      -- Left entry: the merged GEnv takes the left lookup.
      have hLookup := hValid₁ e S h₁
      exact MergeGEnv_Left G₁ G₂ e S hLookup
  | inr h₂ =>
      -- Right entry: disjointness forces the left lookup to be none.
      have hLookup := hValid₂ e S h₂
      have hDisjSym : DisjointG G₂ G₁ := DisjointG_symm hDisjointG
      have hNone : lookupG G₁ e = none :=
        DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hLookup
      have hMerge := MergeGEnv_Right G₁ G₂ e hNone
      simpa [hMerge] using hLookup

/-- Merged linear context preserves uniqueness when sessions are disjoint. -/
theorem mergeLin_unique (L₁ L₂ : LinCtx)
    (hUnique₁ : L₁.Pairwise (fun a b => a.1 ≠ b.1))
    (hUnique₂ : L₂.Pairwise (fun a b => a.1 ≠ b.1))
    (hDisjoint : ∀ e, (∃ S, (e, S) ∈ L₁) → ∀ S', (e, S') ∉ L₂) :
    (mergeLin L₁ L₂).Pairwise (fun a b => a.1 ≠ b.1) := by
  simp only [mergeLin, List.pairwise_append]
  refine ⟨hUnique₁, hUnique₂, ?_⟩
  intro a ha b hb
  -- a is in L₁, b is in L₂, so a.1 ≠ b.1 by disjointness
  intro heq
  have hEx : ∃ S, (a.1, S) ∈ L₁ := ⟨a.2, by rw [Prod.eta]; exact ha⟩
  have hNotIn := hDisjoint a.1 hEx b.2
  rw [heq] at hNotIn
  exact hNotIn (by rw [Prod.eta]; exact hb)

/-- Linear contexts are disjoint when their GEnvs are disjoint. -/
private theorem lin_disjoint_of_disjointG
    {G₁ G₂ : GEnv} {L₁ L₂ : LinCtx}
    (hDisjG : DisjointG G₁ G₂)
    (hValid₁ : ∀ e S, (e, S) ∈ L₁ → lookupG G₁ e = some S)
    (hValid₂ : ∀ e S, (e, S) ∈ L₂ → lookupG G₂ e = some S) :
    ∀ e, (∃ S, (e, S) ∈ L₁) → ∀ S', (e, S') ∉ L₂ := by
  -- Shared endpoints would violate disjointness of session IDs.
  intro e hEx S' hMem
  rcases hEx with ⟨S, hMem₁⟩
  have hLookup₁ := hValid₁ e S hMem₁
  have hLookup₂ := hValid₂ e S' hMem
  have hNone : lookupG G₂ e = none :=
    DisjointG_lookup_left (G₁:=G₁) (G₂:=G₂) hDisjG hLookup₁
  have hEq : (some S') = none := by
    simpa [hLookup₂] using hNone
  cases hEq

/-- HeadCoherent is preserved when merging disjoint sessions. -/
private theorem HeadCoherent_merge
    {G₁ G₂ : GEnv} {D₁ D₂ : DEnv}
    (hDisjG : DisjointG G₁ G₂)
    (hConsD₁ : DConsistent G₁ D₁)
    (hConsD₂ : DConsistent G₂ D₂)
    (hHead₁ : HeadCoherent G₁ D₁)
    (hHead₂ : HeadCoherent G₂ D₂) :
    HeadCoherent (mergeGEnv G₁ G₂) (mergeDEnv D₁ D₂) := by
  -- Split on which side provides the receiver endpoint.
  intro e
  let recvEp : Endpoint := { sid := e.sid, role := e.receiver }
  cases hG : lookupG (mergeGEnv G₁ G₂) recvEp with
  | none =>
      simp [HeadCoherent, recvEp, hG]
  | some L =>
      have hInv := MergeGEnv_inv (G₁:=G₁) (G₂:=G₂) (e:=recvEp) (L:=L) hG
      cases hInv with
      | inl hLeft =>
          have hSid : e.sid ∈ SessionsOf G₁ := ⟨recvEp, L, hLeft, rfl⟩
          have hNot : e.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisjG hSid
          have hD : lookupD (mergeDEnv D₁ D₂) e = lookupD D₁ e :=
            lookupD_merge_left_of_notin_right (G₂:=G₂) (D₁:=D₁) (D₂:=D₂) (e:=e) hConsD₂ hNot
          simpa [HeadCoherent, recvEp, hG, hLeft, hD] using hHead₁ e
      | inr hRight =>
          have hSid : e.sid ∈ SessionsOf G₂ := ⟨recvEp, L, hRight.2, rfl⟩
          have hNot : e.sid ∉ SessionsOf G₁ :=
            sid_not_in_right_of_left (DisjointG_symm hDisjG) hSid
          have hD : lookupD (mergeDEnv D₁ D₂) e = lookupD D₂ e :=
            lookupD_merge_right_of_notin_left (G₁:=G₁) (D₁:=D₁) (D₂:=D₂) (e:=e) hConsD₁ hNot
          simpa [HeadCoherent, recvEp, hG, hRight.2, hD] using hHead₂ e

/-- ValidLabels is preserved when merging disjoint sessions. -/
private theorem ValidLabels_merge
    {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} {B₁ B₂ : Buffers}
    (hDisjG : DisjointG G₁ G₂)
    (hConsB₁ : BConsistent G₁ B₁)
    (hConsB₂ : BConsistent G₂ B₂)
    (hValid₁ : ValidLabels G₁ D₁ B₁)
    (hValid₂ : ValidLabels G₂ D₂ B₂) :
    ValidLabels (mergeGEnv G₁ G₂) (mergeDEnv D₁ D₂) (mergeBufs B₁ B₂) := by
  -- Use the receiver side to select the correct buffer.
  intro e source bs hG
  let recvEp : Endpoint := { sid := e.sid, role := e.receiver }
  have hInv := MergeGEnv_inv (G₁:=G₁) (G₂:=G₂) (e:=recvEp) (L:=.branch source bs) hG
  cases hInv with
  | inl hLeft =>
      have hSid : e.sid ∈ SessionsOf G₁ := ⟨recvEp, _, hLeft, rfl⟩
      have hNot : e.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisjG hSid
      have hBuf : lookupBuf (mergeBufs B₁ B₂) e = lookupBuf B₁ e :=
        lookupBuf_merge_left_of_notin_right (G₂:=G₂) (B₁:=B₁) (B₂:=B₂) (e:=e) hConsB₂ hNot
      simpa [hBuf] using hValid₁ e source bs hLeft
  | inr hRight =>
      have hSid : e.sid ∈ SessionsOf G₂ := ⟨recvEp, _, hRight.2, rfl⟩
      have hNot : e.sid ∉ SessionsOf G₁ :=
        sid_not_in_right_of_left (DisjointG_symm hDisjG) hSid
      have hBuf : lookupBuf (mergeBufs B₁ B₂) e = lookupBuf B₂ e :=
        lookupBuf_merge_right_of_notin_left (G₁:=G₁) (B₁:=B₁) (B₂:=B₂) (e:=e) hConsB₁ hNot
      simpa [hBuf] using hValid₂ e source bs hRight.2

/-- Supply freshness is preserved under merging linear contexts. -/
private theorem supply_fresh_merge {ms₁ ms₂ : MonitorState}
    (hWT₁ : WTMon ms₁) (hWT₂ : WTMon ms₂) :
    ∀ e S, (e, S) ∈ mergeLin ms₁.Lin ms₂.Lin → e.sid < max ms₁.supply ms₂.supply := by
  -- Split membership and lift bounds through max.
  intro e S hMem
  simp [mergeLin] at hMem
  cases hMem with
  | inl h₁ =>
      have hLt := hWT₁.supply_fresh e S h₁
      exact lt_of_lt_of_le hLt (Nat.le_max_left _ _)
  | inr h₂ =>
      have hLt := hWT₂.supply_fresh e S h₂
      exact lt_of_lt_of_le hLt (Nat.le_max_right _ _)

/-- Supply freshness is preserved under merging GEnvs. -/
private theorem supply_fresh_G_merge {ms₁ ms₂ : MonitorState}
    (hWT₁ : WTMon ms₁) (hWT₂ : WTMon ms₂) :
    ∀ e S, (e, S) ∈ mergeGEnv ms₁.G ms₂.G → e.sid < max ms₁.supply ms₂.supply := by
  -- Split membership and lift bounds through max.
  intro e S hMem
  simp [mergeGEnv] at hMem
  cases hMem with
  | inl h₁ =>
      have hLt := hWT₁.supply_fresh_G e S h₁
      exact lt_of_lt_of_le hLt (Nat.le_max_left _ _)
  | inr h₂ =>
      have hLt := hWT₂.supply_fresh_G e S h₂
      exact lt_of_lt_of_le hLt (Nat.le_max_right _ _)

/-- Linking preserves well-typedness (legacy wrapper for the full proof). -/
theorem link_preserves_WTMon_full (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMon p₁.initMonitorState)
    (hWT₂ : WTMon p₂.initMonitorState) :
    WTMon (composeMonitorState p₁.initMonitorState p₂.initMonitorState) := by
  -- Assemble the merged invariants from the per-protocol proofs.
  simp only [composeMonitorState, DeployedProtocol.initMonitorState]
  constructor
  · exact hLink.2.2.2
  ·
    exact HeadCoherent_merge hDisjG p₁.dConsistent_cert p₂.dConsistent_cert
      hWT₁.headCoherent hWT₂.headCoherent
  ·
    exact ValidLabels_merge hDisjG p₁.bConsistent_cert p₂.bConsistent_cert
      hWT₁.validLabels hWT₂.validLabels
  ·
    exact mergeBufs_typed p₁.initGEnv p₂.initGEnv p₁.initDEnv p₂.initDEnv p₁.initBufs p₂.initBufs
      hWT₁.buffers_typed hWT₂.buffers_typed hDisjG p₂.dConsistent_cert p₁.bConsistent_cert
      p₁.bufsDom_cert
  · exact mergeLin_valid _ _ _ _ hWT₁.lin_valid hWT₂.lin_valid hDisjG
  ·
    have hDisj := lin_disjoint_of_disjointG hDisjG hWT₁.lin_valid hWT₂.lin_valid
    exact mergeLin_unique _ _ hWT₁.lin_unique hWT₂.lin_unique hDisj
  · exact supply_fresh_merge hWT₁ hWT₂
  · exact supply_fresh_G_merge hWT₁ hWT₂

/-- Linking preserves well-typedness (legacy wrapper for the full proof). -/
theorem link_preserves_WTMon (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMon p₁.initMonitorState)
    (hWT₂ : WTMon p₂.initMonitorState) :
    WTMon (composeMonitorState p₁.initMonitorState p₂.initMonitorState) := by
  -- Delegate to the full linking proof.
  exact link_preserves_WTMon_full p₁ p₂ hLink hDisjG hWT₁ hWT₂

/-- Linking preserves complete well-typedness (legacy version). -/
theorem link_preserves_WTMon_complete (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMonComplete p₁.initMonitorState)
    (hWT₂ : WTMonComplete p₂.initMonitorState) :
    WTMonComplete (composeMonitorState p₁.initMonitorState p₂.initMonitorState) := by
  -- Reuse WTMon preservation and discharge RoleComplete separately.
  refine ⟨link_preserves_WTMon p₁ p₂ hLink hDisjG hWT₁.1 hWT₂.1, ?_⟩
  -- Role completeness is preserved by merging GEnvs.
  have hRole : RoleComplete (mergeGEnv p₁.initGEnv p₂.initGEnv) :=
    RoleComplete_mergeGEnv p₁.initGEnv p₂.initGEnv hWT₁.2 hWT₂.2
  simpa [composeMonitorState, DeployedProtocol.initMonitorState] using hRole

/-- Linking preserves complete well-typedness (full version). -/
theorem link_preserves_WTMon_complete_full (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMonComplete p₁.initMonitorState)
    (hWT₂ : WTMonComplete p₂.initMonitorState) :
    WTMonComplete (composeMonitorState p₁.initMonitorState p₂.initMonitorState) := by
  -- Use the full WTMon proof, then show role completeness for the merge.
  refine ⟨link_preserves_WTMon_full p₁ p₂ hLink hDisjG hWT₁.1 hWT₂.1, ?_⟩
  -- Role completeness is preserved by merging GEnvs.
  have hRole : RoleComplete (mergeGEnv p₁.initGEnv p₂.initGEnv) :=
    RoleComplete_mergeGEnv p₁.initGEnv p₂.initGEnv hWT₁.2 hWT₂.2
  simpa [composeMonitorState, DeployedProtocol.initMonitorState] using hRole

/-! ## Composition Preserves Deadlock Freedom

The key theorem for safe composition: if both protocols are deadlock-free,
their composition is also deadlock-free.
-/

/-- Disjoint sessions maintain independence. -/
theorem disjoint_sessions_independent (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOK p₁ p₂) :
    p₁.sessionId ≠ p₂.sessionId := by
  -- From disjointSessions: all of p₁'s sessions are not in p₂'s sessions
  obtain ⟨hDisjoint, _, _⟩ := hLink
  intro heq
  -- p₁.sessionId ∈ p₁.interface.sessionIds
  have h₁ := p₁.sessionId_in_interface
  -- p₂.sessionId ∈ p₂.interface.sessionIds
  have h₂ := p₂.sessionId_in_interface
  -- disjointSessions means all s in p₁'s list are not in p₂'s list
  unfold InterfaceType.disjointSessions at hDisjoint
  -- p₁.sessionId is in p₁.interface.sessionIds, so it should not be in p₂'s
  have hAll := List.all_eq_true.mp hDisjoint p₁.sessionId h₁
  -- hAll : !(p₂.interface.sessionIds.contains p₁.sessionId) = true
  -- i.e., p₂.interface.sessionIds.contains p₁.sessionId = false
  have hNotContains : p₂.interface.sessionIds.contains p₁.sessionId = false := by
    simpa using hAll
  -- But if p₁.sessionId = p₂.sessionId, and p₂.sessionId ∈ p₂.interface.sessionIds,
  -- then p₂.interface.sessionIds.contains p₁.sessionId = true - contradiction
  have hContains : p₂.interface.sessionIds.contains p₁.sessionId = true := by
    rw [heq, List.contains_iff_exists_mem_beq]
    exact ⟨p₂.sessionId, h₂, beq_self_eq_true _⟩
  rw [hNotContains] at hContains
  exact Bool.false_ne_true hContains

/-- Composition preserves deadlock freedom.

If both protocols can reach communication independently,
the composed protocol can also make progress.
-/
theorem compose_deadlock_free (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOK p₁ p₂)
    (hDF₁ : ∀ r, r ∈ p₁.roles → ReachesComm (p₁.localTypes r))
    (hDF₂ : ∀ r, r ∈ p₂.roles → ReachesComm (p₂.localTypes r)) :
    ∀ r, r ∈ p₁.roles ++ p₂.roles →
      ReachesComm ((composeBundle (ProtocolBundle.fromDeployed p₁) (ProtocolBundle.fromDeployed p₂)).localTypes r) := by
  intro r hr
  simp only [composeBundle, ProtocolBundle.fromDeployed]
  by_cases h₁ : r ∈ p₁.roles
  · -- r is in p₁.roles
    simp only [h₁, List.elem_eq_mem, ↓reduceIte]
    exact hDF₁ r h₁
  · -- r is in p₂.roles
    have h₂ : r ∈ p₂.roles := by
      simp only [List.mem_append] at hr
      cases hr with
      | inl h => exact absurd h h₁
      | inr h => exact h
    simp only [h₁, List.elem_eq_mem, Bool.false_eq_true, ↓reduceIte, h₂]
    exact hDF₂ r h₂

end
