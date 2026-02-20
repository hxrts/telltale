import Protocol.Deployment.LinkingCore
/-! # Protocol.Deployment.LinkingTheorems
Main linking theorems for WTMon preservation and delegation-aware composition.
-/
/-
The Problem. Lift linking infrastructure into compositional well-typing and coherence results.
Solution Structure. Prove merge preservation properties and assemble story-level theorems.
-/
/- ## Structured Block 1 -/
set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
open scoped Classical
section
-- Linking Theorems
-- Merge Typing Infrastructure
theorem mergeBufs_typed (G₁ G₂ : GEnv) (D₁ D₂ : DEnv) (B₁ B₂ : Buffers)
    (hTyped₁ : BuffersTyped G₁ D₁ B₁)
    (hTyped₂ : BuffersTyped G₂ D₂ B₂)
    (hDisjG : DisjointG G₁ G₂)
    (hConsD₂ : DConsistent G₂ D₂)
    (hConsB₁ : BConsistent G₁ B₁)
    (hDom₁ : BufsDom B₁ D₁) :
    BuffersTyped (mergeGEnv G₁ G₂) (mergeDEnv D₁ D₂) (mergeBufs B₁ B₂) := by
  -- mergeBufs_typed: Case Split on Left Trace Presence
  intro e
  cases hFindD₁ : D₁.find? e with
  | none =>
      by_cases hFindB₁ : B₁.lookup e = none
      · have hTraceEq : lookupD (mergeDEnv D₁ D₂) e = lookupD D₂ e := by
          simpa [mergeDEnv] using
            (lookupD_append_right (D₁ := D₁) (D₂ := D₂) (e := e) hFindD₁)
        have hBufEq : lookupBuf (mergeBufs B₁ B₂) e = lookupBuf B₂ e := by
          simp [lookupBuf, mergeBufs, List.lookup_append, hFindB₁]
        have hBT₂ : BufferTyped G₂ D₂ B₂ e := hTyped₂ e
        have hBT₂' : BufferTyped (mergeGEnv G₁ G₂) D₂ B₂ e :=
          BufferTyped_monoG hBT₂ (by
            intro ep L hLookup
            have hIn₂ : ep.sid ∈ SessionsOf G₂ := session_of_lookupG hLookup
            have hNot₁ : ep.sid ∉ SessionsOf G₁ := sid_not_in_left_of_right hDisjG hIn₂
            have hNone₁ : lookupG G₁ ep = none := lookupG_none_of_not_session hNot₁
            have hEq := lookupG_append_right (G₁ := G₁) (G₂ := G₂) (e := ep) hNone₁
            simpa [mergeGEnv, hEq] using hLookup)
        simpa [BufferTyped, hTraceEq, hBufEq] using hBT₂'
      · cases hB₁ : B₁.lookup e with
        | none =>
            exact (hFindB₁ hB₁).elim
        | some buf₁ =>
            have hSidIn₁ : e.sid ∈ SessionsOf G₁ := hConsB₁ e buf₁ hB₁
            have hNotIn₂ : e.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisjG hSidIn₁
            have hFindD₂_none : D₂.find? e = none :=
              lookupD_none_of_notin_sessions hConsD₂ hNotIn₂
            have hTraceEq : lookupD (mergeDEnv D₁ D₂) e = lookupD D₁ e := by
              simpa [mergeDEnv] using
                (lookupD_append_left_of_right_none (D₁ := D₁) (D₂ := D₂) (e := e) hFindD₂_none)
            have hBufEq : lookupBuf (mergeBufs B₁ B₂) e = lookupBuf B₁ e := by
              simp [lookupBuf, mergeBufs, List.lookup_append, hB₁]
            have hBT₁ : BufferTyped G₁ D₁ B₁ e := hTyped₁ e
            have hBT₁' : BufferTyped (mergeGEnv G₁ G₂) D₁ B₁ e := by
              exact BufferTyped_monoG hBT₁ (by
                intro ep L hLookup
                simpa [mergeGEnv] using
/- ## Structured Block 2 -/
                  (lookupG_append_left (G₁ := G₁) (G₂ := G₂) (e := ep) (L := L) hLookup))
            simpa [BufferTyped, hTraceEq, hBufEq] using hBT₁'
  -- mergeBufs_typed: Left Trace Present Case
  | some ts₁ =>
      have hB₁_not_none : B₁.lookup e ≠ none := by
        intro hNone
        have hD₁_none : D₁.find? e = none := hDom₁ e hNone
        simp [hD₁_none] at hFindD₁
      cases hB₁ : B₁.lookup e with
      | none =>
          exact (hB₁_not_none hB₁).elim
      | some buf₁ =>
          have hSidIn₁ : e.sid ∈ SessionsOf G₁ := hConsB₁ e buf₁ hB₁
          have hNotIn₂ : e.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisjG hSidIn₁
          have hFindD₂_none : D₂.find? e = none :=
            lookupD_none_of_notin_sessions hConsD₂ hNotIn₂
          have hTraceEq : lookupD (mergeDEnv D₁ D₂) e = lookupD D₁ e := by
            simpa [mergeDEnv] using
              (lookupD_append_left_of_right_none (D₁ := D₁) (D₂ := D₂) (e := e) hFindD₂_none)
          have hBufEq : lookupBuf (mergeBufs B₁ B₂) e = lookupBuf B₁ e := by
            simp [lookupBuf, mergeBufs, List.lookup_append, hB₁]
          have hBT₁ : BufferTyped G₁ D₁ B₁ e := hTyped₁ e
          have hBT₁' : BufferTyped (mergeGEnv G₁ G₂) D₁ B₁ e := by
            exact BufferTyped_monoG hBT₁ (by
              intro ep L hLookup
              simpa [mergeGEnv] using
                (lookupG_append_left (G₁ := G₁) (G₂ := G₂) (e := ep) (L := L) hLookup))
          simpa [BufferTyped, hTraceEq, hBufEq] using hBT₁'
-- Linear Context Merge Lemmas
theorem mergeLin_valid (G₁ G₂ : GEnv) (L₁ L₂ : LinCtx)
    (hValid₁ : ∀ e S, (e, S) ∈ L₁ → lookupG G₁ e = some S)
    (hValid₂ : ∀ e S, (e, S) ∈ L₂ → lookupG G₂ e = some S)
    (hDisjointG : DisjointG G₁ G₂) :
    ∀ e S, (e, S) ∈ mergeLin L₁ L₂ → lookupG (mergeGEnv G₁ G₂) e = some S := by
  intro e S hMem
  simp [mergeLin] at hMem
  cases hMem with
  | inl hIn₁ =>
      have hLookup : lookupG G₁ e = some S := hValid₁ e S hIn₁
      simpa [mergeGEnv] using
        (lookupG_append_left (G₁ := G₁) (G₂ := G₂) (e := e) (L := S) hLookup)
  | inr hIn₂ =>
      have hLookup₂ : lookupG G₂ e = some S := hValid₂ e S hIn₂
      have hSidIn₂ : e.sid ∈ SessionsOf G₂ := session_of_lookupG hLookup₂
      have hSidNotIn₁ : e.sid ∉ SessionsOf G₁ := sid_not_in_left_of_right hDisjointG hSidIn₂
      have hLookup₁_none : lookupG G₁ e = none := lookupG_none_of_not_session hSidNotIn₁
      have hEq := lookupG_append_right (G₁ := G₁) (G₂ := G₂) (e := e) hLookup₁_none
      simpa [mergeGEnv, hEq] using hLookup₂

theorem mergeLin_unique (L₁ L₂ : LinCtx)
    (hUnique₁ : L₁.Pairwise (fun a b => a.1 ≠ b.1))
    (hUnique₂ : L₂.Pairwise (fun a b => a.1 ≠ b.1))
    (hDisjoint : ∀ e, (∃ S, (e, S) ∈ L₁) → ∀ S', (e, S') ∉ L₂) :
/- ## Structured Block 3 -/
    (mergeLin L₁ L₂).Pairwise (fun a b => a.1 ≠ b.1) := by
  refine (List.pairwise_append.2 ?_)
  refine ⟨hUnique₁, hUnique₂, ?_⟩
  intro a ha b hb
  by_contra hEq
  have hb' : (a.1, b.2) ∈ L₂ := by simpa [hEq] using hb
  have hNo : (a.1, b.2) ∉ L₂ := hDisjoint a.1 ⟨a.2, ha⟩ b.2
  exact hNo hb'

-- Coherence Component Merge Lemmas
private theorem HeadCoherent_merge_link {G₁ G₂ : GEnv} {D₁ D₂ : DEnv}
    (hHead₁ : HeadCoherent G₁ D₁)
    (hHead₂ : HeadCoherent G₂ D₂)
    (hDisjG : DisjointG G₁ G₂)
    (hCons₁ : DConsistent G₁ D₁)
    (hCons₂ : DConsistent G₂ D₂) :
    HeadCoherent (mergeGEnv G₁ G₂) (mergeDEnv D₁ D₂) := by
  intro e hActive
  rcases hActive with ⟨hSenderSome, hRecvSome⟩
  rcases (Option.isSome_iff_exists).1 hSenderSome with ⟨Lsender, hGsender⟩
  rcases (Option.isSome_iff_exists).1 hRecvSome with ⟨Lrecv, hGrecv⟩
  have hCases :=
    lookupG_append_inv (G₁ := G₁) (G₂ := G₂) (e := { sid := e.sid, role := e.receiver }) (L := Lrecv)
      (by simpa [mergeGEnv] using hGrecv)
  cases hCases with
  | inl hLeft =>
      have hSid : e.sid ∈ SessionsOf G₁ :=
        ⟨{ sid := e.sid, role := e.receiver }, Lrecv, hLeft, rfl⟩
      have hSenderCases :=
        lookupG_append_inv (G₁ := G₁) (G₂ := G₂) (e := { sid := e.sid, role := e.sender }) (L := Lsender)
          (by simpa [mergeGEnv] using hGsender)
      have hSenderLeft : lookupG G₁ { sid := e.sid, role := e.sender } = some Lsender := by
        cases hSenderCases with
        | inl h =>
            exact h
        | inr h =>
            have hSidSender : e.sid ∈ SessionsOf G₂ :=
              ⟨{ sid := e.sid, role := e.sender }, Lsender, h.2, rfl⟩
            have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hSid, hSidSender⟩
            have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := hDisjG
            simp [hEmpty] at hInter
      have hD2none : D₂.find? e = none := lookupD_none_of_disjointG hDisjG hCons₂ hSid
      have hTraceEq : lookupD (mergeDEnv D₁ D₂) e = lookupD D₁ e := by
        simpa [mergeDEnv] using
          (lookupD_append_left_of_right_none (D₁ := D₁) (D₂ := D₂) (e := e) hD2none)
      have hActiveLeft : ActiveEdge G₁ e := ActiveEdge_of_endpoints hSenderLeft hLeft
      have hHeadLeft := hHead₁ e hActiveLeft
      have hHeadLeft' :
          match some Lrecv with
          | some (.recv _ T _) =>
              match lookupD D₁ e with
              | [] => True
/- ## Structured Block 4 -/
              | T' :: _ => T = T'
          | some (.branch _ _) =>
              match lookupD D₁ e with
              | [] => True
              | T' :: _ => T' = .string
          | _ => True := by
        simpa [HeadCoherent, hLeft] using hHeadLeft
      simpa [HeadCoherent, hGrecv, hTraceEq] using hHeadLeft'
  -- HeadCoherent_merge: Receiver-Origin in Right Component
  | inr hRight =>
      have hSid : e.sid ∈ SessionsOf G₂ :=
        ⟨{ sid := e.sid, role := e.receiver }, Lrecv, hRight.2, rfl⟩
      have hSenderCases :=
        lookupG_append_inv (G₁ := G₁) (G₂ := G₂) (e := { sid := e.sid, role := e.sender }) (L := Lsender)
          (by simpa [mergeGEnv] using hGsender)
      have hSenderRight : lookupG G₂ { sid := e.sid, role := e.sender } = some Lsender := by
        cases hSenderCases with
        | inl h =>
            have hSidSender : e.sid ∈ SessionsOf G₁ :=
              ⟨{ sid := e.sid, role := e.sender }, Lsender, h, rfl⟩
            have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hSidSender, hSid⟩
            have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := hDisjG
            simp [hEmpty] at hInter
        | inr h =>
            exact h.2
      have hD1none : D₁.find? e = none :=
        lookupD_none_of_disjointG (G₁ := G₂) (G₂ := G₁) (D₂ := D₁) (DisjointG_symm hDisjG) hCons₁ hSid
      have hTraceEq : lookupD (mergeDEnv D₁ D₂) e = lookupD D₂ e := by
        simpa [mergeDEnv] using
          (lookupD_append_right (D₁ := D₁) (D₂ := D₂) (e := e) hD1none)
      have hActiveRight : ActiveEdge G₂ e := ActiveEdge_of_endpoints hSenderRight hRight.2
      have hHeadRight := hHead₂ e hActiveRight
      have hHeadRight' :
          match some Lrecv with
          | some (.recv _ T _) =>
              match lookupD D₂ e with
              | [] => True
              | T' :: _ => T = T'
          | some (.branch _ _) =>
              match lookupD D₂ e with
              | [] => True
              | T' :: _ => T' = .string
          | _ => True := by
        simpa [HeadCoherent, hRight.2] using hHeadRight
      simpa [HeadCoherent, hGrecv, hTraceEq] using hHeadRight'

-- ValidLabels Merge Lemma
private theorem ValidLabels_merge {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} {B₁ B₂ : Buffers}
    (hValid₁ : ValidLabels G₁ D₁ B₁)
    (hValid₂ : ValidLabels G₂ D₂ B₂)
    (hDisjG : DisjointG G₁ G₂)
    (hConsB₁ : BConsistent G₁ B₁)
    (hConsB₂ : BConsistent G₂ B₂) :
/- ## Structured Block 5 -/
    ValidLabels (mergeGEnv G₁ G₂) (mergeDEnv D₁ D₂) (mergeBufs B₁ B₂) := by
  intro e source bs hActive hBranch
  have hActiveSplit : ActiveEdge G₁ e ∨ ActiveEdge G₂ e :=
    ActiveEdge_mergeGEnv_split hDisjG hActive
  have hCases :=
    lookupG_append_inv (G₁ := G₁) (G₂ := G₂) (e := { sid := e.sid, role := e.receiver }) (L := .branch source bs)
      (by simpa [mergeGEnv] using hBranch)
  cases hCases with
  | inl hLeft =>
      have hSidIn₁ : e.sid ∈ SessionsOf G₁ :=
        ⟨{ sid := e.sid, role := e.receiver }, .branch source bs, hLeft, rfl⟩
      have hSidNotIn₂ : e.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisjG hSidIn₁
      have hB₂none : B₂.lookup e = none := lookupBuf_none_of_notin_sessions hConsB₂ hSidNotIn₂
      have hActive₁ : ActiveEdge G₁ e := by
        cases hActiveSplit with
        | inl hA₁ =>
            exact hA₁
        | inr hA₂ =>
            rcases Option.isSome_iff_exists.mp hA₂.2 with ⟨Lrecv₂, hRecv₂⟩
            have hSidIn₂ : e.sid ∈ SessionsOf G₂ :=
              ⟨{ sid := e.sid, role := e.receiver }, Lrecv₂, hRecv₂, rfl⟩
            exact (hSidNotIn₂ hSidIn₂).elim
      have hBufEq : lookupBuf (mergeBufs B₁ B₂) e = lookupBuf B₁ e := by
        simp [lookupBuf, mergeBufs, List.lookup_append, hB₂none]
      simpa [ValidLabels, mergeGEnv, hBufEq] using hValid₁ e source bs hActive₁ hLeft
  | inr hRight =>
      have hSidIn₂ : e.sid ∈ SessionsOf G₂ :=
        ⟨{ sid := e.sid, role := e.receiver }, .branch source bs, hRight.2, rfl⟩
      have hSidNotIn₁ : e.sid ∉ SessionsOf G₁ := sid_not_in_left_of_right hDisjG hSidIn₂
      have hB₁none : B₁.lookup e = none := lookupBuf_none_of_notin_sessions hConsB₁ hSidNotIn₁
      have hActive₂ : ActiveEdge G₂ e := by
        cases hActiveSplit with
        | inl hA₁ =>
            rcases Option.isSome_iff_exists.mp hA₁.2 with ⟨Lrecv₁, hRecv₁⟩
            have hSidIn₁ : e.sid ∈ SessionsOf G₁ :=
              ⟨{ sid := e.sid, role := e.receiver }, Lrecv₁, hRecv₁, rfl⟩
            exact (hSidNotIn₁ hSidIn₁).elim
        | inr hA₂ =>
            exact hA₂
      have hBufEq : lookupBuf (mergeBufs B₁ B₂) e = lookupBuf B₂ e := by
        simp [lookupBuf, mergeBufs, List.lookup_append, hB₁none]
      simpa [ValidLabels, mergeGEnv, hBufEq] using hValid₂ e source bs hActive₂ hRight.2

-- WTMon Linking Preservation
theorem link_preserves_WTMon_full (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMon p₁.initMonitorState)
    (hWT₂ : WTMon p₂.initMonitorState) :
    WTMon (composeMonitorState p₁.initMonitorState p₂.initMonitorState) := by
  constructor
  · -- coherent
/- ## Structured Block 6 -/
    simpa [composeMonitorState] using LinkOKFull_coherent p₁ p₂ hLink
  · -- headCoherent
    simpa [composeMonitorState] using
      HeadCoherent_merge_link hWT₁.headCoherent hWT₂.headCoherent hDisjG
        p₁.dConsistent_cert p₂.dConsistent_cert
  · -- validLabels
    simpa [composeMonitorState] using
      ValidLabels_merge hWT₁.validLabels hWT₂.validLabels hDisjG
        p₁.bConsistent_cert p₂.bConsistent_cert
  · -- buffers_typed
    simpa [composeMonitorState] using
      mergeBufs_typed p₁.initGEnv p₂.initGEnv p₁.initDEnv p₂.initDEnv
        p₁.initBufs p₂.initBufs
        hWT₁.buffers_typed hWT₂.buffers_typed
        hDisjG p₂.dConsistent_cert p₁.bConsistent_cert p₁.bufsDom_cert
  -- link_preserves_WTMon_full: Linear-Context Obligations
  · -- lin_valid
    intro e S hMem
    simpa [composeMonitorState] using
      mergeLin_valid p₁.initGEnv p₂.initGEnv p₁.initLin p₂.initLin
        hWT₁.lin_valid hWT₂.lin_valid hDisjG e S hMem
  · -- lin_unique
    simpa [composeMonitorState] using
      mergeLin_unique p₁.initLin p₂.initLin hWT₁.lin_unique hWT₂.lin_unique
        (fun e hIn =>
          by
            intro S' hIn₂
            rcases hIn with ⟨S, hIn₁⟩
            have hLookup₁ : lookupG p₁.initGEnv e = some S := hWT₁.lin_valid e S hIn₁
            have hLookup₂ : lookupG p₂.initGEnv e = some S' := hWT₂.lin_valid e S' hIn₂
            have hSidIn₁ : e.sid ∈ SessionsOf p₁.initGEnv := session_of_lookupG hLookup₁
            have hSidIn₂ : e.sid ∈ SessionsOf p₂.initGEnv := session_of_lookupG hLookup₂
            have hInter : e.sid ∈ SessionsOf p₁.initGEnv ∩ SessionsOf p₂.initGEnv := ⟨hSidIn₁, hSidIn₂⟩
            have hEmpty : SessionsOf p₁.initGEnv ∩ SessionsOf p₂.initGEnv = (∅ : Set SessionId) := hDisjG
            have : e.sid ∈ (∅ : Set SessionId) := by
              rw [← hEmpty]
              exact hInter
            exact this.elim)
  -- link_preserves_WTMon_full: Supply Freshness Obligations
  · -- supply_fresh (Lin)
    intro e S hMem
    have hMem' : (e, S) ∈ p₁.initMonitorState.Lin ++ p₂.initMonitorState.Lin := by
      simpa [composeMonitorState, mergeLin] using hMem
    cases List.mem_append.mp hMem' with
    | inl hIn =>
        exact Nat.lt_of_lt_of_le (hWT₁.supply_fresh e S hIn) (Nat.le_max_left _ _)
    | inr hIn =>
        exact Nat.lt_of_lt_of_le (hWT₂.supply_fresh e S hIn) (Nat.le_max_right _ _)
  · -- supply_fresh_G
    intro e S hMem
    have hMem' : (e, S) ∈ p₁.initMonitorState.G ++ p₂.initMonitorState.G := by
      simpa [composeMonitorState, mergeGEnv] using hMem
/- ## Structured Block 7 -/
    cases List.mem_append.mp hMem' with
    | inl hIn =>
        exact Nat.lt_of_lt_of_le (hWT₁.supply_fresh_G e S hIn) (Nat.le_max_left _ _)
    | inr hIn =>
        exact Nat.lt_of_lt_of_le (hWT₂.supply_fresh_G e S hIn) (Nat.le_max_right _ _)

-- WTMon Convenience Corollaries
theorem link_preserves_WTMon (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMon p₁.initMonitorState)
    (hWT₂ : WTMon p₂.initMonitorState) :
    WTMon (composeMonitorState p₁.initMonitorState p₂.initMonitorState) :=
  link_preserves_WTMon_full p₁ p₂ hLink hDisjG hWT₁ hWT₂

theorem link_preserves_WTMon_complete (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMonComplete p₁.initMonitorState)
    (hWT₂ : WTMonComplete p₂.initMonitorState) :
    WTMonComplete (composeMonitorState p₁.initMonitorState p₂.initMonitorState) := by
  refine ⟨link_preserves_WTMon_full p₁ p₂ hLink hDisjG hWT₁.1 hWT₂.1, ?_⟩
  simpa [composeMonitorState] using
    (RoleComplete_mergeGEnv p₁.initGEnv p₂.initGEnv hWT₁.2 hWT₂.2)

theorem link_preserves_WTMon_complete_full (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMonComplete p₁.initMonitorState)
    (hWT₂ : WTMonComplete p₂.initMonitorState) :
    WTMonComplete (composeMonitorState p₁.initMonitorState p₂.initMonitorState) :=
  link_preserves_WTMon_complete p₁ p₂ hLink hDisjG hWT₁ hWT₂

-- Composition and Delegation Story Theorems
theorem disjoint_sessions_independent (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOK p₁ p₂) :
    p₁.sessionId ≠ p₂.sessionId := by
  obtain ⟨hDisj, _, _⟩ := hLink
  intro heq
  simp only [InterfaceType.disjointSessions, List.all_eq_true] at hDisj
  have h := hDisj _ p₁.sessionId_in_interface
  simp only [Bool.not_eq_true'] at h
  rw [heq] at h
  have h2 : p₂.interface.sessionIds.contains p₂.sessionId = true := by
    simpa [List.contains_iff_mem] using p₂.sessionId_in_interface
  simp_all

theorem compose_deadlock_free (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOK p₁ p₂)
    (hDF₁ : ∀ r, r ∈ p₁.roles → ReachesComm (p₁.localTypes r))
    (hDF₂ : ∀ r, r ∈ p₂.roles → ReachesComm (p₂.localTypes r)) :
    ∀ r, r ∈ p₁.roles ++ p₂.roles →
      ReachesComm ((composeBundle (ProtocolBundle.fromDeployed p₁) (ProtocolBundle.fromDeployed p₂)).localTypes r) := by
  intro r hMem
  have hCases : r ∈ p₁.roles ∨ r ∈ p₂.roles := by simpa [List.mem_append] using hMem
  cases hCases with
  | inl hIn₁ =>
/- ## Structured Block 8 -/
      simpa [composeBundle, ProtocolBundle.fromDeployed, List.elem_eq_mem, hIn₁] using hDF₁ r hIn₁
  | inr hIn₂ =>
      by_cases hIn₁ : r ∈ p₁.roles
      · simpa [composeBundle, ProtocolBundle.fromDeployed, List.elem_eq_mem, hIn₁] using hDF₁ r hIn₁
      · simpa [composeBundle, ProtocolBundle.fromDeployed, List.elem_eq_mem, hIn₁, hIn₂] using hDF₂ r hIn₂

-- Harmony Preservation Corollary
/-- Static compositional harmony: linking preserves complete monitor invariants. -/
theorem link_harmony_through_link (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMonComplete p₁.initMonitorState)
    (hWT₂ : WTMonComplete p₂.initMonitorState) :
    WTMonComplete (composeMonitorState p₁.initMonitorState p₂.initMonitorState) :=
  link_preserves_WTMon_complete p₁ p₂ hLink hDisjG hWT₁ hWT₂

-- Delegation Preservation in Composed Systems
/-- Delegation inside one component of a composed system preserves composed coherence.

    Assumes delegation transforms the left component `(G₁,D₁)` into `(G₁',D₁')`
    and post-delegation disjointness/consistency side conditions hold. -/
theorem delegation_within_composed_preserves_coherent
    (G₁ G₁' G₂ : GEnv) (D₁ D₁' D₂ : DEnv)
    (s : SessionId) (A B : Role)
    (hDeleg : DelegationStep G₁ G₁' D₁ D₁' s A B)
    (hCoh₁ : Coherent G₁ D₁)
    (hCoh₂ : Coherent G₂ D₂)
    (hDisjG' : DisjointG G₁' G₂)
    (hCons₁' : DConsistent G₁' D₁')
    (hCons₂ : DConsistent G₂ D₂) :
    Coherent (mergeGEnv G₁' G₂) (mergeDEnv D₁' D₂) := by
  have hCoh₁' : Coherent G₁' D₁' :=
    delegation_preserves_coherent G₁ G₁' D₁ D₁' s A B hCoh₁ hDeleg
  exact link_preserves_coherent G₁' G₂ D₁' D₂ hCoh₁' hCoh₂ hDisjG' hCons₁' hCons₂

-- Flagship Delegation Composition Theorem
/-- Flagship composed-system conservation theorem.

If two components compose coherently before delegation, and one component performs
an admissible delegation step, then the composed system remains coherent after
delegation as well. This packages pre/post composed coherence in one statement. -/
theorem flagship_composed_system_conservation
    (G₁ G₁' G₂ : GEnv) (D₁ D₁' D₂ : DEnv)
    (s : SessionId) (A B : Role)
    (hDeleg : DelegationStep G₁ G₁' D₁ D₁' s A B)
    (hCoh₁ : Coherent G₁ D₁)
    (hCoh₂ : Coherent G₂ D₂)
    (hDisjG : DisjointG G₁ G₂)
    (hDisjG' : DisjointG G₁' G₂)
    (hCons₁ : DConsistent G₁ D₁)
    (hCons₁' : DConsistent G₁' D₁')
    (hCons₂ : DConsistent G₂ D₂) :
    Coherent (mergeGEnv G₁ G₂) (mergeDEnv D₁ D₂) ∧
      Coherent (mergeGEnv G₁' G₂) (mergeDEnv D₁' D₂) := by
  have hPre : Coherent (mergeGEnv G₁ G₂) (mergeDEnv D₁ D₂) :=
    link_preserves_coherent G₁ G₂ D₁ D₂ hCoh₁ hCoh₂ hDisjG hCons₁ hCons₂
  have hPost : Coherent (mergeGEnv G₁' G₂) (mergeDEnv D₁' D₂) :=
    delegation_within_composed_preserves_coherent
      G₁ G₁' G₂ D₁ D₁' D₂ s A B hDeleg hCoh₁ hCoh₂ hDisjG' hCons₁' hCons₂
  exact ⟨hPre, hPost⟩

-- Deployed Delegation Preservation
/-- Paper 3 story-level theorem: delegation in composed systems (deployed form).

Given two deployed protocols that link coherently, if the left protocol performs
an admissible delegation step and remains disjoint/consistent with the right
protocol, then composed coherence is preserved before and after delegation. -/
theorem delegation_in_composed_systems
    (p₁ p₂ : DeployedProtocol)
    (G₁' : GEnv) (D₁' : DEnv)
    (s : SessionId) (A B : Role)
    (hLink : LinkOKFull p₁ p₂)
    (hDeleg : DelegationStep p₁.initGEnv G₁' p₁.initDEnv D₁' s A B)
/- ## Structured Block 9 -/
    (hDisjG' : DisjointG G₁' p₂.initGEnv)
    (hCons₁' : DConsistent G₁' D₁') :
    Coherent (mergeGEnv p₁.initGEnv p₂.initGEnv) (mergeDEnv p₁.initDEnv p₂.initDEnv) ∧
      Coherent (mergeGEnv G₁' p₂.initGEnv) (mergeDEnv D₁' p₂.initDEnv) := by
  have hPre : Coherent (mergeGEnv p₁.initGEnv p₂.initGEnv) (mergeDEnv p₁.initDEnv p₂.initDEnv) :=
    LinkOKFull_coherent p₁ p₂ hLink
  have hPost : Coherent (mergeGEnv G₁' p₂.initGEnv) (mergeDEnv D₁' p₂.initDEnv) :=
    delegation_within_composed_preserves_coherent
      p₁.initGEnv G₁' p₂.initGEnv p₁.initDEnv D₁' p₂.initDEnv s A B
      hDeleg p₁.coherence_cert p₂.coherence_cert hDisjG' hCons₁' p₂.dConsistent_cert
  exact ⟨hPre, hPost⟩
-- Consolidated Composition Story Theorem
/-- Consolidated Paper 3 story theorem:
linking harmony plus delegation preservation in composed systems. -/
theorem delegation_composition_story_complete
    (p₁ p₂ : DeployedProtocol)
    (G₁' : GEnv) (D₁' : DEnv)
    (s : SessionId) (A B : Role)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMonComplete p₁.initMonitorState)
    (hWT₂ : WTMonComplete p₂.initMonitorState)
    (hDeleg : DelegationStep p₁.initGEnv G₁' p₁.initDEnv D₁' s A B)
    (hDisjG' : DisjointG G₁' p₂.initGEnv)
    (hCons₁' : DConsistent G₁' D₁') :
    WTMonComplete (composeMonitorState p₁.initMonitorState p₂.initMonitorState) ∧
      Coherent (mergeGEnv p₁.initGEnv p₂.initGEnv) (mergeDEnv p₁.initDEnv p₂.initDEnv) ∧
      Coherent (mergeGEnv G₁' p₂.initGEnv) (mergeDEnv D₁' p₂.initDEnv) := by
  have hHarmony :
      WTMonComplete (composeMonitorState p₁.initMonitorState p₂.initMonitorState) :=
    link_harmony_through_link p₁ p₂ hLink hDisjG hWT₁ hWT₂
  have hCoherentPair :
      Coherent (mergeGEnv p₁.initGEnv p₂.initGEnv) (mergeDEnv p₁.initDEnv p₂.initDEnv) ∧
        Coherent (mergeGEnv G₁' p₂.initGEnv) (mergeDEnv D₁' p₂.initDEnv) :=
    delegation_in_composed_systems p₁ p₂ G₁' D₁' s A B hLink hDeleg hDisjG' hCons₁'
  exact ⟨hHarmony, hCoherentPair.1, hCoherentPair.2⟩

end
