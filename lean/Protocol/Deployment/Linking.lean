import Protocol.Deployment.Merge
import Protocol.Typing.Compatibility
import Protocol.Coherence.Renaming

/-! # Protocol.Deployment.Linking

Linking theorems and composition preservation results.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Linking Coherence Infrastructure

Reference: Aristotle file 18 (link_preserves_coherent_active)
-/

/-- An endpoint's session is in the sessions of its GEnv. -/
theorem session_of_lookupG {G : GEnv} {e : Endpoint} {L : LocalType}
    (h : lookupG G e = some L) : e.sid ∈ SessionsOf G :=
  ⟨e, L, h, rfl⟩

/-- If sessions are disjoint and e has a lookup in G₁, then lookup in G₂ returns none. -/
theorem lookupG_none_of_disjoint {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType}
    (hDisj : DisjointG G₁ G₂)
    (hG₁ : lookupG G₁ e = some L) :
    lookupG G₂ e = none := by
  by_contra hSome
  cases hG₂ : lookupG G₂ e with
  | none => exact hSome hG₂
  | some L₂ =>
    have hIn₁ : e.sid ∈ SessionsOf G₁ := session_of_lookupG hG₁
    have hIn₂ : e.sid ∈ SessionsOf G₂ := session_of_lookupG hG₂
    have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn₁, hIn₂⟩
    simp only [DisjointG, GEnvDisjoint] at hDisj
    rw [hDisj] at hInter
    exact hInter.elim

/-- If sessions are disjoint and e has a lookup in G₂, then lookup in G₁ returns none. -/
theorem lookupG_none_of_disjoint' {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType}
    (hDisj : DisjointG G₁ G₂)
    (hG₂ : lookupG G₂ e = some L) :
    lookupG G₁ e = none := by
  by_contra hSome
  cases hG₁ : lookupG G₁ e with
  | none => exact hSome hG₁
  | some L₁ =>
    have hIn₁ : e.sid ∈ SessionsOf G₁ := session_of_lookupG hG₁
    have hIn₂ : e.sid ∈ SessionsOf G₂ := session_of_lookupG hG₂
    have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn₁, hIn₂⟩
    simp only [DisjointG, GEnvDisjoint] at hDisj
    rw [hDisj] at hInter
    exact hInter.elim

/-- ActiveEdge in merged GEnv with disjoint sessions: both endpoints in G₁ or both in G₂. -/
theorem ActiveEdge_mergeGEnv_split {G₁ G₂ : GEnv} {e : Edge}
    (hDisj : DisjointG G₁ G₂)
    (hActive : ActiveEdge (mergeGEnv G₁ G₂) e) :
    ActiveEdge G₁ e ∨ ActiveEdge G₂ e := by
  rcases hActive with ⟨hSender, hRecv⟩
  -- Get the actual lookups from isSome
  rcases Option.isSome_iff_exists.mp hSender with ⟨Ls, hLs⟩
  rcases Option.isSome_iff_exists.mp hRecv with ⟨Lr, hLr⟩
  -- Invert the merged lookups
  cases MergeGEnv_inv hLs with
  | inl hG₁s =>
    -- Sender in G₁
    left
    have hG₂s_none : lookupG G₂ ⟨e.sid, e.sender⟩ = none :=
      lookupG_none_of_disjoint hDisj hG₁s
    -- Receiver must also be in G₁ (same session, disjoint)
    cases MergeGEnv_inv hLr with
    | inl hG₁r =>
      exact ⟨Option.isSome_iff_exists.mpr ⟨_, hG₁s⟩, Option.isSome_iff_exists.mpr ⟨_, hG₁r⟩⟩
    | inr hG₂r =>
      -- Contradiction: sender in G₁, receiver in G₂, but same session
      have hIn₁ : e.sid ∈ SessionsOf G₁ := session_of_lookupG hG₁s
      have hIn₂ : e.sid ∈ SessionsOf G₂ := session_of_lookupG hG₂r.2
      have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn₁, hIn₂⟩
      simp only [DisjointG, GEnvDisjoint] at hDisj
      rw [hDisj] at hInter
      exact hInter.elim
  | inr hG₂s =>
    -- Sender in G₂
    right
    have hG₁s_none := hG₂s.1
    -- Receiver must also be in G₂ (same session, disjoint)
    cases MergeGEnv_inv hLr with
    | inl hG₁r =>
      -- Contradiction: sender in G₂, receiver in G₁, but same session
      have hIn₁ : e.sid ∈ SessionsOf G₁ := session_of_lookupG hG₁r
      have hIn₂ : e.sid ∈ SessionsOf G₂ := session_of_lookupG hG₂s.2
      have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn₁, hIn₂⟩
      simp only [DisjointG, GEnvDisjoint] at hDisj
      rw [hDisj] at hInter
      exact hInter.elim
    | inr hG₂r =>
      exact ⟨Option.isSome_iff_exists.mpr ⟨_, hG₂s.2⟩, Option.isSome_iff_exists.mpr ⟨_, hG₂r.2⟩⟩

/-- DEnv lookup in merged env when edge session not in G₂. -/
theorem lookupD_mergeD_left {G₂ : GEnv} {D₁ D₂ : DEnv} {e : Edge}
    (hCons₂ : DConsistent G₂ D₂)
    (hNotIn : e.sid ∉ SessionsOf G₂) :
    lookupD (mergeDEnv D₁ D₂) e = lookupD D₁ e := by
  -- Edge session not in G₂ → edge not in D₂ (by DConsistent)
  have hD₂_none : D₂.find? e = none := by
    by_contra hSome
    cases hFind : D₂.find? e with
    | none => exact hSome hFind
    | some ts =>
      have hSid : e.sid ∈ SessionsOfD D₂ := ⟨e, ts, hFind, rfl⟩
      have hSidG : e.sid ∈ SessionsOf G₂ := hCons₂ hSid
      exact hNotIn hSidG
  -- With D₂.find? e = none, merged lookup equals D₁ lookup
  exact lookupD_append_left_of_right_none hD₂_none

/-- DEnv lookup in merged env when edge session not in G₁. -/
theorem lookupD_mergeD_right {G₁ : GEnv} {D₁ D₂ : DEnv} {e : Edge}
    (hCons₁ : DConsistent G₁ D₁)
    (hNotIn : e.sid ∉ SessionsOf G₁) :
    lookupD (mergeDEnv D₁ D₂) e = lookupD D₂ e := by
  -- Edge session not in G₁ → edge not in D₁ (by DConsistent)
  have hD₁_none : D₁.find? e = none := by
    by_contra hSome
    cases hFind : D₁.find? e with
    | none => exact hSome hFind
    | some ts =>
      have hSid : e.sid ∈ SessionsOfD D₁ := ⟨e, ts, hFind, rfl⟩
      have hSidG : e.sid ∈ SessionsOf G₁ := hCons₁ hSid
      exact hNotIn hSidG
  -- With D₁.find? e = none, merged lookup equals D₂ lookup
  exact lookupD_append_right hD₁_none

/-! ## Main Linking Coherence Theorem

Reference: Aristotle file 18 (link_preserves_coherent_active)

This theorem proves that linking two coherent protocol configurations
produces a coherent configuration, under session disjointness and
DEnv consistency assumptions.
-/

/-- Linking preserves coherence: if G₁, D₁ and G₂, D₂ are coherent
    with disjoint sessions, then the merged environments are coherent. -/
theorem link_preserves_coherent
    (G₁ G₂ : GEnv) (D₁ D₂ : DEnv)
    (hCoh₁ : Coherent G₁ D₁)
    (hCoh₂ : Coherent G₂ D₂)
    (hDisjG : DisjointG G₁ G₂)
    (hCons₁ : DConsistent G₁ D₁)
    (hCons₂ : DConsistent G₂ D₂) :
    Coherent (mergeGEnv G₁ G₂) (mergeDEnv D₁ D₂) := by
  intro e hActive
  -- Split: both endpoints in G₁ or both in G₂
  cases ActiveEdge_mergeGEnv_split hDisjG hActive with
  | inl hActive₁ =>
    -- Edge active in G₁: use Coherent G₁ D₁
    have hCoh := hCoh₁ e hActive₁
    -- EdgeCoherent G₁ D₁ e says: ∀ Lrecv, lookupG G₁ receiverEp = some Lrecv →
    --   ∃ Lsender, lookupG G₁ senderEp = some Lsender ∧ (Consume ...).isSome
    intro Lrecv hLrecv
    -- Translate receiver lookup from merged to G₁
    have hG₂_none : lookupG G₂ ⟨e.sid, e.receiver⟩ = none := by
      rcases Option.isSome_iff_exists.mp hActive₁.2 with ⟨Lr, hLr⟩
      exact lookupG_none_of_disjoint hDisj hLr
    have hLrecv₁ : lookupG G₁ ⟨e.sid, e.receiver⟩ = some Lrecv := by
      have h := MergeGEnv_inv hLrecv
      cases h with
      | inl h => exact h
      | inr h => simp [h.1] at hG₂_none
    -- Apply coherence from G₁
    rcases hCoh Lrecv hLrecv₁ with ⟨Lsender, hLsender, hConsume⟩
    -- Translate sender lookup to merged
    have hLsender' : lookupG (mergeGEnv G₁ G₂) ⟨e.sid, e.sender⟩ = some Lsender :=
      MergeGEnv_Left G₁ G₂ ⟨e.sid, e.sender⟩ Lsender hLsender
    -- Translate DEnv lookup: edge session in G₁, so not in G₂ (disjoint)
    have hNotIn₂ : e.sid ∉ SessionsOf G₂ := by
      intro hIn₂
      have hIn₁ : e.sid ∈ SessionsOf G₁ := session_of_lookupG hLrecv₁
      have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn₁, hIn₂⟩
      simp only [DisjointG, GEnvDisjoint] at hDisjG
      rw [hDisjG] at hInter
      exact hInter.elim
    have hLookupD : lookupD (mergeDEnv D₁ D₂) e = lookupD D₁ e :=
      lookupD_mergeD_left hCons₂ hNotIn₂
    -- Conclude
    refine ⟨Lsender, hLsender', ?_⟩
    rw [hLookupD]
    exact hConsume
  | inr hActive₂ =>
    -- Edge active in G₂: symmetric case using Coherent G₂ D₂
    have hCoh := hCoh₂ e hActive₂
    intro Lrecv hLrecv
    -- Translate receiver lookup from merged to G₂
    have hG₁_none : lookupG G₁ ⟨e.sid, e.receiver⟩ = none := by
      rcases Option.isSome_iff_exists.mp hActive₂.2 with ⟨Lr, hLr⟩
      exact lookupG_none_of_disjoint' hDisjG hLr
    have hLrecv₂ : lookupG G₂ ⟨e.sid, e.receiver⟩ = some Lrecv := by
      have h := MergeGEnv_inv hLrecv
      cases h with
      | inl h => simp [h] at hG₁_none
      | inr h => exact h.2
    -- Apply coherence from G₂
    rcases hCoh Lrecv hLrecv₂ with ⟨Lsender, hLsender, hConsume⟩
    -- Translate sender lookup to merged
    have hLsender' : lookupG (mergeGEnv G₁ G₂) ⟨e.sid, e.sender⟩ = some Lsender := by
      have hG₁s_none : lookupG G₁ ⟨e.sid, e.sender⟩ = none :=
        lookupG_none_of_disjoint' hDisjG hLsender
      exact MergeGEnv_Right G₁ G₂ ⟨e.sid, e.sender⟩ hG₁s_none ▸ hLsender
    -- Translate DEnv lookup: edge session in G₂, so not in G₁ (disjoint)
    have hNotIn₁ : e.sid ∉ SessionsOf G₁ := by
      intro hIn₁
      have hIn₂ : e.sid ∈ SessionsOf G₂ := session_of_lookupG hLrecv₂
      have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn₁, hIn₂⟩
      simp only [DisjointG, GEnvDisjoint] at hDisjG
      rw [hDisjG] at hInter
      exact hInter.elim
    have hLookupD : lookupD (mergeDEnv D₁ D₂) e = lookupD D₂ e :=
      lookupD_mergeD_right hCons₁ hNotIn₁
    -- Conclude
    refine ⟨Lsender, hLsender', ?_⟩
    rw [hLookupD]
    exact hConsume

/-! ## Linking Theorems -/

axiom mergeBufs_typed (G₁ G₂ : GEnv) (D₁ D₂ : DEnv) (B₁ B₂ : Buffers)
    (hTyped₁ : BuffersTyped G₁ D₁ B₁)
    (hTyped₂ : BuffersTyped G₂ D₂ B₂)
    (hDisjG : DisjointG G₁ G₂)
    (hConsD₂ : DConsistent G₂ D₂)
    (hConsB₁ : BConsistent G₁ B₁)
    (hDom₁ : BufsDom B₁ D₁) :
    BuffersTyped (mergeGEnv G₁ G₂) (mergeDEnv D₁ D₂) (mergeBufs B₁ B₂)

axiom mergeLin_valid (G₁ G₂ : GEnv) (L₁ L₂ : LinCtx)
    (hValid₁ : ∀ e S, (e, S) ∈ L₁ → lookupG G₁ e = some S)
    (hValid₂ : ∀ e S, (e, S) ∈ L₂ → lookupG G₂ e = some S)
    (hDisjointG : DisjointG G₁ G₂) :
    ∀ e S, (e, S) ∈ mergeLin L₁ L₂ → lookupG (mergeGEnv G₁ G₂) e = some S

axiom mergeLin_unique (L₁ L₂ : LinCtx)
    (hUnique₁ : L₁.Pairwise (fun a b => a.1 ≠ b.1))
    (hUnique₂ : L₂.Pairwise (fun a b => a.1 ≠ b.1))
    (hDisjoint : ∀ e, (∃ S, (e, S) ∈ L₁) → ∀ S', (e, S') ∉ L₂) :
    (mergeLin L₁ L₂).Pairwise (fun a b => a.1 ≠ b.1)

axiom link_preserves_WTMon_full (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMon p₁.initMonitorState)
    (hWT₂ : WTMon p₂.initMonitorState) :
    WTMon (composeMonitorState p₁.initMonitorState p₂.initMonitorState)

axiom link_preserves_WTMon (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMon p₁.initMonitorState)
    (hWT₂ : WTMon p₂.initMonitorState) :
    WTMon (composeMonitorState p₁.initMonitorState p₂.initMonitorState)

axiom link_preserves_WTMon_complete (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMonComplete p₁.initMonitorState)
    (hWT₂ : WTMonComplete p₂.initMonitorState) :
    WTMonComplete (composeMonitorState p₁.initMonitorState p₂.initMonitorState)

axiom link_preserves_WTMon_complete_full (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOKFull p₁ p₂)
    (hDisjG : DisjointG p₁.initGEnv p₂.initGEnv)
    (hWT₁ : WTMonComplete p₁.initMonitorState)
    (hWT₂ : WTMonComplete p₂.initMonitorState) :
    WTMonComplete (composeMonitorState p₁.initMonitorState p₂.initMonitorState)

theorem disjoint_sessions_independent (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOK p₁ p₂) :
    p₁.sessionId ≠ p₂.sessionId := by
  obtain ⟨hDisj, _, _⟩ := hLink
  intro heq
  simp only [InterfaceType.disjointSessions, List.all_eq_true] at hDisj
  have h := hDisj _ p₁.sessionId_in_interface
  simp only [Bool.not_eq_true'] at h
  rw [heq] at h
  have h2 : p₂.interface.sessionIds.contains p₂.sessionId = true :=
    List.contains_iff.mpr ⟨p₂.sessionId, p₂.sessionId_in_interface, beq_self_eq_true _⟩
  simp_all

axiom compose_deadlock_free (p₁ p₂ : DeployedProtocol)
    (hLink : LinkOK p₁ p₂)
    (hDF₁ : ∀ r, r ∈ p₁.roles → ReachesComm (p₁.localTypes r))
    (hDF₂ : ∀ r, r ∈ p₂.roles → ReachesComm (p₂.localTypes r)) :
    ∀ r, r ∈ p₁.roles ++ p₂.roles →
      ReachesComm ((composeBundle (ProtocolBundle.fromDeployed p₁) (ProtocolBundle.fromDeployed p₂)).localTypes r)
