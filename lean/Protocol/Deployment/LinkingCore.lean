import Protocol.Deployment.Merge
import Protocol.Typing.MergeLemmas
import Protocol.Typing.StepLemmas
import Protocol.Coherence.Renaming
import Protocol.Coherence.Delegation

/-! # Protocol.Deployment.LinkingCore

Foundational merge/disjointness infrastructure for deployment linking.
-/

/-
The Problem. Linking proofs require reusable lemmas for merged lookups, disjoint sessions,
and coherence transfer across merged environments.

Solution Structure. Establish session-membership, disjointness lookup facts, and core
coherence-preservation lemmas used by high-level linking theorems.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical
section

/-! ## Linking Coherence Infrastructure -/

/-- An endpoint lookup witnesses membership of its session in `SessionsOf`. -/
theorem session_of_lookupG {G : GEnv} {e : Endpoint} {L : LocalType}
    (h : lookupG G e = some L) : e.sid ∈ SessionsOf G :=
  ⟨e, L, h, rfl⟩

theorem sid_not_in_right_of_left {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂)
    {s : SessionId} (hIn : s ∈ SessionsOf G₁) :
    s ∉ SessionsOf G₂ := by
  intro hIn₂
  have hInter : s ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn, hIn₂⟩
  have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = ∅ := hDisj
  have : s ∈ (∅ : Set SessionId) := by
    rw [← hEmpty]
    exact hInter
  exact this.elim

theorem sid_not_in_left_of_right {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂)
    {s : SessionId} (hIn : s ∈ SessionsOf G₂) :
    s ∉ SessionsOf G₁ := by
  exact sid_not_in_right_of_left (G₁ := G₂) (G₂ := G₁) (DisjointG_symm hDisj) hIn

theorem lookupD_none_of_notin_sessions {G : GEnv} {D : DEnv} {e : Edge}
    (hCons : DConsistent G D) (hNot : e.sid ∉ SessionsOf G) :
    D.find? e = none := by
  by_contra hSome
  cases hFind : D.find? e with
  | none =>
      exact hSome hFind
  | some ts =>
      have hSid : e.sid ∈ SessionsOfD D := ⟨e, ts, hFind, rfl⟩
      exact hNot (hCons hSid)

theorem lookupBuf_none_of_notin_sessions {G : GEnv} {B : Buffers} {e : Edge}
    (hCons : BConsistent G B) (hNot : e.sid ∉ SessionsOf G) :
    B.lookup e = none := by
  by_contra hSome
  cases hFind : B.lookup e with
  | none =>
      exact hSome hFind
  | some buf =>
      exact hNot (hCons e buf hFind)

/-! ## Typing Lifts Through Merged GEnv -/

theorem BufferTyped_monoG {G G' : GEnv} {D : DEnv} {bufs : Buffers} {e : Edge} :
    BufferTyped G D bufs e →
    (∀ ep L, lookupG G ep = some L → lookupG G' ep = some L) →
    BufferTyped G' D bufs e := by
  intro hBT hMono
  rcases hBT with ⟨hLen, hTy⟩
  refine ⟨hLen, ?_⟩
  intro i hi
  exact HasTypeVal_mono G G' _ _ (hTy i hi) hMono

private theorem HasTypeVal_lift_left {G₁ G₂ : GEnv} {v : Value} {T : ValType} :
    HasTypeVal G₁ v T →
    HasTypeVal (mergeGEnv G₁ G₂) v T := by
  intro hVal
  refine HasTypeVal_mono G₁ (mergeGEnv G₁ G₂) v T hVal ?_
  intro ep L hLookup
  simpa [mergeGEnv] using
    (lookupG_append_left (G₁ := G₁) (G₂ := G₂) (e := ep) (L := L) hLookup)

private theorem HasTypeVal_lift_right {G₁ G₂ : GEnv}
    (hDisj : DisjointG G₁ G₂) {v : Value} {T : ValType} :
    HasTypeVal G₂ v T →
    HasTypeVal (mergeGEnv G₁ G₂) v T := by
  intro hVal
  refine HasTypeVal_mono G₂ (mergeGEnv G₁ G₂) v T hVal ?_
  intro ep L hLookup
  have hIn₂ : ep.sid ∈ SessionsOf G₂ := session_of_lookupG hLookup
  have hNot₁ : ep.sid ∉ SessionsOf G₁ := sid_not_in_left_of_right hDisj hIn₂
  have hNone₁ : lookupG G₁ ep = none := lookupG_none_of_not_session hNot₁
  have hEq := lookupG_append_right (G₁ := G₁) (G₂ := G₂) (e := ep) hNone₁
  simpa [mergeGEnv, hEq] using hLookup

/-! ## Active-Edge Split Across Disjoint Merge -/

theorem ActiveEdge_mergeGEnv_split {G₁ G₂ : GEnv} {e : Edge}
    (hDisj : DisjointG G₁ G₂)
    (hActive : ActiveEdge (mergeGEnv G₁ G₂) e) :
    ActiveEdge G₁ e ∨ ActiveEdge G₂ e := by
  rcases hActive with ⟨hSenderSome, hRecvSome⟩
  rcases Option.isSome_iff_exists.mp hSenderSome with ⟨Lsender, hGsender⟩
  rcases Option.isSome_iff_exists.mp hRecvSome with ⟨Lrecv, hGrecv⟩
  have hRecvCases :=
    lookupG_append_inv (G₁ := G₁) (G₂ := G₂) (e := { sid := e.sid, role := e.receiver }) (L := Lrecv)
      (by simpa [mergeGEnv] using hGrecv)
  cases hRecvCases with
  | inl hRecvLeft =>
      have hSidIn₁ : e.sid ∈ SessionsOf G₁ :=
        ⟨{ sid := e.sid, role := e.receiver }, Lrecv, hRecvLeft, rfl⟩
      have hSidNotIn₂ : e.sid ∉ SessionsOf G₂ := sid_not_in_right_of_left hDisj hSidIn₁
      have hSenderCases :=
        lookupG_append_inv (G₁ := G₁) (G₂ := G₂) (e := { sid := e.sid, role := e.sender }) (L := Lsender)
          (by simpa [mergeGEnv] using hGsender)
      have hSenderLeft : lookupG G₁ { sid := e.sid, role := e.sender } = some Lsender := by
        cases hSenderCases with
        | inl h =>
            exact h
        | inr h =>
            have hSidIn₂ : e.sid ∈ SessionsOf G₂ :=
              ⟨{ sid := e.sid, role := e.sender }, Lsender, h.2, rfl⟩
            exact (hSidNotIn₂ hSidIn₂).elim
      left
      exact ActiveEdge_of_endpoints hSenderLeft hRecvLeft
  | inr hRecvRight =>
      have hSidIn₂ : e.sid ∈ SessionsOf G₂ :=
        ⟨{ sid := e.sid, role := e.receiver }, Lrecv, hRecvRight.2, rfl⟩
      have hSidNotIn₁ : e.sid ∉ SessionsOf G₁ := sid_not_in_left_of_right hDisj hSidIn₂
      have hSenderCases :=
        lookupG_append_inv (G₁ := G₁) (G₂ := G₂) (e := { sid := e.sid, role := e.sender }) (L := Lsender)
          (by simpa [mergeGEnv] using hGsender)
      have hSenderRight : lookupG G₂ { sid := e.sid, role := e.sender } = some Lsender := by
        cases hSenderCases with
        | inl h =>
            have hSidIn₁ : e.sid ∈ SessionsOf G₁ :=
              ⟨{ sid := e.sid, role := e.sender }, Lsender, h, rfl⟩
            exact (hSidNotIn₁ hSidIn₁).elim
        | inr h =>
            exact h.2
      right
      exact ActiveEdge_of_endpoints hSenderRight hRecvRight.2

/-! ## Main Linking Coherence Theorem -/

/-- Linking preserves coherence for disjoint session spaces. -/
theorem link_preserves_coherent
    (G₁ G₂ : GEnv) (D₁ D₂ : DEnv)
    (hCoh₁ : Coherent G₁ D₁)
    (hCoh₂ : Coherent G₂ D₂)
    (hDisjG : DisjointG G₁ G₂)
    (hCons₁ : DConsistent G₁ D₁)
    (hCons₂ : DConsistent G₂ D₂) :
    Coherent (mergeGEnv G₁ G₂) (mergeDEnv D₁ D₂) := by
  simpa [mergeGEnv, mergeDEnv] using
    (Coherent_merge (G₁ := G₁) (G₂ := G₂) (D₁ := D₁) (D₂ := D₂)
      hCoh₁ hCoh₂ hDisjG hCons₁ hCons₂)


end
