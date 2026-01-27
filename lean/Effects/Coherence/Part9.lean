import Effects.Coherence.Part2

/-!
# MPST Coherence

This module defines the coherence invariant for multiparty session types.

In binary session types, coherence states that after consuming in-flight messages,
dual endpoints have dual types. In MPST, this generalizes to:

**For each directed edge (p → q) in session s:**
1. The sender's local type G[s,p] is consistent with what was sent on D[s,p,q]
2. The receiver's local type G[s,q] is consistent with what must be received on D[s,p,q]
3. The communication patterns match: sends to q align with branches from p

## Consume Function

The `Consume` function models how a local type evolves as buffered messages arrive.
For role p's view:
- `Consume L [] = some L` (no messages → unchanged)
- `Consume (recv q T L) (T :: ts) = Consume L ts` (receive consumes a message)
- `Consume (branch q bs) _ = ...` (branch must handle incoming label)

## Coherence Invariant

`Coherent G D` states that for every session and every directed edge:
- Sender's continuation after sending matches what's in the queue
- Receiver's continuation after consuming matches sender's intent

## Proof Technique: Edge Case Analysis

The key preservation proofs (`Coherent_send_preserved`, `Coherent_recv_preserved`)
proceed by case analysis on which edge we're checking coherence for:

1. **e = updated edge**: The sender's/receiver's local type changed, trace changed
2. **e involves modified endpoint**: The other endpoint of e was modified
3. **e unrelated**: Neither endpoint was modified, environments unchanged at e

This 3-way case split is the core proof technique for coherence preservation.
Adapted from binary session types where the split is: a = e, a = e.dual, a unrelated.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

noncomputable section

/-! ## Renaming Preservation Theorems -/

/-- Coherence is preserved under session renaming.
    This is the key lemma for protocol composition: renaming sessions
    doesn't break the coherence invariant. -/
theorem CoherentRenaming (ρ : SessionRenaming) (G : GEnv) (D : DEnv)
    (hCoh : Coherent G D) :
    Coherent (renameGEnv ρ G) (renameDEnv ρ D) := by
  intro e Lsender Lrecv hGsender hGrecv
  -- If lookups succeed in renamed env, preimage endpoints exist
  obtain ⟨senderEp', Lsender', hsenderEq, hLsenderEq, hGsender'⟩ :=
    lookupG_rename_inv ρ G _ _ hGsender
  obtain ⟨recvEp', Lrecv', hrecvEq, hLrecvEq, hGrecv'⟩ :=
    lookupG_rename_inv ρ G _ _ hGrecv
  -- The sender/receiver roles in the renamed edge must match
  have hSenderRole : e.sender = senderEp'.role := by
    have h := congrArg Endpoint.role hsenderEq
    simp only [renameEndpoint] at h
    exact h
  have hRecvRole : e.receiver = recvEp'.role := by
    have h := congrArg Endpoint.role hrecvEq
    simp only [renameEndpoint] at h
    exact h
  -- The sessions must also match (from renaming)
  have hSid1 : e.sid = ρ.f senderEp'.sid := by
    have h := congrArg Endpoint.sid hsenderEq
    simp only [renameEndpoint] at h
    exact h
  have hSid2 : e.sid = ρ.f recvEp'.sid := by
    have h := congrArg Endpoint.sid hrecvEq
    simp only [renameEndpoint] at h
    exact h
  -- Therefore senderEp'.sid = recvEp'.sid (by injectivity of ρ.f)
  have hSidEq : senderEp'.sid = recvEp'.sid := ρ.inj _ _ (hSid1.symm.trans hSid2)
  -- Build the original edge
  let e' : Edge := { sid := senderEp'.sid, sender := senderEp'.role, receiver := recvEp'.role }
  -- Show e = renameEdge ρ e'
  have hEdgeEq : e = renameEdge ρ e' := by
    simp only [renameEdge, e']
    have h1 : e.sid = ρ.f senderEp'.sid := hSid1
    have h2 : e.sender = senderEp'.role := hSenderRole
    have h3 : e.receiver = recvEp'.role := hRecvRole
    -- Construct equality using Edge.eq_iff
    rw [Edge.eq_iff]
    exact ⟨h1, h2, h3⟩
  -- The trace is the renamed original trace
  have hTraceEq : lookupD (renameDEnv ρ D) e = (lookupD D e').map (renameValType ρ) := by
    simpa [hEdgeEq] using (lookupD_rename (ρ:=ρ) (D:=D) (e:=e'))
  -- Apply original coherence at e'
  have hCoh' := hCoh e' Lsender' Lrecv'
  -- Need to show the endpoint conditions match
  have hGsender'' : lookupG G { sid := e'.sid, role := e'.sender } = some Lsender' := by
    simpa [e'] using hGsender'
  have hGrecv'' : lookupG G { sid := e'.sid, role := e'.receiver } = some Lrecv' := by
    have hSid : e'.sid = recvEp'.sid := by
      -- e'.sid = senderEp'.sid and senderEp'.sid = recvEp'.sid
      simpa [e'] using hSidEq
    have hEpEq : { sid := e'.sid, role := e'.receiver : Endpoint } = recvEp' := by
      cases recvEp' with
      | mk sid role =>
          simp [e', hSidEq]
    simpa [hEpEq] using hGrecv'
  have hConsumeOrig : (Consume e'.sender Lrecv' (lookupD D e')).isSome :=
    hCoh' hGsender'' hGrecv''
  have hConsumeRen :
      (Consume e'.sender (renameLocalType ρ Lrecv') ((lookupD D e').map (renameValType ρ))).isSome := by
    have hEq := Consume_rename (ρ:=ρ) (from_:=e'.sender) (L:=Lrecv') (ts:=lookupD D e')
    cases hCons : Consume e'.sender Lrecv' (lookupD D e') with
    | none =>
        have hFalse : False := by
          simpa [hCons] using hConsumeOrig
        exact hFalse.elim
    | some L' =>
        simp [hEq, hCons]
  -- sender role is preserved by renaming, and traces are renamed
  simpa [e', hSenderRole, hLrecvEq, hTraceEq] using hConsumeRen

/-- HasTypeVal is preserved under session renaming. -/
theorem HasTypeVal_rename (ρ : SessionRenaming) (G : GEnv) (v : Value) (T : ValType) :
    HasTypeVal G v T →
    HasTypeVal (renameGEnv ρ G) (renameValue ρ v) (renameValType ρ T) := by
  intro h
  induction h with
  | unit => exact HasTypeVal.unit
  | bool b => exact HasTypeVal.bool b
  | nat n => exact HasTypeVal.nat n
  | string s => exact HasTypeVal.string s
  | prod _ _ ih1 ih2 => exact HasTypeVal.prod ih1 ih2
  | @chan e L hLookup =>
    have hLookup' :
        lookupG (renameGEnv ρ G) (renameEndpoint ρ e) = some (renameLocalType ρ L) := by
      have hLookupRen := lookupG_rename (ρ:=ρ) (G:=G) (e:=e)
      simpa [hLookup] using hLookupRen
    exact HasTypeVal.chan hLookup'

/-- BuffersTyped is preserved under session renaming. -/
theorem BuffersTypedRenaming (ρ : SessionRenaming) (G : GEnv) (D : DEnv) (bufs : Buffers)
    (hTyped : BuffersTyped G D bufs) :
    BuffersTyped (renameGEnv ρ G) (renameDEnv ρ D) (renameBufs ρ bufs) := by
  intro e
  simp only [BufferTyped]
  -- Check if e is in the image of renameEdge
  by_cases h : ∃ e', renameEdge ρ e' = e
  case pos =>
    obtain ⟨e', he'⟩ := h
    subst he'
    -- Use original BufferTyped at e'
    have hTyped' := hTyped e'
    simp only [BufferTyped] at hTyped'
    obtain ⟨hLen, hElem⟩ := hTyped'
    -- Rewrite lookups using simp to avoid dependent type issues
    simp only [lookupBuf_rename, lookupD_rename]
    have hLen' :
        ((lookupBuf bufs e').map (renameValue ρ)).length =
          ((lookupD D e').map (renameValType ρ)).length := by
      simpa [List.length_map] using hLen
    refine ⟨hLen', ?_⟩
    intro i hi
    have hi' : i < (lookupBuf bufs e').length := by
      simpa [List.length_map] using hi
    have hElem' := hElem i hi'
    have hRen := HasTypeVal_rename ρ G _ _ hElem'
    simpa [lookupBuf_rename, lookupD_rename, List.length_map] using hRen
  case neg =>
    -- Edge not in image - both lookups return empty
    -- This case requires showing that lookups in renamed environments
    -- return [] for edges outside the renaming range
    have hTraceEmpty : lookupD (renameDEnv ρ D) e = [] := by
      by_contra hne
      obtain ⟨e', he', _⟩ := lookupD_rename_inv ρ D e hne
      exact h ⟨e', he'.symm⟩
    have hBufEmpty : lookupBuf (renameBufs ρ bufs) e = [] := by
      by_contra hne
      obtain ⟨e', he', _⟩ := lookupBuf_rename_inv ρ bufs e hne
      exact h ⟨e', he'.symm⟩
    refine ⟨?_, ?_⟩
    · simp [hBufEmpty, hTraceEmpty]
    · intro i hi
      have hi' : False := by
        simpa [hBufEmpty] using hi
      exact hi'.elim

/-! ## Disjointness Infrastructure -/

/-- Sessions present in a GEnv. -/
def SessionsOf (G : GEnv) : Set SessionId :=
  { s | ∃ e L, lookupG G e = some L ∧ e.sid = s }

/-- Buffers are consistent with GEnv: every stored edge belongs to a session in G. -/
def BConsistent (G : GEnv) (B : Buffers) : Prop :=
  -- Any buffer entry witnesses that its session exists in G.
  ∀ e buf, B.lookup e = some buf → e.sid ∈ SessionsOf G

/-- Buffer domains cover DEnv domains: no trace exists without a buffer entry. -/
def BufsDom (B : Buffers) (D : DEnv) : Prop :=
  -- If a buffer key is missing, the DEnv has no key either.
  ∀ e, B.lookup e = none → D.find? e = none

/-- Two GEnvs are disjoint if they have no common sessions. -/
def GEnvDisjoint (G1 G2 : GEnv) : Prop :=
  SessionsOf G1 ∩ SessionsOf G2 = ∅

/-- Two session renamings are disjoint on given GEnvs. -/
def RenamingsDisjoint (ρ1 ρ2 : SessionRenaming) (G1 G2 : GEnv) : Prop :=
  ∀ s1 ∈ SessionsOf G1, ∀ s2 ∈ SessionsOf G2, ρ1.f s1 ≠ ρ2.f s2

/-- Renamed environments are disjoint if renamings are disjoint. -/
theorem RenamedDisjoint (ρ1 ρ2 : SessionRenaming) (G1 G2 : GEnv)
    (hDisj : RenamingsDisjoint ρ1 ρ2 G1 G2) :
    GEnvDisjoint (renameGEnv ρ1 G1) (renameGEnv ρ2 G2) := by
  simp only [GEnvDisjoint, Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff]
  intro s ⟨hS1, hS2⟩
  simp only [SessionsOf, Set.mem_setOf_eq] at hS1 hS2
  obtain ⟨e1, L1, hLookup1, hSid1⟩ := hS1
  obtain ⟨e2, L2, hLookup2, hSid2⟩ := hS2
  -- Get preimage endpoints
  obtain ⟨e1', L1', he1Eq, hL1Eq, hLookup1'⟩ :=
    lookupG_rename_inv ρ1 G1 e1 L1 hLookup1
  obtain ⟨e2', L2', he2Eq, hL2Eq, hLookup2'⟩ :=
    lookupG_rename_inv ρ2 G2 e2 L2 hLookup2
  -- e1.sid = ρ1.f e1'.sid and e2.sid = ρ2.f e2'.sid
  have hSid1' : e1.sid = ρ1.f e1'.sid := by rw [he1Eq]; simp only [renameEndpoint]
  have hSid2' : e2.sid = ρ2.f e2'.sid := by rw [he2Eq]; simp only [renameEndpoint]
  -- But s = e1.sid = e2.sid
  have hContra : ρ1.f e1'.sid = ρ2.f e2'.sid := by
    rw [← hSid1', ← hSid2', hSid1, hSid2]
  -- e1'.sid ∈ SessionsOf G1, e2'.sid ∈ SessionsOf G2
  have hIn1 : e1'.sid ∈ SessionsOf G1 := ⟨e1', L1', hLookup1', rfl⟩
  have hIn2 : e2'.sid ∈ SessionsOf G2 := ⟨e2', L2', hLookup2', rfl⟩
  exact hDisj _ hIn1 _ hIn2 hContra

/-! ## Dual Relation for Local Types -/

/-- Duality relation for local types.
    Two types are dual if they communicate in complementary ways. -/
inductive Dual : LocalType → LocalType → Prop where
  | end_ : Dual .end_ .end_
  | send_recv (r : Role) (T : ValType) (L1 L2 : LocalType) :
      Dual L1 L2 → Dual (.send r T L1) (.recv r T L2)
  | recv_send (r : Role) (T : ValType) (L1 L2 : LocalType) :
      Dual L1 L2 → Dual (.recv r T L1) (.send r T L2)
  -- Note: select/branch cases would need matching labels

/-- If L1 is a send to r with continuation L1', and L2 is dual to L1,
    then L2 is a recv from r and their continuations are dual. -/
theorem Dual_send_inv (L1 L2 : LocalType) (r : Role) (T : ValType) (L1' : LocalType)
    (hDual : Dual L1 L2) (hL1 : L1 = .send r T L1') :
    ∃ L2', L2 = .recv r T L2' ∧ Dual L1' L2' := by
  cases hDual with
  | end_ => cases hL1  -- .end_ ≠ .send, contradiction
  | send_recv r' T' L1'' L2' hCont =>
    cases hL1
    exact ⟨L2', rfl, hCont⟩
  | recv_send r' T' L1'' L2' _ =>
    cases hL1  -- .recv ≠ .send, contradiction

/-- Dual types with empty trace are coherent (the bridge initialization lemma).
    Note: The proof actually works for any types with empty trace; duality ensures
    the types will remain coherent as communication proceeds. -/
theorem Dual_implies_Coherent_empty (L1 L2 : LocalType) (r1 r2 : Role)
    (sid : SessionId) (_hDual : Dual L1 L2) :
    let G : GEnv := [({ sid := sid, role := r1 }, L1), ({ sid := sid, role := r2 }, L2)]
    let D : DEnv := Lean.RBMap.empty
    let e12 : Edge := { sid := sid, sender := r1, receiver := r2 }
    let e21 : Edge := { sid := sid, sender := r2, receiver := r1 }
    EdgeCoherent G D e12 ∧ EdgeCoherent G D e21 := by
  -- With empty D, the trace is [] for all edges
  -- EdgeCoherent requires: Consume sender Lrecv [] = some _
  -- Since trace is empty, we need Lrecv to be consumable with no messages
  -- This is trivially true: Consume _ L [] = some L
  constructor
  · -- EdgeCoherent for e12 (r1 → r2)
    intro Lsender Lrecv hGsender hGrecv
    simp [lookupD_empty, Consume]
  · -- EdgeCoherent for e21 (r2 → r1)
    intro Lsender Lrecv hGsender hGrecv
    simp [lookupD_empty, Consume]

end
