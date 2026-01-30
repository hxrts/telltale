import Protocol.Typing.Part1

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

open scoped Classical

noncomputable section

/-! ## Well-Typed Configuration -/

/-- A configuration is well-typed if all components are consistent:
    - Session IDs in store/buffers are < nextSid
    - Store is typed by S and G
    - Buffers are typed by D
    - G and D are coherent
    - Process is typed -/
structure WTConfigN (n : SessionId) (S : SEnv) (G : GEnv) (D : DEnv) (C : Config) : Prop where
  /-- nextSid matches. -/
  nextSid_eq : C.nextSid = n
  /-- Store is typed. -/
  store_typed : StoreTyped G S C.store
  /-- Buffers are typed. -/
  buffers_typed : BuffersTyped G D C.bufs
  /-- Environments are coherent. -/
  coherent : Coherent G D
  /-- Process is typed. -/
  proc_typed : HasTypeProcN n S G D C.proc

/-! ## Typing Lemmas -/

/-- Skip is well-typed under any environments. -/
theorem skip_typed (n : SessionId) (S : SEnv) (G : GEnv) (D : DEnv) :
    HasTypeProcN n S G D .skip :=
  HasTypeProcN.skip

/-- If P is typed and Q is typed, seq P Q is typed. -/
theorem seq_typed (n : SessionId) (S : SEnv) (G : GEnv) (D : DEnv)
    (P Q : Process)
    (hP : HasTypeProcN n S G D P)
    (hQ : HasTypeProcN n S G D Q) :
    HasTypeProcN n S G D (.seq P Q) :=
  HasTypeProcN.seq hP hQ

/-! ## Inversion Lemmas -/

/-- Inversion for send typing.
    Note: The send constructor produces a judgment with updated G,
    so we invert from the updated environment perspective. -/
theorem send_typed_inv {n : SessionId} {S : SEnv} {G : GEnv} {D : DEnv} {k x : Var}
    (h : HasTypeProcN n S G D (.send k x)) :
    ∃ e q T L G',
      lookupSEnv S k = some (.chan e.sid e.role) ∧
      lookupG G' e = some (.send q T L) ∧
      lookupSEnv S x = some T ∧
      G = updateG G' e L := by
  cases h with
  | send hk hG hx => exact ⟨_, _, _, _, _, hk, hG, hx, rfl⟩

/-- Inversion for recv typing.
    Note: The recv constructor produces a judgment with updated S and G. -/
theorem recv_typed_inv {n : SessionId} {S : SEnv} {G : GEnv} {D : DEnv} {k x : Var}
    (h : HasTypeProcN n S G D (.recv k x)) :
    ∃ e p T L S' G',
      lookupSEnv S' k = some (.chan e.sid e.role) ∧
      lookupG G' e = some (.recv p T L) ∧
      S = updateSEnv S' x T ∧
      G = updateG G' e L := by
  cases h with
  | recv hk hG => exact ⟨_, _, _, _, _, _, hk, hG, rfl, rfl⟩

/-- Inversion for select typing.
    Note: The select constructor produces a judgment with updated G.
    Reference: `work/effects/008.lean:287-292` -/
theorem select_typed_inv {n : SessionId} {S : SEnv} {G : GEnv} {D : DEnv} {k : Var} {l : Label}
    (h : HasTypeProcN n S G D (.select k l)) :
    ∃ e q bs L G',
      lookupSEnv S k = some (.chan e.sid e.role) ∧
      lookupG G' e = some (.select q bs) ∧
      bs.find? (fun b => b.1 == l) = some (l, L) ∧
      G = updateG G' e L := by
  cases h with
  | select hk hG hbs => exact ⟨_, _, _, _, _, hk, hG, hbs, rfl⟩

/-- Inversion for branch typing.
    Reference: `work/effects/008.lean:294-300` -/
theorem branch_typed_inv {n : SessionId} {S : SEnv} {G : GEnv} {D : DEnv}
    {k : Var} {procs : List (Label × Process)}
    (h : HasTypeProcN n S G D (.branch k procs)) :
    ∃ e p bs,
      lookupSEnv S k = some (.chan e.sid e.role) ∧
      lookupG G e = some (.branch p bs) ∧
      bs.length = procs.length ∧
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        (procs.get ⟨i, hip⟩).1 = (bs.get ⟨i, hi⟩).1) ∧
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcN n S (updateG G e (bs.get ⟨i, hi⟩).2) D (procs.get ⟨i, hip⟩).2) := by
  cases h with
  | branch hk hG hLen hLabels hBodies =>
    exact ⟨_, _, _, hk, hG, hLen, hLabels, hBodies⟩

/-! ## Progress-Oriented Typing

For the progress theorem, we need a typing relation that uses "pre-update"
environments (the actual runtime state), not "post-update" environments.
This matches the approach in `work/effects/008.lean`.

Reference: `work/effects/008.lean:151-176` -/

/-- Pre-update style process typing for progress theorem.
    Unlike HasTypeProcN which uses post-update environments, this relation
    uses the environment as-is, making it suitable for connecting to runtime state.

    This is an alternative view of typing where:
    - HasTypeProcN says "after effects, we have these types"
    - HasTypeProcPre says "given current types, this process is well-formed" -/
inductive HasTypeProcPre : SEnv → SEnv → GEnv → Process → Prop where
  /-- Skip is always well-typed. -/
  | skip {Ssh Sown G} : HasTypeProcPre Ssh Sown G .skip

  /-- Send: channel k points to endpoint e, e has send type, payload x has correct type. -/
  | send {Ssh Sown G k x e q T L} :
      lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.send q T L) →
      lookupSEnv (SEnvAll Ssh Sown) x = some T →
      HasTypeProcPre Ssh Sown G (.send k x)

  /-- Recv: channel k points to endpoint e, e has recv type. -/
  | recv {Ssh Sown G k x e p T L} :
      lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.recv p T L) →
      lookupSEnv Ssh x = none →
      HasTypeProcPre Ssh Sown G (.recv k x)

  /-- Select: channel k points to endpoint e, e has select type with label l. -/
  | select {Ssh Sown G k l e q bs L} :
      lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.select q bs) →
      bs.find? (fun b => b.1 == l) = some (l, L) →
      HasTypeProcPre Ssh Sown G (.select k l)

  /-- Branch: channel k points to endpoint e, e has branch type, all branches typed. -/
  | branch {Ssh Sown G k procs e p bs} :
      lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.branch p bs) →
      bs.length = procs.length →
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        (procs.get ⟨i, hip⟩).1 = (bs.get ⟨i, hi⟩).1) →
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown (updateG G e (bs.get ⟨i, hi⟩).2) (procs.get ⟨i, hip⟩).2) →
      HasTypeProcPre Ssh Sown G (.branch k procs)

  /-- Sequential composition. -/
  | seq {Ssh Sown G P Q} :
      HasTypeProcPre Ssh Sown G P →
      HasTypeProcPre Ssh Sown G Q →
      HasTypeProcPre Ssh Sown G (.seq P Q)

  /-- Parallel composition. -/
  | par {Ssh S₁ S₂ G P Q} :
      DisjointS S₁ S₂ →
      HasTypeProcPre Ssh S₁ G P →
      HasTypeProcPre Ssh S₂ G Q →
      HasTypeProcPre Ssh (S₁ ++ S₂) G (.par P Q)

  /-- Assignment. -/
  | assign {Ssh Sown G x v T} :
      lookupSEnv Ssh x = none →
      HasTypeVal G v T →
      HasTypeProcPre Ssh Sown G (.assign x v)

/-! ### Inversion Lemmas for Pre-Update Typing

These lemmas directly extract type information from pre-update typing judgments.
Reference: `work/effects/008.lean:274-300` -/

/-- Inversion for send (pre-update style).
    Reference: `work/effects/008.lean:274-279` -/
theorem inversion_send {Ssh Sown : SEnv} {G : GEnv} {k x : Var}
    (h : HasTypeProcPre Ssh Sown G (.send k x)) :
    ∃ e q T L,
      lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e.sid e.role) ∧
      lookupG G e = some (.send q T L) ∧
      lookupSEnv (SEnvAll Ssh Sown) x = some T := by
  cases h with
  | send hk hG hx => exact ⟨_, _, _, _, hk, hG, hx⟩

/-- Inversion for recv (pre-update style).
    Reference: `work/effects/008.lean:281-285` -/
theorem inversion_recv {Ssh Sown : SEnv} {G : GEnv} {k x : Var}
    (h : HasTypeProcPre Ssh Sown G (.recv k x)) :
    ∃ e p T L,
      lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e.sid e.role) ∧
      lookupG G e = some (.recv p T L) ∧
      lookupSEnv Ssh x = none := by
  cases h with
  | recv hk hG hx => exact ⟨_, _, _, _, hk, hG, hx⟩

/-- Inversion for select (pre-update style).
    Reference: `work/effects/008.lean:287-292` -/
theorem inversion_select {Ssh Sown : SEnv} {G : GEnv} {k : Var} {l : Label}
    (h : HasTypeProcPre Ssh Sown G (.select k l)) :
    ∃ e q bs L,
      lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e.sid e.role) ∧
      lookupG G e = some (.select q bs) ∧
      bs.find? (fun b => b.1 == l) = some (l, L) := by
  cases h with
  | select hk hG hbs => exact ⟨_, _, _, _, hk, hG, hbs⟩

/-- Inversion for branch (pre-update style).
    Reference: `work/effects/008.lean:294-300` -/
theorem inversion_branch {Ssh Sown : SEnv} {G : GEnv} {k : Var} {procs : List (Label × Process)}
    (h : HasTypeProcPre Ssh Sown G (.branch k procs)) :
    ∃ e p bs,
      lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e.sid e.role) ∧
      lookupG G e = some (.branch p bs) ∧
      bs.length = procs.length ∧
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        (procs.get ⟨i, hip⟩).1 = (bs.get ⟨i, hi⟩).1) ∧
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown (updateG G e (bs.get ⟨i, hi⟩).2) (procs.get ⟨i, hip⟩).2) := by
  cases h with
  | branch hk hG hLen hLabels hBodies =>
      exact ⟨_, _, _, hk, hG, hLen, hLabels, hBodies⟩

/-! ## Linear Resource Transition Typing

**Core Judgment**: `TypedStep G D Ssh Sown C C' G' D' Sown'`

**Reading**: Configuration C consumes resources (G, D, S) and steps to C',
producing resources (G', D', S').

This design ensures preservation by making the pre/post-state distinction
intrinsic to the typing judgment.

**References**: Theoretical foundation: Wadler (2012) "Propositions as Sessions"

## Key Properties

1. **Preservation**: Trivial (the judgment itself proves it)
2. **Progress**: Structured case analysis on configuration
3. **Coherence**: Uses existing `Coherent_send_preserved`, `Coherent_recv_preserved`
4. **Soundness**: TypedStep refines Step -/

/-! ### Pre-Update Typing with Post Environments -/

/-- Pre-update style process typing with explicit post environments.

    This relation tracks how the session/value environments evolve after the
    *entire* process completes. It is used to avoid the sequential monotonicity
    issue in preservation: after a single step, the remaining process should
    still lead to the same final environments. -/
inductive HasTypeProcPreOut : SEnv → SEnv → GEnv → Process → SEnv → GEnv → Footprint → DeltaSEnv → Prop where
  /-- Skip leaves environments unchanged. -/
  | skip {Ssh Sown G} : HasTypeProcPreOut Ssh Sown G .skip Sown G [] ∅

  /-- Send advances the sender's local type. -/
  | send {Ssh Sown G k x e q T L} :
      lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.send q T L) →
      lookupSEnv (SEnvAll Ssh Sown) x = some T →
      HasTypeProcPreOut Ssh Sown G (.send k x) Sown (updateG G e L) [] ∅

  /-- Recv advances the receiver's local type and extends S for x. -/
  | recv_new {Ssh Sown G k x e p T L} :
      lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.recv p T L) →
      lookupSEnv Ssh x = none →
      lookupSEnv Sown x = none →
      HasTypeProcPreOut Ssh Sown G (.recv k x)
        (updateSEnv Sown x T) (updateG G e L) [x] (updateSEnv ∅ x T)

  | recv_old {Ssh Sown G k x e p T L T'} :
      lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.recv p T L) →
      lookupSEnv Ssh x = none →
      lookupSEnv Sown x = some T' →
      HasTypeProcPreOut Ssh Sown G (.recv k x)
        (updateSEnv Sown x T) (updateG G e L) [x] ∅

  /-- Select advances the sender's local type. -/
  | select {Ssh Sown G k l e q bs L} :
      lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.select q bs) →
      bs.find? (fun b => b.1 == l) = some (l, L) →
      HasTypeProcPreOut Ssh Sown G (.select k l) Sown (updateG G e L) [] ∅

  /-- Branch: all branches are pre-typed; post environments follow the runtime label. -/
  | branch {Ssh Sown G k procs e p bs S' G' W Δ} :
      lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e.sid e.role) →
      lookupG G e = some (.branch p bs) →
      bs.length = procs.length →
      (∀ j (hj : j < bs.length) (hjp : j < procs.length),
        (procs.get ⟨j, hjp⟩).1 = (bs.get ⟨j, hj⟩).1) →
      (∀ j (hj : j < bs.length) (hjp : j < procs.length),
        HasTypeProcPre Ssh Sown (updateG G e (bs.get ⟨j, hj⟩).2) (procs.get ⟨j, hjp⟩).2) →
      (∀ lbl P L,
        procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
        bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
        HasTypeProcPreOut Ssh Sown (updateG G e L) P S' G' W Δ) →
      SEnvDomSubset Sown S' →
      HasTypeProcPreOut Ssh Sown G (.branch k procs) S' G' W Δ

  /-- Sequential composition: compose post environments. -/
  | seq {Ssh Sown G P Q S₁ G₁ S₂ G₂ W₁ W₂ Δ₁ Δ₂} :
      HasTypeProcPreOut Ssh Sown G P S₁ G₁ W₁ Δ₁ →
      HasTypeProcPreOut Ssh S₁ G₁ Q S₂ G₂ W₂ Δ₂ →
      HasTypeProcPreOut Ssh Sown G (.seq P Q) S₂ G₂ (W₁ ++ W₂) (Δ₁ ++ Δ₂)

  /-- Parallel composition with disjoint resources (explicit split witness). -/
  | par {Ssh S G P Q Sfin Gfin Wfin Δfin
         S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂} (split : ParSplit S G) :
      Sfin = (S₁' ++ S₂') →
      Gfin = (G₁' ++ G₂') →
      Wfin = (W₁ ++ W₂) →
      Δfin = (Δ₁ ++ Δ₂) →
      DisjointG split.G1 split.G2 →
      DisjointS split.S1 split.S2 →
      DisjointS S₁' split.S2 →
      DisjointS split.S1 S₂' →
      DisjointS S₁' S₂' →
      DisjointW W₁ W₂ →
      DisjointS Δ₁ Δ₂ →
      HasTypeProcPreOut Ssh split.S1 split.G1 P S₁' G₁' W₁ Δ₁ →
      HasTypeProcPreOut Ssh split.S2 split.G2 Q S₂' G₂' W₂ Δ₂ →
      HasTypeProcPreOut Ssh S G (.par P Q) Sfin Gfin Wfin Δfin

  /-- Assignment updates S with x's type. -/
  | assign_new {Ssh Sown G x v T} :
      lookupSEnv Ssh x = none →
      lookupSEnv Sown x = none →
      HasTypeVal G v T →
      HasTypeProcPreOut Ssh Sown G (.assign x v) (updateSEnv Sown x T) G [x] (updateSEnv ∅ x T)

  | assign_old {Ssh Sown G x v T T'} :
      lookupSEnv Ssh x = none →
      lookupSEnv Sown x = some T' →
      HasTypeVal G v T →
      HasTypeProcPreOut Ssh Sown G (.assign x v) (updateSEnv Sown x T) G [x] ∅


/-! ### Inversion Helpers for Pre-Out Typing -/

/-- Inversion for parallel pre-out typing with explicit environment splits. -/
theorem HasTypeProcPreOut_par_inv {Ssh S G P Q Sfin Gfin Wfin Δfin} :
    HasTypeProcPreOut Ssh S G (.par P Q) Sfin Gfin Wfin Δfin →
    ∃ S₁ S₂ G₁ G₂ S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂,
      S = (S₁ ++ S₂) ∧
      G = (G₁ ++ G₂) ∧
      Sfin = (S₁' ++ S₂') ∧
      Gfin = (G₁' ++ G₂') ∧
      Wfin = (W₁ ++ W₂) ∧
      Δfin = (Δ₁ ++ Δ₂) ∧
      DisjointG G₁ G₂ ∧
      DisjointS S₁ S₂ ∧
      DisjointS S₁' S₂ ∧
      DisjointS S₁ S₂' ∧
      DisjointS S₁' S₂' ∧
      DisjointW W₁ W₂ ∧
      DisjointS Δ₁ Δ₂ ∧
      HasTypeProcPreOut Ssh S₁ G₁ P S₁' G₁' W₁ Δ₁ ∧
      HasTypeProcPreOut Ssh S₂ G₂ Q S₂' G₂' W₂ Δ₂ := by
  intro h
  cases h with
  | par split hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hP hQ =>
      cases split with
      | mk S₁ S₂ G₁ G₂ hS hG =>
          exact ⟨S₁, S₂, G₁, G₂, _, _, _, _, _, _, _, _, hS, hG, hSfin, hGfin, hW, hΔ,
            hDisjG, hDisjS, hDisjS_left, hDisjS_right, hDisjS', hDisjW, hDisjΔ, hP, hQ⟩

-- NOTE: We do not provide a general "forgetful" lemma from HasTypeProcPreOut to
-- HasTypeProcPre, because seq/par pre-out typing does not imply pre-typing for
-- the whole process without additional monotonicity assumptions.

/-! ### TypedStep Inductive Definition -/

/-- Linear resource transition typing judgment.

    **Interpretation**: Process P with state (G, D, S, store, bufs) transitions
    to process P' with state (G', D', S', store', bufs').

    **Linear Resources**:
    - Each endpoint in G is consumed exactly once and produces a continuation
    - Buffers and traces evolve consistently (append on send, pop on recv)
    - Variables are typed as they're assigned

    **Compositionality**: Parallel processes have disjoint resources -/
inductive TypedStep : GEnv → DEnv → SEnv → SEnv → Store → Buffers → Process →
                      GEnv → DEnv → SEnv → Store → Buffers → Process → Prop
  | send {G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'} :
      -- Pre-conditions (resources consumed)
      lookupStr store k = some (.chan e) →
      lookupStr store x = some v →
      lookupG G e = some (.send target T L) →
      lookupSEnv (SEnvAll Ssh Sown) x = some T →
      HasTypeVal G v T →
      -- Receiver readiness: ensures coherence preservation
      (∀ Lrecv, lookupG G { sid := e.sid, role := target } = some Lrecv →
        ∃ L', Consume e.role Lrecv (lookupD D { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
              (Consume e.role L' [T]).isSome) →

      -- Resource transition definitions
      sendEdge = { sid := e.sid, sender := e.role, receiver := target } →
      G' = updateG G e L →
      D' = appendD D sendEdge T →
      bufs' = enqueueBuf bufs sendEdge v →

      -- Judgment
      TypedStep G D Ssh Sown store bufs (.send k x)
                G' D' Sown store bufs' .skip

  | recv {G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'} :
      -- Pre-conditions (resources consumed)
      lookupStr store k = some (.chan e) →
      lookupG G e = some (.recv source T L) →
      recvEdge = { sid := e.sid, sender := source, receiver := e.role } →
      lookupBuf bufs recvEdge = v :: vs →
      HasTypeVal G v T →  -- derived from BuffersTyped invariant
      (lookupD D recvEdge).head? = some T →  -- trace head matches (from BuffersTyped + Coherent)

      -- Resource transition definitions
      G' = updateG G e L →
      D' = updateD D recvEdge (lookupD D recvEdge).tail →
      Sown' = updateSEnv Sown x T →
      store' = updateStr store x v →
      bufs' = updateBuf bufs recvEdge vs →

      -- Judgment
      TypedStep G D Ssh Sown store bufs (.recv k x)
                G' D' Sown' store' bufs' .skip

  | select {G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'} :
      -- Pre-conditions (resources consumed)
      lookupStr store k = some (.chan e) →
      lookupG G e = some (.select target bs) →
      bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
      -- Receiver readiness for label
      (∀ Ltarget, lookupG G { sid := e.sid, role := target } = some Ltarget →
        ∃ L', Consume e.role Ltarget (lookupD D { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
              (Consume e.role L' [.string]).isSome) →

      -- Resource transition definitions
      selectEdge = { sid := e.sid, sender := e.role, receiver := target } →
      G' = updateG G e L →
      D' = appendD D selectEdge .string →
      bufs' = enqueueBuf bufs selectEdge (.string ℓ) →

      -- Judgment
      TypedStep G D Ssh Sown store bufs (.select k ℓ)
                G' D' Sown store bufs' .skip

  | branch {G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'} :
      -- Pre-conditions (resources consumed)
      lookupStr store k = some (.chan e) →
      lookupG G e = some (.branch source bs) →
      branchEdge = { sid := e.sid, sender := source, receiver := e.role } →
      lookupBuf bufs branchEdge = .string ℓ :: vs →
      procs.find? (fun b => b.1 == ℓ) = some (ℓ, P) →
      bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
      (lookupD D branchEdge).head? = some .string →

      -- Resource transition definitions
      G' = updateG G e L →
      D' = updateD D branchEdge (lookupD D branchEdge).tail →
      bufs' = updateBuf bufs branchEdge vs →

      -- Judgment
      TypedStep G D Ssh Sown store bufs (.branch k procs)
                G' D' Sown store bufs' P

  | assign {G D Ssh Sown store bufs x v T S' store'} :
      -- Pre-condition: value is well-typed
      HasTypeVal G v T →

      -- Resource transition definitions (S and store change)
      S' = updateSEnv Sown x T →
      store' = updateStr store x v →

      -- Judgment
      TypedStep G D Ssh Sown store bufs (.assign x v)
                G D S' store' bufs .skip

  | seq_step {G D Ssh Sown G' D' Sown' store bufs store' bufs' P P' Q} :
      -- Resources flow through first process
      TypedStep G D Ssh Sown store bufs P
                G' D' Sown' store' bufs' P' →

      TypedStep G D Ssh Sown store bufs (.seq P Q)
                G' D' Sown' store' bufs' (.seq P' Q)

  | seq_skip {G D Ssh Sown store bufs Q} :
      -- Skip elimination (identity transition)
      TypedStep G D Ssh Sown store bufs (.seq .skip Q)
                G D Sown store bufs Q

  | par_left {Ssh store bufs store' bufs' P P' Q S G D₁ D₂ G₁' D₁' S₁'} (split : ParSplit S G) :
      -- Left process transitions with its resources
      TypedStep split.G1 D₁ Ssh split.S1 store bufs P
                G₁' D₁' S₁' store' bufs' P' →

      -- Resources must be disjoint for parallel composition
      DisjointG split.G1 split.G2 →
      DisjointD D₁ D₂ →
      DisjointS split.S1 split.S2 →
      DConsistent split.G1 D₁ →
      DConsistent split.G2 D₂ →

      -- Combined transition
      TypedStep G (D₁ ++ D₂) Ssh S store bufs (.par P Q)
                (G₁' ++ split.G2) (D₁' ++ D₂) (S₁' ++ split.S2) store' bufs' (.par P' Q)

  | par_right {Ssh store bufs store' bufs' P Q Q' S G D₁ D₂ G₂' D₂' S₂'} (split : ParSplit S G) :
      -- Right process transitions with its resources
      TypedStep split.G2 D₂ Ssh split.S2 store bufs Q
                G₂' D₂' S₂' store' bufs' Q' →

      -- Resources must be disjoint
      DisjointG split.G1 split.G2 →
      DisjointD D₁ D₂ →
      DisjointS split.S1 split.S2 →
      DConsistent split.G1 D₁ →
      DConsistent split.G2 D₂ →

      -- Combined transition
      TypedStep G (D₁ ++ D₂) Ssh S store bufs (.par P Q)
                (split.G1 ++ G₂') (D₁ ++ D₂') (split.S1 ++ S₂') store' bufs' (.par P Q')

  | par_skip_left {G D Ssh Sown store bufs Q} :
      -- Skip elimination from parallel
      TypedStep G D Ssh Sown store bufs (.par .skip Q)
                G D Sown store bufs Q

  | par_skip_right {G D Ssh Sown store bufs P} :
      -- Skip elimination from parallel
      TypedStep G D Ssh Sown store bufs (.par P .skip)
                G D Sown store bufs P


end
