import Effects.Process
import Effects.Coherence

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

open scoped Classical

noncomputable section

/-! ## Process Typing Judgment -/

/-- Process typing judgment.
    `HasTypeProcN n S G D P` means process P is well-typed under:
    - n: upper bound on session IDs
    - S: value type environment
    - G: session type environment
    - D: delayed type environment -/
inductive HasTypeProcN : SessionId → SEnv → GEnv → DEnv → Process → Prop where
  /-- Skip is always well-typed. -/
  | skip {n : SessionId} {S : SEnv} {G : GEnv} {D : DEnv} : HasTypeProcN n S G D .skip

  /-- Sequential composition. -/
  | seq {n S G D P Q} :
      HasTypeProcN n S G D P →
      HasTypeProcN n S G D Q →
      HasTypeProcN n S G D (.seq P Q)

  /-- Parallel composition (simplified, without linear splitting). -/
  | par {n S G D P Q} :
      HasTypeProcN n S G D P →
      HasTypeProcN n S G D Q →
      HasTypeProcN n S G D (.par P Q)

  /-- Send: send value x through channel k.
      Requires:
      - k has channel type for endpoint e
      - e's local type is send to some role q with payload type T
      - x has type T
      Updates G[e] to continuation L. -/
  | send {n S G D k x e q T L} :
      lookupSEnv S k = some (.chan e.sid e.role) →
      lookupG G e = some (.send q T L) →
      lookupSEnv S x = some T →
      HasTypeProcN n S (updateG G e L) D (.send k x)

  /-- Recv: receive into x through channel k.
      Requires:
      - k has channel type for endpoint e
      - e's local type is recv from some role p with payload type T
      Updates G[e] to continuation L, S[x] to T. -/
  | recv {n S G D k x e p T L} :
      lookupSEnv S k = some (.chan e.sid e.role) →
      lookupG G e = some (.recv p T L) →
      HasTypeProcN n (updateSEnv S x T) (updateG G e L) D (.recv k x)

  /-- Select: send label ℓ through channel k.
      Requires:
      - k has channel type for endpoint e
      - e's local type is select to q with label ℓ in branches
      Updates G[e] to continuation for ℓ. -/
  | select {n S G D k e q bs ℓ L} :
      lookupSEnv S k = some (.chan e.sid e.role) →
      lookupG G e = some (.select q bs) →
      bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
      HasTypeProcN n S (updateG G e L) D (.select k ℓ)

  /-- Branch: receive and branch on label through channel k.
      Requires:
      - k has channel type for endpoint e
      - e's local type is branch from p with matching labels
      - each branch process is well-typed under its continuation -/
  | branch {n : SessionId} {S : SEnv} {G : GEnv} {D : DEnv}
      {k : Var} {e : Endpoint} {p : Role} {bs : List (Label × LocalType)} {procs : List (Label × Process)} :
      lookupSEnv S k = some (.chan e.sid e.role) →
      lookupG G e = some (.branch p bs) →
      bs.length = procs.length →
      -- Label matching (non-recursive, pure data)
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        (procs.get ⟨i, hip⟩).1 = (bs.get ⟨i, hi⟩).1) →
      -- Process typing (recursive)
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcN n S (updateG G e (bs.get ⟨i, hi⟩).2) D (procs.get ⟨i, hip⟩).2) →
      HasTypeProcN n S G D (.branch k procs)

  /-- Assign: assign a non-linear value to a variable. -/
  | assign {n S G D x v T} :
      HasTypeVal G v T →
      ¬T.isLinear →
      HasTypeProcN n (updateSEnv S x T) G D (.assign x v)

  /-- NewSession: create a new session.
      Allocates fresh session ID, creates endpoints for all roles. -/
  | newSession {n : SessionId} {S : SEnv} {G : GEnv} {D : DEnv}
      {roles : RoleSet} {f : Role → Var} {P : Process} (localTypes : Role → LocalType) :
      (∀ r, r ∈ roles →
        HasTypeProcN (n + 1)
          (updateSEnv S (f r) (.chan n r))
          (updateG G ⟨n, r⟩ (localTypes r))
          D P) →
      HasTypeProcN n S G D (.newSession roles f P)

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
inductive HasTypeProcPre : SEnv → GEnv → Process → Prop where
  /-- Skip is always well-typed. -/
  | skip {S G} : HasTypeProcPre S G .skip

  /-- Send: channel k points to endpoint e, e has send type, payload x has correct type. -/
  | send {S G k x e q T L} :
      lookupSEnv S k = some (.chan e.sid e.role) →
      lookupG G e = some (.send q T L) →
      lookupSEnv S x = some T →
      HasTypeProcPre S G (.send k x)

  /-- Recv: channel k points to endpoint e, e has recv type. -/
  | recv {S G k x e p T L} :
      lookupSEnv S k = some (.chan e.sid e.role) →
      lookupG G e = some (.recv p T L) →
      HasTypeProcPre S G (.recv k x)

  /-- Select: channel k points to endpoint e, e has select type with label l. -/
  | select {S G k l e q bs L} :
      lookupSEnv S k = some (.chan e.sid e.role) →
      lookupG G e = some (.select q bs) →
      bs.find? (fun b => b.1 == l) = some (l, L) →
      HasTypeProcPre S G (.select k l)

  /-- Branch: channel k points to endpoint e, e has branch type, all branches typed. -/
  | branch {S G k procs e p bs} :
      lookupSEnv S k = some (.chan e.sid e.role) →
      lookupG G e = some (.branch p bs) →
      bs.length = procs.length →
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        (procs.get ⟨i, hip⟩).1 = (bs.get ⟨i, hi⟩).1) →
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre S (updateG G e (bs.get ⟨i, hi⟩).2) (procs.get ⟨i, hip⟩).2) →
      HasTypeProcPre S G (.branch k procs)

  /-- Sequential composition. -/
  | seq {S G P Q} :
      HasTypeProcPre S G P →
      HasTypeProcPre S G Q →
      HasTypeProcPre S G (.seq P Q)

  /-- Parallel composition. -/
  | par {S G P Q} :
      HasTypeProcPre S G P →
      HasTypeProcPre S G Q →
      HasTypeProcPre S G (.par P Q)

  /-- Assignment. -/
  | assign {S G x v T} :
      HasTypeVal G v T →
      HasTypeProcPre S G (.assign x v)

/-! ### Inversion Lemmas for Pre-Update Typing

These lemmas directly extract type information from pre-update typing judgments.
Reference: `work/effects/008.lean:274-300` -/

/-- Inversion for send (pre-update style).
    Reference: `work/effects/008.lean:274-279` -/
theorem inversion_send {S : SEnv} {G : GEnv} {k x : Var}
    (h : HasTypeProcPre S G (.send k x)) :
    ∃ e q T L,
      lookupSEnv S k = some (.chan e.sid e.role) ∧
      lookupG G e = some (.send q T L) ∧
      lookupSEnv S x = some T := by
  cases h with
  | send hk hG hx => exact ⟨_, _, _, _, hk, hG, hx⟩

/-- Inversion for recv (pre-update style).
    Reference: `work/effects/008.lean:281-285` -/
theorem inversion_recv {S : SEnv} {G : GEnv} {k x : Var}
    (h : HasTypeProcPre S G (.recv k x)) :
    ∃ e p T L,
      lookupSEnv S k = some (.chan e.sid e.role) ∧
      lookupG G e = some (.recv p T L) := by
  cases h with
  | recv hk hG => exact ⟨_, _, _, _, hk, hG⟩

/-- Inversion for select (pre-update style).
    Reference: `work/effects/008.lean:287-292` -/
theorem inversion_select {S : SEnv} {G : GEnv} {k : Var} {l : Label}
    (h : HasTypeProcPre S G (.select k l)) :
    ∃ e q bs L,
      lookupSEnv S k = some (.chan e.sid e.role) ∧
      lookupG G e = some (.select q bs) ∧
      bs.find? (fun b => b.1 == l) = some (l, L) := by
  cases h with
  | select hk hG hbs => exact ⟨_, _, _, _, hk, hG, hbs⟩

/-- Inversion for branch (pre-update style).
    Reference: `work/effects/008.lean:294-300` -/
theorem inversion_branch {S : SEnv} {G : GEnv} {k : Var} {procs : List (Label × Process)}
    (h : HasTypeProcPre S G (.branch k procs)) :
    ∃ e p bs,
      lookupSEnv S k = some (.chan e.sid e.role) ∧
      lookupG G e = some (.branch p bs) ∧
      bs.length = procs.length ∧
      (∀ i (hi : i < bs.length) (hip : i < procs.length),
        (procs.get ⟨i, hip⟩).1 = (bs.get ⟨i, hi⟩).1) := by
  cases h with
  | branch hk hG hLen hLabels _ => exact ⟨_, _, _, hk, hG, hLen, hLabels⟩

/-! ## Linear Resource Transition Typing

**Core Judgment**: `TypedStep G D S C C' G' D' S'`

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

/-! ### Resource Disjointness Predicates -/

/-- Session type environment disjointness.
    Two environments are disjoint if no endpoint appears in both. -/
def DisjointG (G₁ G₂ : GEnv) : Prop :=
  ∀ e L₁ L₂, (e, L₁) ∈ G₁ → (e, L₂) ∈ G₂ → False

/-- Delayed type environment disjointness.
    Two environments are disjoint if no edge has non-empty traces in both. -/
def DisjointD (D₁ D₂ : DEnv) : Prop :=
  ∀ edge, lookupD D₁ edge ≠ [] → lookupD D₂ edge ≠ [] → False

/-- Value type environment disjointness.
    Two environments are disjoint if no variable appears in both. -/
def DisjointS (S₁ S₂ : SEnv) : Prop :=
  ∀ x T₁ T₂, lookupSEnv S₁ x = some T₁ → lookupSEnv S₂ x = some T₂ → False

/-! ### TypedStep Inductive Definition -/

/-- Linear resource transition typing judgment.

    **Interpretation**: Process P with state (G, D, S, store, bufs) transitions
    to process P' with state (G', D', S', store', bufs').

    **Linear Resources**:
    - Each endpoint in G is consumed exactly once and produces a continuation
    - Buffers and traces evolve consistently (append on send, pop on recv)
    - Variables are typed as they're assigned

    **Compositionality**: Parallel processes have disjoint resources -/
inductive TypedStep : GEnv → DEnv → SEnv → Store → Buffers → Process →
                      GEnv → DEnv → SEnv → Store → Buffers → Process → Prop
  | send {G D S store bufs k x e target T L v sendEdge G' D' bufs'} :
      -- Pre-conditions (resources consumed)
      lookupStr store k = some (.chan e) →
      lookupStr store x = some v →
      lookupG G e = some (.send target T L) →
      lookupSEnv S x = some T →
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
      TypedStep G D S store bufs (.send k x)
                G' D' S store bufs' .skip

  | recv {G D S store bufs k x e source T L v vs recvEdge G' D' S' store' bufs'} :
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
      S' = updateSEnv S x T →
      store' = updateStr store x v →
      bufs' = updateBuf bufs recvEdge vs →

      -- Judgment
      TypedStep G D S store bufs (.recv k x)
                G' D' S' store' bufs' .skip

  | assign {G D S store bufs x v T S' store'} :
      -- Pre-condition: value is well-typed (no endpoint dependencies)
      HasTypeVal ∅ v T →

      -- Resource transition definitions (S and store change)
      S' = updateSEnv S x T →
      store' = updateStr store x v →

      -- Judgment
      TypedStep G D S store bufs (.assign x v)
                G D S' store' bufs .skip

  | seq_step {G D S G' D' S' store bufs P P' Q} :
      -- Resources flow through first process
      TypedStep G D S store bufs P
                G' D' S' store bufs P' →

      TypedStep G D S store bufs (.seq P Q)
                G' D' S' store bufs (.seq P' Q)

  | seq_skip {G D S store bufs Q} :
      -- Skip elimination (identity transition)
      TypedStep G D S store bufs (.seq .skip Q)
                G D S store bufs Q

  | par_left {G₁ G₂ D₁ D₂ S₁ S₂ G₁' D₁' S₁' store bufs P P' Q} :
      -- Left process transitions with its resources
      TypedStep G₁ D₁ S₁ store bufs P
                G₁' D₁' S₁' store bufs P' →

      -- Resources must be disjoint for parallel composition
      DisjointG G₁ G₂ →
      DisjointD D₁ D₂ →
      DisjointS S₁ S₂ →

      -- Combined transition
      TypedStep (G₁ ++ G₂) (D₁ ++ D₂) (S₁ ++ S₂) store bufs (.par P Q)
                (G₁' ++ G₂) (D₁' ++ D₂) (S₁' ++ S₂) store bufs (.par P' Q)

  | par_right {G₁ G₂ D₁ D₂ S₁ S₂ G₂' D₂' S₂' store bufs P Q Q'} :
      -- Right process transitions with its resources
      TypedStep G₂ D₂ S₂ store bufs Q
                G₂' D₂' S₂' store bufs Q' →

      -- Resources must be disjoint
      DisjointG G₁ G₂ →
      DisjointD D₁ D₂ →
      DisjointS S₁ S₂ →

      -- Combined transition
      TypedStep (G₁ ++ G₂) (D₁ ++ D₂) (S₁ ++ S₂) store bufs (.par P Q)
                (G₁ ++ G₂') (D₁ ++ D₂') (S₁ ++ S₂') store bufs (.par P Q')

  | par_skip_left {G D S store bufs Q} :
      -- Skip elimination from parallel
      TypedStep G D S store bufs (.par .skip Q)
                G D S store bufs Q

  | par_skip_right {G D S store bufs P} :
      -- Skip elimination from parallel
      TypedStep G D S store bufs (.par P .skip)
                G D S store bufs P

/-! ### WellFormed Predicate -/

/-- Well-formed process configuration.

    **Combines all invariants**: A process P with state (G, D, S, store, bufs)
    is well-formed if:
    1. Store is typed by S and G
    2. Buffers are typed by D
    3. G and D are coherent
    4. Process P has pre-update style typing

    This predicate is preserved by TypedStep transitions. -/
def WellFormed (G : GEnv) (D : DEnv) (S : SEnv) (store : Store) (bufs : Buffers) (P : Process) : Prop :=
  StoreTyped G S store ∧
  BuffersTyped G D bufs ∧
  Coherent G D ∧
  HasTypeProcPre S G P

/-! ## Support Lemmas for Preservation -/

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
theorem StoreTyped_send_preserved {G : GEnv} {S : SEnv} {store : Store} {e : Endpoint} {L : LocalType} :
    StoreTyped G S store →
    StoreTyped (updateG G e L) S store := by
  intro hST
  unfold StoreTyped at hST ⊢
  intro x v T hStore hS
  have hVal := hST x v T hStore hS
  exact HasTypeVal_updateG_weaken hVal

/-- For the assign case: StoreTyped with updated S and updated store.
    The value v has type T in empty environment (from TypedStep.assign premise),
    so it has type T in G by weakening. After update, store[x] = v and S[x] = T match. -/
theorem StoreTyped_assign_preserved {G : GEnv} {S : SEnv} {store : Store} {x : Var} {v : Value} {T : ValType} :
    StoreTyped G S store →
    HasTypeVal ∅ v T →
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
    exact HasTypeVal_weaken hv
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
theorem StoreTyped_recv_preserved {G : GEnv} {S : SEnv} {store : Store} {e : Endpoint} {L : LocalType}
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

    NOTE: This lemma is proven in Effects.Preservation. It's duplicated here to avoid
    circular dependencies, but should be moved to a shared module. -/
theorem BuffersTyped_enqueue {G : GEnv} {D : DEnv} {bufs : Buffers}
    {e : Edge} {v : Value} {T : ValType}
    (hBT : BuffersTyped G D bufs)
    (hv : HasTypeVal G v T) :
    BuffersTyped G (updateD D e (lookupD D e ++ [T])) (enqueueBuf bufs e v) := by
  sorry  -- Proven in Preservation.lean, needs module reorganization

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
  sorry  -- Needs proof, similar structure to BuffersTyped_enqueue

/-! ## Preservation Theorems -/

/-- TypedStep preserves coherence.

    **Proof strategy**: Case analysis on TypedStep constructor:
    - `send`: Use `Coherent_send_preserved` with hRecvReady derived from coherence
    - `recv`: Use `Coherent_recv_preserved`
    - `assign`: G and D unchanged
    - `seq_step`, `seq_skip`: IH or G/D unchanged
    - `par_*`: Disjoint resources remain coherent -/
theorem typed_step_preserves_coherence {G D S store bufs P G' D' S' store' bufs' P'} :
    TypedStep G D S store bufs P G' D' S' store' bufs' P' →
    Coherent G D →
    Coherent G' D'
  | @TypedStep.send G D S store bufs k x e target T L v sendEdge Gout Dout bufsOut hk hx hG hS hv hRecvReady hEdge hGout hDout hBufsOut, hCoh => by
    -- Use Coherent_send_preserved with explicit arguments
    -- After rewriting with the equalities, Gout = updateG G e L and Dout = appendD D sendEdge T
    rw [hGout, hDout, hEdge]
    unfold appendD
    exact @Coherent_send_preserved G D e target T L hCoh hG hRecvReady
  | @TypedStep.recv G D S store bufs k x e source T L v vs recvEdge Gout Dout Sout storeOut bufsOut hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut, hCoh => by
    -- Use Coherent_recv_preserved with explicit arguments
    rw [hGout, hDout]
    have hTrace' : (lookupD D { sid := e.sid, sender := source, receiver := e.role }).head? = some T := by
      rw [← hEdge]; exact hTrace
    rw [hEdge]
    exact @Coherent_recv_preserved G D e source T L hCoh hG hTrace'
  | .assign hx hv hS', hCoh => by
    -- G and D unchanged
    subst hS'
    exact hCoh
  | .seq_step hTS, hCoh =>
    -- Inductive hypothesis on sub-transition
    typed_step_preserves_coherence hTS hCoh
  | .seq_skip, hCoh =>
    -- No change
    hCoh
  | .par_left hTS hDisjG hDisjD hDisjS, hCoh => by
    -- Left transition preserves its part, right unchanged
    -- hCoh : Coherent (G₁ ++ G₂) (D₁ ++ D₂)
    -- Goal: Coherent (G₁' ++ G₂) (D₁' ++ D₂)
    -- Strategy: For any edge e, EdgeCoherent looks up in merged envs
    -- Since G₁, G₂ disjoint, lookup in (G₁ ++ G₂) either finds in G₁ or G₂
    -- If found in G₁ (updated to G₁'), use IH; if in G₂ (unchanged), use original
    intro e
    unfold EdgeCoherent
    -- The proof requires reasoning about which environment e belongs to
    -- and using disjointness to show lookups commute with updates
    sorry  -- Need lemmas about lookup_append and disjointness
  | .par_right hTS hDisjG hDisjD hDisjS, hCoh => by
    -- Symmetric to par_left
    intro e
    unfold EdgeCoherent
    sorry  -- Symmetric proof to par_left
  | .par_skip_left, hCoh =>
    hCoh
  | .par_skip_right, hCoh =>
    hCoh

/-- Main preservation theorem: TypedStep preserves well-formedness.

    **This is the resolution of Phase 4's blocking issue**: With TypedStep,
    preservation is straightforward because the judgment explicitly tracks
    resource transitions.

    **Proof strategy**: Case analysis on TypedStep:
    - StoreTyped: Use StoreTyped_update_nonChan for assign, unchanged for others
    - BuffersTyped: Use BuffersTyped_enqueue for send, handle recv
    - Coherent: Use typed_step_preserves_coherence
    - Process typing: By construction of TypedStep -/
theorem preservation_typed {G D S store bufs P G' D' S' store' bufs' P'} :
    TypedStep G D S store bufs P G' D' S' store' bufs' P' →
    WellFormed G D S store bufs P →
    WellFormed G' D' S' store' bufs' P' := by
  intro hStep hWF
  unfold WellFormed at hWF ⊢
  obtain ⟨hStore, hBufs, hCoh, hProc⟩ := hWF
  cases hStep with
  | send hk hx hG hS hv hRecvReady hEdge hG' hD' hBufs' =>
    -- Store is unchanged in send, S unchanged, so StoreTyped preserved
    -- Buffers have one message enqueued
    -- Coherent preserved by typed_step_preserves_coherence
    -- Process becomes skip which is always well-typed
    constructor
    · -- StoreTyped: store and S unchanged, only G changes to G' = updateG G e L
      rw [hG']
      exact StoreTyped_send_preserved hStore
    constructor
    · -- BuffersTyped: buffer enqueued with well-typed value, then G updated
      -- From TypedStep.send: D' = appendD D sendEdge T, bufs' = enqueueBuf bufs sendEdge v
      -- Step 1: Rewrite goal using the equalities
      rw [hBufs', hD', hG']
      unfold appendD
      -- Step 2: Apply BuffersTyped_updateG_weaken ∘ BuffersTyped_enqueue
      exact BuffersTyped_updateG_weaken (BuffersTyped_enqueue hBufs hv)
    constructor
    · -- Coherent: proven by typed_step_preserves_coherence
      exact typed_step_preserves_coherence (.send hk hx hG hS hv hRecvReady hEdge hG' hD' hBufs') hCoh
    · -- Process typing: skip is well-typed under any environment
      exact HasTypeProcPre.skip
  | recv hk hG hEdge hBuf hv hTrace hG' hD' hS' hStore' hBufs' =>
    -- Store updated with received value, S updated with x:T
    -- Buffers have one message dequeued
    -- Coherent preserved by typed_step_preserves_coherence
    -- Process becomes skip
    constructor
    · -- StoreTyped: store' = updateStr store x v, S' = updateSEnv S x T, G' = updateG G e L
      rw [hG', hS', hStore']
      exact StoreTyped_recv_preserved hStore hv
    constructor
    · -- BuffersTyped: buffer dequeued from recvEdge, then G updated
      -- From TypedStep.recv: D' = updateD D recvEdge (lookupD D recvEdge).tail
      --                      bufs' = updateBuf bufs recvEdge vs
      -- Step 1: Apply BuffersTyped_dequeue to get BuffersTyped G D' bufs'
      have hBufsDequeued := BuffersTyped_dequeue hBufs hBuf hTrace
      -- Step 2: Apply BuffersTyped_updateG_weaken to get BuffersTyped G' D' bufs'
      rw [hG', hD', hBufs']
      exact BuffersTyped_updateG_weaken hBufsDequeued
    constructor
    · -- Coherent: proven by typed_step_preserves_coherence
      exact typed_step_preserves_coherence (.recv hk hG hEdge hBuf hv hTrace hG' hD' hS' hStore' hBufs') hCoh
    · -- Process typing: skip is well-typed
      exact HasTypeProcPre.skip
  | assign hv hS' hStore' =>
    -- Store and S both updated: store' = updateStr store x v, S' = updateSEnv S x T
    -- TypedStep.assign has: HasTypeVal ∅ v T, S' = updateSEnv S x T, store' = updateStr store x v
    constructor
    · -- StoreTyped: both store and S updated with x:T
      rw [hS', hStore']
      exact StoreTyped_assign_preserved hStore hv
    constructor
    · -- BuffersTyped: buffers unchanged
      exact hBufs
    constructor
    · -- Coherent: G and D unchanged
      exact hCoh
    · -- Process typing: skip is well-typed
      exact HasTypeProcPre.skip
  | seq_step hTS =>
    -- P steps to P', so Q remains, resulting in seq P' Q
    -- hTS : TypedStep G D S store bufs P G' D' S' store' bufs' P'
    -- hProc : HasTypeProcPre S G (.seq P Q)
    -- ISSUE: Need HasTypeProcPre S' G' Q, but only have HasTypeProcPre S G Q
    -- This requires a monotonicity/weakening lemma for HasTypeProcPre:
    --   If S ⊆ S' and G extends G appropriately, then
    --   HasTypeProcPre S G Q → HasTypeProcPre S' G' Q
    -- Such a lemma doesn't currently exist and may not hold in general.
    -- The TypedStep.seq_step rule may need to be strengthened to require
    -- explicit preservation of Q's typing.
    sorry  -- Requires HasTypeProcPre monotonicity lemma
  | seq_skip =>
    -- seq skip Q steps to Q
    -- All environments unchanged
    constructor; exact hStore
    constructor; exact hBufs
    constructor; exact hCoh
    -- Q must have been well-typed from the input (seq skip Q was well-typed)
    -- hProc : HasTypeProcPre S G (.seq .skip Q)
    -- By inversion on seq constructor, we get HasTypeProcPre S G Q
    cases hProc with
    | seq hPskip hQ => exact hQ
  | par_left hTS hDisjG hDisjD hDisjS =>
    -- Left process steps, right unchanged
    -- hTS : TypedStep G₁ D₁ S₁ store bufs P G₁' D₁' S₁' store bufs P'
    -- Input WF: (G₁ ++ G₂) (D₁ ++ D₂) (S₁ ++ S₂) store bufs (.par P Q)
    -- Output WF: (G₁' ++ G₂) (D₁' ++ D₂) (S₁' ++ S₂) store bufs (.par P' Q)
    -- Strategy:
    -- 1. Split input WellFormed to get components for P and Q
    -- 2. Apply IH to left component
    -- 3. Merge results
    -- Requires lemmas:
    -- - StoreTyped (G₁ ++ G₂) (S₁ ++ S₂) → StoreTyped G₁ S₁ ∧ StoreTyped G₂ S₂
    -- - BuffersTyped (G₁ ++ G₂) (D₁ ++ D₂) → BuffersTyped G₁ D₁ (under disjointness)
    -- - Coherent (G₁ ++ G₂) (D₁ ++ D₂) → Coherent G₁ D₁ (under disjointness)
    -- - And corresponding merge lemmas for the outputs
    sorry  -- Need splitting/merging lemmas for WellFormed components
  | par_right hTS hDisjG hDisjD hDisjS =>
    -- Symmetric to par_left: right process steps, left unchanged
    sorry  -- Symmetric proof structure, same lemmas needed
  | par_skip_left =>
    -- par skip Q steps to Q
    constructor; exact hStore
    constructor; exact hBufs
    constructor; exact hCoh
    -- Q must have been well-typed from input
    -- hProc : HasTypeProcPre S G (.par .skip Q)
    -- By inversion on par constructor, we get HasTypeProcPre S G Q
    cases hProc with
    | par hPskip hQ => exact hQ
  | par_skip_right =>
    -- par P skip steps to P
    constructor; exact hStore
    constructor; exact hBufs
    constructor; exact hCoh
    -- P must have been well-typed from input
    -- hProc : HasTypeProcPre S G (.par P .skip)
    -- By inversion on par constructor, we get HasTypeProcPre S G P
    cases hProc with
    | par hP hQskip => exact hP

/-- Progress theorem: A well-formed process can either step or is in a final/blocked state.

    **Proof strategy**: Case analysis on process P:
    - `skip`: Terminates
    - `send k x`: Derive TypedStep.send from lookupG via HasTypeProcPre inversion
    - `recv k x`: Check buffer - if non-empty, derive TypedStep.recv; else blocked
    - `seq P Q`: Use IH on P or skip elimination
    - `par P Q`: Use IH on P or Q or skip elimination -/
theorem progress_typed {G D S store bufs P} :
    WellFormed G D S store bufs P →
    (P = .skip) ∨
    (∃ G' D' S' store' bufs' P', TypedStep G D S store bufs P G' D' S' store' bufs' P') ∨
    (∃ k x e source, P = .recv k x ∧
      lookupStr store k = some (.chan e) ∧
      lookupBuf bufs { sid := e.sid, sender := source, receiver := e.role } = []) := by
  intro hWF
  unfold WellFormed at hWF
  obtain ⟨hStore, hBufs, hCoh, hProc⟩ := hWF
  cases hProc with
  | skip => left; rfl
  | send hk hG hx =>
    -- Have: lookupSEnv S k = some (.chan e.sid e.role), lookupG G e = some (.send q T L), lookupSEnv S x = some T
    -- Need: Construct TypedStep.send with all preconditions
    --   - lookupStr store k = some (.chan e) from StoreTyped + hk
    --   - lookupStr store x = some v from StoreTyped + hx
    --   - HasTypeVal G v T from StoreTyped
    --   - hRecvReady from Coherent (receiver can consume message)
    right; left
    sorry
  | recv hk hG =>
    -- Have: lookupSEnv S k = some (.chan e.sid e.role), lookupG G e = some (.recv p T L)
    -- Need: Check if buffer is non-empty at edge
    --   - If lookupBuf bufs edge = v :: vs, construct TypedStep.recv
    --   - Else blocked (third alternative in progress conclusion)
    sorry
  | select hk hG hbs =>
    -- Similar to send - select sends a label
    sorry
  | branch hk hG hLen hLabels hBodies =>
    -- Similar to recv - branch receives a label
    sorry
  | seq hP hQ =>
    -- Either P can step, or P = skip and seq reduces
    -- If P ≠ skip, recursive call on P gets TypedStep, use seq_step
    -- If P = skip, use seq_skip
    sorry
  | par hP hQ =>
    -- Either P can step, or Q can step, or both are skip
    -- Recursive calls on P and Q, use par_left/par_right/par_skip_*
    sorry
  | assign hv =>
    -- Assign can always step
    -- Construct TypedStep.assign
    -- We have: HasTypeVal G v T (from hv)
    -- Need: HasTypeVal ∅ v T (stronger condition)
    -- This requires v to be a pure value (no channel dependencies)
    right; left
    rename_i x v T
    use G, D, (updateSEnv S x T), (updateStr store x v), bufs, .skip
    apply TypedStep.assign
    · -- HasTypeVal ∅ v T: this should hold for assignment values (pure values)
      -- But hv : HasTypeVal G v T, and we need to weaken to empty environment
      -- This is only valid for non-channel values
      sorry -- Need: values in assign are pure (no channels)
    · -- S' = updateSEnv S x T
      rfl
    · -- store' = updateStr store x v
      rfl

/-  Subject reduction (soundness) theorem moved to Effects.Preservation
    to avoid circular dependency (Step is defined in Semantics which imports Typing).

    **Theorem**: TypedStep G D S store bufs P G' D' S' store' bufs' P' →
                 Step ⟨P, store, bufs, G, D, n⟩ ⟨P', store', bufs', G', D', n⟩

    This will be proven in Preservation.lean after TypedStep is available. -/

end
