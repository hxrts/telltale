import Effects.Process

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

    **Interpretation**: Configuration C transitions from resource state (G, D, S)
    to configuration C' with resource state (G', D', S').

    **Linear Resources**:
    - Each endpoint in G is consumed exactly once and produces a continuation
    - Buffers and traces evolve consistently (append on send, pop on recv)
    - Variables are typed as they're assigned

    **Compositionality**: Parallel processes have disjoint resources -/
inductive TypedStep : GEnv → DEnv → SEnv → Config →
                      Config → GEnv → DEnv → SEnv → Prop
  | send {G D S store bufs k x e target T L v} :
      -- Pre-conditions (resources consumed)
      lookupStr store k = some (.chan e) →
      lookupStr store x = some v →
      lookupG G e = some (.send target T L) →
      lookupSEnv S x = some T →
      HasTypeVal G v T →

      -- Resource transition
      let sendEdge : Edge := { sid := e.sid, sender := e.role, receiver := target }
      let G' := updateG G e L
      let D' := appendD D sendEdge T
      let bufs' := enqueueBuf bufs sendEdge v

      -- Judgment
      TypedStep G D S
                ⟨store, bufs, .send k x⟩
                ⟨store, bufs', .skip⟩
                G' D' S

  | recv {G D S store bufs k x e source T L v vs} :
      -- Pre-conditions (resources consumed)
      lookupStr store k = some (.chan e) →
      lookupG G e = some (.recv source T L) →
      let recvEdge : Edge := { sid := e.sid, sender := source, receiver := e.role }
      lookupBuf bufs recvEdge = v :: vs →
      HasTypeVal G v T →  -- derived from BuffersTyped invariant

      -- Resource transition
      let G' := updateG G e L
      let D' := updateD D recvEdge (lookupD D recvEdge).tail
      let S' := updateSEnv S x T
      let store' := updateStr store x v
      let bufs' := updateBuf bufs recvEdge vs

      -- Judgment
      TypedStep G D S
                ⟨store, bufs, .recv k x⟩
                ⟨store', bufs', .skip⟩
                G' D' S'

  | assign {G D S store bufs x v T} :
      -- Pre-condition: value is well-typed (no endpoint dependencies)
      lookupStr store x = some v →
      HasTypeVal ∅ v T →

      -- Resource transition (only S changes)
      let S' := updateSEnv S x T

      -- Judgment
      TypedStep G D S
                ⟨store, bufs, .assign x (valueToExpr v)⟩
                ⟨store, bufs, .skip⟩
                G D S'

  | newSession {G D S store bufs supply roles localTypes} :
      -- Pre-conditions: fresh session ID allocation
      let sid := supply
      let (G', D', bufs') := initSession sid roles localTypes
      (∀ e L, (e, L) ∈ G' → e.sid = sid) →  -- all new endpoints have sid
      (∀ e L, (e, L) ∈ G → e.sid ≠ sid) →   -- sid is fresh

      -- Resource transition: merge fresh resources
      let G'' := G ++ G'  -- disjoint merge
      let D'' := D ++ D'
      let bufs'' := bufs ++ bufs'

      -- Judgment
      TypedStep G D S
                ⟨store, bufs, .newSession roles localTypes⟩
                ⟨store, bufs'', .skip⟩
                G'' D'' S

  | seq_step {G D S G' D' S' store bufs P P' Q} :
      -- Resources flow through first process
      TypedStep G D S
                ⟨store, bufs, P⟩
                ⟨store, bufs, P'⟩
                G' D' S' →

      TypedStep G D S
                ⟨store, bufs, .seq P Q⟩
                ⟨store, bufs, .seq P' Q⟩
                G' D' S'

  | seq_skip {G D S store bufs Q} :
      -- Skip elimination (identity transition)
      TypedStep G D S
                ⟨store, bufs, .seq .skip Q⟩
                ⟨store, bufs, Q⟩
                G D S

  | par_left {G₁ G₂ D₁ D₂ S₁ S₂ G₁' D₁' S₁' store bufs P P' Q} :
      -- Left process transitions with its resources
      TypedStep G₁ D₁ S₁
                ⟨store, bufs, P⟩
                ⟨store, bufs, P'⟩
                G₁' D₁' S₁' →

      -- Resources must be disjoint for parallel composition
      DisjointG G₁ G₂ →
      DisjointD D₁ D₂ →
      DisjointS S₁ S₂ →

      -- Combined transition
      TypedStep (G₁ ++ G₂) (D₁ ++ D₂) (S₁ ++ S₂)
                ⟨store, bufs, .par P Q⟩
                ⟨store, bufs, .par P' Q⟩
                (G₁' ++ G₂) (D₁' ++ D₂) (S₁' ++ S₂)

  | par_right {G₁ G₂ D₁ D₂ S₁ S₂ G₂' D₂' S₂' store bufs P Q Q'} :
      -- Right process transitions with its resources
      TypedStep G₂ D₂ S₂
                ⟨store, bufs, Q⟩
                ⟨store, bufs, Q'⟩
                G₂' D₂' S₂' →

      -- Resources must be disjoint
      DisjointG G₁ G₂ →
      DisjointD D₁ D₂ →
      DisjointS S₁ S₂ →

      -- Combined transition
      TypedStep (G₁ ++ G₂) (D₁ ++ D₂) (S₁ ++ S₂)
                ⟨store, bufs, .par P Q⟩
                ⟨store, bufs, .par P Q'⟩
                (G₁ ++ G₂') (D₁ ++ D₂') (S₁ ++ S₂')

  | par_skip_left {G D S store bufs Q} :
      -- Skip elimination from parallel
      TypedStep G D S
                ⟨store, bufs, .par .skip Q⟩
                ⟨store, bufs, Q⟩
                G D S

  | par_skip_right {G D S store bufs P} :
      -- Skip elimination from parallel
      TypedStep G D S
                ⟨store, bufs, .par P .skip⟩
                ⟨store, bufs, P⟩
                G D S

end
