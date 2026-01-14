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

end
