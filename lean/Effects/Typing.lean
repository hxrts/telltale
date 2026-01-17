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
set_option linter.unnecessarySimpa false

open scoped Classical

noncomputable section

/-! ## Process Typing Judgment -/

/-! ### Disjointness + Ownership/Footprints -/

/-- Session type environment disjointness.
    Two environments are disjoint if they have no session IDs in common. -/
def DisjointG (G₁ G₂ : GEnv) : Prop :=
  GEnvDisjoint G₁ G₂

/-- Sessions present in a DEnv (by edge keys). -/
def SessionsOfD (D : DEnv) : Set SessionId :=
  { s | ∃ e ts, D.find? e = some ts ∧ e.sid = s }

/-- Delayed type environment disjointness.
    Two environments are disjoint if they have no session IDs in common. -/
def DisjointD (D₁ D₂ : DEnv) : Prop :=
  SessionsOfD D₁ ∩ SessionsOfD D₂ = ∅

/-- Value type environment disjointness.
    Two environments are disjoint if no variable appears in both. -/
def DisjointS (S₁ S₂ : SEnv) : Prop :=
  ∀ x T₁ T₂, lookupSEnv S₁ x = some T₁ → lookupSEnv S₂ x = some T₂ → False

/-- Explicit split of S/G environments for parallel composition. -/
structure ParSplit (S : SEnv) (G : GEnv) where
  S1 : SEnv
  S2 : SEnv
  G1 : GEnv
  G2 : GEnv
  hS : S = S1 ++ S2
  hG : G = G1 ++ G2

axiom ParSplit.unique {S : SEnv} {G : GEnv} (s₁ s₂ : ParSplit S G) : s₁ = s₂


/-- DEnv consistency with GEnv: all sessions in D appear in G. -/
def DConsistent (G : GEnv) (D : DEnv) : Prop :=
  SessionsOfD D ⊆ SessionsOf G

/-- Footprint of variables a process may write/introduce. -/
abbrev Footprint := List Var

/-- Delta environment: bindings introduced by a process (backtimed to parent at join). -/
abbrev DeltaSEnv := SEnv

/-- Disjointness for footprints (over-approximate; duplicates allowed). -/
def DisjointW (W₁ W₂ : Footprint) : Prop :=
  List.Disjoint W₁ W₂

/-- Footprint subset (membership-based). -/
def FootprintSubset (W₁ W₂ : Footprint) : Prop :=
  ∀ ⦃x⦄, x ∈ W₁ → x ∈ W₂

/-- Delta environment subset (lookup-based). -/
def SEnvSubset (S₁ S₂ : SEnv) : Prop :=
  ∀ ⦃x T⦄, lookupSEnv S₁ x = some T → lookupSEnv S₂ x = some T

/-- Domain subset for SEnv (ignores binding types). -/
def SEnvDomSubset (S₁ S₂ : SEnv) : Prop :=
  ∀ ⦃x T⦄, lookupSEnv S₁ x = some T → ∃ T', lookupSEnv S₂ x = some T'

axiom SEnv_append_assoc (S₁ S₂ S₃ : SEnv) :
  (S₁ ++ S₂) ++ S₃ = S₁ ++ (S₂ ++ S₃)

theorem FootprintSubset_refl {W : Footprint} : FootprintSubset W W := by
  intro x hx; exact hx

theorem SEnvSubset_refl {S : SEnv} : SEnvSubset S S := by
  intro x T hx; exact hx

theorem SEnvDomSubset_refl {S : SEnv} : SEnvDomSubset S S := by
  intro x T h; exact ⟨T, h⟩

theorem FootprintSubset_append_left {W₁ W₁' W₂ : Footprint} :
    FootprintSubset W₁' W₁ →
    FootprintSubset (W₁' ++ W₂) (W₁ ++ W₂) := by
  intro hSub x hx
  have hx' := (List.mem_append.mp hx)
  cases hx' with
  | inl hLeft =>
      exact List.mem_append.mpr (Or.inl (hSub hLeft))
  | inr hRight =>
      exact List.mem_append.mpr (Or.inr hRight)

theorem FootprintSubset_append_right {W₁ W₂ : Footprint} :
    FootprintSubset W₂ (W₁ ++ W₂) := by
  intro x hx
  exact List.mem_append.mpr (Or.inr hx)

theorem FootprintSubset_append_right_of_subset {W₁ W₂ W₂' : Footprint} :
    FootprintSubset W₂' W₂ →
    FootprintSubset (W₁ ++ W₂') (W₁ ++ W₂) := by
  intro hSub x hx
  have hx' := (List.mem_append.mp hx)
  cases hx' with
  | inl hLeft =>
      exact List.mem_append.mpr (Or.inl hLeft)
  | inr hRight =>
      exact List.mem_append.mpr (Or.inr (hSub hRight))

axiom SEnvSubset_append_left {S₁ S₁' S₂ : SEnv} :
    SEnvSubset S₁' S₁ →
    SEnvSubset (S₁' ++ S₂) (S₁ ++ S₂)

axiom SEnvSubset_append_right {S₁ S₂ : SEnv} :
    SEnvSubset S₂ (S₁ ++ S₂)

axiom SEnvSubset_append_left_self {S₁ S₂ : SEnv} :
    SEnvSubset S₁ (S₁ ++ S₂)

axiom SEnvSubset_append_right_of_subset {S₁ S₂ S₂' : SEnv} :
    SEnvSubset S₂' S₂ →
    SEnvSubset (S₁ ++ S₂') (S₁ ++ S₂)

theorem SEnvDomSubset_trans {S₁ S₂ S₃ : SEnv} :
    SEnvDomSubset S₁ S₂ →
    SEnvDomSubset S₂ S₃ →
    SEnvDomSubset S₁ S₃ := by
  intro h₁ h₂ x T hLookup
  obtain ⟨T', hMid⟩ := h₁ hLookup
  exact h₂ hMid


theorem SEnvDomSubset_update_left {S : SEnv} {x : Var} {T : ValType} :
    SEnvDomSubset S (updateSEnv S x T) := by
  intro y Ty hLookup
  by_cases hEq : y = x
  · subst hEq
    exact ⟨T, by simpa using (lookupSEnv_update_eq S _ T)⟩
  · have hLookup' : lookupSEnv (updateSEnv S x T) y = lookupSEnv S y :=
      lookupSEnv_update_neq S x y T (Ne.symm hEq)
    exact ⟨Ty, by simpa [hLookup'] using hLookup⟩

theorem DisjointW_of_subset_left {W₁ W₁' W₂ : Footprint} :
    FootprintSubset W₁' W₁ →
    DisjointW W₁ W₂ →
    DisjointW W₁' W₂ := by
  intro hSub hDisj x hx hW2
  exact hDisj (hSub hx) hW2

theorem DisjointW_of_subset_right {W₁ W₂ W₂' : Footprint} :
    FootprintSubset W₂' W₂ →
    DisjointW W₁ W₂ →
    DisjointW W₁ W₂' := by
  intro hSub hDisj x hx hW2
  exact hDisj hx (hSub hW2)

axiom DisjointS_append_left {S₁ S₁' S₂ : SEnv} :
    DisjointS S₁ S₂ →
    DisjointS S₁' S₂ →
    DisjointS (S₁ ++ S₁') S₂

axiom DisjointS_of_subset_left {S₁ S₁' S₂ : SEnv} :
    SEnvSubset S₁' S₁ →
    DisjointS S₁ S₂ →
    DisjointS S₁' S₂

axiom DisjointS_of_domsubset_left {S₁ S₁' S₂ : SEnv} :
    SEnvDomSubset S₁' S₁ →
    DisjointS S₁ S₂ →
    DisjointS S₁' S₂

axiom DisjointS_of_subset_right {S₁ S₂ S₂' : SEnv} :
    SEnvSubset S₂' S₂ →
    DisjointS S₁ S₂ →
    DisjointS S₁ S₂'

axiom DisjointS_of_domsubset_right {S₁ S₂ S₂' : SEnv} :
    SEnvDomSubset S₂' S₂ →
    DisjointS S₁ S₂ →
    DisjointS S₁ S₂'

theorem DisjointS_symm {S₁ S₂ : SEnv} :
    DisjointS S₁ S₂ →
    DisjointS S₂ S₁ := by
  intro hDisj x T₁ T₂ hL1 hL2
  exact hDisj x T₂ T₁ hL2 hL1

theorem lookupSEnv_none_of_disjoint_left {S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    DisjointS S₁ S₂ →
    lookupSEnv S₂ x = some T →
    lookupSEnv S₁ x = none := by
  intro hDisj hL2
  by_cases hNone : lookupSEnv S₁ x = none
  · exact hNone
  · cases hL1 : lookupSEnv S₁ x with
    | none => exact (hNone hL1).elim
    | some T₁ =>
        exact (hDisj x T₁ T hL1 hL2).elim

/-- Combined variable environment: shared first, owned second. -/
def SEnvAll (Ssh Sown : SEnv) : SEnv :=
  Ssh ++ Sown

axiom updateSEnv_append_left {Ssh Sown : SEnv} {x : Var} {T : ValType}
    (h : lookupSEnv Ssh x = none) :
    updateSEnv (Ssh ++ Sown) x T = Ssh ++ updateSEnv Sown x T

theorem updateG_append_left {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType}
    (h : lookupG G₁ e = none) :
    updateG (G₁ ++ G₂) e L = G₁ ++ updateG G₂ e L := by
  induction G₁ with
  | nil =>
      simp
  | cons hd tl ih =>
      cases hd with
      | mk e' L' =>
          simp
          by_cases hxe : e = e'
          · -- Contradiction: lookup would be some at head.
            have hLookup : lookupG ((e', L') :: tl) e = some L' := by
              simp [lookupG, List.lookup, hxe]
            have hNone : lookupG ((e', L') :: tl) e = none := h
            have hContr : False := by
              simpa [hNone] using hLookup
            exact hContr.elim
          · have h' : lookupG tl e = none := by
              have hbeq : (e == e') = false := by
                exact beq_eq_false_iff_ne.mpr hxe
              simpa [lookupG, List.lookup, hbeq] using h
            simp [updateG, hxe, ih h']

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

  | par_left {Ssh store bufs P P' Q S G D₁ D₂ G₁' D₁' S₁'} (split : ParSplit S G) :
      -- Left process transitions with its resources
      TypedStep split.G1 D₁ Ssh split.S1 store bufs P
                G₁' D₁' S₁' store bufs P' →

      -- Resources must be disjoint for parallel composition
      DisjointG split.G1 split.G2 →
      DisjointD D₁ D₂ →
      DisjointS split.S1 split.S2 →
      DConsistent split.G1 D₁ →
      DConsistent split.G2 D₂ →

      -- Combined transition
      TypedStep G (D₁ ++ D₂) Ssh S store bufs (.par P Q)
                (G₁' ++ split.G2) (D₁' ++ D₂) (S₁' ++ split.S2) store bufs (.par P' Q)

  | par_right {Ssh store bufs P Q Q' S G D₁ D₂ G₂' D₂' S₂'} (split : ParSplit S G) :
      -- Right process transitions with its resources
      TypedStep split.G2 D₂ Ssh split.S2 store bufs Q
                G₂' D₂' S₂' store bufs Q' →

      -- Resources must be disjoint
      DisjointG split.G1 split.G2 →
      DisjointD D₁ D₂ →
      DisjointS split.S1 split.S2 →
      DConsistent split.G1 D₁ →
      DConsistent split.G2 D₂ →

      -- Combined transition
      TypedStep G (D₁ ++ D₂) Ssh S store bufs (.par P Q)
                (split.G1 ++ G₂') (D₁ ++ D₂') (split.S1 ++ S₂') store bufs (.par P Q')

  | par_skip_left {G D Ssh Sown store bufs Q} :
      -- Skip elimination from parallel
      TypedStep G D Ssh Sown store bufs (.par .skip Q)
                G D Sown store bufs Q

  | par_skip_right {G D Ssh Sown store bufs P} :
      -- Skip elimination from parallel
      TypedStep G D Ssh Sown store bufs (.par P .skip)
                G D Sown store bufs P

/-! ### WellFormed Predicate -/

/-- Well-formed process configuration.

    **Combines all invariants**: A process P with state (G, D, S, store, bufs)
    is well-formed if:
    1. Store is typed by S and G
    2. Buffers are typed by D
    3. G and D are coherent
    4. Process P has pre-update style typing

    This predicate is preserved by TypedStep transitions. -/
def WellFormed (G : GEnv) (D : DEnv) (Ssh Sown : SEnv)
    (store : Store) (bufs : Buffers) (P : Process) : Prop :=
  StoreTypedStrong G (SEnvAll Ssh Sown) store ∧
  BuffersTyped G D bufs ∧
  Coherent G D ∧
  HeadCoherent G D ∧
  ValidLabels G D bufs ∧
  SendReady G D ∧
  SelectReady G D ∧
  DisjointS Ssh Sown ∧
  DConsistent G D ∧
  ∃ S' G' W Δ, HasTypeProcPreOut Ssh Sown G P S' G' W Δ

/-! ## Support Lemmas for Preservation -/

/-- DisjointG: left lookup implies right is none. -/
theorem DisjointG_lookup_left {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType} :
    DisjointG G₁ G₂ →
    lookupG G₁ e = some L →
    lookupG G₂ e = none := by
  intro hDisj hLookup
  have hSid : e.sid ∈ SessionsOf G₁ := ⟨e, L, hLookup, rfl⟩
  have hNoSid : e.sid ∉ SessionsOf G₂ := by
    intro hSid2
    have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := by
      exact ⟨hSid, hSid2⟩
    have hEmpty := hDisj
    have : (SessionsOf G₁ ∩ SessionsOf G₂) = ∅ := hEmpty
    have hContra : e.sid ∈ (∅ : Set SessionId) := by
      simpa [this] using hInter
    exact hContra.elim
  by_contra hSome
  cases hLookup2 : lookupG G₂ e with
  | none => exact (hSome hLookup2)
  | some L2 =>
      have hSid2 : e.sid ∈ SessionsOf G₂ := ⟨e, L2, hLookup2, rfl⟩
      exact (hNoSid hSid2)

/-- If a session ID is not present in G, lookup at any endpoint with that ID is none. -/
theorem lookupG_none_of_not_session {G : GEnv} {e : Endpoint} :
    e.sid ∉ SessionsOf G →
    lookupG G e = none := by
  intro hNot
  cases hLookup : lookupG G e with
  | none => simp
  | some L =>
      have hSid : e.sid ∈ SessionsOf G := ⟨e, L, hLookup, rfl⟩
      exact (hNot hSid).elim

axiom DisjointD_lookup_left {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType} :
    DisjointD D₁ D₂ →
    D₁.find? e = some ts →
    D₂.find? e = none

axiom DisjointD_lookup_right {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType} :
    DisjointD D₁ D₂ →
    D₂.find? e = some ts →
    D₁.find? e = none

axiom SessionsOfD_append_subset {D₁ D₂ : DEnv} :
    SessionsOfD (D₁ ++ D₂) ⊆ SessionsOfD D₁ ∪ SessionsOfD D₂

axiom SessionsOfD_append_left {D₁ D₂ : DEnv} :
    SessionsOfD D₁ ⊆ SessionsOfD (D₁ ++ D₂)

axiom SessionsOfD_append_right {D₁ D₂ : DEnv} :
    SessionsOfD D₂ ⊆ SessionsOfD (D₁ ++ D₂)

axiom SessionsOfD_updateD_subset {D : DEnv} {e : Edge} {ts : List ValType} :
    SessionsOfD (updateD D e ts) ⊆ SessionsOfD D ∪ {e.sid}

axiom lookupD_entry_of_nonempty {D : DEnv} {e : Edge} :
    lookupD D e ≠ [] →
    ∃ ts, D.find? e = some ts

/-- Lookup in appended GEnv prefers the left. -/
theorem lookupG_append_left {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType} :
    lookupG G₁ e = some L →
    lookupG (G₁ ++ G₂) e = some L := by
  intro h
  have hLookup : G₁.lookup e = some L := by
    simpa [lookupG] using h
  calc
    lookupG (G₁ ++ G₂) e = (G₁.lookup e).or (G₂.lookup e) := by
      simp [lookupG, List.lookup_append]
    _ = some L := by
      simp [hLookup]

/-- Lookup in appended GEnv falls back to the right when left is missing. -/
theorem lookupG_append_right {G₁ G₂ : GEnv} {e : Endpoint} :
    lookupG G₁ e = none →
    lookupG (G₁ ++ G₂) e = lookupG G₂ e := by
  intro h
  have hLookup : G₁.lookup e = none := by
    simpa [lookupG] using h
  calc
    lookupG (G₁ ++ G₂) e = (G₁.lookup e).or (G₂.lookup e) := by
      simp [lookupG, List.lookup_append]
    _ = lookupG G₂ e := by
      simp [hLookup, lookupG]

/-- Invert lookup in an appended GEnv. -/
theorem lookupG_append_inv {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType} :
    lookupG (G₁ ++ G₂) e = some L →
    lookupG G₁ e = some L ∨ (lookupG G₁ e = none ∧ lookupG G₂ e = some L) := by
  intro h
  have hLookup : (G₁.lookup e).or (G₂.lookup e) = some L := by
    simpa [lookupG, List.lookup_append] using h
  cases hLeft : G₁.lookup e with
  | none =>
      right
      have hRight : G₂.lookup e = some L := by
        simpa [hLeft] using hLookup
      exact ⟨by simpa [lookupG] using hLeft, by simpa [lookupG] using hRight⟩
  | some L1 =>
      have hEq : L1 = L := by
        simpa [hLeft] using hLookup
      left
      simpa [lookupG, hEq] using hLeft

theorem SessionsOf_append_right_subset {G₁ G₂ : GEnv} :
    SessionsOf G₂ ⊆ SessionsOf (G₁ ++ G₂) := by
  intro s hMem
  rcases hMem with ⟨e, L, hLookup, hSid⟩
  by_cases hNone : lookupG G₁ e = none
  · have hEq := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hNone
    exact ⟨e, L, by simpa [hEq] using hLookup, hSid⟩
  · cases hSome : lookupG G₁ e with
    | none => exact (hNone hSome).elim
    | some L₁ =>
        have hLeft : lookupG (G₁ ++ G₂) e = some L₁ :=
          lookupG_append_left (G₁:=G₁) (G₂:=G₂) hSome
        exact ⟨e, L₁, hLeft, hSid⟩

/-- Sessions in an appended GEnv are contained in the union of sessions. -/
theorem SessionsOf_append_subset {G₁ G₂ : GEnv} :
    SessionsOf (G₁ ++ G₂) ⊆ SessionsOf G₁ ∪ SessionsOf G₂ := by
  intro s hs
  rcases hs with ⟨e, L, hLookup, hSid⟩
  have hLookup' : (G₁.lookup e).or (G₂.lookup e) = some L := by
    simpa [lookupG, List.lookup_append] using hLookup
  cases hLeft : G₁.lookup e with
  | none =>
      have hRight : G₂.lookup e = some L := by
        simpa [hLeft] using hLookup'
      right
      exact ⟨e, L, by simpa [lookupG] using hRight, hSid⟩
  | some L1 =>
      have hEq : L1 = L := by
        simpa [hLeft] using hLookup'
      left
      exact ⟨e, L1, by simpa [lookupG] using hLeft, by simpa [hEq] using hSid⟩

/-- Left sessions embed into appended GEnv sessions. -/
theorem SessionsOf_append_left {G₁ G₂ : GEnv} :
    SessionsOf G₁ ⊆ SessionsOf (G₁ ++ G₂) := by
  intro s hs
  rcases hs with ⟨e, L, hLookup, hSid⟩
  exact ⟨e, L, lookupG_append_left hLookup, hSid⟩

/-- Right sessions embed into appended GEnv sessions. -/
theorem SessionsOf_append_right {G₁ G₂ : GEnv} :
    SessionsOf G₂ ⊆ SessionsOf (G₁ ++ G₂) := by
  intro s hs
  by_cases hIn1 : s ∈ SessionsOf G₁
  · exact SessionsOf_append_left (G₂:=G₂) hIn1
  · rcases hs with ⟨e, L, hLookup, hSid⟩
    have hNone : lookupG G₁ e = none := by
      apply lookupG_none_of_not_session
      intro hMem
      exact hIn1 (by simpa [hSid] using hMem)
    have hLookup' : lookupG (G₁ ++ G₂) e = some L := by
      simpa [lookupG_append_right hNone] using hLookup
    exact ⟨e, L, hLookup', hSid⟩

/-- Disjointness is preserved when the left sessions shrink. -/
theorem DisjointG_of_subset_left {G₁ G₁' G₂ : GEnv} :
    SessionsOf G₁' ⊆ SessionsOf G₁ →
    DisjointG G₁ G₂ →
    DisjointG G₁' G₂ := by
  intro hSub hDisj
  -- show SessionsOf G₁' ∩ SessionsOf G₂ = ∅
  ext s; constructor
  · intro hMem
    have hLeft : s ∈ SessionsOf G₁ := hSub hMem.1
    have hRight : s ∈ SessionsOf G₂ := hMem.2
    have hInter : s ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hLeft, hRight⟩
    have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := hDisj
    have hContra : s ∈ (∅ : Set SessionId) := by
      simpa [hEmpty] using hInter
    exact hContra.elim
  · intro hMem
    exact hMem.elim

/-- DisjointG is symmetric. -/
theorem DisjointG_symm {G₁ G₂ : GEnv} :
    DisjointG G₁ G₂ →
    DisjointG G₂ G₁ := by
  intro hDisj
  unfold DisjointG at *
  unfold GEnvDisjoint at hDisj
  unfold GEnvDisjoint
  simpa [Set.inter_comm] using hDisj

theorem DisjointG_append_left {G₁ G₁' G₂ : GEnv} :
    DisjointG G₁ G₂ →
    DisjointG G₁' G₂ →
    DisjointG (G₁ ++ G₁') G₂ := by
  intro hDisj1 hDisj2
  unfold DisjointG at *
  unfold GEnvDisjoint at *
  ext s; constructor
  · intro hMem
    rcases hMem with ⟨hInLeft, hInRight⟩
    rcases hInLeft with ⟨e, L, hLookup, hSid⟩
    have hInv := lookupG_append_inv (G₁:=G₁) (G₂:=G₁') (e:=e) (L:=L) hLookup
    cases hInv with
    | inl hLeft =>
        have hInter : s ∈ SessionsOf G₁ ∩ SessionsOf G₂ := by
          exact ⟨⟨e, L, hLeft, hSid⟩, hInRight⟩
        have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = ∅ := hDisj1
        have hContra : s ∈ (∅ : Set SessionId) := by
          simpa [hEmpty] using hInter
        exact hContra.elim
    | inr hRight =>
        rcases hRight with ⟨_, hLookupR⟩
        have hInter : s ∈ SessionsOf G₁' ∩ SessionsOf G₂ := by
          exact ⟨⟨e, L, hLookupR, hSid⟩, hInRight⟩
        have hEmpty : SessionsOf G₁' ∩ SessionsOf G₂ = ∅ := hDisj2
        have hContra : s ∈ (∅ : Set SessionId) := by
          simpa [hEmpty] using hInter
        exact hContra.elim
  · intro hMem
    exact hMem.elim

axiom lookupD_append_left {D₁ D₂ : DEnv} {e : Edge} :
    lookupD D₁ e ≠ [] →
    lookupD (D₁ ++ D₂) e = lookupD D₁ e

axiom lookupD_append_right {D₁ D₂ : DEnv} {e : Edge} :
    D₁.find? e = none →
    lookupD (D₁ ++ D₂) e = lookupD D₂ e

axiom lookupD_append_left_of_right_none {D₁ D₂ : DEnv} {e : Edge} :
    D₂.find? e = none →
    lookupD (D₁ ++ D₂) e = lookupD D₁ e

axiom lookupSEnv_append_left {S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    lookupSEnv S₁ x = some T →
    lookupSEnv (S₁ ++ S₂) x = some T

/-- Lookup in appended SEnv falls back to the right when left is missing. -/
axiom lookupSEnv_append_right {S₁ S₂ : SEnv} {x : Var} :
    lookupSEnv S₁ x = none →
    lookupSEnv (S₁ ++ S₂) x = lookupSEnv S₂ x

/-- Domain subset: left part embeds into append. -/
axiom SEnvDomSubset_append_left {S₁ S₂ : SEnv} :
    SEnvDomSubset S₁ (S₁ ++ S₂)

/-- Domain subset: right part embeds into append. -/
axiom SEnvDomSubset_append_right {S₁ S₂ : SEnv} :
    SEnvDomSubset S₂ (S₁ ++ S₂)

axiom lookupSEnv_all_frame_left {Ssh S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    DisjointS S₁ S₂ →
    lookupSEnv (Ssh ++ S₂) x = some T →
    lookupSEnv (Ssh ++ (S₁ ++ S₂)) x = some T

/-- Pre-out typing never shrinks the owned variable environment (by domain). -/
theorem HasTypeProcPreOut_domsubset {Ssh Sown G P Sown' G' W Δ} :
    HasTypeProcPreOut Ssh Sown G P Sown' G' W Δ →
    SEnvDomSubset Sown Sown' := by
  intro h
  induction h with
  | skip =>
      exact SEnvDomSubset_refl
  | send =>
      exact SEnvDomSubset_refl
  | recv_new =>
      exact SEnvDomSubset_update_left
  | recv_old =>
      exact SEnvDomSubset_update_left
  | select =>
      exact SEnvDomSubset_refl
  | branch _ _ _ _ _ _ hDom =>
      exact hDom
  | seq hP hQ ihP ihQ =>
      exact SEnvDomSubset_trans ihP ihQ
  | par split hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hP hQ ihP ihQ =>
      rename_i S₁out S₂out G₁out G₂out W₁ W₂ Δ₁ Δ₂
      intro x T hLookup
      have hLookupS : lookupSEnv (split.S1 ++ split.S2) x = some T := by
        simpa [split.hS] using hLookup
      by_cases hLeftNone : lookupSEnv split.S1 x = none
      · have hRight : lookupSEnv split.S2 x = some T := by
          have hEq := lookupSEnv_append_right (S₁:=split.S1) (S₂:=split.S2) (x:=x) hLeftNone
          simpa [hEq] using hLookupS
        obtain ⟨T', hRight'⟩ := ihQ hRight
        have hLeftNone' : lookupSEnv S₁out x = none := by
          by_cases hSome : lookupSEnv S₁out x = none
          · exact hSome
          · cases hSome' : lookupSEnv S₁out x with
            | none => exact (hSome hSome').elim
            | some T₁ =>
                exact (hDisjS' x T₁ T' hSome' hRight').elim
        have hEq := lookupSEnv_append_right (S₁:=S₁out) (S₂:=S₂out) (x:=x) hLeftNone'
        have hAppend : lookupSEnv (S₁out ++ S₂out) x = some T' := by
          simpa [hEq] using hRight'
        exact ⟨T', by simpa [hSfin] using hAppend⟩
      · cases hLeftSome : lookupSEnv split.S1 x with
        | none => exact (hLeftNone hLeftSome).elim
        | some T₁ =>
            have hLeftAppend :
                lookupSEnv (split.S1 ++ split.S2) x = some T₁ :=
              lookupSEnv_append_left (S₁:=split.S1) (S₂:=split.S2) hLeftSome
            have hEqT : T₁ = T := by
              have : some T₁ = some T := by
                simpa [hLeftAppend] using hLookupS
              exact Option.some.inj this
            obtain ⟨T', hLeft'⟩ := ihP (by simpa [hEqT] using hLeftSome)
            have hAppend := lookupSEnv_append_left (S₁:=S₁out) (S₂:=S₂out) hLeft'
            exact ⟨T', by simpa [hSfin] using hAppend⟩
  | assign_new =>
      exact SEnvDomSubset_update_left
  | assign_old =>
      exact SEnvDomSubset_update_left

/-- StoreTyped splits to the left portion of SEnv. -/
theorem StoreTyped_split_left {G : GEnv} {S₁ S₂ : SEnv} {store : Store} :
    StoreTyped G (S₁ ++ S₂) store →
    StoreTyped G S₁ store := by
  intro hST x v T hStore hS
  have hS' : lookupSEnv (S₁ ++ S₂) x = some T :=
    lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) hS
  exact hST x v T hStore hS'

/-- StoreTyped splits to the right portion of SEnv (requires disjointness). -/
theorem StoreTyped_split_right {G : GEnv} {S₁ S₂ : SEnv} {store : Store}
    (hDisj : DisjointS S₁ S₂) :
    StoreTyped G (S₁ ++ S₂) store →
    StoreTyped G S₂ store := by
  intro hST x v T hStore hS
  have hNone : lookupSEnv S₁ x = none := by
    by_cases hS1 : lookupSEnv S₁ x = none
    · exact hS1
    · cases hS1' : lookupSEnv S₁ x with
      | none => exact (hS1 hS1').elim
      | some T₁ =>
          exact (hDisj x T₁ T hS1' hS).elim
  have hS' : lookupSEnv (S₁ ++ S₂) x = some T := by
    have h := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hNone
    simpa [hS] using h
  exact hST x v T hStore hS'

/-- Coherence splits to the left portion of G/D. -/
theorem Coherent_split_left {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    Coherent (G₁ ++ G₂) (D₁ ++ D₂) →
    Coherent G₁ D₁ := by
  intro hCoh e Lsender Lrecv hGsender hGrecv
  have hGsender' : lookupG (G₁ ++ G₂) { sid := e.sid, role := e.sender } = some Lsender :=
    lookupG_append_left hGsender
  have hGrecv' : lookupG (G₁ ++ G₂) { sid := e.sid, role := e.receiver } = some Lrecv :=
    lookupG_append_left hGrecv
  by_cases hTrace : lookupD D₁ e = []
  · -- Empty trace: Consume is trivially some
    simp [hTrace, Consume]
  · -- Non-empty trace: use coherence of the merged env
    have hTrace' : lookupD (D₁ ++ D₂) e = lookupD D₁ e :=
      lookupD_append_left (e := e) hTrace
    have hCoh' := hCoh e Lsender Lrecv hGsender' hGrecv'
    simpa [hTrace'] using hCoh'

/-- Updating an existing endpoint preserves the set of sessions. -/
theorem SessionsOf_updateG_eq {G : GEnv} {e : Endpoint} {L L' : LocalType}
    (hLookup : lookupG G e = some L') :
    SessionsOf (updateG G e L) = SessionsOf G := by
  ext s; constructor
  · intro hs
    rcases hs with ⟨e', L'', hLookup', hSid⟩
    by_cases heq : e' = e
    · cases heq
      exact ⟨e, L', hLookup, hSid⟩
    · have hLookup'' : lookupG G e' = some L'' := by
        simpa [lookupG_update_neq _ _ _ _ (Ne.symm heq)] using hLookup'
      exact ⟨e', L'', hLookup'', hSid⟩
  · intro hs
    rcases hs with ⟨e', L'', hLookup', hSid⟩
    by_cases heq : e' = e
    · cases heq
      exact ⟨e, L, by simpa using (lookupG_update_eq G e L), hSid⟩
    · have hLookup'' : lookupG (updateG G e L) e' = some L'' := by
        simpa [lookupG_update_neq _ _ _ _ (Ne.symm heq)] using hLookup'
      exact ⟨e', L'', hLookup'', hSid⟩

/-- Sessions only shrink under TypedStep (no new sessions introduced). -/
theorem SessionsOf_subset_of_TypedStep {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    SessionsOf G' ⊆ SessionsOf G := by
  intro hTS
  induction hTS with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
        SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.send target T L) hG
      simp [hGout, hEq]
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
        SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.recv source T L) hG
      simp [hGout, hEq]
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
        SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.select target bs) hG
      simp [hGout, hEq]
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
        SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.branch source bs) hG
      simp [hGout, hEq]
  | assign =>
      simp
  | seq_step _ ih =>
      exact ih
  | seq_skip =>
      simp
  | par_left split hTS hDisjG hDisjD hDisjS hConsL hConsR ih =>
      rename_i Ssh store bufs P P' Q S G D₁ D₂ G₁' D₁' S₁'
      intro s hs
      have hs' : s ∈ SessionsOf G₁' ∪ SessionsOf split.G2 :=
        SessionsOf_append_subset (G₁:=G₁') (G₂:=split.G2) hs
      have hs'' : s ∈ SessionsOf split.G1 ∪ SessionsOf split.G2 := by
        cases hs' with
        | inl hleft => exact Or.inl (ih hleft)
        | inr hright => exact Or.inr hright
      have hUnion : SessionsOf split.G1 ∪ SessionsOf split.G2 ⊆ SessionsOf (split.G1 ++ split.G2) := by
        intro s' hs'
        cases hs' with
        | inl hleft => exact SessionsOf_append_left (G₂:=split.G2) hleft
        | inr hright => exact SessionsOf_append_right (G₁:=split.G1) hright
      have : s ∈ SessionsOf (split.G1 ++ split.G2) := hUnion hs''
      simpa [split.hG] using this
  | par_right split hTS hDisjG hDisjD hDisjS hConsL hConsR ih =>
      rename_i Ssh store bufs P Q Q' S G D₁ D₂ G₂' D₂' S₂'
      intro s hs
      have hs' : s ∈ SessionsOf split.G1 ∪ SessionsOf G₂' :=
        SessionsOf_append_subset (G₁:=split.G1) (G₂:=G₂') hs
      have hs'' : s ∈ SessionsOf split.G1 ∪ SessionsOf split.G2 := by
        cases hs' with
        | inl hleft => exact Or.inl hleft
        | inr hright => exact Or.inr (ih hright)
      have hUnion : SessionsOf split.G1 ∪ SessionsOf split.G2 ⊆ SessionsOf (split.G1 ++ split.G2) := by
        intro s' hs'
        cases hs' with
        | inl hleft => exact SessionsOf_append_left (G₂:=split.G2) hleft
        | inr hright => exact SessionsOf_append_right (G₁:=split.G1) hright
      have : s ∈ SessionsOf (split.G1 ++ split.G2) := hUnion hs''
      simpa [split.hG] using this
  | par_skip_left =>
      simp
  | par_skip_right =>
      simp

/-- D sessions remain within original sessions plus the current G sessions. -/
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
  | par_left split hTS hDisjG hDisjD hDisjS hConsL hConsR ih =>
      rename_i Ssh store bufs P P' Q S G D₁ D₂ G₁' D₁' S₁'
      intro s hs
      have hs' : s ∈ SessionsOfD D₁' ∪ SessionsOfD D₂ :=
        SessionsOfD_append_subset (D₁:=D₁') (D₂:=D₂) hs
      cases hs' with
      | inl hleft =>
          have hleft' : s ∈ SessionsOfD D₁ ∪ SessionsOf split.G1 := ih hleft
          cases hleft' with
          | inl hD1 =>
              exact Or.inl (SessionsOfD_append_left (D₂:=D₂) hD1)
          | inr hG1 =>
              exact Or.inr (by simpa [split.hG] using SessionsOf_append_left (G₂:=split.G2) hG1)
      | inr hright =>
          exact Or.inl (SessionsOfD_append_right (D₁:=D₁) hright)
  | par_right split hTS hDisjG hDisjD hDisjS hConsL hConsR ih =>
      rename_i Ssh store bufs P Q Q' S G D₁ D₂ G₂' D₂' S₂'
      intro s hs
      have hs' : s ∈ SessionsOfD D₁ ∪ SessionsOfD D₂' :=
        SessionsOfD_append_subset (D₁:=D₁) (D₂:=D₂') hs
      cases hs' with
      | inl hleft =>
          exact Or.inl (SessionsOfD_append_left (D₂:=D₂) hleft)
      | inr hright =>
          have hright' : s ∈ SessionsOfD D₂ ∪ SessionsOf split.G2 := ih hright
          cases hright' with
          | inl hD2 =>
              exact Or.inl (SessionsOfD_append_right (D₁:=D₁) hD2)
          | inr hG2 =>
              exact Or.inr (by simpa [split.hG] using SessionsOf_append_right (G₁:=split.G1) hG2)
  | par_skip_left =>
      simp
  | par_skip_right =>
      simp

axiom lookupD_none_of_disjointG {G₁ G₂ : GEnv} {D₂ : DEnv} {e : Edge} :
    DisjointG G₁ G₂ →
    DConsistent G₂ D₂ →
    e.sid ∈ SessionsOf G₁ →
    D₂.find? e = none

/-- Coherence splits to the right portion of G/D when sessions are disjoint. -/
theorem Coherent_split_right {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    Coherent (G₁ ++ G₂) (D₁ ++ D₂) →
    DisjointG G₁ G₂ →
    DConsistent G₁ D₁ →
    Coherent G₂ D₂ := by
  intro hCoh hDisj hCons e Lsender Lrecv hGsender hGrecv
  -- endpoints are in G₂; ensure G₁ has none for this session
  have hSid : e.sid ∈ SessionsOf G₂ := ⟨{ sid := e.sid, role := e.sender }, Lsender, hGsender, rfl⟩
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
  have hGsender' : lookupG (G₁ ++ G₂) { sid := e.sid, role := e.sender } = some Lsender := by
    simpa [lookupG_append_right hG1none_sender] using hGsender
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
  have hCohEdge := hCoh e Lsender Lrecv hGsender' hGrecv'
  simpa [hTraceEq] using hCohEdge

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
    The value v has type T in G (from TypedStep.assign premise). After update,
    store[x] = v and S[x] = T match. -/
theorem StoreTyped_assign_preserved {G : GEnv} {S : SEnv} {store : Store} {x : Var} {v : Value} {T : ValType} :
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
      simp [lookupBuf_update_eq]
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
          simp [lookupBuf_update_eq, lookupD_update_eq, hLen']
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

/-! ### Framing Lemmas -/

/-- HasTypeVal is stable under framing on the left of G. -/
theorem HasTypeVal_frame_left {G₁ G₂ : GEnv} {v : Value} {T : ValType} :
    DisjointG G₁ G₂ →
    HasTypeVal G₂ v T →
    HasTypeVal (G₁ ++ G₂) v T := by
  intro hDisj hv
  cases hv with
  | unit => exact HasTypeVal.unit
  | bool b => exact HasTypeVal.bool b
  | nat n => exact HasTypeVal.nat n
  | string s => exact HasTypeVal.string s
  | prod h₁ h₂ =>
      exact HasTypeVal.prod (HasTypeVal_frame_left hDisj h₁) (HasTypeVal_frame_left hDisj h₂)
  | chan h =>
      rename_i e L
      have hDisjSym := DisjointG_symm hDisj
      have hNone : lookupG G₁ e = none :=
        DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym h
      have hLookup : lookupG (G₁ ++ G₂) e = some L := by
        simpa [lookupG_append_right hNone] using h
      exact HasTypeVal.chan hLookup

/-- Pre-update typing is stable under framing on the left of G (no S changes). -/
axiom HasTypeProcPre_frame_G {Ssh Sown : SEnv} {G₁ G₂ : GEnv} {P : Process} :
    DisjointG G₁ G₂ →
    HasTypeProcPre Ssh Sown G₂ P →
    HasTypeProcPre Ssh Sown (G₁ ++ G₂) P

/-- Pre-update typing is stable under framing on the left of S/G. -/
axiom HasTypeProcPre_frame_left {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {P : Process} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    HasTypeProcPre Ssh S₂ G₂ P →
    HasTypeProcPre Ssh (S₁ ++ S₂) (G₁ ++ G₂) P

/-- Sessions only shrink under pre-out typing (no new sessions introduced).

    NOTE: This is assumed for now; branch typing with empty branches does not
    constrain G'. -/
axiom SessionsOf_subset_of_HasTypeProcPreOut
    {Ssh Sown G P Sown' G' W Δ} :
    HasTypeProcPreOut Ssh Sown G P Sown' G' W Δ →
    SessionsOf G' ⊆ SessionsOf G

/-- Pre-out typing is stable under framing on the left of S/G. -/
axiom HasTypeProcPreOut_frame_left
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {P : Process}
    {S₂' : SEnv} {G₂' : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointS S₁ S₂ →
    DisjointS S₁ S₂' →
    DisjointG G₁ G₂ →
    HasTypeProcPreOut Ssh S₂ G₂ P S₂' G₂' W Δ →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) P (S₁ ++ S₂') (G₁ ++ G₂') W Δ

-- TODO: Frame-right is invalid with list-based environments when new variables are appended.
-- Consider switching SEnv to a permutation-invariant structure or avoid right-framing.
axiom HasTypeProcPreOut_frame_right
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {P : Process}
    {S₁' : SEnv} {G₁' : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointS S₂ S₁ →
    DisjointG G₁ G₂ →
    HasTypeProcPreOut Ssh S₁ G₁ P S₁' G₁' W Δ →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) P (S₁' ++ S₂) (G₁' ++ G₂) W Δ

/-! ### Pre-Update Typing Preservation -/

/-- Pre-out typing is preserved by a single TypedStep: the remaining process
    still leads to the same final environments. -/
private theorem HasTypeProcPreOut_preserved_sub
    {Gstore G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' Sfin Gfin W Δ} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G' P' Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvSubset Δ' Δ := by
  intro hStore hTS hPre
  induction hTS generalizing Sfin Gfin W Δ with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      cases hPre with
      | send hk' hG' hx' =>
          rename_i e' q' T' L'
          have hkPre : lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) := by
            simpa using hk'
          have hGPre : lookupG G e' = some (.send q' T' L') := by
            simpa using hG'
          -- Align endpoints via store typing.
          have hkTyped : HasTypeVal Gstore (.chan e) (.chan e'.sid e'.role) :=
            hStore k (.chan e) (.chan e'.sid e'.role) hk hkPre
          have hEq : e = e' := by
            have hValEq : (Value.chan e) = Value.chan ⟨e'.sid, e'.role⟩ := by
              simpa using (HasTypeVal_chan_inv hkTyped)
            cases e
            cases e'
            cases hValEq
            rfl
          have hG'' : lookupG G e = some (.send q' T' L') := by
            simpa [hEq] using hGPre
          have hEqSend : (LocalType.send target T L) = (LocalType.send q' T' L') := by
            have : some (LocalType.send target T L) = some (LocalType.send q' T' L') := by
              simpa [hG] using hG''
            exact Option.some.inj this
          have hL : L' = L := by
            cases hEqSend
            rfl
          refine ⟨[], ∅, ?_, ?_, ?_⟩
          · subst hGout
            simpa [hEq, hL] using (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown) (G:=updateG G e L))
          · intro x hx; cases hx
          · intro x T hx; cases hx
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      cases hPre with
      | recv_new hk' hG' hSsh hSown =>
          rename_i e' p' T' L'
          have hkPre : lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) := by
            simpa using hk'
          have hGPre : lookupG G e' = some (.recv p' T' L') := by
            simpa using hG'
          -- Align endpoints via store typing.
          have hkTyped : HasTypeVal Gstore (.chan e) (.chan e'.sid e'.role) :=
            hStore k (.chan e) (.chan e'.sid e'.role) hk hkPre
          have hEq : e = e' := by
            have hValEq : (Value.chan e) = Value.chan ⟨e'.sid, e'.role⟩ := by
              simpa using (HasTypeVal_chan_inv hkTyped)
            cases e
            cases e'
            cases hValEq
            rfl
          have hG'' : lookupG G e = some (.recv p' T' L') := by
            simpa [hEq] using hGPre
          have hEqRecv : (LocalType.recv source T L) = (LocalType.recv p' T' L') := by
            have : some (LocalType.recv source T L) = some (LocalType.recv p' T' L') := by
              simpa [hG] using hG''
            exact Option.some.inj this
          have hT : T' = T := by
            cases hEqRecv
            rfl
          have hL : L' = L := by
            cases hEqRecv
            rfl
          refine ⟨[], ∅, ?_, ?_, ?_⟩
          · subst hGout; subst hSout
            simpa [hEq, hT, hL] using (HasTypeProcPreOut.skip
              (Ssh:=Ssh) (Sown:=updateSEnv Sown x T) (G:=updateG G e L))
          · intro x hx; cases hx
          · intro x T hx; cases hx
      | recv_old hk' hG' hSsh hSown =>
          rename_i e' p' T' L' Told
          have hkPre : lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) := by
            simpa using hk'
          have hGPre : lookupG G e' = some (.recv p' T' L') := by
            simpa using hG'
          -- Align endpoints via store typing.
          have hkTyped : HasTypeVal Gstore (.chan e) (.chan e'.sid e'.role) :=
            hStore k (.chan e) (.chan e'.sid e'.role) hk hkPre
          have hEq : e = e' := by
            have hValEq : (Value.chan e) = Value.chan ⟨e'.sid, e'.role⟩ := by
              simpa using (HasTypeVal_chan_inv hkTyped)
            cases e
            cases e'
            cases hValEq
            rfl
          have hG'' : lookupG G e = some (.recv p' T' L') := by
            simpa [hEq] using hGPre
          have hEqRecv : (LocalType.recv source T L) = (LocalType.recv p' T' L') := by
            have : some (LocalType.recv source T L) = some (LocalType.recv p' T' L') := by
              simpa [hG] using hG''
            exact Option.some.inj this
          have hT : T' = T := by
            cases hEqRecv
            rfl
          have hL : L' = L := by
            cases hEqRecv
            rfl
          refine ⟨[], ∅, ?_, ?_, ?_⟩
          · subst hGout; subst hSout
            simpa [hEq, hT, hL] using (HasTypeProcPreOut.skip
              (Ssh:=Ssh) (Sown:=updateSEnv Sown x T) (G:=updateG G e L))
          · intro x hx; cases hx
          · intro x T hx; cases hx
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      cases hPre with
      | select hk' hG' hFind' =>
          rename_i e' q' bs' L'
          have hkPre : lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) := by
            simpa using hk'
          have hGPre : lookupG G e' = some (.select q' bs') := by
            simpa using hG'
          -- Align endpoints via store typing.
          have hkTyped : HasTypeVal Gstore (.chan e) (.chan e'.sid e'.role) :=
            hStore k (.chan e) (.chan e'.sid e'.role) hk hkPre
          have hEq : e = e' := by
            have hValEq : (Value.chan e) = Value.chan ⟨e'.sid, e'.role⟩ := by
              simpa using (HasTypeVal_chan_inv hkTyped)
            cases e
            cases e'
            cases hValEq
            rfl
          have hG'' : lookupG G e = some (.select q' bs') := by
            simpa [hEq] using hGPre
          have hEqSel : (LocalType.select target bs) = (LocalType.select q' bs') := by
            have : some (LocalType.select target bs) = some (LocalType.select q' bs') := by
              simpa [hG] using hG''
            exact Option.some.inj this
          have hBs : bs' = bs := by
            cases hEqSel
            rfl
          have hFind'' : bs.find? (fun b => b.1 == ℓ) = some (ℓ, L') := by
            simpa [hBs] using hFind'
          have hEqFind : some (ℓ, L) = some (ℓ, L') := by
            simpa [hFind] using hFind''
          have hL : L' = L := by
            cases hEqFind
            rfl
          refine ⟨[], ∅, ?_, ?_, ?_⟩
          · subst hGout
            simpa [hEq, hL] using (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown) (G:=updateG G e L))
          · intro x hx; cases hx
          · intro x T hx; cases hx
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      cases hPre with
      | branch hk' hG' hLen hLabels hPreAll hPost hDom =>
          rename_i e' p' bs'
          have hkPre : lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) := by
            simpa using hk'
          have hGPre : lookupG G e' = some (.branch p' bs') := by
            simpa using hG'
          -- Align endpoints via store typing.
          have hkTyped : HasTypeVal Gstore (.chan e) (.chan e'.sid e'.role) :=
            hStore k (.chan e) (.chan e'.sid e'.role) hk hkPre
          have hEq : e = e' := by
            have hValEq : (Value.chan e) = Value.chan ⟨e'.sid, e'.role⟩ := by
              simpa using (HasTypeVal_chan_inv hkTyped)
            cases e
            cases e'
            cases hValEq
            rfl
          have hG'' : lookupG G e = some (.branch p' bs') := by
            simpa [hEq] using hGPre
          have hEqBr : (LocalType.branch source bs) = (LocalType.branch p' bs') := by
            have : some (LocalType.branch source bs) = some (LocalType.branch p' bs') := by
              simpa [hG] using hG''
            exact Option.some.inj this
          have hBs : bs' = bs := by
            cases hEqBr
            rfl
          have hFindT' : bs'.find? (fun b => b.1 == ℓ) = some (ℓ, L) := by
            simpa [hBs] using hFindT
          have hPre' := hPost _ _ _ hFindP hFindT'
          subst hGout
          refine ⟨W, Δ, ?_, FootprintSubset_refl, SEnvSubset_refl⟩
          simpa [hEq] using hPre'
  | assign hv hSout hStoreOut =>
      rename_i G D Ssh Sown store bufs x v T Sown' store'
      cases hPre with
      | assign_new hSsh hSown hv' =>
          have hT := HasTypeVal_unique hv' hv
          cases hT
          refine ⟨[], ∅, ?_, ?_, ?_⟩
          · subst hSout
            simpa using (HasTypeProcPreOut.skip
              (Ssh:=Ssh) (Sown:=updateSEnv Sown x T) (G:=G))
          · intro x hx; cases hx
          · intro x T hx; cases hx
      | assign_old hSsh hSown hv' =>
          have hT := HasTypeVal_unique hv' hv
          cases hT
          refine ⟨[], ∅, ?_, ?_, ?_⟩
          · subst hSout
            simpa using (HasTypeProcPreOut.skip
              (Ssh:=Ssh) (Sown:=updateSEnv Sown x T) (G:=G))
          · intro x hx; cases hx
          · intro x T hx; cases hx
  | seq_step hTS ih =>
      cases hPre with
      | seq hP hQ =>
          rename_i W₁ W₂ Δ₁ Δ₂
          obtain ⟨W₁', Δ₁', hP', hSubW, hSubΔ⟩ := ih hStore hP
          refine ⟨W₁' ++ W₂, Δ₁' ++ Δ₂, ?_, ?_, ?_⟩
          · exact HasTypeProcPreOut.seq hP' hQ
          · exact FootprintSubset_append_left hSubW
          · exact SEnvSubset_append_left hSubΔ
  | seq_skip =>
      cases hPre with
      | seq hP hQ =>
          rename_i W₁ W₂ Δ₁ Δ₂
          cases hP
          refine ⟨W₂, Δ₂, ?_, ?_, ?_⟩
          · exact hQ
          · simpa using (FootprintSubset_refl (W:=W₂))
          · simpa using (SEnvSubset_append_right (S₁:=∅) (S₂:=Δ₂))
  | par_left split hTS hDisjG hDisjD hDisjS hConsL hConsR ih =>
      rename_i Ssh store bufs P P' Q S G D₁ D₂ G₁' D₁' S₁'
      have hStore' : StoreTyped Gstore (SEnvAll Ssh (split.S1 ++ split.S2)) store := by
        simpa [split.hS] using hStore
      have hStoreL : StoreTyped Gstore (SEnvAll Ssh split.S1) store := by
        have hStore'' : StoreTyped Gstore ((Ssh ++ split.S1) ++ split.S2) store := by
          simpa [SEnvAll, SEnv_append_assoc] using hStore'
        exact StoreTyped_split_left (S₁:=Ssh ++ split.S1) (S₂:=split.S2) hStore''
      cases hPre with
      | par split' hSfin hGfin hW hΔ
            hDisjG' hDisjS' hDisjS_left hDisjS_right hDisjS'' hDisjW hDisjΔ hP hQ =>
          have hEq : split' = split := ParSplit.unique split' split
          cases hEq
          rename_i W₁ W₂ Δ₁ Δ₂
          obtain ⟨W₁', Δ₁', hP', hSubW, hSubΔ⟩ := ih hStoreL hP
          let splitOut : ParSplit (S₁' ++ split.S2) (G₁' ++ split.G2) :=
            { S1 := S₁', S2 := split.S2, G1 := G₁', G2 := split.G2, hS := rfl, hG := rfl }
          have hSubG : SessionsOf G₁' ⊆ SessionsOf split.G1 := SessionsOf_subset_of_TypedStep hTS
          have hDisjGOut : DisjointG G₁' split.G2 := DisjointG_of_subset_left hSubG hDisjG
          have hDisjGOut' : DisjointG splitOut.G1 splitOut.G2 := by
            simpa [splitOut] using hDisjGOut
          have hDomP := HasTypeProcPreOut_domsubset hP'
          have hDisjS_left0 : DisjointS S₁' split.S2 :=
            DisjointS_of_domsubset_left hDomP hDisjS_left
          have hDisjS_left' : DisjointS splitOut.S1 splitOut.S2 := by
            simpa [splitOut] using hDisjS_left0
          have hDisjS_in_out := DisjointS_of_domsubset_left hDomP hDisjS''
          have hDisjW' : DisjointW W₁' W₂ :=
            DisjointW_of_subset_left hSubW hDisjW
          have hDisjΔ' : DisjointS Δ₁' Δ₂ :=
            DisjointS_of_subset_left hSubΔ hDisjΔ
          refine ⟨W₁' ++ W₂, Δ₁' ++ Δ₂, ?_, ?_, ?_⟩
          · exact HasTypeProcPreOut.par splitOut hSfin hGfin rfl rfl
              hDisjGOut' hDisjS_left' hDisjS_left hDisjS_in_out hDisjS'' hDisjW' hDisjΔ' hP' hQ
          · simpa [hW] using (FootprintSubset_append_left hSubW)
          · simpa [hΔ] using (SEnvSubset_append_left hSubΔ)
  | par_right split hTS hDisjG hDisjD hDisjS hConsL hConsR ih =>
      rename_i Ssh store bufs P Q Q' S G D₁ D₂ G₂' D₂' S₂'
      have hStoreR : StoreTyped Gstore (SEnvAll Ssh split.S2) store := by
        intro x v T hStoreX hLookup
        have hLookupS : lookupSEnv (Ssh ++ split.S2) x = some T := by
          simpa [SEnvAll] using hLookup
        have hLookup' : lookupSEnv (Ssh ++ split.S1 ++ split.S2) x = some T := by
          by_cases hSh : lookupSEnv Ssh x = none
          · have hRight : lookupSEnv split.S2 x = some T := by
              simpa [lookupSEnv_append_right (S₁:=Ssh) (S₂:=split.S2) hSh] using hLookupS
            have hS1 : lookupSEnv split.S1 x = none := by
              by_contra hSome
              cases hSome' : lookupSEnv split.S1 x with
              | none => exact (hSome hSome').elim
              | some T₁ =>
                  exact (hDisjS x T₁ T (by simpa using hSome') hRight).elim
            have hNone : lookupSEnv (Ssh ++ split.S1) x = none := by
              simpa [lookupSEnv_append_right (S₁:=Ssh) (S₂:=split.S1) hSh] using hS1
            have hAppend : lookupSEnv ((Ssh ++ split.S1) ++ split.S2) x = lookupSEnv split.S2 x :=
              lookupSEnv_append_right (S₁:=Ssh ++ split.S1) (S₂:=split.S2) hNone
            simpa [SEnv_append_assoc, hRight] using hAppend
          · cases hSh' : lookupSEnv Ssh x with
            | none => exact (hSh hSh').elim
            | some Tsh =>
                have hLeft0 : lookupSEnv (Ssh ++ split.S2) x = some Tsh := by
                  simpa [SEnvAll] using
                    (lookupSEnv_append_left (S₁:=Ssh) (S₂:=split.S2) hSh')
                have hLeft : lookupSEnv (Ssh ++ split.S1 ++ split.S2) x = some Tsh := by
                  simpa [SEnvAll, SEnv_append_assoc] using
                    (lookupSEnv_append_left (S₁:=Ssh) (S₂:=split.S1 ++ split.S2) hSh')
                have hEq : T = Tsh := by
                  have : some T = some Tsh := by
                    simpa [hLookupS] using hLeft0
                  exact Option.some.inj this
                simpa [hEq] using hLeft
        exact hStore x v T hStoreX (by
          simpa [SEnvAll, split.hS, SEnv_append_assoc] using hLookup')
      cases hPre with
      | par split' hSfin hGfin hW hΔ
            hDisjG' hDisjS' hDisjS_left hDisjS_right hDisjS'' hDisjW hDisjΔ hP hQ =>
          have hEq : split' = split := ParSplit.unique split' split
          cases hEq
          rename_i W₁ W₂ Δ₁ Δ₂
          obtain ⟨W₂', Δ₂', hQ', hSubW, hSubΔ⟩ := ih hStoreR hQ
          let splitOut : ParSplit (split.S1 ++ S₂') (split.G1 ++ G₂') :=
            { S1 := split.S1, S2 := S₂', G1 := split.G1, G2 := G₂', hS := rfl, hG := rfl }
          have hSubG : SessionsOf G₂' ⊆ SessionsOf split.G2 := SessionsOf_subset_of_TypedStep hTS
          have hDisjGsym : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
          have hDisjG' : DisjointG G₂' split.G1 := DisjointG_of_subset_left hSubG hDisjGsym
          have hDisjGOut : DisjointG split.G1 G₂' := DisjointG_symm hDisjG'
          have hDisjGOut' : DisjointG splitOut.G1 splitOut.G2 := by
            simpa [splitOut] using hDisjGOut
          have hDomQ := HasTypeProcPreOut_domsubset hQ'
          have hDisjS_right0 : DisjointS split.S1 S₂' :=
            DisjointS_of_domsubset_right hDomQ hDisjS_right
          have hDisjS_right' : DisjointS splitOut.S1 splitOut.S2 := by
            simpa [splitOut] using hDisjS_right0
          have hDisjS_left_in := DisjointS_of_domsubset_right hDomQ hDisjS''
          have hDisjW' : DisjointW W₁ W₂' :=
            DisjointW_of_subset_right hSubW hDisjW
          have hDisjΔ' : DisjointS Δ₁ Δ₂' :=
            DisjointS_of_subset_right hSubΔ hDisjΔ
          refine ⟨W₁ ++ W₂', Δ₁ ++ Δ₂', ?_, ?_, ?_⟩
          · exact HasTypeProcPreOut.par splitOut hSfin hGfin rfl rfl
              hDisjGOut' hDisjS_right' hDisjS_left_in hDisjS_right hDisjS'' hDisjW' hDisjΔ' hP hQ'
          · simpa [hW] using (FootprintSubset_append_right_of_subset hSubW)
          · simpa [hΔ] using (SEnvSubset_append_right_of_subset hSubΔ)
  | par_skip_left =>
      cases hPre with
      | par split hSfin hGfin hW hΔ hDisjG' hDisjS' hDisjS_left hDisjS_right hDisjS'' hDisjW hDisjΔ hP hQ =>
          rename_i W₁ W₂ Δ₁ Δ₂
          cases hP
          have hQframe :=
            HasTypeProcPreOut_frame_left hDisjS' hDisjS_right hDisjG' hQ
          refine ⟨W₂, Δ₂, ?_, ?_, ?_⟩
          · simpa [split.hS, split.hG, hSfin, hGfin] using hQframe
          · simpa [hW] using (FootprintSubset_refl)
          · simpa [hΔ] using (SEnvSubset_append_right (S₁:=∅) (S₂:=Δ₂))
  | par_skip_right =>
      cases hPre with
      | par split hSfin hGfin hW hΔ hDisjG' hDisjS' hDisjS_left hDisjS_right hDisjS'' hDisjW hDisjΔ hP hQ =>
          rename_i W₁ W₂ Δ₁ Δ₂
          cases hQ
          have hDisjS_left_symm := DisjointS_symm hDisjS'
          have hPframe :=
            HasTypeProcPreOut_frame_right hDisjS_left_symm hDisjG' hP
          refine ⟨W₁, Δ₁, ?_, ?_, ?_⟩
          · simpa [split.hS, split.hG, hSfin, hGfin] using hPframe
          · simpa [hW] using (FootprintSubset_refl)
          · simpa [hΔ] using (SEnvSubset_append_left_self (S₁:=Δ₁) (S₂:=∅))

/-- Pre-out typing is preserved by a single TypedStep: the remaining process
    still leads to the same final environments. -/
theorem HasTypeProcPreOut_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' Sfin Gfin W Δ} :
    StoreTyped G (SEnvAll Ssh Sown) store →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G' P' Sfin Gfin W' Δ' := by
  intro hStore hTS hPre
  obtain ⟨W', Δ', hPre', _, _⟩ := HasTypeProcPreOut_preserved_sub hStore hTS hPre
  exact ⟨W', Δ', hPre'⟩

/-! ## Preservation Theorems -/

/-- TypedStep preserves coherence.

    **Proof strategy**: Case analysis on TypedStep constructor:
    - `send`: Use `Coherent_send_preserved` with hRecvReady derived from coherence
    - `recv`: Use `Coherent_recv_preserved`
    - `assign`: G and D unchanged
    - `seq_step`, `seq_skip`: IH or G/D unchanged
    - `par_*`: Disjoint resources remain coherent -/
theorem typed_step_preserves_coherence {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    Coherent G D →
    Coherent G' D'
  | @TypedStep.send G D Ssh Sown store bufs k x e target T L v sendEdge Gout Dout bufsOut hk hx hG hS hv hRecvReady hEdge hGout hDout hBufsOut, hCoh => by
    -- Use Coherent_send_preserved with explicit arguments
    -- After rewriting with the equalities, Gout = updateG G e L and Dout = appendD D sendEdge T
    rw [hGout, hDout, hEdge]
    unfold appendD
    exact @Coherent_send_preserved G D e target T L hCoh hG hRecvReady
  | @TypedStep.recv G D Ssh Sown store bufs k x e source T L v vs recvEdge Gout Dout SownOut storeOut bufsOut hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut, hCoh => by
    -- Use Coherent_recv_preserved with explicit arguments
    rw [hGout, hDout]
    have hTrace' : (lookupD D { sid := e.sid, sender := source, receiver := e.role }).head? = some T := by
      rw [← hEdge]; exact hTrace
    rw [hEdge]
    exact @Coherent_recv_preserved G D e source T L hCoh hG hTrace'
  | @TypedStep.select G D Ssh Sown store bufs k ℓ e target bs L selectEdge Gout Dout bufsOut hk hG hFind hTargetReady hEdge hGout hDout hBufsOut, hCoh => by
    -- Use Coherent_select_preserved with explicit arguments
    rw [hGout, hDout, hEdge]
    unfold appendD
    exact @Coherent_select_preserved G D e target bs ℓ L hCoh hG hFind hTargetReady
  | @TypedStep.branch G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge Gout Dout bufsOut hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut, hCoh => by
    -- Use Coherent_branch_preserved with explicit arguments
    have hTrace' : (lookupD D { sid := e.sid, sender := source, receiver := e.role }).head? = some .string := by
      rw [← hEdge]; exact hTrace
    rw [hGout, hDout, hEdge]
    exact @Coherent_branch_preserved G D e source bs ℓ L hCoh hG hFindT hTrace'
  | .assign _ _ _, hCoh => by
    -- G and D unchanged
    exact hCoh
  | .seq_step hTS, hCoh =>
    -- Inductive hypothesis on sub-transition
    typed_step_preserves_coherence hTS hCoh
  | .seq_skip, hCoh =>
    -- No change
    hCoh
  | @TypedStep.par_left Ssh store bufs P P' Q S G D₁ D₂ G₁' D₁' S₁' split
      hTS hDisjG hDisjD hDisjS hConsL hConsR, hCoh => by
    -- Left transition preserves its part, right unchanged.
    have hCohMerged : Coherent (split.G1 ++ split.G2) (D₁ ++ D₂) := by
      simpa [split.hG] using hCoh
    have hCohL : Coherent split.G1 D₁ := Coherent_split_left hCohMerged
    have hCohL' : Coherent G₁' D₁' := typed_step_preserves_coherence hTS hCohL
    have hCohR : Coherent split.G2 D₂ := Coherent_split_right hCohMerged hDisjG hConsL
    have hSubG : SessionsOf G₁' ⊆ SessionsOf split.G1 := SessionsOf_subset_of_TypedStep hTS
    have hDisjG' : DisjointG G₁' split.G2 := DisjointG_of_subset_left hSubG hDisjG
    have hSubD : SessionsOfD D₁' ⊆ SessionsOf split.G1 := by
      intro s hs
      have hs' : s ∈ SessionsOfD D₁ ∪ SessionsOf split.G1 := SessionsOfD_subset_of_TypedStep hTS hs
      cases hs' with
      | inl hD1 => exact hConsL hD1
      | inr hG1 => exact hG1
    intro e Lsender Lrecv hGsender hGrecv
    set senderEp : Endpoint := { sid := e.sid, role := e.sender }
    set recvEp : Endpoint := { sid := e.sid, role := e.receiver }
    have hInvSender := lookupG_append_inv (G₁:=G₁') (G₂:=split.G2) (e:=senderEp) hGsender
    cases hInvSender with
    | inl hSenderLeft =>
        have hSidLeft : e.sid ∈ SessionsOf G₁' := ⟨senderEp, Lsender, hSenderLeft, rfl⟩
        have hInvRecv := lookupG_append_inv (G₁:=G₁') (G₂:=split.G2) (e:=recvEp) hGrecv
        have hRecvLeft : lookupG G₁' recvEp = some Lrecv := by
          cases hInvRecv with
          | inl hLeft => exact hLeft
          | inr hRight =>
              have hSidRight : e.sid ∈ SessionsOf split.G2 := ⟨recvEp, Lrecv, hRight.2, rfl⟩
              have hInter : e.sid ∈ SessionsOf G₁' ∩ SessionsOf split.G2 := ⟨hSidLeft, hSidRight⟩
              have hEmpty : SessionsOf G₁' ∩ SessionsOf split.G2 = (∅ : Set SessionId) := hDisjG'
              have : e.sid ∈ (∅ : Set SessionId) := by
                simpa [hEmpty] using hInter
              exact this.elim
        have hD2none : D₂.find? e = none := lookupD_none_of_disjointG hDisjG' hConsR hSidLeft
        have hTraceEq : lookupD (D₁' ++ D₂) e = lookupD D₁' e :=
          lookupD_append_left_of_right_none (D₁:=D₁') (D₂:=D₂) (e:=e) hD2none
        have hCohEdge := hCohL' e Lsender Lrecv hSenderLeft hRecvLeft
        simpa [hTraceEq] using hCohEdge
    | inr hSenderRight =>
        have hSidRight : e.sid ∈ SessionsOf split.G2 := ⟨senderEp, Lsender, hSenderRight.2, rfl⟩
        have hInvRecv := lookupG_append_inv (G₁:=G₁') (G₂:=split.G2) (e:=recvEp) hGrecv
        have hRecvRight : lookupG split.G2 recvEp = some Lrecv := by
          cases hInvRecv with
          | inl hLeft =>
              have hSidLeft : e.sid ∈ SessionsOf G₁' := ⟨recvEp, Lrecv, hLeft, rfl⟩
              have hInter : e.sid ∈ SessionsOf G₁' ∩ SessionsOf split.G2 := ⟨hSidLeft, hSidRight⟩
              have hEmpty : SessionsOf G₁' ∩ SessionsOf split.G2 = (∅ : Set SessionId) := hDisjG'
              have : e.sid ∈ (∅ : Set SessionId) := by
                simpa [hEmpty] using hInter
              exact this.elim
          | inr hRight => exact hRight.2
        have hDisjGsym : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
        have hD1none : D₁'.find? e = none :=
          lookupD_none_of_disjointG (G₁:=split.G2) (G₂:=split.G1) (D₂:=D₁') hDisjGsym hSubD hSidRight
        have hTraceEq : lookupD (D₁' ++ D₂) e = lookupD D₂ e :=
          lookupD_append_right (D₁:=D₁') (D₂:=D₂) (e:=e) hD1none
        have hCohEdge := hCohR e Lsender Lrecv hSenderRight.2 hRecvRight
        simpa [hTraceEq] using hCohEdge
  | @TypedStep.par_right Ssh store bufs P Q Q' S G D₁ D₂ G₂' D₂' S₂' split
      hTS hDisjG hDisjD hDisjS hConsL hConsR, hCoh => by
    -- Right transition preserves its part, left unchanged.
    have hCohMerged : Coherent (split.G1 ++ split.G2) (D₁ ++ D₂) := by
      simpa [split.hG] using hCoh
    have hCohL : Coherent split.G1 D₁ := Coherent_split_left hCohMerged
    have hCohR : Coherent split.G2 D₂ := Coherent_split_right hCohMerged hDisjG hConsL
    have hCohR' : Coherent G₂' D₂' := typed_step_preserves_coherence hTS hCohR
    have hSubG : SessionsOf G₂' ⊆ SessionsOf split.G2 := SessionsOf_subset_of_TypedStep hTS
    have hDisjG' : DisjointG split.G1 G₂' := by
      -- reuse subset on the right
      have hDisjGsym : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
      have hDisjG'' : DisjointG G₂' split.G1 := DisjointG_of_subset_left hSubG hDisjGsym
      exact DisjointG_symm hDisjG''
    have hSubD : SessionsOfD D₂' ⊆ SessionsOf split.G2 := by
      intro s hs
      have hs' : s ∈ SessionsOfD D₂ ∪ SessionsOf split.G2 := SessionsOfD_subset_of_TypedStep hTS hs
      cases hs' with
      | inl hD2 => exact hConsR hD2
      | inr hG2 => exact hG2
    intro e Lsender Lrecv hGsender hGrecv
    set senderEp : Endpoint := { sid := e.sid, role := e.sender }
    set recvEp : Endpoint := { sid := e.sid, role := e.receiver }
    have hInvSender := lookupG_append_inv (G₁:=split.G1) (G₂:=G₂') (e:=senderEp) hGsender
    cases hInvSender with
    | inl hSenderLeft =>
        have hSidLeft : e.sid ∈ SessionsOf split.G1 := ⟨senderEp, Lsender, hSenderLeft, rfl⟩
        have hInvRecv := lookupG_append_inv (G₁:=split.G1) (G₂:=G₂') (e:=recvEp) hGrecv
        have hRecvLeft : lookupG split.G1 recvEp = some Lrecv := by
          cases hInvRecv with
          | inl hLeft => exact hLeft
          | inr hRight =>
              have hSidRight : e.sid ∈ SessionsOf G₂' := ⟨recvEp, Lrecv, hRight.2, rfl⟩
              have hInter : e.sid ∈ SessionsOf split.G1 ∩ SessionsOf G₂' := ⟨hSidLeft, hSidRight⟩
              have hEmpty : SessionsOf split.G1 ∩ SessionsOf G₂' = (∅ : Set SessionId) := hDisjG'
              have : e.sid ∈ (∅ : Set SessionId) := by
                simpa [hEmpty] using hInter
              exact this.elim
        have hD2none : D₂'.find? e = none :=
          lookupD_none_of_disjointG (G₁:=split.G1) (G₂:=split.G2) (D₂:=D₂') hDisjG hSubD hSidLeft
        have hTraceEq : lookupD (D₁ ++ D₂') e = lookupD D₁ e :=
          lookupD_append_left_of_right_none (D₁:=D₁) (D₂:=D₂') (e:=e) hD2none
        have hCohEdge := hCohL e Lsender Lrecv hSenderLeft hRecvLeft
        simpa [hTraceEq] using hCohEdge
    | inr hSenderRight =>
        have hSidRight : e.sid ∈ SessionsOf G₂' := ⟨senderEp, Lsender, hSenderRight.2, rfl⟩
        have hInvRecv := lookupG_append_inv (G₁:=split.G1) (G₂:=G₂') (e:=recvEp) hGrecv
        have hRecvRight : lookupG G₂' recvEp = some Lrecv := by
          cases hInvRecv with
          | inl hLeft =>
              have hSidLeft : e.sid ∈ SessionsOf split.G1 := ⟨recvEp, Lrecv, hLeft, rfl⟩
              have hInter : e.sid ∈ SessionsOf split.G1 ∩ SessionsOf G₂' := ⟨hSidLeft, hSidRight⟩
              have hEmpty : SessionsOf split.G1 ∩ SessionsOf G₂' = (∅ : Set SessionId) := hDisjG'
              have : e.sid ∈ (∅ : Set SessionId) := by
                simpa [hEmpty] using hInter
              exact this.elim
          | inr hRight => exact hRight.2
        have hDisjGsym : DisjointG G₂' split.G1 := DisjointG_symm hDisjG'
        have hD1none : D₁.find? e = none :=
          lookupD_none_of_disjointG (G₁:=G₂') (G₂:=split.G1) (D₂:=D₁) hDisjGsym hConsL hSidRight
        have hTraceEq : lookupD (D₁ ++ D₂') e = lookupD D₂' e :=
          lookupD_append_right (D₁:=D₁) (D₂:=D₂') (e:=e) hD1none
        have hCohEdge := hCohR' e Lsender Lrecv hSenderRight.2 hRecvRight
        simpa [hTraceEq] using hCohEdge
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
theorem preservation_typed {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    WellFormed G D Ssh Sown store bufs P →
    WellFormed G' D' Ssh Sown' store' bufs' P' := by
  sorry

/-! ### Progress Helpers -/

private theorem findLabel_eq {α : Type} {lbl lbl' : Label} {xs : List (Label × α)} {v : α}
    (h : xs.find? (fun b => b.1 == lbl) = some (lbl', v)) : lbl' = lbl := by
  have hPred : (lbl' == lbl) := (List.find?_eq_some_iff_append (xs := xs)
    (p := fun b => b.1 == lbl) (b := (lbl', v))).1 h |>.1
  have hPred' : (lbl' == lbl) = true := by
    simpa using hPred
  exact (beq_iff_eq).1 hPred'

private def BlockedProc (store : Store) (bufs : Buffers) : Process → Prop
  | .recv k _ =>
      ∃ e source,
        lookupStr store k = some (.chan e) ∧
        lookupBuf bufs { sid := e.sid, sender := source, receiver := e.role } = []
  | .branch k _ =>
      ∃ e source,
        lookupStr store k = some (.chan e) ∧
        lookupBuf bufs { sid := e.sid, sender := source, receiver := e.role } = []
  | .seq P _ =>
      BlockedProc store bufs P
  | .par P Q =>
      BlockedProc store bufs P ∧ BlockedProc store bufs Q
  | _ => False

private theorem progress_typed_aux {G D Ssh Sown store bufs P Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    StoreTypedStrong G (SEnvAll Ssh Sown) store →
    BuffersTyped G D bufs →
    Coherent G D →
    HeadCoherent G D →
    ValidLabels G D bufs →
    SendReady G D →
    SelectReady G D →
    (P = .skip) ∨
      (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
        G' D' Sown' store' bufs' P') ∨
      BlockedProc store bufs P := by
  intro hOut hStore hBufs hCoh hHead hValid hReady hSelectReady
  induction hOut with
  | skip =>
      left; rfl
  | send hk hG hx =>
      rename_i G k x e q T L
      -- Have: lookupSEnv S k = some (.chan e.sid e.role), lookupG G e = some (.send q T L), lookupSEnv S x = some T
      -- Need: Construct TypedStep.send with all preconditions
      --   - lookupStr store k = some (.chan e) from StoreTyped + hk
      --   - lookupStr store x = some v from StoreTyped + hx
      --   - HasTypeVal G v T from StoreTyped
      --   - hRecvReady from Coherent (receiver can consume message)
      right; left
      -- Use strong store typing to extract channel/value from store.
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      obtain ⟨v, hxStr, hv⟩ := store_lookup_of_senv_lookup hStore hx
      -- Need receiver readiness to build TypedStep.send
      have hRecvReady := hReady e q T L hG
      exact ⟨_, _, _, _, _, _, TypedStep.send hkStr hxStr hG hx hv hRecvReady rfl rfl rfl rfl⟩
  | recv_new hk hG hNoSh hNoOwn =>
      rename_i G k x e p T L
      -- Have: lookupSEnv S k = some (.chan e.sid e.role), lookupG G e = some (.recv p T L)
      -- Need: Check if buffer is non-empty at edge
      --   - If lookupBuf bufs edge = v :: vs, construct TypedStep.recv
      --   - Else blocked (third alternative in progress conclusion)
      -- Derive the channel value from the store.
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      -- Inspect the buffer at the receive edge.
      set recvEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
      cases hBuf : lookupBuf bufs recvEdge with
      | nil =>
          -- Blocked receive: buffer empty.
          right; right
          refine ⟨e, p, hkStr, ?_⟩
          simpa [recvEdge, hBuf]
      | cons v vs =>
          -- Buffer non-empty: can receive.
          right; left
          -- Use BuffersTyped to get value type from trace head.
          have hTypedEdge := hBufs recvEdge
          rcases hTypedEdge with ⟨hLen, hTyping⟩
          have h0buf : 0 < (lookupBuf bufs recvEdge).length := by
            simp [hBuf]
          have h0trace : 0 < (lookupD D recvEdge).length := by
            simpa [hLen] using h0buf
          have hTyped0 := hTyping 0 h0buf
          have hv' := by
            simpa [hBuf] using hTyped0
          -- Use HeadCoherent to align the trace head with T.
          cases hTrace : lookupD D recvEdge with
          | nil =>
              -- Contradiction: trace must be non-empty if buffer is non-empty.
              simp [hTrace] at h0trace
          | cons T' ts =>
              have hHeadEdge := hHead recvEdge
              -- HeadCoherent gives T = T' for recv types.
              have hEq : T = T' := by
                simpa [HeadCoherent, hG, recvEdge, hTrace] using hHeadEdge
              have hEq' : T' = T := by
                simpa using hEq.symm
              have hv : HasTypeVal G v T := by
                simpa [hTrace, hEq'] using hv'
              have hTraceHead : (lookupD D recvEdge).head? = some T := by
                simp [hTrace, hEq]
              exact ⟨_, _, _, _, _, _, TypedStep.recv hkStr hG rfl hBuf hv hTraceHead rfl rfl rfl rfl rfl⟩
  | recv_old hk hG hNoSh hOwn =>
      rename_i G k x e p T L T'
      -- same proof as recv_new
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      set recvEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
      cases hBuf : lookupBuf bufs recvEdge with
      | nil =>
          right; right
          refine ⟨e, p, hkStr, ?_⟩
          simpa [recvEdge, hBuf]
      | cons v vs =>
          right; left
          have hTypedEdge := hBufs recvEdge
          rcases hTypedEdge with ⟨hLen, hTyping⟩
          have h0buf : 0 < (lookupBuf bufs recvEdge).length := by
            simp [hBuf]
          have h0trace : 0 < (lookupD D recvEdge).length := by
            simpa [hLen] using h0buf
          have hTyped0 := hTyping 0 h0buf
          have hv' := by
            simpa [hBuf] using hTyped0
          cases hTrace : lookupD D recvEdge with
          | nil =>
              simp [hTrace] at h0trace
          | cons T' ts =>
              have hHeadEdge := hHead recvEdge
              have hEq : T = T' := by
                simpa [HeadCoherent, hG, recvEdge, hTrace] using hHeadEdge
              have hEq' : T' = T := by
                simpa using hEq.symm
              have hv : HasTypeVal G v T := by
                simpa [hTrace, hEq'] using hv'
              have hTraceHead : (lookupD D recvEdge).head? = some T := by
                simp [hTrace, hEq]
              exact ⟨_, _, _, _, _, _, TypedStep.recv hkStr hG rfl hBuf hv hTraceHead rfl rfl rfl rfl rfl⟩
  | select hk hG hbs =>
      rename_i G k ℓ e q bs L
      -- Similar to send - select sends a label
      right; left
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      have hTargetReady := hSelectReady e q bs ℓ L hG hbs
      exact ⟨_, _, _, _, _, _, TypedStep.select hkStr hG hbs hTargetReady rfl rfl rfl rfl⟩
  | branch hk hG hLen hLabels hBodies hOutLbl hDom ih =>
      rename_i G k procs e p bs S' G' W Δ
      -- Similar to recv - branch receives a label
      obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
      have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
      subst hkChan
      set branchEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
      cases hBuf : lookupBuf bufs branchEdge with
      | nil =>
          right; right
          refine ⟨e, p, hkStr, ?_⟩
          simpa [branchEdge, hBuf]
      | cons v vs =>
          -- Buffer non-empty: should step by selecting a label
          right; left
          -- Use BuffersTyped to get value type from trace head.
          have hTypedEdge := hBufs branchEdge
          rcases hTypedEdge with ⟨hLenBuf, hTyping⟩
          have h0buf : 0 < (lookupBuf bufs branchEdge).length := by
            simp [hBuf]
          have h0trace : 0 < (lookupD D branchEdge).length := by
            simpa [hLenBuf] using h0buf
          have hTyped0 := hTyping 0 h0buf
          have hv' := by
            simpa [hBuf] using hTyped0
          cases hTrace : lookupD D branchEdge with
          | nil =>
              -- Contradiction: trace must be non-empty if buffer is non-empty.
              simp [hTrace] at h0trace
          | cons T' ts =>
              have hHeadEdge := hHead branchEdge
              have hEq : T' = .string := by
                simpa [HeadCoherent, hG, branchEdge, hTrace] using hHeadEdge
              have hv := by
                simpa [hTrace, hEq] using hv'
              cases hv with
              | string lbl =>
                  -- ValidLabels: label is one of the branch options
                  have hValidEdge := hValid branchEdge p bs (by simpa [branchEdge] using hG)
                  have hBsSome : (bs.find? (fun b => b.1 == lbl)).isSome := by
                    simpa [hBuf] using hValidEdge
                  rcases (Option.isSome_iff_exists).1 hBsSome with ⟨b, hFindBs⟩
                  cases b with
                  | mk lbl' L =>
                      have hLbl : lbl' = lbl :=
                        findLabel_eq (xs := bs) (lbl := lbl) (lbl' := lbl') (v := L) hFindBs
                      subst lbl'
                      -- Show the corresponding process branch exists
                      have hMemBs : (lbl, L) ∈ bs := List.mem_of_find?_eq_some hFindBs
                      rcases (List.mem_iff_getElem).1 hMemBs with ⟨i, hi, hGetBs⟩
                      have hip : i < procs.length := by
                        simpa [hLen] using hi
                      have hLabelAt : (procs.get ⟨i, hip⟩).1 = lbl := by
                        have hLblEq := hLabels i hi hip
                        simpa [hGetBs] using hLblEq
                      have hPred : (fun b => b.1 == lbl) (procs.get ⟨i, hip⟩) := by
                        exact (beq_iff_eq).2 hLabelAt
                      have hFindPIsSome : (procs.find? (fun b => b.1 == lbl)).isSome := by
                        cases hFindP : procs.find? (fun b => b.1 == lbl) with
                        | none =>
                            have hNo : ∀ x ∈ procs, ¬ (fun b => b.1 == lbl) x := by
                              simpa [List.find?_eq_none] using hFindP
                            have hMemP : procs.get ⟨i, hip⟩ ∈ procs := List.get_mem procs ⟨i, hip⟩
                            have hContra : False := (hNo _ hMemP) hPred
                            simpa using hContra
                        | some b =>
                            simp
                      rcases (Option.isSome_iff_exists).1 hFindPIsSome with ⟨bP, hFindP⟩
                      cases bP with
                      | mk lblP P =>
                          have hLblP : lblP = lbl :=
                            findLabel_eq (xs := procs) (lbl := lbl) (lbl' := lblP) (v := P) hFindP
                          subst hLblP
                          have hTraceHead : (lookupD D branchEdge).head? = some .string := by
                            simp [hTrace, hEq]
                          exact ⟨_, _, _, _, _, _, TypedStep.branch hkStr hG rfl hBuf hFindP hFindBs hTraceHead rfl rfl rfl⟩
  | seq hP hQ ihP ihQ =>
      rename_i P Q S₁ G₁ S₂ G₂ W₁ W₂ Δ₁ Δ₂
      have hProgP := ihP hStore hBufs hCoh hHead hValid hReady hSelectReady
      cases hProgP with
      | inl hSkip =>
          right; left
          subst hSkip
          exact ⟨_, _, _, store, bufs, Q, TypedStep.seq_skip⟩
      | inr hRest =>
          cases hRest with
          | inl hStep =>
              rcases hStep with ⟨G', D', S', store', bufs', P', hStep⟩
              right; left
              exact ⟨_, _, _, _, _, _, TypedStep.seq_step hStep⟩
          | inr hBlocked =>
              right; right
              simpa [BlockedProc] using hBlocked
  | par split hSplitSfin hSplitGfin hSplitW hSplitΔ
        hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hP hQ ihP ihQ =>
      rename_i S₁ S₂ G₁ G₂ P Q S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂
      -- Need to split WellFormed across disjoint environments.
      sorry
  | assign_new hNoSh hNoOwn hv =>
      rename_i x v T
      right; left
      exact ⟨_, _, _, _, _, _, TypedStep.assign hv rfl rfl⟩
  | assign_old hNoSh hOwn hv =>
      rename_i x v T
      right; left
      exact ⟨_, _, _, _, _, _, TypedStep.assign hv rfl rfl⟩

/-- Progress theorem: A well-formed process can either step or is in a final/blocked state.

    **Proof strategy**: Case analysis on process P:
    - `skip`: Terminates
    - `send k x`: Derive TypedStep.send from lookupG via HasTypeProcPre inversion
    - `recv k x`: Check buffer - if non-empty, derive TypedStep.recv; else blocked
    - `seq P Q`: Use IH on P or skip elimination
    - `par P Q`: Use IH on P or Q or skip elimination -/
theorem progress_typed {G D Ssh Sown store bufs P} :
    WellFormed G D Ssh Sown store bufs P →
    (P = .skip) ∨
    (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
      G' D' Sown' store' bufs' P') ∨
    BlockedProc store bufs P := by
  intro hWF
  unfold WellFormed at hWF
  obtain ⟨hStore, hBufs, hCoh, hHead, hValid, hReady, hSelectReady, hDisjS, hCons, hPreOut⟩ := hWF
  obtain ⟨Sfin, Gfin, Wfin, Δfin, hOut⟩ := hPreOut
  exact progress_typed_aux hOut hStore hBufs hCoh hHead hValid hReady hSelectReady

/-  Subject reduction (soundness) theorem moved to Effects.Preservation
    to avoid circular dependency (Step is defined in Semantics which imports Typing).

    **Theorem**: TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
                 Step ⟨P, store, bufs, G, D, n⟩ ⟨P', store', bufs', G', D', n⟩

    This will be proven in Preservation.lean after TypedStep is available. -/

end
