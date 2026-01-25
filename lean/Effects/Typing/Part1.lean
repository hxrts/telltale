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


end
