import Protocol.Process
import Protocol.Coherence

/-! # MPST Process Typing: Core

This module defines the core typing judgment for MPST processes. -/

/-
The Problem. We need a typing judgment that ensures processes respect their
local types, handle linear resources correctly, and compose safely in parallel.

Solution Structure. We define:
1. `HasTypeProcN`: process typing judgment with session bound
2. `WTConfigN`: well-typed configuration judgment
3. Typing rules for each process constructor (skip, seq, par, send, recv, etc.)
4. Linear context management for channel resources
-/

/-! ## Key Judgments

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
open Batteries

section

/-! ## Process Typing Judgment -/

/-! ## Disjointness + Ownership/Footprints -/

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
  -- Note: the full environment is ordered as left ++ right.
  hS : S = S1 ++ S2
  hG : G = G1 ++ G2

theorem ParSplit.unique {S : SEnv} {G : GEnv} (s₁ s₂ : ParSplit S G)
    (hSlen : s₁.S1.length = s₂.S1.length)
    (hGlen : s₁.G1.length = s₂.G1.length) : s₁ = s₂ := by
  have hSS : s₁.S1 ++ s₁.S2 = s₂.S1 ++ s₂.S2 := by
    rw [← s₁.hS, ← s₂.hS]
  have hGG : s₁.G1 ++ s₁.G2 = s₂.G1 ++ s₂.G2 := by
    rw [← s₁.hG, ← s₂.hG]
  have hS1 := List.append_inj_left hSS hSlen
  have hS2 := List.append_inj_right hSS hSlen
  have hG1 := List.append_inj_left hGG hGlen
  have hG2 := List.append_inj_right hGG hGlen
  cases s₁; cases s₂; simp_all

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

private instance : Std.TransCmp (α := Var) compare := inferInstance

def insertPairS (acc : SEnv) (p : Var × ValType) : SEnv :=
  updateSEnv acc p.1 p.2

theorem lookupSEnv_foldl_insert_preserve
    (L : List (Var × ValType)) (env : SEnv) (x : Var) (T : ValType)
    (hlookup : lookupSEnv env x = some T)
    (hSame : ∀ T', (x, T') ∈ L → T' = T) :
    lookupSEnv (L.foldl insertPairS env) x = some T := by
  induction L generalizing env with
  | nil =>
      simpa using hlookup
  | cons p L ih =>
      cases p with
      | mk x' T' =>
          have hSame' : ∀ T'', (x, T'') ∈ L → T'' = T := by
            intro T'' hmem
            exact hSame T'' (List.mem_cons_of_mem _ hmem)
          by_cases hEq : x' = x
          · cases hEq
            have hT' : T' = T := hSame T' (by simp)
            cases hT'
            have hlookup' : lookupSEnv (updateSEnv env x T) x = some T := by
              simpa using (lookupSEnv_update_eq (env:=env) (x:=x) (T:=T))
            simpa [List.foldl, insertPairS] using
              (ih (env := updateSEnv env x T) (hlookup := hlookup') (hSame := hSame'))
          · have hlookup' : lookupSEnv (updateSEnv env x' T') x = some T := by
              have h := lookupSEnv_update_neq (env:=env) (x:=x') (y:=x) (T:=T') hEq
              simpa [hlookup] using h
            simpa [List.foldl, insertPairS] using
              (ih (env := updateSEnv env x' T') (hlookup := hlookup') (hSame := hSame'))

theorem lookupSEnv_foldl_insert_of_mem
    (L : List (Var × ValType)) (env : SEnv) (x : Var) (T : ValType)
    (hmem : (x, T) ∈ L)
    (hSame : ∀ T', (x, T') ∈ L → T' = T) :
    lookupSEnv (L.foldl insertPairS env) x = some T := by
  induction L generalizing env with
  | nil =>
      cases hmem
  | cons p L ih =>
      cases p with
      | mk x' T' =>
          have hSame' : ∀ T'', (x, T'') ∈ L → T'' = T := by
            intro T'' hmem'
            exact hSame T'' (List.mem_cons_of_mem _ hmem')
          cases hmem with
          | head _ =>
              have hlookup' : lookupSEnv (updateSEnv env x T) x = some T := by
                simpa using (lookupSEnv_update_eq (env:=env) (x:=x) (T:=T))
              simpa [List.foldl, insertPairS] using
                (lookupSEnv_foldl_insert_preserve (L:=L) (env:=updateSEnv env x T)
                  (x:=x) (T:=T) hlookup' hSame')
          | tail _ htail =>
              simpa [List.foldl, insertPairS] using
                (ih (env := updateSEnv env x' T') (hmem := htail) (hSame := hSame'))

theorem lookupSEnv_foldl_insert_notin
    (L : List (Var × ValType)) (env : SEnv) (x : Var) (v : Option ValType)
    (hlookup : lookupSEnv env x = v)
    (hNot : ∀ T, (x, T) ∈ L → False) :
    lookupSEnv (L.foldl insertPairS env) x = v := by
  induction L generalizing env with
  | nil =>
      simpa using hlookup
  | cons p L ih =>
      cases p with
      | mk x' T' =>
          have hNot' : ∀ T, (x, T) ∈ L → False := by
            intro T hmem
            exact hNot T (List.mem_cons_of_mem _ hmem)
          have hneq : x' ≠ x := by
            intro hEq
            exact hNot T' (by simpa [hEq])
          have hlookup' : lookupSEnv (updateSEnv env x' T') x = v := by
            have h := lookupSEnv_update_neq (env:=env) (x:=x') (y:=x) (T:=T') hneq
            simpa [hlookup] using h
          simpa [List.foldl, insertPairS] using
            (ih (env := updateSEnv env x' T') (hlookup := hlookup') (hNot := hNot'))

theorem lookupSEnv_append_left {S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    lookupSEnv S₁ x = some T →
    lookupSEnv (S₁ ++ S₂) x = some T := by
  intro hlookup
  induction S₁ with
  | nil =>
      cases hlookup
  | cons hd tl ih =>
      by_cases hEq : x == hd.1
      · have hT : T = hd.2 := by
          have : some hd.2 = some T := by
            simpa [lookupSEnv, List.lookup, hEq] using hlookup
          exact Option.some.inj this.symm
        subst hT
        simp [lookupSEnv, List.lookup, hEq]
      · have hTail : lookupSEnv tl x = some T := by
          simpa [lookupSEnv, List.lookup, hEq] using hlookup
        have hTail' := ih hTail
        simpa [lookupSEnv, List.lookup, hEq] using hTail'

theorem lookupSEnv_append_right {S₁ S₂ : SEnv} {x : Var} :
    lookupSEnv S₁ x = none →
    lookupSEnv (S₁ ++ S₂) x = lookupSEnv S₂ x := by
  intro hlookup
  induction S₁ with
  | nil =>
      simp [lookupSEnv]
  | cons hd tl ih =>
      by_cases hEq : x == hd.1
      · have : lookupSEnv (hd :: tl) x = some hd.2 := by
          simp [lookupSEnv, List.lookup, hEq]
        have hContra : (none : Option ValType) = some hd.2 := by
          simpa [hlookup] using this
        cases hContra
      · have hTail : lookupSEnv tl x = none := by
          simpa [lookupSEnv, List.lookup, hEq] using hlookup
        have hTail' := ih hTail
        simpa [lookupSEnv, List.lookup, hEq] using hTail'

theorem lookupSEnv_append_assoc {S₁ S₂ S₃ : SEnv} {x : Var} :
    lookupSEnv ((S₁ ++ S₂) ++ S₃) x = lookupSEnv (S₁ ++ (S₂ ++ S₃)) x := by
  cases h1 : lookupSEnv S₁ x with
  | some T₁ =>
      have h12 : lookupSEnv (S₁ ++ S₂) x = some T₁ :=
        lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T₁) h1
      have hLeft : lookupSEnv ((S₁ ++ S₂) ++ S₃) x = some T₁ :=
        lookupSEnv_append_left (S₁:=S₁ ++ S₂) (S₂:=S₃) (x:=x) (T:=T₁) h12
      have hRight : lookupSEnv (S₁ ++ (S₂ ++ S₃)) x = some T₁ :=
        lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂ ++ S₃) (x:=x) (T:=T₁) h1
      simpa [hLeft, hRight]
  | none =>
      have h12 : lookupSEnv (S₁ ++ S₂) x = lookupSEnv S₂ x :=
        lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) h1
      cases h2 : lookupSEnv S₂ x with
      | some T₂ =>
          have h12' : lookupSEnv (S₁ ++ S₂) x = some T₂ := by
            simpa [h2] using h12
          have hLeft : lookupSEnv ((S₁ ++ S₂) ++ S₃) x = some T₂ :=
            lookupSEnv_append_left (S₁:=S₁ ++ S₂) (S₂:=S₃) (x:=x) (T:=T₂) h12'
          have h23 : lookupSEnv (S₂ ++ S₃) x = some T₂ :=
            lookupSEnv_append_left (S₁:=S₂) (S₂:=S₃) (x:=x) (T:=T₂) h2
          have hRight : lookupSEnv (S₁ ++ (S₂ ++ S₃)) x = some T₂ := by
            have hRight' := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂ ++ S₃) (x:=x) h1
            simpa [hRight'] using h23
          simpa [hLeft, hRight]
      | none =>
          have h12' : lookupSEnv (S₁ ++ S₂) x = none := by
            simpa [h2] using h12
          have hLeft : lookupSEnv ((S₁ ++ S₂) ++ S₃) x = lookupSEnv S₃ x :=
            lookupSEnv_append_right (S₁:=S₁ ++ S₂) (S₂:=S₃) (x:=x) h12'
          have h23 : lookupSEnv (S₂ ++ S₃) x = lookupSEnv S₃ x :=
            lookupSEnv_append_right (S₁:=S₂) (S₂:=S₃) (x:=x) h2
          have hRight : lookupSEnv (S₁ ++ (S₂ ++ S₃)) x = lookupSEnv S₃ x := by
            have hRight' := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂ ++ S₃) (x:=x) h1
            simpa [hRight'] using h23
          simpa [hLeft, hRight]

theorem SEnv_append_assoc (S₁ S₂ S₃ : SEnv) :
    (S₁ ++ S₂) ++ S₃ = S₁ ++ (S₂ ++ S₃) := by
  simpa [List.append_assoc]

/-- DEnv extensionality (lookup-based) using canonical list representation. -/
theorem DEnv_ext {D₁ D₂ : DEnv} :
  (∀ e, D₁.find? e = D₂.find? e) → D₁ = D₂ := by
  intro h
  cases D₁ with
  | mk l₁ m₁ hm₁ hs₁ =>
    cases D₂ with
      | mk l₂ m₂ hm₂ hs₂ =>
      have hlookup : ∀ e, l₁.lookup e = l₂.lookup e := by
        intro e
        have h1 := DEnv_find?_eq_lookup (env := { list := l₁, map := m₁, map_eq := hm₁, sorted := hs₁ }) (e := e)
        have h2 := DEnv_find?_eq_lookup (env := { list := l₂, map := m₂, map_eq := hm₂, sorted := hs₂ }) (e := e)
        simpa [h1, h2] using (h e)
      have hsub12 : l₁ ⊆ l₂ := by
        intro p hp
        have hlookup₁ : l₁.lookup p.1 = some p.2 :=
          lookup_eq_some_of_mem_pairwise hs₁ hp
        have hlookup₂ : l₂.lookup p.1 = some p.2 := by
          simpa [hlookup₁] using (hlookup p.1).symm
        exact lookup_mem hlookup₂
      have hsub21 : l₂ ⊆ l₁ := by
        intro p hp
        have hlookup₂ : l₂.lookup p.1 = some p.2 :=
          lookup_eq_some_of_mem_pairwise hs₂ hp
        have hlookup₁ : l₁.lookup p.1 = some p.2 := by
          simpa [hlookup₂] using hlookup p.1
        exact lookup_mem hlookup₁
      have hl : l₁ = l₂ :=
        list_eq_of_subset_pairwise hs₁ hs₂ hsub12 hsub21
      have hm : m₁ = m₂ := by
        simpa [hl, hm₁, hm₂]
      cases hl
      cases hm
      simp

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

theorem SEnvDomSubset_append_left_of_domsubset {S₁ S₁' S₂ : SEnv} :
    SEnvDomSubset S₁' S₁ →
    SEnvDomSubset (S₁' ++ S₂) (S₁ ++ S₂) := by
  intro hSub x T hLookup
  cases hLeft : lookupSEnv S₁' x with
  | some T₁ =>
      have hLeft' := lookupSEnv_append_left (S₁:=S₁') (S₂:=S₂) (x:=x) (T:=T₁) hLeft
      have hEq : T₁ = T := by
        have : some T₁ = some T := by simpa [hLeft'] using hLookup
        exact Option.some.inj this
      obtain ⟨T', hIn⟩ := hSub hLeft
      exact ⟨T', by simpa [hEq] using lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T') hIn⟩
  | none =>
      have hRight := lookupSEnv_append_right (S₁:=S₁') (S₂:=S₂) (x:=x) hLeft
      have hS2 : lookupSEnv S₂ x = some T := by
        simpa [hRight] using hLookup
      cases hS1 : lookupSEnv S₁ x with
      | some T₁ =>
          exact ⟨T₁, lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T₁) hS1⟩
      | none =>
          have hRight' := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hS1
          exact ⟨T, by simpa [hRight'] using hS2⟩

theorem SEnvDomSubset_append_right_of_domsubset {S₁ S₂ S₂' : SEnv} :
    SEnvDomSubset S₂' S₂ →
    SEnvDomSubset (S₁ ++ S₂') (S₁ ++ S₂) := by
  intro hSub x T hLookup
  cases hLeft : lookupSEnv S₁ x with
  | some T₁ =>
      exact ⟨T₁, lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T₁) hLeft⟩
  | none =>
      have hRight := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂') (x:=x) hLeft
      have hS2' : lookupSEnv S₂' x = some T := by
        simpa [hRight] using hLookup
      obtain ⟨T', hS2⟩ := hSub hS2'
      have hRight' := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hLeft
      exact ⟨T', by simpa [hRight'] using hS2⟩

theorem SEnvSubset_append_left_self {S₁ S₂ : SEnv} :
    SEnvSubset S₁ (S₁ ++ S₂) := by
  intro x T hLookup
  exact lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T) hLookup

theorem SEnvSubset_append_right_of_subset {S₁ S₂ S₂' : SEnv} :
    SEnvSubset S₂' S₂ →
    SEnvSubset (S₁ ++ S₂') (S₁ ++ S₂) := by
  intro hSub x T hLookup
  cases hLeft : lookupSEnv S₁ x with
  | some T₁ =>
      have hLeft' := lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂') (x:=x) (T:=T₁) hLeft
      have hEq : T₁ = T := by
        have : some T₁ = some T := by simpa [hLeft'] using hLookup
        cases this
        rfl
      have hLeft'' := lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T₁) hLeft
      simpa [hEq] using hLeft''
  | none =>
      have hEq := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂') (x:=x) hLeft
      have hS2' : lookupSEnv S₂' x = some T := by
        simpa [hEq] using hLookup
      have hS2 : lookupSEnv S₂ x = some T := hSub hS2'
      have hEq' := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hLeft
      simpa [hEq'] using hS2

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

theorem DisjointS_append_left {S₁ S₁' S₂ : SEnv} :
    DisjointS S₁ S₂ →
    DisjointS S₁' S₂ →
    DisjointS (S₁ ++ S₁') S₂ := by
  intro hDisj hDisj' x T₁ T₂ hLookup hL2
  cases hLeft : lookupSEnv S₁ x with
  | some T₁' =>
      have hLeft' := lookupSEnv_append_left (S₁:=S₁) (S₂:=S₁') (x:=x) (T:=T₁') hLeft
      have hEq : T₁' = T₁ := by
        have : some T₁' = some T₁ := by simpa [hLeft'] using hLookup
        cases this
        rfl
      exact hDisj x T₁' T₂ hLeft (by simpa [hEq] using hL2)
  | none =>
      have hEq := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₁') (x:=x) hLeft
      have hLookup' : lookupSEnv S₁' x = some T₁ := by
        simpa [hEq] using hLookup
      exact hDisj' x T₁ T₂ hLookup' hL2

theorem DisjointS_of_subset_left {S₁ S₁' S₂ : SEnv} :
    SEnvSubset S₁' S₁ →
    DisjointS S₁ S₂ →
    DisjointS S₁' S₂ := by
  intro hSub hDisj x T₁ T₂ hL1 hL2
  exact hDisj x T₁ T₂ (hSub hL1) hL2

theorem DisjointS_of_domsubset_left {S₁ S₁' S₂ : SEnv} :
    SEnvDomSubset S₁' S₁ →
    DisjointS S₁ S₂ →
    DisjointS S₁' S₂ := by
  intro hSub hDisj x T₁ T₂ hL1 hL2
  obtain ⟨T₁', hL1'⟩ := hSub hL1
  exact hDisj x T₁' T₂ hL1' hL2


end
