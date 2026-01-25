# RumpsteakV2 Code Map

**Last Updated:** 2026-01-24

This document provides a comprehensive map of key proofs, lemmas, and definitions in the RumpsteakV2 formal verification codebase.

## Table of Contents

1. [Overview](#overview)
2. [Core Protocol Types](#core-protocol-types)
3. [Projection System](#projection-system)
4. [Coinductive Types](#coinductive-types)
5. [Main Theorems](#main-theorems)
6. [Supporting Lemmas](#supporting-lemmas)
7. [Cross-Reference Index](#cross-reference-index)

---

## Overview

**Codebase Statistics:**
- Total files: 79 .lean files
- Total size: ~1.4MB
- Main modules: Protocol, Semantics, Proofs, Coinductive
- Central result: Choreographic projection correctness and safety

**Axiom Inventory (V2):**
- Inductive projection path: 0 axioms (all discharged)
- Coinductive EQ2 path: 0 axioms (EQ2 transitivity via Bisim detour)

**Key Research Questions Addressed:**
1. Does choreographic projection preserve semantics? (Harmony theorem)
2. Are projected protocols deterministic? (Determinism proofs)
3. Are projected protocols deadlock-free? (Safety proofs)
4. Can we decide bisimulation for session types? (Decidability proofs)

---

## Core Protocol Types

### Protocol/GlobalType.lean
**Location:** `RumpsteakV2/Protocol/GlobalType.lean` (64KB)

**Key Definitions:**
- `GlobalType` - Global choreography types
  - `.end` - Termination
  - `.var` - Type variable
  - `.mu` - Recursive type
  - `.comm sender receiver branches` - Communication

**Key Functions:**
- `allCommsNonEmpty : GlobalType → Bool` - Check all communications have branches
- `allCommsNonEmptyBranches : List (Label × GlobalType) → Bool` - Branch checking
- `wellFormed : GlobalType → Bool` - Well-formedness predicate

**Important Theorems:**
- `allCommsNonEmpty_comm` - Characterization for comm constructor
- `wellFormed_comm_branches` - Well-formedness for branches

---

### Protocol/LocalTypeR.lean
**Location:** `RumpsteakV2/Protocol/LocalTypeR.lean` (74KB)

**Key Definitions:**
- `LocalTypeR` - Recursive local session types
  - `.end` - Termination
  - `.var v` - Type variable
  - `.mu v body` - Recursive binding
  - `.send partner branches` - Send action
  - `.recv partner branches` - Receive action

**Key Functions:**
- `substitute : LocalTypeR → String → LocalTypeR → LocalTypeR` - Variable substitution
- `unfold : LocalTypeR → LocalTypeR` - One-step mu unfolding
- `fullUnfold : LocalTypeR → LocalTypeR` - Complete unfolding
- `isGuarded : LocalTypeR → String → Bool` - Guardedness check
- `isContractive : LocalTypeR → Bool` - Contractiveness check
- `freeVars : LocalTypeR → List String` - Free variable collection
- `isClosed : LocalTypeR → Bool` - Closedness test

**Key Lemmas:**
- `dual_dual : ∀ t, t.dual.dual = t` - Duality is involution
- `dual_substitute` - Duality commutes with substitution
- `substitute_var_same` - Substitution identity
- `substitute_var_diff` - Substitution variable mismatch

---

### Protocol/Participation.lean
**Location:** `RumpsteakV2/Protocol/Participation.lean` (12KB)

**Key Theorems:**
- `part_of2_iff_participates` - Boolean participation ⇔ inductive participation
- `participatesBranches_iff_part_of2` - Branch participation ⇔ ∃ participating branch

---

## Projection System

### Protocol/Projection/Project.lean (re-export)
**Location:** `RumpsteakV2/Protocol/Projection/Project.lean` (1.2KB)

**Role:**
- Re-exports the split Project modules under `Protocol/Projection/Project/`.
- Provides a stable import path for downstream proofs.

### Protocol/Projection/Project/* (split modules)
**Location:** `RumpsteakV2/Protocol/Projection/Project/` (20 files)

**Central Definitions (split across modules):**
- `CProjectF` / `CProject` - core projection relation (Project/ImplBase.lean)
- `Projectable` / `ProjectableClosedWellFormed` - projectability predicates (Project/Core.lean)
- `BranchesProjRel` / `AllBranchesProj` - branch-wise projection relations (Project/ImplBase.lean)

**File Size Table (split):**

| File | Size | Purpose |
|------|------|---------|
| Core.lean | 4.0KB | Projectable, projectR? core API |
| CProjectTransRel.lean | 0.9KB | CProject→EQ2 trans wrappers |
| CProjectU.lean | 0.8KB | Unfold-insensitive projection interface |
| Completeness.lean | 0.7KB | projectR? completeness |
| Props.lean | 0.6KB | determinism/props re-export |
| Impl.lean | 0.6KB | Impl re-export |
| ImplBase.lean | 14.1KB | core CProject proofs |
| ImplConstructors.lean | 20.7KB | constructor-specific trans lemmas |
| ImplTransRelComp.lean | 28.8KB | postfix/comp proofs for trans relation |
| ImplObservables.lean | 16.7KB | observable preservation |
| ImplHeadPreservation.lean | 15.6KB | head preservation lemmas |
| ImplCompleteness.lean | 14.9KB | completeness scaffolding |
| ImplCompPostfix.lean | 42.4KB | comp postfix lemmas |
| ImplExtraction.lean | 30.2KB | extraction / compose-through-mu |
| ImplU.lean | 37.0KB | CProjectU proofs |
| Muve.lean | 0.7KB | muve front-end |
| MuveImpl.lean | 0.3KB | muve re-export |
| MuveImplBase.lean | 24.8KB | muve base proofs |
| MuveImplNonPart.lean | 18.5KB | non-participant muve |
| MuveImplParticipant.lean | 19.5KB | participant muve |

**Key Theorems (new locations):**
- `CProject_unfold` / `CProject_fold` / `CProject_coind` / `CProject_destruct` → Project/ImplBase.lean
- `branches_project_coherent` → Proofs/Projection/Harmony.lean (coherence via participation)
- Observable preservation lemmas → Project/ImplObservables.lean

---

### Protocol/Projection/Projectb.lean
**Location:** `RumpsteakV2/Protocol/Projection/Projectb.lean` (62.5KB)

**Key Definitions:**
- Alternative projection formulation using boolean guards
- `projectb : GlobalType → String → LocalTypeR` - Computable projection

**Key Theorems:**
- `projectb_sound : CProject g role (projectb g role)` - Soundness
- `projectb_trans : projectb g role ≈ trans g role` - Equivalence to trans

---

### Protocol/Projection/Trans.lean
**Location:** `RumpsteakV2/Protocol/Projection/Trans.lean` (35.5KB)

**Key Definition:**
- `trans : GlobalType → String → LocalTypeR` - Direct projection function

**Key Lemmas:**
- `trans_end` - Projection of end
- `trans_comm_sender` - Projection for sender
- `trans_comm_receiver` - Projection for receiver
- `trans_comm_other` - Projection for non-participant
- `lcontractive` - Trans produces contractive types

**Substitution:**
- `trans_substitute_unfold` - Substitution unfolding for trans

---

### Protocol/Projection/Embed.lean
**Location:** `RumpsteakV2/Protocol/Projection/Embed.lean` (9KB)

**Key Definitions:**
- `CEmbedF` - One-step embedding generator
- `CEmbed : LocalTypeR → String → GlobalType → Prop` - Embedding relation

**Main Theorem:**
- `CEmbed_implies_CProject` - Embedding implies projection (soundness)
- `CEmbed_has_project` - Every embedding has a projection

---

### Protocol/Projection/EmbedProps.lean
**Location:** `RumpsteakV2/Protocol/Projection/EmbedProps.lean` (21KB)

**Key Theorems:**
- `embed_deterministic` - Embedding is unique up to equality
- `branches_embed_deterministic` - Branch embedding determinism
- `embed_project_roundtrip` - Embed then project is identity (up to EQ2)
- `localType_has_embed` - Existence of embeddings for local types

---

### Protocol/Projection/ProjectProps.lean
**Location:** `RumpsteakV2/Protocol/Projection/ProjectProps.lean` (5.8KB)

**Key Theorems:**
- `project_deterministic` - Projection is deterministic up to EQ2
- `branches_proj_deterministic` - Branch projection determinism

---

## Coinductive Types

### Protocol/CoTypes/CoinductiveRel.lean
**Location:** `RumpsteakV2/Protocol/CoTypes/CoinductiveRel.lean`

**Framework:**
- `CoinductiveRel (F : Rel → Rel)` - Typeclass for coinductive relations
- `gfp` - Greatest fixed point
- `coind` - Coinduction principle
- `unfold` - Unfolding lemma
- `fold` - Folding lemma

---

### Protocol/CoTypes/CoinductiveRelPaco.lean
**Location:** `RumpsteakV2/Protocol/CoTypes/CoinductiveRelPaco.lean`

**PACO Framework:**
- Parametric coinduction infrastructure
- `paco` - PACO combinator
- `paco_acc` - Accumulation lemma
- `paco_mon` - Monotonicity

---

### Protocol/CoTypes/EQ2.lean
**Location:** `RumpsteakV2/Protocol/CoTypes/EQ2.lean` (706 lines)

**Key Definition:**
- `EQ2 : LocalTypeR → LocalTypeR → Prop` - Coinductive equality for local types
- `ReflRel` - Unfold-closure relation used to prove reflexivity without axioms

**Key Theorems:**
- `EQ2_refl` - Reflexivity
- `EQ2_symm` - Symmetry
- `EQ2_trans_via_end` - Transitivity via `.end` without full trans
- `EQ2_trans_via_var` - Transitivity via `.var v` without full trans
- `EQ2_unfold_left` - Unfold left mu
- `EQ2_unfold_right` - Unfold right mu
- `EQ2_send_head` - Send constructor equality
- `EQ2_recv_head` - Receive constructor equality

**Coinduction:**
- `EQ2_coind` - Coinduction principle
- `EQ2_coind_upto` - Coinduction up-to technique
- `EQ2_closure` - Closure under EQ2

---

### Protocol/CoTypes/EQ2Paco.lean
**Location:** `RumpsteakV2/Protocol/CoTypes/EQ2Paco.lean` (8KB)

**PACO-based EQ2:**
- `EQ2_paco` - PACO version of EQ2
- `EQ2_paco_coind` - PACO coinduction
- `EQ2_paco_unfold` - PACO unfolding

---

### Protocol/CoTypes/EQ2Props.lean
**Location:** `RumpsteakV2/Protocol/CoTypes/EQ2Props.lean` (24 lines)

**Bisim-based EQ2 Properties:**
- `EQ2_trans_wf` - Transitivity via Bisim (requires WellFormed hypotheses)

---

### Protocol/CoTypes/Bisim.lean
**Location:** `RumpsteakV2/Protocol/CoTypes/Bisim.lean` (156KB, largest in CoTypes)

**Key Definition:**
- `Bisim : LocalTypeR → LocalTypeR → Prop` - Bisimulation relation

**Key Theorems:**
- `Bisim_refl` - Reflexivity
- `Bisim_symm` - Symmetry
- `Bisim_trans` - Transitivity
- `Bisim_implies_EQ2` - Bisimulation implies EQ2
- `EQ2_implies_Bisim` - EQ2 implies bisimulation (for well-formed types)
- `EQ2_send_not_UnfoldsToEnd/Var/CanRecv` - Incompatibility lemmas for send vs observables
- `ObservableRel.toEQ2` - Build EQ2 from observables (requires WellFormed on both sides)
- `EQ2_iff_observable_correspond` - EQ2 ↔ observable correspondence (WellFormed on both sides)

**Bisimulation Up-To:**
- `bisim_upto` - Up-to technique
- `bisim_upto_eq` - Up-to equality

---

### Protocol/CoTypes/Dual.lean
**Location:** `RumpsteakV2/Protocol/CoTypes/Dual.lean` (13KB)

**Key Theorems:**
- `dual_involutive : t.dual.dual = t` - Duality involution
- `dual_isGuarded` - Duality preserves guardedness
- `dual_isContractive` - Duality preserves contractiveness
- `freeVars_dual` - Duality preserves free variables
- `EQ2_dual` - EQ2 respects duality

**Observable Duality:**
- `UnfoldsToEnd.dual` - Unfolding to end preserved by dual
- `UnfoldsToVar.dual` - Unfolding to var preserved by dual
- `CanSend.dual` - Dual of CanSend is CanRecv
- `CanRecv.dual` - Dual of CanRecv is CanSend

---

### Protocol/CoTypes/FullUnfold.lean
**Location:** `RumpsteakV2/Protocol/CoTypes/FullUnfold.lean` (11KB)

**Key Definitions:**
- `muHeight : LocalTypeR → Nat` - Count nested mu constructors
- `singleUnfold : LocalTypeR → LocalTypeR` - One unfold step
- `fullUnfold : LocalTypeR → LocalTypeR` - Complete unfolding

**Key Theorems:**
- `fullUnfold_mu_subst` - Guarded mu: full unfold commutes with substitution
- `muHeight_substitute_guarded` - Height preservation for guarded substitution
- `EQ2_of_fullUnfold_eq` - Equality of full unfolds implies EQ2
- `fullUnfold_eq_of_EQ2` - EQ2 implies EQ2 of full unfolds
- `EQ2_iff_fullUnfold_eq` - EQ2 ⇔ EQ2 of full unfolds

---

### Protocol/CoTypes/SubstCommBarendregt.lean
**Location:** `RumpsteakV2/Protocol/CoTypes/SubstCommBarendregt.lean` (58KB)

**Main Result:**
- Barendregt's substitution commutation lemma for session types
- Alpha-equivalence preservation through substitution

**Key Lemmas:**
- Variable freshness conditions
- Substitution composition
- Alpha-conversion compatibility

---

## Main Theorems

### Proofs/Projection/Harmony.lean
**Location:** `RumpsteakV2/Proofs/Projection/Harmony.lean` (81KB)

**CENTRAL RESULT - Projection Harmony:**

```lean
theorem step_harmony {g : GlobalType} {env : ProjectedEnv} {g' : GlobalType}
    (hstep : GlobalStep g action g')
    (hproj : projEnv g env) :
    ∃ env', EnvStep env action env' ∧ projEnv g' env'
```

This theorem states that global choreography steps correspond to local environment steps.

**Supporting Theorems:**

- `trans_subst_comm` - Trans commutes with substitution (via paco coinduction)
  ```lean
  theorem trans_subst_comm (g : GlobalType) (t : String) (role : String) :
      EQ2 (trans g role).substitute t (trans g role)
          (trans (g.substitute t g) role)
  ```

- `proj_trans_sender_step` - Sender projection step
- `proj_trans_receiver_step` - Receiver projection step
- `proj_trans_other_step` - Non-participant projection step (requires `ProjectableClosedWellFormed`;
  mu case chains via `EQ2_trans_wf` with WellFormed witnesses)

- `trans_branches_coherent_EQ2` - Branches project coherently
  ```lean
  theorem trans_branches_coherent_EQ2
      (gbs : List (Label × GlobalType)) (role : String) :
      ∀ l g, (l, g) ∈ gbs →
        ∃ lbs, BranchesProjRel CProject gbs role lbs ∧
               ∀ l' e, (l', e) ∈ lbs → l = l' → EQ2 (trans g role) e
  ```

- `trans_produces_CProject` - Trans produces valid CProject
  ```lean
  theorem trans_produces_CProject (g : GlobalType) (role : String) :
      CProject g role (trans g role)
  ```

**Branch Helpers:**
- `transBranches_satisfies_BranchesProjRel` - Trans branches satisfy projection relation

---

### Proofs/Projection/MuUnfoldLemmas.lean
**Location:** `RumpsteakV2/Proofs/Projection/MuUnfoldLemmas.lean` (12KB)

**Key Mu-Unfolding Theorems:**

- `EQ2_mu_crossed_unfold_left` - Left mu unfold crossing
  ```lean
  theorem EQ2_mu_crossed_unfold_left (t : String) (body e : LocalTypeR) :
      EQ2 (.mu t body) e →
      EQ2 (body.substitute t (.mu t body)) e
  ```

- `EQ2_mu_crossed_unfold_right` - Right mu unfold crossing
  ```lean
  theorem EQ2_mu_crossed_unfold_right (e : LocalTypeR) (t : String) (body : LocalTypeR) :
      EQ2 e (.mu t body) →
      EQ2 e (body.substitute t (.mu t body))
  ```

- `EQ2_mu_unguarded_to_end` - Unguarded mu to end
- `EQ2_end_to_mu_unguarded` - End to unguarded mu

---

### Proofs/Projection/SubstEndUnguarded.lean
**Location:** `RumpsteakV2/Proofs/Projection/SubstEndUnguarded.lean` (8KB)

**Key Theorem:**

- `subst_end_unguarded_eq2_end` - Substitution of end in unguarded position
  ```lean
  theorem subst_end_unguarded_eq2_end (t : String) (body : LocalTypeR)
      (hunguarded : body.isGuarded t = false)
      (hbody_end : EQ2 body .end) :
      EQ2 (body.substitute t .end) .end
  ```

Proven via coinductive `UnfoldsToEnd` relation.

---

### Proofs/Safety/Determinism.lean
**Location:** `RumpsteakV2/Proofs/Safety/Determinism.lean` (40KB)

**Main Theorem:**
```lean
theorem protocol_deterministic (g : GlobalType) :
    ∀ action₁ g₁ action₂ g₂,
      GlobalStep g action₁ g₁ →
      GlobalStep g action₂ g₂ →
      action₁ = action₂ ∧ g₁ = g₂
```

Protocol execution is deterministic - each global type can step to at most one successor.

---

### Proofs/Safety/DeadlockFreedom.lean
**Location:** `RumpsteakV2/Proofs/Safety/DeadlockFreedom.lean` (10KB)

**Main Theorem:**
```lean
theorem deadlock_free (g : GlobalType) :
    WellFormed g →
    (g = .end ∨ ∃ action g', GlobalStep g action g')
```

Well-formed protocols either terminate gracefully or can make progress.

---

### Proofs/Safety/SubjectReduction.lean
**Location:** `RumpsteakV2/Proofs/Safety/SubjectReduction.lean` (7KB)

**Main Theorem:**
```lean
theorem subject_reduction (g g' : GlobalType) (action : Action) :
    WellFormed g →
    GlobalStep g action g' →
    WellFormed g'
```

Well-formedness is preserved by global steps (type safety).

---

## Coinductive Module

### Coinductive/LocalTypeC.lean
**Location:** `RumpsteakV2/Coinductive/LocalTypeC.lean` (5KB)

**Key Definition:**
- `LocalTypeC` - Coinductive local types via M-types (greatest fixed point of polynomial functor)

**Smart Constructors:**
- `mkEnd : LocalTypeC` - Coinductive end
- `mkVar : String → LocalTypeC` - Coinductive variable
- `mkMu : String → LocalTypeC → LocalTypeC` - Coinductive mu
- `mkSend : String → List (Label × LocalTypeC) → LocalTypeC` - Coinductive send
- `mkRecv : String → List (Label × LocalTypeC) → LocalTypeC` - Coinductive receive

**Destructors:**
- `destruct : LocalTypeC → LocalTypeCF LocalTypeC` - Coinductive destructor

---

### Coinductive/EQ2C.lean
**Location:** `RumpsteakV2/Coinductive/EQ2C.lean` (18KB)

**Key Definition:**
- `EQ2C : LocalTypeC → LocalTypeC → Prop` - Coinductive equality for coinductive types

**Key Theorems:**
- `EQ2C_refl` - Reflexivity
- `EQ2C_symm` - Symmetry
- `EQ2C_trans` - Transitivity
- `EQ2C_unfold_left` - Unfold left mu
- `EQ2C_unfold_right` - Unfold right mu

---

### Coinductive/BisimDecidable.lean
**Location:** `RumpsteakV2/Coinductive/BisimDecidable.lean` (51KB)

**Main Result:**
- Decidable bisimulation algorithm for regular session types
- Soundness proof (completeness dropped in paco-first approach)

**Key Definitions:**
- `BisimRel = BisimRelCore ∨ EQ2C` - Combined bisimulation relation
- `maxUnfoldDepth` - Bound for observable types

**Key Theorems:**
- `BisimRel_postfixpoint` - BisimRel is post-fixpoint
- `EQ2C_postfixpoint` - EQ2C compatibility

---

### Coinductive/Roundtrip.lean
**Location:** `RumpsteakV2/Coinductive/Roundtrip.lean` (63KB, 1,214 lines)

**Conversion Functions:**
- `toInductive : LocalTypeC → LocalTypeR` - Convert coinductive to inductive
- `toCoind : LocalTypeR → LocalTypeC` - Convert inductive to coinductive

**Main Theorems (proved):**
- `toCoind_toInductive_eq2ce` - Round-trip in EQ2CE

**Key Lemmas (erasure + μ-paco bridge):**
- `EQ2C_mu_paco_le_paco_of_productive` - Collapse μ-aware paco to EQ2C_paco under productivity
- `EQ2CE_resolved'_implies_EQ2C` - Environment erasure (requires productivity on both sides)
- `toCoind_toInductive_eq2c_of_env_toCoind` - Round-trip for `toCoind` images (discharges productivity)
- `envOf`, `nameOf` - Environment/name generation (definitions, no axioms)
- `BranchesRelC_gupaco_clo`, `gupaco_clo_obs_of_rr` - gpaco_clo helper lemmas (guarded observable extraction)

---

### Coinductive/RoundtripWIP.lean
**Location:** `RumpsteakV2/Coinductive/RoundtripWIP.lean` (0.2KB)

**Status:**
- Deprecated wrapper (content consolidated into Roundtrip.lean)

**Key Result (now in Roundtrip.lean):**
- `EQ2CE_resolved'_implies_EQ2C` - Environment erasure (μ-paco bridge; no sorry)

---

## Supporting Lemmas

### Proofs/Core/Assumptions.lean
**Location:** `RumpsteakV2/Proofs/Core/Assumptions.lean` (0.3KB)

**Notes:**
- No axioms currently live in this module (kept for centralized assumptions)

### Protocol/CoTypes/Observable.lean
**Location:** `RumpsteakV2/Protocol/CoTypes/Observable.lean` (11KB)

**Observable Predicates:**

- `UnfoldsToEnd : LocalTypeR → Prop` - Type unfolds to end
- `UnfoldsToVar : LocalTypeR → String → Prop` - Type unfolds to variable
- `CanSend : LocalTypeR → String → List (Label × LocalTypeR) → Prop` - Type can send
- `CanRecv : LocalTypeR → String → List (Label × LocalTypeR) → Prop` - Type can receive

**Key Lemmas:**
- `UnfoldsToEnd.mu` - Mu unfolding to end
- `CanSend.mu` - Mu can send
- `CanRecv.mu` - Mu can receive

---

### Semantics/EnvStep.lean
**Location:** `RumpsteakV2/Semantics/EnvStep.lean` (7KB)

**Key Definitions:**

- `ProjectedEnv` - Maps roles to local types
  ```lean
  def ProjectedEnv := Role → LocalTypeR
  ```

- `projEnv : GlobalType → ProjectedEnv → Prop` - Environment projection
  ```lean
  def projEnv (g : GlobalType) (env : ProjectedEnv) : Prop :=
    ∀ role, CProject g role (env role)
  ```

- `EnvStep : ProjectedEnv → Action → ProjectedEnv → Prop` - Environment stepping
  - Lifts local steps to environment transitions

**Key Lemmas:**
- `projEnv_deterministic` - Projected environments are unique up to EQ2
- `envStep_role_match` - Step actions match role types

---

## Cross-Reference Index

### By Topic

#### **Projection Correctness**
1. `trans_produces_CProject` - Trans.lean → Harmony.lean
2. `projectb_sound` - Projectb.lean → Harmony.lean
3. `CProject_implies_EQ2_trans` - Project.lean → ProjectProps.lean
4. `step_harmony` - Harmony.lean (uses all above)

#### **Projectability Assumptions**
1. `Projectable` - Project.lean (global projectability predicate)
2. `ProjectableClosedWellFormed` - Project/Core.lean (assumption used by Harmony/SubjectReduction)

#### **Determinism Chain**
1. `project_deterministic` - ProjectProps.lean
2. `protocol_deterministic` - Determinism.lean
3. `envStep_deterministic` - EnvStep.lean

#### **EQ2 Theory**
1. `EQ2` definition - EQ2.lean
2. `EQ2_paco_coind` - EQ2Paco.lean
3. `EQ2_trans_wf` - EQ2Props.lean
4. `Bisim_implies_EQ2` - Bisim.lean
5. `EQ2_dual` - Dual.lean
6. `EQ2_of_fullUnfold_eq` - FullUnfold.lean

#### **Substitution Commutation**
1. `trans_subst_comm` - Harmony.lean (main proof)
2. `trans_substitute_unfold` - Trans.lean (helper)
3. `dual_substitute` - LocalTypeR.lean
4. Barendregt lemmas - SubstCommBarendregt.lean

#### **Mu-Type Handling**
1. `fullUnfold_mu_subst` - FullUnfold.lean
2. `EQ2_mu_crossed_unfold_left/right` - MuUnfoldLemmas.lean
3. `subst_end_unguarded_eq2_end` - SubstEndUnguarded.lean
4. `isGuarded` preservation - Various files

#### **Coinductive/Inductive Bridge**
1. `toInductive` / `toCoind` - Roundtrip.lean
2. `toCoind_toInductive_eq2ce` - Roundtrip.lean
3. `EQ2CE_resolved'_implies_EQ2C` - Roundtrip.lean
4. `BisimDecidable` - BisimDecidable.lean
5. `EQ2C_mu_paco_le_paco_of_productive` - Roundtrip.lean (μ-paco collapse under productivity)

### By Dependency

#### **Core Dependencies** (used everywhere)
- `GlobalType` - GlobalType.lean
- `LocalTypeR` - LocalTypeR.lean
- `CProject` - Project.lean
- `EQ2` - EQ2.lean

#### **Projection Stack**
```
GlobalType.lean
    ↓
Trans.lean → Projectb.lean → Project.lean
    ↓              ↓              ↓
ProjectProps.lean ← Embed.lean ← EmbedProps.lean
    ↓
Harmony.lean
```

#### **Safety Stack**
```
Harmony.lean
    ↓
SubjectReduction.lean
    ↓
Determinism.lean + DeadlockFreedom.lean
```

#### **Coinductive Stack**
```
CoinductiveRel.lean → CoinductiveRelPaco.lean
    ↓                         ↓
EQ2.lean → EQ2Paco.lean      Bisim.lean
    ↓                         ↓
LocalTypeC.lean → EQ2C.lean → BisimDecidable.lean
    ↓
Roundtrip.lean
```

---

## Axiom Inventory

### Inductive Codebase (0 axioms)

| File | Count | Key Axioms |
|------|-------|------------|
| Project.lean | 0 | *(none)* |
| Projectb.lean | 0 | *(none)* |
| DBBridge.lean | 0 | *(none)* |
| Proofs/Core/Assumptions.lean | 0 | *(none)* |

### Coinductive Codebase (0 axioms)

| File | Count | Key Axioms |
|------|-------|------------|
| EQ2.lean | 0 | *(none)* |

### Sorry Inventory

**Inductive:** 0

**Coinductive:** 0

---

## File Size Reference

**Largest Files (Top 10):**
1. Project.lean - 226KB (~4,899 lines)
2. Bisim.lean - 157KB
3. LocalTypeR.lean - 74KB
4. GlobalType.lean - 64KB
5. Harmony.lean - 81KB (~1,618 lines)
6. SubstCommBarendregt.lean - 58KB
7. BisimDecidable.lean - 51KB
8. Determinism.lean - 40KB
9. Projectb.lean - 40KB
10. Trans.lean - 31KB

---

## Quick Navigation Guide

**Want to understand...**

- **How projection works?** → Start with Trans.lean, then Project.lean
- **Why projection is correct?** → Read Harmony.lean (step_harmony theorem)
- **How EQ2 equality works?** → Start with EQ2.lean, then EQ2Paco.lean
- **Bisimulation theory?** → Read Bisim.lean, then BisimDecidable.lean
- **Coinductive types?** → Start with LocalTypeC.lean, then EQ2C.lean
- **Safety properties?** → Read Determinism.lean and DeadlockFreedom.lean
- **Mu-type unfolding?** → Read FullUnfold.lean and MuUnfoldLemmas.lean
- **Substitution theory?** → Read SubstCommBarendregt.lean
- **Round-trip conversions?** → Read Roundtrip.lean

---

## Version History

- 2026-01-16: Initial code map created
- Future: Will be updated as proofs are completed

---

## Contributing

When adding new theorems or lemmas, please update this code map with:
1. Theorem name and location
2. Brief description
3. Dependencies and cross-references
4. Related theorems

## License

Same as RumpsteakV2 project.
