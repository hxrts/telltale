# CODE_MAP.md — RumpsteakV2 Lean Verification

**176 files | 40,470 lines | 0 axioms | 0 sorries — fully verified**

Last updated: 2026-01-29

---

## Table of Contents

1. [Overview](#1-overview)
2. [Core Protocol Types](#2-core-protocol-types)
3. [Projection System](#3-projection-system)
4. [Coinductive Types](#4-coinductive-types)
5. [Coinductive Module](#5-coinductive-module)
6. [Main Theorems](#6-main-theorems)
7. [Proof Strategies](#7-proof-strategies)
8. [Axiom Inventory](#8-axiom-inventory)
9. [Cross-Reference Index](#9-cross-reference-index)
10. [File Size Reference](#10-file-size-reference)
11. [Quick Navigation Guide](#11-quick-navigation-guide)

---

## 1. Overview

RumpsteakV2 formally verifies choreographic projection and session-type safety properties in Lean 4. The development covers:

- **Global and local session types** with de Bruijn indices and recursive binders
- **Coinductive projection** via greatest fixed points, with a boolean checker and soundness proof
- **Bisimulation and coinductive equality (EQ2)** for local types, including decidability for regular types
- **Harmony**: global protocol steps correspond precisely to local environment steps
- **Safety**: deadlock freedom, subject reduction, determinism, and progress
- **Blindness**: axiom-free projectability via a syntactic uniformity predicate
- **Coinductive round-trip**: bridging inductive `LocalTypeR` and coinductive `LocalTypeC` representations

**Key Research Questions Addressed:**

1. Does choreographic projection preserve semantics? (Harmony theorem)
2. Are projected protocols deterministic? (Determinism proofs)
3. Are projected protocols deadlock-free? (Safety proofs)
4. Can we decide bisimulation for session types? (Decidability proofs)

**Main modules:** Protocol, Semantics, Proofs, Coinductive

All results are axiom-free and sorry-free.

---

## 2. Core Protocol Types

### GlobalType — `Protocol/GlobalType.lean` (re-export) + `GlobalType/Part1–5`

The global session type inductive, representing choreographies with communication, branching, recursion, and end.

| File | Contents |
|------|----------|
| `Part1` | `GlobalType` inductive definition, basic constructors |
| `Part2` | `wellFormed` predicate |
| `Part3` | `allCommsNonEmpty`, structural predicates |
| `Part4` | `substitute`, `roles` |
| `Part5` | `freeVars`, auxiliary lemmas (571 lines) |

### LocalTypeR — `Protocol/LocalTypeR.lean` (re-export) + `LocalTypeR/Part1–5`

The inductive local session type with recursive types, sends, receives, and branching.

| File | Contents |
|------|----------|
| `Part1` | `LocalTypeR` inductive, `substitute` (511 lines) |
| `Part2` | `unfold`, `fullUnfold` |
| `Part3` | `isGuarded`, `isContractive` |
| `Part4` | `freeVars` |
| `Part5` | `dual` |

### Core — `Protocol/Core.lean`

`Role` and `Action` types shared across the development.

### Participation — `Protocol/Participation.lean` (re-export)

| File | Contents |
|------|----------|
| `Participation/Core.lean` | `part_of2`, `part_of_all2`, `participates`, `part_of2_iff_participates`, `participatesBranches_iff_part_of2` |
| `Participation/Extra.lean` | Additional participation lemmas |

### Other Core Files

| File | Contents |
|------|----------|
| `Protocol/Semantics.lean` | Global type operational semantics |
| `Protocol/Spatial.lean` | Spatial predicates on types |
| `Protocol/TypeContext.lean` | Typing contexts (518 lines) |
| `Protocol/LocalTypeConv*.lean` | Conversion lemmas between type representations |
| `Protocol/LocalTypeDB/` | De Bruijn bridge, including `Preservation.lean` (551 lines) |

---

## 3. Projection System

### Trans — `Protocol/Projection/Trans/`

Direct (functional) projection from global to local types.

| Definition | Location | Description |
|------------|----------|-------------|
| `trans` | `Trans/Core.lean` | Direct projection function |
| `trans_comm_sender` | `Trans/Core.lean` | Sender case of projection |
| `trans_comm_receiver` | `Trans/Core.lean` | Receiver case of projection |
| `trans_comm_other` | `Trans/Core.lean` | Non-participant case |
| `trans_closed_of_closed` | `Trans/` | Closedness preservation under projection |

### Projectb — `Protocol/Projection/Projectb/`

Boolean projection checker and its soundness proof. `Projectb/Part4.lean` is 560 lines.

| Definition | Location | Description |
|------------|----------|-------------|
| `projectb` | `Projectb/` | Boolean projection checker |
| `projectb_sound` | `Projectb/` | `CProject g role (projectb g role)` |

### CProject / Project — `Protocol/Projection/Project/`

Coinductive projection relation defined as a greatest fixed point.

| Definition | Location | Description |
|------------|----------|-------------|
| `CProjectF` | `Project/ImplBase.lean` | Generator functor for coinductive projection |
| `CProject` | `Project/ImplBase.lean` | Greatest fixed point: coinductive projection relation |
| `CProject_unfold` | `Project/ImplBase.lean` | Unfold principle |
| `CProject_fold` | `Project/ImplBase.lean` | Fold principle |
| `CProject_coind` | `Project/ImplBase.lean` | Coinduction principle |
| `CProject_destruct` | `Project/ImplBase.lean` | Destruction principle |
| `CProject_implies_EQ2_trans` | `Project/` | Projection relates to `trans` via EQ2 |
| `Projectable` | `Project/Core.lean` | Global projectability predicate |
| `ProjectableClosedWellFormed` | `Project/Core.lean` | Bundle: closed + wellFormed + projectable |
| `BranchesProjRel` | `Project/ImplBase.lean` | Branch-wise projection relation |
| `AllBranchesProj` | `Project/ImplBase.lean` | All-branches projection |

### ProjectProps — `Protocol/Projection/ProjectProps.lean`

| Definition | Description |
|------------|-------------|
| `project_deterministic` | Projection is deterministic up to EQ2 |

### ProjSubst — `Protocol/Projection/ProjSubst.lean`

Projection-substitution interaction lemmas.

### Blind — `Protocol/Projection/Blind/`

Blindness predicates that eliminate the projectability axiom entirely.

| Definition | Location | Description |
|------------|----------|-------------|
| `isBlind` | `Blind/Part1.lean` | Syntactic blindness predicate |
| `branchesUniformFor` | `Blind/Part1.lean:45` | Uniform branches for non-participants |
| `WellFormedBlind` | `Blind/Part1.lean:80` | Closed + wellFormed + blind |
| `trans_uniform_for_nonparticipant` | `Blind/Part1.lean:287` | Core blindness property |
| `projectb_trans_of_wellFormedBlind` | `Blind/Part1.lean:468` | Boolean projection agrees with trans under blindness |
| `projectable_of_wellFormedBlind` | `Blind/Part1.lean:478` | **Eliminates projectability axiom** |
| `isBlind_substitute` | `Blind/Part2.lean:72` | Blindness preserved by substitution |
| `isBlindBranches_step` | `Blind/Part2.lean:173` | Blindness preserved by step |

### Erasure — `Protocol/Projection/Erasure/`

Erasure and deployment-related projection results.

| File | Contents |
|------|----------|
| `Erasure/Part1.lean` | `Erases` relation, `Erasable` predicate |
| `Erasure/Part2a.lean` | `merge`, `mergeAll` |
| `Erasure/Part2b.lean` | `merge_sound`, `mergeAll_sound` |

### Embed — `Protocol/Projection/Embed.lean`, `EmbedProps.lean`

| Definition | Location | Description |
|------------|----------|-------------|
| `CEmbedF` | `Embed.lean` | One-step embedding generator |
| `CEmbed` | `Embed.lean` | Embedding relation |
| `embed_project_roundtrip` | `EmbedProps.lean` | Embed-project round-trip property |
| `embed_deterministic` | `EmbedProps.lean` | Embedding is unique up to equality |

`EmbedProps.lean` is 519 lines.

---

## 4. Coinductive Types

### EQ2 — `Protocol/CoTypes/EQ2/`

Coinductive equality on local types, defined as a greatest fixed point.

| Definition | Location | Description |
|------------|----------|-------------|
| `EQ2` | `EQ2/Core.lean` | Coinductive equality (greatest fixed point) |
| `ReflRel` | `EQ2/Core.lean` | Unfold-closure relation for axiom-free reflexivity |
| `EQ2_refl` | `EQ2/Core.lean` | Reflexivity |
| `EQ2_symm` | `EQ2/Core.lean` | Symmetry |
| `EQ2_trans_via_end` | `EQ2/Core.lean` | Partial transitivity (end case) |
| `EQ2_trans_via_var` | `EQ2/Core.lean` | Partial transitivity (var case) |
| `EQ2_unfold_left` | `EQ2/Core.lean` | Left unfolding |
| `EQ2_unfold_right` | `EQ2/Core.lean` | Right unfolding |
| `EQ2_coind` | `EQ2/Core.lean` | Coinduction principle |
| `EQ2_coind_upto` | `EQ2/Core.lean` | Up-to coinduction |
| `EQ2_closure` | `EQ2/Core.lean` | Closure properties |

### EQ2Paco — `Protocol/CoTypes/EQ2Paco.lean`

Parametric coinduction (paco) for EQ2.

| Definition | Description |
|------------|-------------|
| `EQ2_paco` | Parametric accumulation for EQ2 |
| `EQ2_paco_coind` | Paco coinduction principle |
| `EQ2_paco_unfold` | Paco unfolding |

### EQ2Props — `Protocol/CoTypes/EQ2Props.lean`

| Definition | Description |
|------------|-------------|
| `EQ2_trans_wf` | **Transitivity via Bisim detour** (requires WellFormed) |

### Bisim — `Protocol/CoTypes/Bisim/Part1–10` (10 files)

Full bisimulation relation on local types.

| Definition | Description |
|------------|-------------|
| `Bisim` | Bisimulation relation |
| `Bisim_refl` | Reflexivity |
| `Bisim_symm` | Symmetry |
| `Bisim_trans` | Transitivity |
| `Bisim_implies_EQ2` | Bisim to EQ2 (WellFormed) |
| `EQ2_implies_Bisim` | EQ2 to Bisim (WellFormed) |

### Observable — `Protocol/CoTypes/Observable.lean`

| Definition | Description |
|------------|-------------|
| `UnfoldsToEnd` | Unfolds to end observable |
| `UnfoldsToVar` | Unfolds to variable observable |
| `CanSend` | Send capability observable |
| `CanRecv` | Receive capability observable |
| `ObservableRel.toEQ2` | Build EQ2 from observable agreement |
| `EQ2_send_not_UnfoldsToEnd` | Incompatibility: send vs end |
| `EQ2_send_not_UnfoldsToVar` | Incompatibility: send vs var |
| `EQ2_send_not_CanRecv` | Incompatibility: send vs recv |

### Dual — `Protocol/CoTypes/Dual.lean`

| Definition | Description |
|------------|-------------|
| `dual_involutive` | Duality is involution (`t.dual.dual = t`) |
| `dual_isGuarded` | Duality preserves guardedness |
| `dual_isContractive` | Duality preserves contractiveness |
| `freeVars_dual` | Duality preserves free variables |
| `EQ2_dual` | EQ2 respects duality |

### FullUnfold — `Protocol/CoTypes/FullUnfold.lean`

| Definition | Description |
|------------|-------------|
| `fullUnfold` | Complete mu-unfolding |
| `EQ2_iff_fullUnfold_eq` | EQ2 if and only if full unfolds are EQ2 |
| `EQ2_of_fullUnfold_eq` | Equality of full unfolds implies EQ2 |

### SubstCommBarendregt — `Protocol/CoTypes/SubstCommBarendregt/`

Barendregt substitution commutation lemma for session types. `Main.lean` is 546 lines.

### Other CoTypes Files

| File | Contents |
|------|----------|
| `CoinductiveRel.lean` | Generic coinductive relation infrastructure (`gfp`, `coind`, `unfold`, `fold`) |
| `CoinductiveRelPaco.lean` | Paco for generic coinductive relations (`paco`, `paco_acc`, `paco_mon`) |
| `Quotient.lean` | Quotient constructions on types |
| `DBBridge.lean` | De Bruijn bridge utilities |
| `Substitute.lean` | Substitution on coinductive types |

---

## 5. Coinductive Module

### LocalTypeC — `Coinductive/LocalTypeC.lean`

Coinductive local types via M-types (infinite trees).

### EQ2C — `Coinductive/EQ2C.lean`

Coinductive equality for `LocalTypeC`.

| File | Contents |
|------|----------|
| `EQ2CEnv.lean` | EQ2C with environments |
| `EQ2CMu.lean` | EQ2C under mu-binders |
| `EQ2CPaco.lean` | Parametric coinduction for EQ2C |
| `EQ2CProps.lean` | Properties of EQ2C |

### BisimDecidable — `Coinductive/BisimDecidable/Part1–3`

Decidable bisimulation for regular (finite-state) types.

### Roundtrip — `Coinductive/Roundtrip/`

Bridging inductive `LocalTypeR` and coinductive `LocalTypeC`. Five parts plus `GpacoCollapse`. `Roundtrip/Part4.lean` is 539 lines.

| Definition | Location | Description |
|------------|----------|-------------|
| `toInductive` | `Roundtrip/` | `LocalTypeC` to `LocalTypeR` |
| `toCoind` | `Roundtrip/` | `LocalTypeR` to `LocalTypeC` |
| `toCoind_toInductive_eq2ce` | `Roundtrip/` | Round-trip theorem |
| `EQ2C_mu_paco_le_paco_of_productive` | `Roundtrip/` | Mu-paco collapse under productivity |
| `EQ2CE_resolved'_implies_EQ2C` | `Roundtrip/` | Environment erasure |
| `productive_toCoind` | `Roundtrip/` | Productivity discharge for `toCoind` |
| `reachable_toCoind` | `Roundtrip/` | Reachability discharge for `toCoind` |

### Other Coinductive Files

| File | Contents |
|------|----------|
| `Bridge.lean` | Inductive-coinductive bridge |
| `ToInductive.lean` | Coinductive to inductive conversion |
| `ToCoindRegular.lean` | Coinductive conversion for regular types |
| `ToCoindInjectivity.lean` | Injectivity of coinductive conversion |
| `Regularity.lean` | Regularity properties |
| `RegularityLemmas.lean` | Supporting regularity lemmas |
| `RegularSystemBisim.lean` | Bisimulation for regular systems |
| `FiniteSystem.lean` | Finite-state system characterization |
| `Coalgebra.lean` | Coalgebraic structure |
| `Congruence.lean` | Congruence properties |
| `Observable.lean` | Observable predicates for coinductive types |
| `WellFormed.lean` | Well-formedness for coinductive types |
| `BisimHelpers.lean` | Bisimulation helper lemmas |
| `RoundtripHelpers.lean` | Round-trip helper lemmas |
| `RoundtripWIP.lean` | Additional round-trip results |
| `Dual.lean` | Duality for coinductive types |
| `ProjectC.lean` | Projection for coinductive types |

---

## 6. Main Theorems

### Harmony — `Proofs/Projection/Harmony.lean` (re-export) + `Harmony/Part1–4, Part3b`

The central correctness result: global protocol steps correspond to local environment steps.

| Theorem | Location | Description |
|---------|----------|-------------|
| `step_harmony` | `Harmony/Part1.lean:206` | Global steps correspond to local env steps |
| `trans_branches_coherent_EQ2` | `Harmony/Part1.lean:307` | Branch coherence under projection |
| `trans_produces_CProject` | `Harmony/Part1.lean:372` | `trans` output satisfies `CProject` |
| `branches_project_coherent` | `Harmony/Part1.lean:407` | Projected branches are coherent |
| `trans_substitute_unfold` | `Harmony/Part2.lean:501` | Substitution-unfolding for projection |
| `proj_trans_sender_step` | `Harmony/Part3.lean:64` | Sender case of harmony |
| `proj_trans_receiver_step` | `Harmony/Part3.lean:111` | Receiver case of harmony |
| `step_preserves_wellFormed` | `Harmony/Part3.lean:514` | Steps preserve well-formedness |
| `proj_trans_other_step` | `Harmony/Part4.lean:52` | Non-participant case (uses `ProjectableClosedWellFormed`) |

Supporting files:

| File | Contents |
|------|----------|
| `MuUnfoldLemmas.lean` | `EQ2_mu_crossed_unfold_left`, `EQ2_mu_crossed_unfold_right` |
| `StepProjection.lean` | Step-level projection lemmas |
| `SubstEndUnguarded.lean` | `subst_end_unguarded_eq2_end` |

### Determinism — `Proofs/Safety/Determinism.lean` (re-export) + `Determinism/Part1–2`

| Theorem | Location | Description |
|---------|----------|-------------|
| `local_step_det` | `Determinism/Part1.lean` | Local step determinism |
| `config_step_det` | `Determinism/Part1.lean:418` | Configuration step determinism |
| `env_step_det` | `Determinism/Part1.lean` | Environment step determinism |
| `diamond_independent` | `Determinism/Part2.lean:463` | Diamond property for independent steps |

`Determinism/Part1.lean` is the largest file at 600 lines.

### Deadlock Freedom — `Proofs/Safety/DeadlockFreedom.lean`

| Theorem | Location | Description |
|---------|----------|-------------|
| `deadlock_free` | `DeadlockFreedom.lean:234` | WellFormed implies end or exists step |
| `not_stuck` | `DeadlockFreedom.lean:247` | No stuck configurations |
| `deadlock_free_trichotomy` | `DeadlockFreedom.lean:265` | Three-way classification of states |

Progress is treated as a conditional property (`ReachesComm`) inside this file.

### Subject Reduction — `Proofs/Safety/SubjectReduction.lean`

| Theorem | Location | Description |
|---------|----------|-------------|
| `step_preserves_typing` | `SubjectReduction.lean:130` | Typing preserved under reduction |
| `step_preserves_wellformed` | `SubjectReduction.lean:153` | Well-formedness preserved under reduction |
| `other_type_preserved` | `SubjectReduction.lean:185` | Non-participant types preserved (uses `ProjectableClosedWellFormed`) |

### Semantics — `Semantics/`

| File | Contents |
|------|----------|
| `EnvStep.lean` | `ProjectedEnv`, `projEnv`, `EnvStep` -- environment step relation |
| `Environment.lean` | Environment definitions |
| `Typing.lean` | Typing judgments |

### Axiom Assumptions — `Proofs/Core/Assumptions.lean`

This file is **empty** -- no axioms are assumed.

---

## 7. Proof Strategies

### Strategy 1: EQ2 Transitivity via Bisim Detour

Direct coinductive proof of EQ2 transitivity is problematic because the coinductive hypothesis does not provide enough information to close the proof under unfolding. The solution (`EQ2_trans_wf` in `EQ2Props.lean`):

```
EQ2 a b  and  EQ2 b c
  -> Bisim a b  and  Bisim b c     (via EQ2_implies_Bisim, requires WellFormed)
  -> Bisim a c                      (via Bisim_trans)
  -> EQ2 a c                        (via Bisim_implies_EQ2)
```

This detour through the richer Bisim relation, which carries explicit simulation witnesses, makes transitivity provable. The WellFormed requirement is acceptable because all types arising from projection are well-formed.

**Key files:** `Protocol/CoTypes/EQ2Props.lean`, `Protocol/CoTypes/Bisim/Part1-10`

### Strategy 2: Mu-Paco Collapse

The coinductive round-trip between `LocalTypeR` and `LocalTypeC` uses mu-aware parametric coinduction (mu-paco). Standard paco accumulates a set of "already proven" pairs; mu-paco additionally tracks recursive binder contexts. The collapse lemma:

```
EQ2C_mu_paco_le_paco_of_productive
```

shows that mu-paco reduces to standard paco when the types involved are productive (every recursive path passes through a constructor). This bridges the inductive world (where recursion is structural) and the coinductive world (where recursion is guarded).

**Key files:** `Coinductive/Roundtrip/`, `Coinductive/Roundtrip/GpacoCollapse.lean`

### Strategy 3: Blindness for Axiom-Free Projectability

Classical MPST theory assumes a projectability axiom: that every global type can be projected for every participant. The `isBlind` predicate provides a syntactic sufficient condition:

- `branchesUniformFor`: all branches in a choice are identical for non-participants
- `isBlind`: recursive check that all choices satisfy `branchesUniformFor` for non-senders

The key theorem `projectable_of_wellFormedBlind` shows that closed + well-formed + blind global types are projectable without any axiom. Blindness is preserved by substitution (`isBlind_substitute`) and stepping (`isBlindBranches_step`).

**Key files:** `Protocol/Projection/Blind/Part1.lean`, `Protocol/Projection/Blind/Part2.lean`

### Strategy 4: CProject as Greatest Fixed Point

Projection is defined coinductively rather than inductively to handle infinite (recursive) types:

- `CProjectF` is the monotone generator functor
- `CProject = gfp CProjectF` is the greatest fixed point
- `CProject_coind`: to prove `CProject g r l`, supply a relation `R` with `R g r l` and show `R` is contained in `CProjectF R`
- `CProject_destruct`: from `CProject g r l`, obtain `CProjectF CProject g r l`

This enables proving projection properties by coinduction rather than requiring structural recursion on types.

**Key files:** `Protocol/Projection/Project/ImplBase.lean`

### Strategy 5: Harmony via Three Cases

The `step_harmony` theorem decomposes into three cases matching the three roles in a communication:

1. **Sender** (`proj_trans_sender_step`, `Harmony/Part3.lean:64`): The sender's local type takes a send step matching the global step.
2. **Receiver** (`proj_trans_receiver_step`, `Harmony/Part3.lean:111`): The receiver's local type takes a receive step matching the global step.
3. **Non-participant** (`proj_trans_other_step`, `Harmony/Part4.lean:52`): Any other role's local type is preserved (up to EQ2). This case chains through `EQ2_trans_wf` with `ProjectableClosedWellFormed` witnesses, using the blindness property to ensure the projection is unchanged.

**Key files:** `Proofs/Projection/Harmony/Part1-4`, `Proofs/Projection/Harmony/Part3b`

---

## 8. Axiom Inventory

| Category | Count | Details |
|----------|-------|---------|
| Axioms | **0** | `Proofs/Core/Assumptions.lean` is empty |
| Sorries | **0** | All proofs are complete |

The development is entirely axiom-free and sorry-free. Projectability (traditionally an axiom in MPST theory) is discharged via the blindness predicate (`projectable_of_wellFormedBlind`).

**Verification:** Both the inductive path (Protocol, Proofs) and coinductive path (Coinductive module) carry zero axioms and zero sorries.

---

## 9. Cross-Reference Index

### By Concept

| Concept | Defined In | Used By |
|---------|-----------|---------|
| `GlobalType` | `Protocol/GlobalType/Part1` | Projection, Harmony, Semantics |
| `LocalTypeR` | `Protocol/LocalTypeR/Part1` | EQ2, Bisim, Projection, Safety |
| `LocalTypeC` | `Coinductive/LocalTypeC` | Roundtrip, BisimDecidable, ProjectC |
| `EQ2` | `Protocol/CoTypes/EQ2/Core` | EQ2Props, Bisim, Harmony, ProjectProps |
| `EQ2_trans_wf` | `Protocol/CoTypes/EQ2Props` | Harmony/Part4 (non-participant case) |
| `Bisim` | `Protocol/CoTypes/Bisim/Part1` | EQ2Props (transitivity detour) |
| `CProject` | `Protocol/Projection/Project/ImplBase` | Harmony, ProjectProps, EmbedProps |
| `trans` | `Protocol/Projection/Trans/Core` | Harmony, Blind, Projectb |
| `isBlind` | `Protocol/Projection/Blind/Part1` | Harmony/Part4, Safety proofs |
| `WellFormedBlind` | `Protocol/Projection/Blind/Part1` | Harmony entry point |
| `wellFormed` | `Protocol/GlobalType/Part2` | Blind, Harmony, Safety |
| `part_of2` | `Protocol/Participation/Core` | Projection, Harmony |
| `EnvStep` | `Semantics/EnvStep` | Harmony, Safety |
| `deadlock_free` | `Proofs/Safety/DeadlockFreedom` | Top-level safety result |
| `step_harmony` | `Proofs/Projection/Harmony/Part1` | Top-level correctness result |
| `config_step_det` | `Proofs/Safety/Determinism/Part1` | Top-level determinism result |
| `step_preserves_typing` | `Proofs/Safety/SubjectReduction` | Top-level type safety result |

### By Dependency Chain

**Projection Stack:**
```
GlobalType
    |
    v
Trans  ->  Projectb  ->  Project (CProject)
    |           |              |
    v           v              v
ProjectProps  <-  Embed  <-  EmbedProps
    |
    v
Harmony
```

**Safety Stack:**
```
Harmony
    |
    v
SubjectReduction
    |
    v
Determinism + DeadlockFreedom + Progress
```

**Coinductive Stack:**
```
CoinductiveRel  ->  CoinductiveRelPaco
    |                       |
    v                       v
EQ2  ->  EQ2Paco           Bisim (Part1-10)
    |                       |
    v                       v
EQ2Props  <-----------------+
    |
    v
LocalTypeC  ->  EQ2C  ->  BisimDecidable
    |
    v
Roundtrip (Part1-5 + GpacoCollapse)
```

### By Topic

**Projection Correctness:**
1. `trans_produces_CProject` -- Trans output satisfies CProject (Harmony/Part1)
2. `projectb_sound` -- Boolean checker is sound (Projectb)
3. `CProject_implies_EQ2_trans` -- CProject relates to trans via EQ2 (Project)
4. `step_harmony` -- Central harmony result (Harmony/Part1)

**Projectability:**
1. `Projectable` -- Global projectability predicate (Project/Core)
2. `ProjectableClosedWellFormed` -- Bundle used by Harmony and SubjectReduction (Project/Core)
3. `projectable_of_wellFormedBlind` -- Axiom elimination (Blind/Part1)

**Determinism Chain:**
1. `project_deterministic` -- Projection determinism up to EQ2 (ProjectProps)
2. `config_step_det` -- Configuration step determinism (Determinism/Part1)
3. `diamond_independent` -- Diamond property (Determinism/Part2)

**EQ2 Theory:**
1. `EQ2` definition (EQ2/Core)
2. `EQ2_paco_coind` -- Paco coinduction (EQ2Paco)
3. `EQ2_trans_wf` -- Transitivity via Bisim (EQ2Props)
4. `Bisim_implies_EQ2` / `EQ2_implies_Bisim` -- Bidirectional bridge (Bisim)
5. `EQ2_dual` -- Duality respect (Dual)
6. `EQ2_iff_fullUnfold_eq` -- Full unfold characterization (FullUnfold)

**Substitution:**
1. `trans_substitute_unfold` -- Projection substitution (Harmony/Part2)
2. Barendregt lemmas (SubstCommBarendregt)
3. `isBlind_substitute` -- Blindness preserved (Blind/Part2)

**Mu-Type Handling:**
1. `fullUnfold` (FullUnfold)
2. `EQ2_mu_crossed_unfold_left/right` (MuUnfoldLemmas)
3. `subst_end_unguarded_eq2_end` (SubstEndUnguarded)

**Coinductive/Inductive Bridge:**
1. `toInductive` / `toCoind` (Roundtrip)
2. `toCoind_toInductive_eq2ce` -- Round-trip (Roundtrip)
3. `EQ2C_mu_paco_le_paco_of_productive` -- Mu-paco collapse (Roundtrip)
4. `EQ2CE_resolved'_implies_EQ2C` -- Environment erasure (Roundtrip)
5. `BisimDecidable` (BisimDecidable/Part1-3)

---

## 10. File Size Reference

Top 15 files by line count:

| Rank | File | Lines |
|------|------|-------|
| 1 | `Proofs/Safety/Determinism/Part1.lean` | 600 |
| 2 | `Protocol/GlobalType/Part5.lean` | 571 |
| 3 | `Protocol/LocalTypeConvProofs/Part3.lean` | 571 |
| 4 | `MuveImplBase.lean` | 561 |
| 5 | `Protocol/Projection/Projectb/Part4.lean` | 560 |
| 6 | `Protocol/LocalTypeDB/Preservation.lean` | 551 |
| 7 | `Protocol/CoTypes/SubstCommBarendregt/Main.lean` | 546 |
| 8 | `Coinductive/Roundtrip/Part4.lean` | 539 |
| 9 | `MuveImplParticipant.lean` | 538 |
| 10 | `Proofs/Projection/Harmony/Part3.lean` | 521 |
| 11 | `Protocol/Projection/EmbedProps.lean` | 519 |
| 12 | `Protocol/TypeContext.lean` | 518 |
| 13 | `Proofs/Projection/Harmony/Part2.lean` | 514 |
| 14 | `Protocol/LocalTypeR/Part1.lean` | 511 |
| 15 | `Proofs/Safety/Determinism/Part2.lean` | 511 |

---

## 11. Quick Navigation Guide

| Topic | Start Here |
|-------|-----------|
| Global types and their structure | `Protocol/GlobalType/Part1.lean` |
| Local types and operations | `Protocol/LocalTypeR/Part1.lean` |
| How projection works (functional) | `Protocol/Projection/Trans/Core.lean` |
| How projection works (coinductive) | `Protocol/Projection/Project/ImplBase.lean` |
| Boolean projection checker | `Protocol/Projection/Projectb/` |
| Why no projectability axiom | `Protocol/Projection/Blind/Part1.lean` |
| Coinductive equality | `Protocol/CoTypes/EQ2/Core.lean` |
| EQ2 transitivity proof | `Protocol/CoTypes/EQ2Props.lean` |
| Bisimulation theory | `Protocol/CoTypes/Bisim/Part1.lean` |
| Observable predicates | `Protocol/CoTypes/Observable.lean` |
| Duality | `Protocol/CoTypes/Dual.lean` |
| Substitution commutation | `Protocol/CoTypes/SubstCommBarendregt/Main.lean` |
| Coinductive types (M-types) | `Coinductive/LocalTypeC.lean` |
| Inductive/coinductive bridge | `Coinductive/Roundtrip/` |
| Decidable bisimulation | `Coinductive/BisimDecidable/Part1.lean` |
| Harmony theorem | `Proofs/Projection/Harmony/Part1.lean` |
| Deadlock freedom | `Proofs/Safety/DeadlockFreedom.lean` |
| Subject reduction | `Proofs/Safety/SubjectReduction.lean` |
| Determinism and diamond | `Proofs/Safety/Determinism/Part1.lean` |
| Axiom audit | `Proofs/Core/Assumptions.lean` (empty file) |
| Operational semantics | `Semantics/EnvStep.lean` |
| Mu-type unfolding | `Protocol/CoTypes/FullUnfold.lean` |
| Participation predicates | `Protocol/Participation/Core.lean` |
