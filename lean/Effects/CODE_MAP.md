# Effects Code Map

**Last Updated:** 2026-01-30

This document provides a comprehensive map of the Effects directory -- a formal verification library for asynchronous multiparty session types (MPST) with buffered communication in Lean 4.

## Table of Contents

1. [Overview](#overview)
2. [Foundational Types](#foundational-types)
3. [Type System](#type-system)
4. [Operational Semantics](#operational-semantics)
5. [Main Theorems](#main-theorems)
6. [Runtime & Monitoring](#runtime--monitoring)
7. [Supporting Infrastructure](#supporting-infrastructure)
8. [Axiom Inventory](#axiom-inventory)
9. [Cross-Reference Index](#cross-reference-index)
10. [Proof Strategies](#proof-strategies)
11. [Quick Navigation Guide](#quick-navigation-guide)

---

## Overview

**Directory Statistics:**
- Total files: 43 .lean files
- Total size: 17,083 lines of Lean code
- Axioms: 35 (see [Axiom Inventory](#axiom-inventory))
- Sorries: 0
- Largest file: Typing/Part6.lean (2,128 lines)

**Key Research Contributions:**
1. **Async buffered communication** as first-class with explicit FIFO buffers
2. **Coherence invariant** replaces traditional duality for multiparty settings
3. **Linear capability tokens** for unforgeable endpoint access
4. **Proof-carrying runtime monitor** for untrusted code execution
5. **Complete metatheory**: preservation, progress, determinism, deadlock freedom

**Architectural Layers:**
```
Layer 5: Applications      -> Examples, Simulation, Deployment
Layer 4: Metatheory        -> Preservation, Determinism, DeadlockFreedom
Layer 3: Monitoring        -> Monitor, Spatial
Layer 2: Semantics         -> Typing, Semantics, Coherence
Layer 1: Foundation        -> Basic, LocalType, Values, Environments, Process
```

---

## Foundational Types

### Basic.lean
**Location:** `Effects/Basic.lean` (185 lines)

Core abstractions for multiparty communication:

```lean
def SessionId : Type := Nat
def Role : Type := String
def Endpoint : Type := SessionId * Role

structure Edge where
  sid : SessionId
  sender : Role
  receiver : Role

def Label : Type := String
```

**RoleSet Operations:**
```lean
structure RoleSet where
  roles : List Role

def RoleSet.allEdges (rs : RoleSet) (sid : SessionId) : List Edge
def RoleSet.allEndpoints (rs : RoleSet) (sid : SessionId) : List Endpoint
```

**Design Note:** Endpoints are session-scoped, enabling multi-session reasoning. Edges are directed triples `(sid, sender, receiver)`.

---

### LocalType.lean
**Location:** `Effects/LocalType.lean` (155 lines)

**Value Types:**
```lean
inductive ValType
  | unit | bool | nat | string
  | prod (T1 T2 : ValType)
  | chan (sid : SessionId) (role : Role)
```

**Local Session Types:**
```lean
inductive LocalType
  | send (target : Role) (T : ValType) (L : LocalType)
  | recv (source : Role) (T : ValType) (L : LocalType)
  | select (target : Role) (branches : List (Label * LocalType))
  | branch (source : Role) (branches : List (Label * LocalType))
  | end_
  | var (n : Nat)           -- De Bruijn index
  | mu (body : LocalType)   -- Recursive type
```

**Key Operations:**
- `unfold : LocalType -> LocalType` -- unfold mu-type: mu(L) ~> L[var 0 := mu(L)]
- `advanceSend / advanceRecv / advanceSelect / advanceBranch` -- type advancement after communication

---

### Values.lean
**Location:** `Effects/Values.lean` (191 lines)

**Runtime Values:**
```lean
inductive Value
  | unit | bool (b : Bool) | nat (n : Nat) | string (s : String)
  | prod (v1 v2 : Value)
  | chan (endpoint : Endpoint)
```

**Linear Capability Tokens:**
```lean
structure Token where
  endpoint : Endpoint
  localType : LocalType

def LinCtx : Type := List (Endpoint * LocalType)
```

**Session ID Bounds:**
- `Value.sidLt (v : Value) (n : SessionId) : Prop` -- value contains only session IDs < n
- `sidLt_monotone` -- bounds are monotone

---

### Process.lean
**Location:** `Effects/Process.lean` (149 lines)

**Process Language:**
```lean
inductive Process
  | skip
  | seq (P Q : Process)
  | par (P Q : Process)
  | send (k : Var) (x : Var)
  | recv (k : Var) (x : Var)
  | select (k : Var) (l : Label)
  | branch (k : Var) (branches : List (Label * Process))
  | assign (x : Var) (v : Value)
  | newSession (roles : RoleSet) (f : Role -> LocalType)
```

**Configuration:**
```lean
structure Config where
  nextSid : SessionId
  store : Store
  buffers : Buffers
  proc : Process
```

---

## Type System

### Environments (Part1-Part2)
**Location:** `Effects/Environments/Part1.lean` (938 lines), `Effects/Environments/Part2.lean` (493 lines)

Re-exported via `Effects/Environments.lean`.

**Environment Types:**
```lean
def Store : Type := List (Var * Value)
def SEnv : Type := List (Var * ValType)
def GEnv : Type := List (Endpoint * LocalType)
structure DEnv                             -- RBMap-backed, canonical list representation
def Buffers : Type := List (Edge * List Value)
```

**Part1** defines lookup/update operations and initialization:
- `initBuffers (sid : SessionId) (roles : RoleSet) : Buffers`
- `initDEnv (sid : SessionId) (roles : RoleSet) : DEnv`
- Lookup/update lemmas for all five environment types

**Part2** defines session renaming:
```lean
structure SessionRenaming where
  f : SessionId -> SessionId
  inj : forall s1 s2, f s1 = f s2 -> s1 = s2

def renameEndpoint / renameEdge / renameGEnv / renameDEnv / renameBufs
```
- Renaming injectivity/commutativity lemmas
- `lookupG_rename`, `lookupD_rename`, `lookupBuf_rename` and their inverse forms

---

### Typing (Part1-Part7)
**Location:** Re-exported via `Effects/Typing.lean`. Split across Part1 (651 lines), Part2 (567 lines), Part3a (992 lines), Part3b, Part4 (478 lines), Part5 (1,632 lines), Part6 (2,128 lines), Part7 (472 lines). Part1 contains 1 axiom (`ParSplit.unique`); Part5 contains 2 axioms; Part6 contains 1 axiom (`DisjointS_preserved_TypedStep_right`).

**Part1 -- Disjointness and Splitting:**
```lean
def DisjointG (G1 G2 : GEnv) : Prop
def DisjointD (D1 D2 : DEnv) : Prop
def DisjointS (S1 S2 : SEnv) : Prop
structure ParSplit  -- environment splitting for parallel composition
def DConsistent (G : GEnv) (D : DEnv) : Prop
```
Contains 1 axiom: `ParSplit.unique`. `DEnv_ext` is proven via the canonical list representation.

**Part2 -- Process Typing Judgment:**
```lean
inductive HasTypeProcN : SessionId -> SEnv -> GEnv -> DEnv -> Process -> Prop
```
Rules for skip, seq, par, send, recv, select, branch, assign, newSession.

**Part3a/Part3b -- SEnv Append/Lookup Lemmas:**
Environment composition lemmas including `lookupD_append_left/right`, `lookupSEnv_append_left/right`.

**Part4 -- Well-Typed Configuration:**
```lean
structure WTConfigN (n : SessionId) (S : SEnv) (G : GEnv) (D : DEnv) (C : Config) : Prop where
  nextSid_eq : C.nextSid = n
  store_typed : StoreTyped G S C.store
  buffers_typed : BuffersTyped G D C.buffers
  coherent : Coherent G D
  proc_typed : HasTypeProcN n S G D C.proc
```
Inversion lemmas for each process construct.

**Part5 -- Frame Lemmas:**
`HasTypeProcPreOut` frame properties (proved; no axioms).

**Part6 -- Preservation Sub-Lemmas (2,128 lines):**
The largest file. Contains `Compatible` and preservation sub-lemmas for each step kind.

**Part7 -- Progress Helpers:**
DEnv union lemmas (`DEnvUnion_empty_right/left`) and environment append properties used by preservation and progress proofs.

---

### Coherence (Part1-Part9)
**Location:** Re-exported via `Effects/Coherence.lean`. Split across 9 parts.

The central invariant of the formalization.

**Part1 -- Core Definitions:**
```lean
def consumeOne (from_ : Role) (T : ValType) (L : LocalType) : Option LocalType
def Consume (from_ : Role) (L : LocalType) (ts : List ValType) : Option LocalType

def EdgeCoherent (G : GEnv) (D : DEnv) (edge : Edge) : Prop
def Coherent (G : GEnv) (D : DEnv) : Prop :=
  forall edge : Edge, EdgeCoherent G D edge

inductive HasTypeVal : GEnv -> Value -> ValType -> Prop
```

**Part2 -- Buffer and Store Typing:**
`BufferTyped`, `StoreTyped`.

**Part3 -- Typing Variants:**
`StoreTypedStrong`, `EdgeCoherent_updateG/D_irrelevant`.

**Part4 -- Send/Recv Coherence Preservation (601 lines):**
```lean
theorem Coherent_send_preserved  -- Coherence/Part4.lean:81
theorem Coherent_recv_preserved  -- Coherence/Part4.lean:285
```

**Part5 -- Select/Branch Coherence Preservation:**
```lean
theorem Coherent_select_preserved  -- Coherence/Part5.lean:52
theorem Coherent_branch_preserved  -- Coherence/Part5.lean:192
```

**Part6 -- Additional Helper Lemmas (507 lines)**

**Part7 -- HeadCoherent Preservation:**
`HeadCoherent_select/branch_preserved`.

**Part8 -- Initialization and ValidLabels (661 lines):**
```lean
theorem Coherent_empty           -- Coherence/Part8.lean:617
theorem initSession_coherent     -- Coherence/Part8.lean:634
```
Also: `ValidLabels_*_preserved`, `BuffersTyped_*_preserved`.

**Part9 -- Renaming and Duality:**
```lean
theorem CoherentRenaming         -- Coherence/Part9.lean:57
theorem HasTypeVal_rename
theorem BuffersTypedRenaming
def Dual
theorem Dual_implies_Coherent_empty
```

---

## Operational Semantics

### Semantics.lean
**Location:** `Effects/Semantics.lean`

**Base Steps:**
```lean
inductive StepBase : Config -> Config -> Prop
  | send    -- enqueue value to edge buffer
  | recv    -- dequeue value from edge buffer
  | select  -- enqueue label to edge buffer
  | branch  -- dequeue label, select branch
  | newSession  -- allocate fresh session
  | assign  -- update store
  | seq2    -- skip ; P ~> P
  | par_skip_left / par_skip_right
```

**Contextual Closure:**
```lean
inductive Step : Config -> Config -> Prop
  | base      -- lift StepBase
  | seq_left / seq_right   -- step under sequential composition
  | par_left / par_right   -- step under parallel composition
```

**Key Theorem:**
- `stepBase_deterministic : StepBase C C1 -> StepBase C C2 -> C1 = C2`

---

## Main Theorems

### Preservation.lean
**Location:** `Effects/Preservation.lean` (192 lines)

Contains 6 axioms stating the main safety theorems. These are the top-level claims whose proofs depend on the sub-lemmas in Typing/Part5-Part7 and Coherence/Part4-Part8.

```lean
axiom preservation_typed         -- line 107
axiom progress_send/recv/select/branch  -- lines 154-175
axiom subject_reduction          -- line 187
```

---

### Determinism.lean
**Location:** `Effects/Determinism.lean`

```lean
theorem stepBase_det             -- base step determinism
theorem diamond_independent      -- diamond property for independent steps

def IndependentActions           -- actions on disjoint sessions
theorem session_isolation        -- steps on one session don't affect others
```

---

### DeadlockFreedom.lean
**Location:** `Effects/DeadlockFreedom.lean` (490 lines)

```lean
inductive Guarded : LocalType -> Prop       -- no unproductive recursion
inductive ReachesComm : LocalType -> Prop   -- reaches a communication action

def Done (C : Config) : Prop               -- all skip, all buffers empty
def CanProgress (C : Config) : Prop        -- exists C', Step C C'
def Stuck (C : Config) : Prop              -- neither Done nor CanProgress

theorem progress                            -- WellFormed -> Done \/ CanProgress
theorem deadlock_free                       -- line 404, main deadlock freedom theorem
theorem not_stuck                           -- well-typed configs are not stuck
theorem session_isolation                   -- line 453
theorem disjoint_sessions_commute
```

---

## Runtime & Monitoring

### Monitor (Part1-Part2)
**Location:** `Effects/Monitor/Part1.lean` (477 lines), `Effects/Monitor/Part2.lean` (187 lines). Re-exported via `Effects/Monitor.lean`.

**Part1 -- Definitions:**
```lean
inductive ProtoAction
  | send (e : Endpoint) (target : Role) (T : ValType)
  | recv (e : Endpoint) (source : Role) (T : ValType)
  | select (e : Endpoint) (target : Role) (l : Label)
  | branch (e : Endpoint) (source : Role) (l : Label)

structure MonitorState where
  G : GEnv
  D : DEnv
  bufs : Buffers
  Lin : LinCtx
  supply : SessionId

inductive MonStep : MonitorState -> MonitorState -> Prop
structure WTMon (ms : MonitorState) : Prop
structure WTMonComplete (ms : MonitorState) : Prop
```
Token management lemmas.

**Part2 -- Preservation (187 lines):**
Contains 2 axioms and proven helper lemmas (token consumption, buffer/DEnv consistency, session creation).
```lean
axiom MonStep_preserves_WTMon        -- line 62
axiom newSession_preserves_WTMon     -- line 184
```

---

### Deployment (Part1, Part2a, Part2b)
**Location:** `Effects/Deployment/Part1.lean` (391 lines), `Effects/Deployment/Part2.lean` (re-export), `Effects/Deployment/Part2a.lean`, `Effects/Deployment/Part2b.lean`. Re-exported via `Effects/Deployment.lean`.

**Part1 -- Core Definitions:**
```lean
structure InterfaceType           -- what a protocol exports/imports
structure DeployedProtocol        -- bundle with all certificates
structure ProtocolBundle          -- lightweight bundle without proofs
-- linking infrastructure
```

**Part2a/Part2b -- Composition Metatheory:**
`MergeDEnv` proved. Disjoint session IDs, matching exports/imports, merged environments remain coherent.

---

### Spatial.lean
**Location:** `Effects/Spatial.lean`

```lean
inductive SpatialReq
  | netCapable (s : Site) | timeoutCapable (s : Site)
  | colocated (r1 r2 : Role) | reliableEdge (r1 r2 : Role)
  | conj (R1 R2 : SpatialReq) | top | bot

structure Topology              -- site assignment for roles
def Satisfies (topo : Topology) (R : SpatialReq) : Prop

def SpatialLe (R1 R2 : SpatialReq) : Prop
theorem spatial_le_sound        -- monotonicity: R1 <= R2 -> (topo |= R1 -> topo |= R2)
```

---

## Supporting Infrastructure

### Simulation.lean
**Location:** `Effects/Simulation.lean` (540 lines)

```lean
def stepBaseDecide (C : Config) : Option Config
def stepDecide (C : Config) : Option Config

def runSteps (C : Config) (n : Nat) : List Config
def traceSteps (C : Config) (max_steps : Nat) : List Config

-- Correctness
theorem stepDecide_sound
theorem stepDecide_complete
```

---

### Examples.lean
**Location:** `Effects/Examples.lean`

Concrete protocol examples with full well-typedness proofs:
- **PingPong**: two-party ping-pong protocol
- **TwoBuyer**: three-party buyer protocol
- Coherence, deadlock freedom, and buffer typing demonstrated

---

### Decidability.lean
**Location:** `Effects/Decidability.lean`

DecidableEq instances for Edge, Endpoint, Role, LocalType. Decidable `ReachesComm` and `Satisfies`.

---

## Axiom Inventory

35 axioms, 0 sorries. Axioms represent theorem statements whose proofs are planned but not yet mechanized.

| File | Count | Axioms |
|------|-------|--------|
| Preservation.lean | 6 | `preservation_typed`, `progress_send`, `progress_recv`, `progress_select`, `progress_branch`, `subject_reduction` |
| DeadlockFreedom.lean | 7 | `muDepth_subst_of_decide`, `reachesComm_unfold_mu`, `reachesComm_body_implies_unfold_aux`, `reachesComm_body_implies_unfold`, `reachesCommDecide_sound`, `deadlock_free`, `not_stuck` |
| Deployment/Part1.lean | 6 | `mkInitGEnv_lookup`, `mkInitGEnv_sessionsOf_of_mem`, `mkInitBufs_lookup_mem`, `mkInit_bConsistent`, `mkInit_bufsDom`, `mkInit_dConsistent` |
| Deployment/Part2b.lean | 9 | `mergeBufs_typed`, `mergeLin_valid`, `mergeLin_unique`, `link_preserves_WTMon_full`, `link_preserves_WTMon`, `link_preserves_WTMon_complete`, `link_preserves_WTMon_complete_full`, `disjoint_sessions_independent`, `compose_deadlock_free` |
| Monitor/Part2.lean | 2 | `MonStep_preserves_WTMon`, `newSession_preserves_WTMon` |
| Typing/Part1.lean | 1 | `ParSplit.unique` |
| Typing/Part5.lean | 2 | `SessionsOf_subset_of_HasTypeProcPreOut`, `updateSEnv_append_left_any` |
| Typing/Part6.lean | 1 | `DisjointS_preserved_TypedStep_right` |
| Examples.lean | 1 | `examples_stub` |

**Note:** The 4 axioms in Typing (Part1/Part5/Part6) support frame lemmas. The 6 in Preservation are top-level safety claims. The 9 in Deployment/Part2b cover composition metatheory. The `examples_stub` axiom is a placeholder.

---

## Cross-Reference Index

### By Topic

**Core Type System:**
1. `LocalType` definition -> LocalType.lean
2. `HasTypeProcN` judgment -> Typing/Part2.lean
3. `WTConfigN` well-typed config -> Typing/Part4.lean
4. `HasTypeVal` value typing -> Coherence/Part1.lean
5. `ParSplit` environment splitting -> Typing/Part1.lean

**Coherence Chain:**
1. `Consume` / `consumeOne` -> Coherence/Part1.lean
2. `EdgeCoherent` / `Coherent` -> Coherence/Part1.lean
3. `BufferTyped` / `StoreTyped` -> Coherence/Part2.lean, Part3.lean
4. `Coherent_send/recv_preserved` -> Coherence/Part4.lean
5. `Coherent_select/branch_preserved` -> Coherence/Part5.lean
6. `Coherent_empty` / `initSession_coherent` -> Coherence/Part8.lean
7. `CoherentRenaming` -> Coherence/Part9.lean

**Safety Properties:**
1. `preservation_typed` -> Preservation.lean:107 (axiom)
2. `progress_send/recv/select/branch` -> Preservation.lean:154-175 (axioms)
3. `subject_reduction` -> Preservation.lean:187 (axiom)
4. `stepBase_det` / `diamond_independent` -> Determinism.lean
5. `deadlock_free` / `not_stuck` -> DeadlockFreedom.lean (axioms)
6. `session_isolation` -> DeadlockFreedom.lean

**Runtime Infrastructure:**
1. `MonStep` monitor transitions -> Monitor/Part1.lean
2. `MonStep_preserves_WTMon` -> Monitor/Part2.lean:62
3. `newSession_preserves_WTMon` -> Monitor/Part2.lean:184
4. `stepDecide` executable simulation -> Simulation.lean
5. `DeployedProtocol` / `ProtocolBundle` -> Deployment/Part1.lean
6. `spatial_le_sound` -> Spatial.lean

### By Dependency

**Foundation Stack:**
```
Basic.lean
    |
LocalType.lean -> Values.lean
    |              |
Environments/Part1.lean -> Environments/Part2.lean
    |
Process.lean
```

**Type System Stack:**
```
Coherence/Part1-9 (defines Consume, Coherent, HasTypeVal)
    |
Typing/Part1-7 (uses Coherent in WTConfigN)
    |
Semantics.lean (operational rules)
    |
Preservation.lean (proves type safety)
```

**Metatheory Stack:**
```
Preservation.lean
    |
Determinism.lean + DeadlockFreedom.lean + Spatial.lean
```

**Runtime Stack:**
```
Typing + Coherence
    |
Monitor/Part1-2 (validates actions)
    |
Deployment/Part1, Part2a, Part2b (distributed execution)
```

---

## Proof Strategies

### 1. Coherence as Central Invariant
Traditional binary session types use endpoint duality (`L <-> L_bar`). This formalization replaces duality with **coherence**: for each directed edge, consuming the in-flight message trace from the receiver's perspective succeeds. This generalizes naturally to multiparty async settings.

### 2. Consumption Function
The `Consume` function operationally models how a receiver's local type evolves as buffered messages arrive. The key composition property -- `Consume L (ts1 ++ ts2) = (Consume L ts1).bind (fun L' => Consume L' ts2)` -- is critical for preservation.

### 3. Three-Way Edge Analysis
Coherence preservation proofs split into three cases per edge:
1. **Updated edge** -- type and trace both change
2. **Related edge** -- shares an endpoint with the updated edge
3. **Unrelated edge** -- environments unchanged, coherence trivially preserved

### 4. Canonicalized Environments
`SEnv` is list-backed. `DEnv` is RBMap-backed with a canonical list representation; lookup-based reasoning avoids ordering dependencies in environment composition proofs.

### 5. Linear Capability Tokens
Tokens are unforgeable capabilities tied to endpoints. Protocol steps consume and produce tokens, enforcing linear resource usage and preventing aliasing. The monitor validates token ownership before permitting any action.

### 6. Frame Lemmas Under Disjointness
`Step_frame_append_left` and `Step_frame_append_right` (Preservation.lean) enable compositional reasoning: a step on one part of a configuration leaves disjoint parts unchanged.

---

## Quick Navigation Guide

**Want to understand...**

- **How async MPST works?** -> Start with README.md, then Basic.lean, LocalType.lean
- **The coherence invariant?** -> Coherence/Part1.lean (`Consume`, `EdgeCoherent`, `Coherent`)
- **Coherence preservation?** -> Coherence/Part4.lean (send/recv), Part5.lean (select/branch)
- **Type system?** -> Typing/Part2.lean (`HasTypeProcN`), Typing/Part4.lean (`WTConfigN`)
- **Environment splitting?** -> Typing/Part1.lean (`ParSplit`, `DisjointG/D/S`)
- **Operational semantics?** -> Semantics.lean (`StepBase`, `Step`)
- **Type safety proof?** -> Preservation.lean, supported by Typing/Part6.lean
- **Determinism?** -> Determinism.lean (`stepBase_det`, `diamond_independent`)
- **Deadlock freedom?** -> DeadlockFreedom.lean (`Guarded`, `ReachesComm`, `deadlock_free`)
- **Runtime monitoring?** -> Monitor/Part1.lean (definitions), Monitor/Part2.lean (preservation)
- **Session renaming?** -> Environments/Part2.lean (`SessionRenaming`)
- **Testing protocols?** -> Simulation.lean and Examples.lean
- **Deployment composition?** -> Deployment/Part1.lean, Part2a.lean, Part2b.lean
- **Spatial requirements?** -> Spatial.lean (`SpatialReq`, `Topology`, `Satisfies`)
- **What is axiomatized?** -> [Axiom Inventory](#axiom-inventory) above
