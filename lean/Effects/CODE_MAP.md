# Effects Code Map

**Last Updated:** 2026-01-16

This document provides a comprehensive map of the Effects directory - a formal verification library for asynchronous multiparty session types (MPST) with buffered communication in Lean 4.

## Table of Contents

1. [Overview](#overview)
2. [Foundational Types](#foundational-types)
3. [Type System](#type-system)
4. [Operational Semantics](#operational-semantics)
5. [Coherence: The Central Invariant](#coherence-the-central-invariant)
6. [Main Theorems](#main-theorems)
7. [Runtime & Monitoring](#runtime--monitoring)
8. [Supporting Infrastructure](#supporting-infrastructure)
9. [Cross-Reference Index](#cross-reference-index)

---

## Overview

**Directory Statistics:**
- Total files: 18 .lean files + 1 README.md
- Total size: ~10,000 lines of Lean code
- Largest file: Coherence.lean (2,724 lines)
- Central innovation: Coherence invariant for async MPST

**Key Research Contributions:**
1. **Async buffered communication** as first-class with explicit FIFO buffers
2. **Coherence invariant** replaces traditional duality for multiparty settings
3. **Linear capability tokens** for unforgeable endpoint capabilities
4. **Proof-carrying runtime monitor** for untrusted code execution
5. **Complete metatheory**: Preservation, progress, determinism

**Architectural Layers:**
```
Layer 5: Applications      → Examples, Simulation, Deployment
Layer 4: Metatheory        → Preservation, Determinism, DeadlockFreedom
Layer 3: Monitoring        → Monitor, Spatial
Layer 2: Semantics         → Typing, Semantics, Coherence ★
Layer 1: Foundation        → Basic, LocalType, Values, Environments, Process
```

---

## Foundational Types

### Basic.lean
**Location:** `Effects/Basic.lean` (114 lines)

**Core Abstractions:**

```lean
-- Session and participant identifiers
def SessionId : Type := Nat
def Role : Type := String
def Endpoint : Type := SessionId × Role

-- Communication topology
structure Edge where
  sender : Endpoint
  receiver : Endpoint

def Label : Type := String
```

**RoleSet Operations:**
```lean
structure RoleSet where
  roles : List Role

def RoleSet.allEdges (rs : RoleSet) (sid : SessionId) : List Edge
  -- Generate all directed edges between roles

def RoleSet.allEndpoints (rs : RoleSet) (sid : SessionId) : List Endpoint
  -- Generate all endpoint pairs
```

**Key Theorems:**
- `allEdges_sid : ∀ e ∈ allEdges rs sid, e.sender.1 = sid ∧ e.receiver.1 = sid`
  - All edges preserve session ID

- `reverse_reverse : ∀ e : Edge, e.reverse.reverse = e`
  - Edge reversal is involution

**Design Note:** Endpoints are session-scoped, enabling multi-session reasoning.

---

### LocalType.lean
**Location:** `Effects/LocalType.lean` (155 lines)

**Value Types:**
```lean
inductive ValType
  | unit
  | bool
  | nat
  | string
  | prod (T₁ T₂ : ValType)
  | chan (sid : SessionId) (role : Role)  -- Channel capability
```

**Local Session Types:**
```lean
inductive LocalType
  | send (target : Role) (T : ValType) (L : LocalType)
  | recv (source : Role) (T : ValType) (L : LocalType)
  | select (target : Role) (branches : List (Label × LocalType))
  | branch (source : Role) (branches : List (Label × LocalType))
  | end_
  | var (n : Nat)              -- De Bruijn index
  | mu (body : LocalType)      -- Recursive type
```

**Key Operations:**

- `unfold : LocalType → LocalType`
  ```lean
  -- Unfold μ-type: μ(L) ~> L[var 0 := μ(L)]
  def unfold : LocalType → LocalType
    | .mu body => body.subst 0 (.mu body)
    | L => L
  ```

- **Predicates:**
  - `canSendTo : LocalType → Role → Prop` - Type supports send to role
  - `canRecvFrom : LocalType → Role → Prop` - Type supports receive from role
  - `canSelectTo : LocalType → Role → Prop` - Type supports select to role
  - `canBranchFrom : LocalType → Role → Prop` - Type supports branch from role

- **Type Advancement:**
  - `advanceSend : LocalType → Role → ValType → Option LocalType`
  - `advanceRecv : LocalType → Role → ValType → Option LocalType`
  - `advanceSelect : LocalType → Role → Label → Option LocalType`
  - `advanceBranch : LocalType → Role → Label → Option LocalType`

**Example Type (Two-Buyer Protocol, Buyer1's view):**
```lean
-- Buyer1 sends book title to Seller, receives quote,
-- shares quote with Buyer2, receives decision, sends choice to Seller
mu (
  send "Seller" string (
  recv "Seller" nat (
  send "Buyer2" nat (
  recv "Buyer2" bool (
  select "Seller" [
    ("buy", recv "Seller" string end_),
    ("quit", end_)
  ]
)))))
```

---

### Values.lean
**Location:** `Effects/Values.lean` (191 lines)

**Runtime Values:**
```lean
inductive Value
  | unit
  | bool (b : Bool)
  | nat (n : Nat)
  | string (s : String)
  | prod (v₁ v₂ : Value)
  | chan (endpoint : Endpoint)  -- Channel is an endpoint capability
```

**Extractors:**
```lean
def Value.sessionId? : Value → Option SessionId
  | .chan (sid, _) => some sid
  | _ => none

def Value.role? : Value → Option Role
  | .chan (_, role) => some role
  | _ => none

def Value.endpoint? : Value → Option Endpoint
  | .chan e => some e
  | _ => none

def Value.isChan : Value → Bool
  | .chan _ => true
  | _ => false
```

**Session ID Bounds:**
```lean
-- Value only contains session IDs < n
def Value.sidLt (v : Value) (n : SessionId) : Prop :=
  match v.sessionId? with
  | none => True
  | some sid => sid < n

def List.sidLt (vs : List Value) (n : SessionId) : Prop :=
  ∀ v ∈ vs, v.sidLt n
```

**Linear Capability Tokens:**
```lean
structure Token where
  endpoint : Endpoint
  localType : LocalType

def LinCtx : Type := List (Endpoint × LocalType)

-- Token management
def consumeToken (Lin : LinCtx) (e : Endpoint) : Option LinCtx
def produceToken (Lin : LinCtx) (e : Endpoint) (L : LocalType) : LinCtx
def stepToken (Lin : LinCtx) (e : Endpoint) (L' : LocalType) : Option LinCtx
```

**Key Theorems:**
- `sidLt_unit`, `sidLt_bool`, `sidLt_nat`, `sidLt_string` - Non-channel values always satisfy sidLt
- `sidLt_chan` - Channel sidLt iff its session ID is bounded
- `sidLt_prod` - Product sidLt iff both components satisfy sidLt
- `sidLt_monotone` - Session ID bounds are monotone

---

## Type System

### Environments.lean
**Location:** `Effects/Environments.lean` (695 lines)

**Environment Types:**

```lean
-- Runtime store: variable bindings
def Store : Type := List (Var × Value)

-- Static type environment: variable types (permutation-invariant)
def SEnv : Type := RBMap Var ValType compare

-- Global endpoint environment: current session types
def GEnv : Type := List (Endpoint × LocalType)

-- In-flight message trace environment (permutation-invariant)
def DEnv : Type := RBMap Edge (List ValType) compare

-- Runtime message buffers
def Buffers : Type := List (Edge × List Value)
```

**Lookup/Update Lemmas (×5 environments):**

For each environment type (Store, Buffers, GEnv, DEnv):
- `lookup_update_eq : (env.update k v).lookup k = v`
  - Update then lookup same key returns updated value

- `lookup_update_neq : k₁ ≠ k₂ → (env.update k₁ v).lookup k₂ = env.lookup k₂`
  - Update different key preserves other lookups

**Session Initialization:**
```lean
-- Initialize empty buffers for all directed edges in a session
def initBuffers (sid : SessionId) (roles : RoleSet) : Buffers :=
  (RoleSet.allEdges sid roles).map fun e => (e, [])

-- Initialize empty type traces for all directed edges
def initDEnv (sid : SessionId) (roles : RoleSet) : DEnv :=
  (RoleSet.allEdges sid roles).foldl (fun env e => env.insert e []) RBMap.empty
```

**Key Initialization Theorems:**
- `initBuffers_lookup_mem : e ∈ allEdges sid roles → initBuffers sid roles.lookup e = some []`
- `initBuffers_lookup_none : e.sid ≠ sid → initBuffers sid roles.lookup e = none`
- `initDEnv_lookup_mem : e ∈ allEdges sid roles → lookupD (initDEnv sid roles) e = []`
- `initDEnv_lookup_none : e.sid ≠ sid → lookupD (initDEnv sid roles) e = []`

**Session Renaming Infrastructure:**

Critical for multi-session reasoning and session creation:

```lean
structure SessionRenaming where
  f : SessionId → SessionId
  inj : ∀ s1 s2, f s1 = f s2 → s1 = s2

def renameValType (ρ : SessionRenaming) : ValType → ValType
def renameLocalType (ρ : SessionRenaming) : LocalType → LocalType
def renameValue (ρ : SessionRenaming) : Value → Value

def renameEndpoint (ρ : SessionRenaming) (e : Endpoint) : Endpoint :=
  { sid := ρ.f e.sid, role := e.role }

def renameEdge (ρ : SessionRenaming) (e : Edge) : Edge :=
  { sid := ρ.f e.sid, sender := e.sender, receiver := e.receiver }

def renameGEnv (ρ : SessionRenaming) (G : GEnv) : GEnv :=
  G.map fun (e, L) => (renameEndpoint ρ e, renameLocalType ρ L)

def renameDEnv (ρ : SessionRenaming) (D : DEnv) : DEnv :=
  D.map fun (e, ts) => (renameEdge ρ e, ts.map (renameValType ρ))

def renameBufs (ρ : SessionRenaming) (bufs : Buffers) : Buffers :=
  bufs.map fun (e, buf) => (renameEdge ρ e, buf.map (renameValue ρ))
```

**Renaming Theorems:**
- `renameValType_inj`, `renameValType_beq` (injectivity + BEq preservation)
- `renameEndpoint_inj`, `renameEdge_inj` (injectivity on endpoints/edges)
- `lookupG_rename : lookupG (renameGEnv ρ G) (renameEndpoint ρ e) = (lookupG G e).map (renameLocalType ρ)`
- `lookupD_rename : lookupD (renameDEnv ρ D) (renameEdge ρ e) = (lookupD D e).map (renameValType ρ)`
- `lookupBuf_rename : lookupBuf (renameBufs ρ bufs) (renameEdge ρ e) = (lookupBuf bufs e).map (renameValue ρ)`
- `lookupG_rename_inv` (preimage endpoint + renamed local type)
- `lookupD_rename_inv`, `lookupBuf_rename_inv` (preimage edge for non-empty lookups)

**Design Insight:** Renaming is essential for creating fresh sessions without collision.

---

### Typing.lean
**Location:** `Effects/Typing.lean` (1,346 lines)

**Disjointness Predicates:**

```lean
-- No endpoint overlap
def DisjointG (G₁ G₂ : GEnv) : Prop :=
  ∀ e, (G₁ e ≠ end_ → G₂ e = end_) ∧ (G₂ e ≠ end_ → G₁ e = end_)

-- No edge overlap (both have empty traces)
def DisjointD (D₁ D₂ : DEnv) : Prop :=
  ∀ edge, (D₁ edge ≠ [] → D₂ edge = []) ∧ (D₂ edge ≠ [] → D₁ edge = [])

-- No variable overlap
def DisjointS (S₁ S₂ : SEnv) : Prop :=
  ∀ x, S₁ x = none ∨ S₂ x = none

-- Footprint disjointness (for parallel composition)
def DisjointW (P₁ P₂ : Process) : Prop :=
  -- P₁ and P₂ access disjoint variables and endpoints
```

**Process Typing Judgment:**

```lean
inductive HasTypeProcN : SessionId → SEnv → GEnv → DEnv → Process → Prop
  | skip : HasTypeProcN n S ∅ ∅ .skip

  | seq {S₁ S₂ G₁ G₂ D₁ D₂ P Q} :
      HasTypeProcN n S₁ G₁ D₁ P →
      HasTypeProcN n S₂ G₂ D₂ Q →
      HasTypeProcN n (S₁ ∪ S₂) (G₁ ∪ G₂) (D₁ ∪ D₂) (P ; Q)

  | par {S₁ S₂ G₁ G₂ D₁ D₂ P Q} :
      HasTypeProcN n S₁ G₁ D₁ P →
      HasTypeProcN n S₂ G₂ D₂ Q →
      DisjointG G₁ G₂ →
      DisjointD D₁ D₂ →
      DisjointS S₁ S₂ →
      DisjointW P Q →
      HasTypeProcN n (S₁ ∪ S₂) (G₁ ∪ G₂) (D₁ ∪ D₂) (P ∥ Q)

  | send {e target T L x} :
      S k = .chan e →
      G e = .send target T L →
      S x = T →
      HasTypeProcN n S (G.update e L) D (send k x)

  | recv {e source T L x} :
      S k = .chan e →
      G e = .recv source T L →
      HasTypeProcN n (S.update x T) (G.update e L) D (recv k x)

  | select {e target ℓ L} :
      S k = .chan e →
      G e = .select target branches →
      (ℓ, L) ∈ branches →
      HasTypeProcN n S (G.update e L) D (select k ℓ)

  | branch {e source branches} :
      S k = .chan e →
      G e = .branch source branches →
      (∀ ℓ L ∈ branches, HasTypeProcN n Sℓ Gℓ Dℓ Pℓ) →
      HasTypeProcN n (⋃ Sℓ) (G.update e (⋃ Gℓ)) (⋃ Dℓ)
        (branch k [(ℓ₁, P₁), ..., (ℓₙ, Pₙ)])

  | assign {x v T} :
      v.sidLt n →
      HasTypeVal ∅ v T →
      HasTypeProcN n (S.update x T) ∅ ∅ (assign x v)

  | newSession {roles f P} :
      (∀ r ∈ roles, ∃ L, f r = L ∧ HasTypeProcN (n+1) Sᵣ Gᵣ Dᵣ Pᵣ) →
      HasTypeProcN n (⋃ Sᵣ) (⋃ Gᵣ.rename) (⋃ Dᵣ.rename) (newSession roles f)
```

**Well-Typed Configuration:**

```lean
structure WTConfigN (n : SessionId) (S : SEnv) (G : GEnv) (D : DEnv) (C : Config) : Prop where
  nextSid_eq : C.nextSid = n
  store_typed : StoreTyped G S C.store
  buffers_typed : BuffersTyped G D C.buffers
  coherent : Coherent G D                    -- ★ Central invariant
  proc_typed : HasTypeProcN n S G D C.proc
```

**Inversion Lemmas (~200 lines):**

Extract typing facts from typed processes:
- `inversion_send : HasTypeProcN n S G D (send k x) → ∃ e target T L, ...`
- `inversion_recv : HasTypeProcN n S G D (recv k x) → ∃ e source T L, ...`
- `inversion_select : HasTypeProcN n S G D (select k ℓ) → ∃ e target branches L, ...`
- `inversion_branch : HasTypeProcN n S G D (branch k bs) → ∃ e source branches, ...`
- `inversion_newSession : HasTypeProcN n S G D (newSession roles f) → ...`

---

## Operational Semantics

### Process.lean
**Location:** `Effects/Process.lean` (149 lines)

**Process Language:**

```lean
inductive Process
  | skip
  | seq (P Q : Process)
  | par (P Q : Process)
  | send (k : Var) (x : Var)                    -- send x on channel k
  | recv (k : Var) (x : Var)                    -- receive into x from channel k
  | select (k : Var) (ℓ : Label)                -- send label ℓ on k
  | branch (k : Var) (branches : List (Label × Process))  -- receive label, branch
  | assign (x : Var) (v : Value)                -- non-linear assignment
  | newSession (roles : RoleSet) (f : Role → LocalType)  -- create session
```

**Configuration:**

```lean
structure Config where
  nextSid : SessionId      -- Fresh session ID counter
  store : Store            -- Variable bindings
  buffers : Buffers        -- FIFO message queues
  proc : Process           -- Current process
```

---

### Semantics.lean
**Location:** `Effects/Semantics.lean` (358 lines)

**Base Operational Steps:**

```lean
inductive StepBase : Config → Config → Prop
  | send {k x e target T L v} :
      store k = .chan e →
      store x = v →
      G e = .send target T L →
      StepBase ⟨n, store, bufs, send k x⟩
               ⟨n, store, bufs.enqueue edge v, skip⟩
      where edge = ⟨e, (e.1, target)⟩

  | recv {k x e source T L v} :
      store k = .chan e →
      G e = .recv source T L →
      bufs edge = v :: rest →
      StepBase ⟨n, store, bufs, recv k x⟩
               ⟨n, store.update x v, bufs.update edge rest, skip⟩
      where edge = ⟨(e.1, source), e⟩

  | select {k e target ℓ L} :
      store k = .chan e →
      G e = .select target branches →
      (ℓ, L) ∈ branches →
      StepBase ⟨n, store, bufs, select k ℓ⟩
               ⟨n, store, bufs.enqueue edge (.label ℓ), skip⟩
      where edge = ⟨e, (e.1, target)⟩

  | branch {k e source ℓ P} :
      store k = .chan e →
      G e = .branch source branches →
      bufs edge = .label ℓ :: rest →
      (ℓ, P) ∈ branches →
      StepBase ⟨n, store, bufs, branch k branches⟩
               ⟨n, store, bufs.update edge rest, P⟩
      where edge = ⟨(e.1, source), e⟩

  | newSession {roles f} :
      StepBase ⟨n, store, bufs, newSession roles f⟩
               ⟨n+1, store', bufs', P'⟩
      where
        store' = store.extend (allocate_channels n roles)
        bufs' = bufs ∪ initBuffers (allEdges roles n)
        P' = compose_roles roles f

  | assign {x v} :
      StepBase ⟨n, store, bufs, assign x v⟩
               ⟨n, store.update x v, bufs, skip⟩

  -- Structural rules
  | seq2 {P} : StepBase ⟨n, store, bufs, skip ; P⟩ ⟨n, store, bufs, P⟩
  | par_skip_left {Q} : StepBase ⟨n, store, bufs, skip ∥ Q⟩ ⟨n, store, bufs, Q⟩
  | par_skip_right {P} : StepBase ⟨n, store, bufs, P ∥ skip⟩ ⟨n, store, bufs, P⟩
```

**Contextual Steps:**

```lean
inductive Step : Config → Config → Prop
  | base {C C'} : StepBase C C' → Step C C'
  | seq_left {C C' P Q} : Step ⟨n, store, bufs, P⟩ C' → Step ⟨n, store, bufs, P ; Q⟩ ⟨..., C'.proc ; Q⟩
  | seq_right {C C' P Q} : Step ⟨n, store, bufs, Q⟩ C' → Step ⟨n, store, bufs, P ; Q⟩ ⟨..., P ; C'.proc⟩
  | par_left {C C' P Q} : Step ⟨n, store, bufs, P⟩ C' → Step ⟨n, store, bufs, P ∥ Q⟩ ⟨..., C'.proc ∥ Q⟩
  | par_right {C C' P Q} : Step ⟨n, store, bufs, Q⟩ C' → Step ⟨n, store, bufs, P ∥ Q⟩ ⟨..., P ∥ C'.proc⟩
```

**Key Theorems:**

- `stepBase_deterministic : StepBase C C₁ → StepBase C C₂ → C₁ = C₂`
  - Base steps are deterministic (except `par skip skip` reduction order)

- `send_can_step : store k = .chan e → G e = .send target T L → store x = v → ∃ C', StepBase C C'`
  - Send actions can always step if preconditions met

- `recv_can_step : store k = .chan e → G e = .recv source T L → bufs edge ≠ [] → ∃ C', StepBase C C'`
  - Receive actions can step if buffer non-empty

---

## Coherence: The Central Invariant

### Coherence.lean ★
**Location:** `Effects/Coherence.lean` (2,724 lines - largest file)

This is the **core contribution** of the Effects library.

**The Coherence Problem:**

Traditional binary session types use **endpoint duality**: `L ⊥ L̄` ensures type-safe communication. In multiparty settings with async buffers, duality doesn't suffice because:
1. Messages can arrive out of order from different senders
2. Buffers accumulate messages from multiple sources
3. Local types must track expected messages from specific roles

**The Coherence Solution:**

For each directed edge `e = (sender_endpoint → receiver_endpoint)`:
- Track **in-flight messages** as a type trace `D[e] : List ValType`
- Receiver's local type must be able to **consume** all in-flight messages in order
- `Coherent(G, D)` ensures this consumption property holds globally

**Core Consumption Function:**

```lean
-- Consume one message of type T from role r
def consumeOne (from_ : Role) (T : ValType) (L : LocalType) : Option LocalType :=
  match L with
  | .recv from_ T L' => some L'  -- Matches expected receive
  | _ => none                     -- Type error

-- Consume a list of message types
def Consume (from_ : Role) (L : LocalType) (ts : List ValType) : Option LocalType :=
  match ts with
  | [] => some L
  | T :: ts' =>
      match consumeOne from_ T L with
      | some L' => Consume from_ L' ts'
      | none => none
```

**Edge Coherence:**

```lean
def EdgeCoherent (G : GEnv) (D : DEnv) (edge : Edge) : Prop :=
  let sender := edge.sender
  let receiver := edge.receiver
  let sender_role := sender.2
  let trace := D edge
  -- Receiver can consume all in-flight messages from sender
  ∃ L', Consume sender_role (G receiver) trace = some L'
```

**Full Coherence:**

```lean
def Coherent (G : GEnv) (D : DEnv) : Prop :=
  ∀ edge : Edge, EdgeCoherent G D edge
```

**Critical Consumption Lemmas:**

```lean
-- Appending to trace corresponds to eventual reception
theorem Consume_append (from_ : Role) (L : LocalType) (ts₁ ts₂ : List ValType) :
    Consume from_ L (ts₁ ++ ts₂) =
    (Consume from_ L ts₁).bind (fun L' => Consume from_ L' ts₂)

-- Cons version
theorem Consume_cons (from_ : Role) (L : LocalType) (T : ValType) (ts : List ValType) :
    Consume from_ L (T :: ts) =
    (consumeOne from_ T L).bind (fun L' => Consume from_ L' ts)

-- Empty trace preservation
theorem Consume_nil (from_ : Role) (L : LocalType) :
    Consume from_ L [] = some L
```

**Renaming Preservation (new):**
- `consumeOne_rename`, `Consume_rename` (renaming commutes with consumption)
- `CoherentRenaming` (coherence preserved under `renameGEnv`/`renameDEnv`)
- `HasTypeVal_rename` (values/types rename consistently)
- `BuffersTypedRenaming` (buffers/traces rename consistently)

**Coherence Shortcut Lemmas:**

These solve critical edge cases where receiver's type doesn't match the sender:

```lean
-- If receiver has send type, trace must be empty
theorem trace_empty_when_send_receiver
    (G : GEnv) (D : DEnv) (edge : Edge)
    (hCoherent : EdgeCoherent G D edge)
    (hSend : G edge.receiver = .send target T L) :
    D edge = []

-- If receiver expects recv from r but edge has different sender, trace empty
theorem trace_empty_when_recv_other_sender
    (G : GEnv) (D : DEnv) (edge : Edge)
    (hCoherent : EdgeCoherent G D edge)
    (hRecv : G edge.receiver = .recv expected_source T L)
    (hDiff : edge.sender.2 ≠ expected_source) :
    D edge = []

-- Similar for branch types
theorem trace_empty_when_branch_other_sender
    (G : GEnv) (D : DEnv) (edge : Edge)
    (hCoherent : EdgeCoherent G D edge)
    (hBranch : G edge.receiver = .branch expected_source branches)
    (hDiff : edge.sender.2 ≠ expected_source) :
    D edge = []
```

**Value Typing:**

```lean
inductive HasTypeVal : GEnv → Value → ValType → Prop
  | unit {G} : HasTypeVal G .unit .unit
  | bool {G b} : HasTypeVal G (.bool b) .bool
  | nat {G n} : HasTypeVal G (.nat n) .nat
  | string {G s} : HasTypeVal G (.string s) .string
  | prod {G v₁ v₂ T₁ T₂} :
      HasTypeVal G v₁ T₁ →
      HasTypeVal G v₂ T₂ →
      HasTypeVal G (.prod v₁ v₂) (.prod T₁ T₂)
  | chan {G e sid role} :
      e = (sid, role) →
      G e ≠ end_ →
      HasTypeVal G (.chan e) (.chan sid role)
```

**Value Typing Theorems:**

```lean
-- Each value has unique type
theorem HasTypeVal_unique {G v T₁ T₂} :
    HasTypeVal G v T₁ → HasTypeVal G v T₂ → T₁ = T₂

-- Typing is monotone under GEnv extension
theorem HasTypeVal_mono {G₁ G₂ v T} :
    (∀ e, G₁ e ≠ end_ → G₂ e = G₁ e) →
    HasTypeVal G₁ v T →
    HasTypeVal G₂ v T

-- Channel value extraction
theorem HasTypeVal_chan_inv {G v sid role} :
    HasTypeVal G v (.chan sid role) → ∃ e, v = .chan e ∧ e = (sid, role)
```

**Buffer Typing:**

```lean
def BufferTyped (G : GEnv) (D : DEnv) (bufs : Buffers) (edge : Edge) : Prop :=
  let trace := D edge
  let buffer := bufs edge
  -- Buffer length matches trace length
  buffer.length = trace.length ∧
  -- Each buffer value has corresponding trace type
  ∀ i v T, buffer.get? i = some v → trace.get? i = some T → HasTypeVal G v T
```

**Store Typing:**

```lean
def StoreTyped (G : GEnv) (S : SEnv) (store : Store) : Prop :=
  ∀ x T, S x = some T →
    match T with
    | .chan sid role =>
        ∃ e, store x = .chan e ∧ e = (sid, role) ∧ G e ≠ end_
    | _ =>
        HasTypeVal G (store x) T
```

**Advanced Coherence Properties:**

```lean
-- Buffer head type matches receiver's expected type
def HeadCoherent (G : GEnv) (D : DEnv) (bufs : Buffers) (edge : Edge) : Prop :=
  match bufs edge, D edge with
  | v :: _, T :: _ =>
      match G edge.receiver with
      | .recv edge.sender.2 T' L => T = T' ∧ HasTypeVal G v T
      | _ => False
  | [], [] => True
  | _, _ => False

-- Branch labels in buffers are valid for receiver's branch type
def ValidLabels (G : GEnv) (bufs : Buffers) (edge : Edge) : Prop :=
  match bufs edge with
  | .label ℓ :: _ =>
      match G edge.receiver with
      | .branch edge.sender.2 branches => ∃ L, (ℓ, L) ∈ branches
      | _ => False
  | _ => True

-- Receiver ready to consume next message
def SendReady (G : GEnv) (edge : Edge) : Prop :=
  ∃ T L, G edge.receiver = .recv edge.sender.2 T L

def SelectReady (G : GEnv) (edge : Edge) : Prop :=
  ∃ branches, G edge.receiver = .branch edge.sender.2 branches
```

**Why Coherence Works:**

1. **Send action**: Enqueues `v : T` to buffer, appends `T` to trace
   - By `Consume_append`, consuming `trace ++ [T]` = consuming trace then consuming `[T]`
   - Sender's type advances from `send target T L` to `L`
   - Coherence preserved if receiver can eventually consume `T`

2. **Recv action**: Dequeues `v : T` from buffer, removes `T` from trace head
   - By `Consume_cons`, consuming `T :: trace` = consuming `[T]` then consuming `trace`
   - Receiver's type advances from `recv source T L` to `L`
   - Coherence preserved by construction

3. **Edge case shortcuts**: When receiver doesn't expect message from edge's sender, trace must be empty (by shortcut lemmas), so coherence trivially holds

---

## Main Theorems

### Preservation.lean
**Location:** `Effects/Preservation.lean` (533 lines)

**Subject Reduction (Preservation):**

```lean
theorem preservation
    (n : SessionId) (S : SEnv) (G : GEnv) (D : DEnv) (C C' : Config)
    (hWT : WTConfigN n S G D C)
    (hStep : Step C C') :
    ∃ n' S' G' D', WTConfigN n' S' G' D' C'
```

**Meaning:** Well-typed configurations remain well-typed after taking a step.

**Key Helper Lemmas:**

```lean
-- Store typing preserved on non-channel update
theorem StoreTyped_update_nonChan {G S store x v T} :
    StoreTyped G S store →
    ¬ T.isChan →
    HasTypeVal G v T →
    StoreTyped G (S.update x T) (store.update x v)

-- Buffer typing preserved when enqueuing well-typed value
theorem BuffersTyped_enqueue {G D bufs edge v T} :
    BuffersTyped G D bufs edge →
    HasTypeVal G v T →
    BuffersTyped G (D.update edge (D edge ++ [T]))
                   (bufs.update edge (bufs edge ++ [v])) edge

-- Buffer typing preserved when dequeuing
theorem BuffersTyped_dequeue {G D bufs edge v T rest_trace rest_buf} :
    BuffersTyped G D bufs edge →
    bufs edge = v :: rest_buf →
    D edge = T :: rest_trace →
    BuffersTyped G (D.update edge rest_trace)
                   (bufs.update edge rest_buf) edge

-- Coherence preserved through send
theorem coherent_after_send {G D edge sender_e T L v} :
    Coherent G D →
    G sender_e = .send target T L →
    HasTypeVal G v T →
    Coherent (G.update sender_e L) (D.update edge (D edge ++ [T]))

-- Coherence preserved through recv
theorem coherent_after_recv {G D edge receiver_e source T L rest} :
    Coherent G D →
    G receiver_e = .recv source T L →
    D edge = T :: rest →
    Coherent (G.update receiver_e L) (D.update edge rest)
```

**Proof Strategy:**
1. Induct on step derivation
2. For each step kind, update S, G, D appropriately
3. Use helper lemmas to show each WTConfigN component preserved
4. Coherence preservation is most complex - requires careful edge analysis

---

### Determinism.lean
**Location:** `Effects/Determinism.lean` (360 lines)

**Determinism of Base Steps:**

```lean
theorem stepBase_det {C C₁ C₂} :
    StepBase C C₁ → StepBase C C₂ → C₁ = C₂
```

**Exception:** `par skip skip` can reduce to `skip` in two ways (left or right first).

**Branch Label Uniqueness:**

```lean
theorem uniqueBranchLabelsList (branches : List (Label × Process)) :
    ∀ ℓ P₁ P₂, (ℓ, P₁) ∈ branches → (ℓ, P₂) ∈ branches → P₁ = P₂

theorem mem_branch_unique_label {branches ℓ P₁ P₂} :
    (ℓ, P₁) ∈ branches → (ℓ, P₂) ∈ branches → P₁ = P₂
```

**Independent Actions:**

```lean
-- Actions on disjoint sessions are independent
def IndependentActions (step₁ step₂ : Config → Config → Prop) : Prop :=
  ∀ C C₁ C₂,
    step₁ C C₁ →
    step₂ C C₂ →
    sessions_disjoint C₁ C₂ →
    ∃ C', step₂ C₁ C' ∧ step₁ C₂ C'

-- Diamond property for independent steps
theorem diamond_independent {step₁ step₂} :
    IndependentActions step₁ step₂ →
    ∀ C C₁ C₂, step₁ C C₁ → step₂ C C₂ →
      ∃ C', step₂ C₁ C' ∧ step₁ C₂ C'
```

---

### DeadlockFreedom.lean
**Location:** `Effects/DeadlockFreedom.lean` (574 lines)

**Type Guardedness:**

```lean
-- Type eventually performs an observable action
inductive Guarded : LocalType → Prop
  | send : Guarded (.send r T L)
  | recv : Guarded (.recv r T L)
  | select : Guarded (.select r bs)
  | branch : Guarded (.branch r bs)
  | mu : Guarded L → Guarded (.mu L)
  | end_ : Guarded .end_
```

**Reachability:**

```lean
-- Type can reach a communication action
inductive ReachesComm : LocalType → Prop
  | send : ReachesComm (.send r T L)
  | recv : ReachesComm (.recv r T L)
  | select : ReachesComm (.select r bs)
  | branch : ReachesComm (.branch r bs)
  | mu : ReachesComm L → ReachesComm (.mu L)

-- Decidable checker
def reachesCommDecide : LocalType → Bool
  | .send _ _ _ => true
  | .recv _ _ _ => true
  | .select _ _ => true
  | .branch _ _ => true
  | .mu L => reachesCommDecide L
  | .end_ => false
  | .var _ => false
```

**Configuration States:**

```lean
-- Configuration has terminated
def Done (C : Config) : Prop :=
  C.proc = .skip ∧ (∀ edge, C.buffers edge = [])

-- Configuration can take a step
def CanProgress (C : Config) : Prop :=
  ∃ C', Step C C'

-- Configuration is stuck (neither done nor can progress)
def Stuck (C : Config) : Prop :=
  ¬ Done C ∧ ¬ CanProgress C
```

**Progress Theorems:**

```lean
-- Well-typed configs with guarded types can progress or are done
theorem progress {n S G D C} :
    WTConfigN n S G D C →
    (∀ e, Guarded (G e)) →
    Done C ∨ CanProgress C

-- More specific: if all endpoints reach communication, can progress
theorem progress_reachesComm {n S G D C} :
    WTConfigN n S G D C →
    (∀ e, G e ≠ end_ → ReachesComm (G e)) →
    Done C ∨ CanProgress C
```

---

## Runtime & Monitoring

### Monitor.lean
**Location:** `Effects/Monitor.lean` (928 lines)

**Proof-Carrying Runtime Monitor** for untrusted code execution.

**Protocol Actions:**

```lean
inductive ProtoAction
  | send (e : Endpoint) (target : Role) (T : ValType)
  | recv (e : Endpoint) (source : Role) (T : ValType)
  | select (e : Endpoint) (target : Role) (ℓ : Label)
  | branch (e : Endpoint) (source : Role) (ℓ : Label)
```

**Monitor State:**

```lean
structure MonitorState where
  G : GEnv                      -- Current local types
  D : DEnv                      -- In-flight message traces
  bufs : Buffers                -- Runtime buffers
  Lin : LinCtx                  -- Linear capability tokens
  supply : SessionId            -- Fresh session ID supply
```

**Monitor Transition:**

```lean
inductive MonStep : MonitorState → ProtoAction → MonitorState → Prop
  | send {e target T L token v} :
      -- Validate action
      (e, .send target T L) ∈ Mon.Lin →
      -- Consume token
      let Lin' := consumeToken Mon.Lin (e, .send target T L)
      -- Update environments
      let G' := Mon.G.update e L
      let D' := Mon.D.update edge (Mon.D edge ++ [T])
      let bufs' := Mon.bufs.enqueue edge v
      -- Produce new token
      let Lin'' := produceToken Lin' (e, L)
      MonStep Mon (.send e target T) ⟨G', D', bufs', Lin'', Mon.supply⟩
      where edge = ⟨e, (e.1, target)⟩

  | recv {e source T L v rest} :
      (e, .recv source T L) ∈ Mon.Lin →
      Mon.bufs edge = v :: rest →
      Mon.D edge = T :: rest_trace →
      let Lin' := consumeToken Mon.Lin (e, .recv source T L)
      let G' := Mon.G.update e L
      let D' := Mon.D.update edge rest_trace
      let bufs' := Mon.bufs.update edge rest
      let Lin'' := produceToken Lin' (e, L)
      MonStep Mon (.recv e source T) ⟨G', D', bufs', Lin'', Mon.supply⟩
      where edge = ⟨(e.1, source), e⟩

  | select {e target ℓ L} :
      (e, .select target branches) ∈ Mon.Lin →
      (ℓ, L) ∈ branches →
      let Lin' := consumeToken Mon.Lin (e, .select target branches)
      let G' := Mon.G.update e L
      let D' := Mon.D.update edge (Mon.D edge ++ [.label])
      let bufs' := Mon.bufs.enqueue edge (.label ℓ)
      let Lin'' := produceToken Lin' (e, L)
      MonStep Mon (.select e target ℓ) ⟨G', D', bufs', Lin'', Mon.supply⟩
      where edge = ⟨e, (e.1, target)⟩

  | branch {e source ℓ L rest} :
      (e, .branch source branches) ∈ Mon.Lin →
      Mon.bufs edge = .label ℓ :: rest →
      (ℓ, L) ∈ branches →
      let Lin' := consumeToken Mon.Lin (e, .branch source branches)
      let G' := Mon.G.update e L
      let D' := Mon.D.update edge (tail Mon.D edge)
      let bufs' := Mon.bufs.update edge rest
      let Lin'' := produceToken Lin' (e, L)
      MonStep Mon (.branch e source ℓ) ⟨G', D', bufs', Lin'', Mon.supply⟩
      where edge = ⟨(e.1, source), e⟩
```

**Key Monitor Theorems:**

```lean
-- Monitor transitions preserve coherence
theorem MonStep_preserves_coherent {Mon action Mon'} :
    MonStep Mon action Mon' →
    Coherent Mon.G Mon.D →
    Coherent Mon'.G Mon'.D

-- Monitor validates only type-safe actions
theorem MonStep_soundness {Mon action Mon'} :
    MonStep Mon action Mon' →
    ∃ C C', WTConfigN Mon.supply S Mon.G Mon.D C ∧
            Step C C' ∧
            WTConfigN Mon'.supply S' Mon'.G Mon'.D C'

-- Linear tokens prevent aliasing
theorem Lin_unique_endpoint {Lin e L₁ L₂} :
    (e, L₁) ∈ Lin → (e, L₂) ∈ Lin → L₁ = L₂
```

**Usage Pattern:**
1. Create monitor with initial session types and tokens
2. Untrusted code requests actions
3. Monitor validates each action against current types and tokens
4. Valid actions update monitor state; invalid actions rejected
5. Linear tokens ensure endpoint capabilities aren't duplicated

---

### Spatial.lean
**Location:** `Effects/Spatial.lean` (364 lines)

**Session Isolation:**

```lean
-- Two sessions are disjoint
def SessionsDisjoint (sid₁ sid₂ : SessionId) (G : GEnv) : Prop :=
  ∀ e, e.1 = sid₁ → G e = end_ ∨ e.1 ≠ sid₂

-- Step on one session doesn't affect other session
theorem spatial_independence {C C' sid₁ sid₂} :
    Step C C' →
    SessionsDisjoint sid₁ sid₂ C.G →
    -- Endpoints in sid₂ unchanged
    ∀ e, e.1 = sid₂ → C'.G e = C.G e
```

**Locality Lemmas:**

```lean
-- GEnv update preserves other sessions
theorem GEnv_update_preserves_other_sessions {G e L sid} :
    e.1 ≠ sid →
    ∀ e', e'.1 = sid → (G.update e L) e' = G e'

-- DEnv update preserves other sessions
theorem DEnv_update_preserves_other_sessions {D edge trace sid} :
    edge.sender.1 ≠ sid →
    edge.receiver.1 ≠ sid →
    ∀ edge', edge'.sender.1 = sid ∨ edge'.receiver.1 = sid →
      (D.update edge trace) edge' = D edge'
```

---

### Deployment.lean
**Location:** `Effects/Deployment.lean` (546 lines)

**Multi-Node Deployment:**

```lean
-- Node identifier
def NodeId : Type := Nat

-- Deployment topology: which endpoints run on which nodes
def Topology : Type := Endpoint → NodeId

-- Cross-node message
structure NetworkMessage where
  from_node : NodeId
  to_node : NodeId
  edge : Edge
  payload : Value

-- Distributed configuration
structure DistConfig where
  nodes : NodeId → Config              -- Per-node local configuration
  network : List NetworkMessage        -- In-flight cross-node messages
  topology : Topology                  -- Endpoint placement
```

**Distributed Step:**

```lean
inductive DistStep : DistConfig → DistConfig → Prop
  | local_step {nid C C'} :
      Step C C' →
      -- All endpoints in C belong to nid
      (∀ e, used_in C e → DC.topology e = nid) →
      DistStep DC (DC.update_node nid C')

  | send_cross_node {nid e target v} :
      DC.topology e = nid →
      DC.topology (e.1, target) ≠ nid →
      -- Enqueue to network instead of local buffer
      DistStep DC (DC.enqueue_network ⟨nid, DC.topology (e.1, target), edge, v⟩)
      where edge = ⟨e, (e.1, target)⟩

  | recv_cross_node {nid msg} :
      msg ∈ DC.network →
      msg.to_node = nid →
      -- Deliver from network to local buffer
      DistStep DC (DC.deliver_message msg)
```

**Deployment Correctness:**

```lean
-- Distributed execution simulates centralized execution
theorem deployment_simulation {DC DC'} :
    DistStep DC DC' →
    ∃ C C', centralize DC = C ∧
            centralize DC' = C' ∧
            Step C C'

-- Centralized execution can be distributed
theorem deployment_completeness {C C'} :
    Step C C' →
    ∀ topology, ∃ DC DC',
      centralize DC = C ∧
      centralize DC' = C' ∧
      DistStep DC DC'
```

---

## Supporting Infrastructure

### Simulation.lean
**Location:** `Effects/Simulation.lean` (534 lines)

**Executable Simulation:**

```lean
-- Attempt one base step
def stepBaseDecide (C : Config) : Option Config :=
  -- Try send
  if store k = .chan e ∧ G e = .send target T L ∧ store x = v
  then some ⟨C.nextSid, C.store, C.buffers.enqueue edge v, .skip⟩
  -- Try recv
  else if store k = .chan e ∧ G e = .recv source T L ∧ bufs edge = v :: rest
  then some ⟨C.nextSid, C.store.update x v, C.buffers.update edge rest, .skip⟩
  -- Try other actions...
  else none

-- Attempt contextual step
def stepDecide (C : Config) : Option Config :=
  stepBaseDecide C <|>
  match C.proc with
  | .seq P Q => stepDecide ⟨..., P⟩ |>.map (fun C' => ⟨..., C'.proc ; Q⟩)
  | .par P Q => stepDecide ⟨..., P⟩ |>.map (fun C' => ⟨..., C'.proc ∥ Q⟩) <|>
                stepDecide ⟨..., Q⟩ |>.map (fun C' => ⟨..., P ∥ C'.proc⟩)
  | _ => none

-- Execute n steps, collecting configs
def runSteps (C : Config) (n : Nat) : List Config :=
  match n with
  | 0 => [C]
  | n+1 =>
      match stepDecide C with
      | some C' => C :: runSteps C' n
      | none => [C]

-- Collect full execution trace
def traceSteps (C : Config) (max_steps : Nat) : List Config :=
  runSteps C max_steps
```

**Use Case:** Testing protocols before deployment.

---

### Examples.lean
**Location:** `Effects/Examples.lean` (401 lines)

**Ping-Pong Protocol:**

```lean
-- Roles: Alice, Bob
-- Alice sends ping, Bob replies with pong

def aliceType : LocalType :=
  .send "Bob" .unit (.recv "Bob" .unit .end_)

def bobType : LocalType :=
  .recv "Alice" .unit (.send "Alice" .unit .end_)

-- Process implementations
def aliceProc : Process :=
  send k_alice () ;
  recv k_alice x ;
  skip

def bobProc : Process :=
  recv k_bob y ;
  send k_bob () ;
  skip

-- Well-typedness proof
theorem pingpong_welltyped :
    ∃ S G D, HasTypeProcN 1 S G D (aliceProc ∥ bobProc) ∧
             Coherent G D
```

**Three-Party Protocol:**

```lean
-- Buyer-Seller protocol with mediator
-- Buyer sends request to Seller, Seller quotes Mediator,
-- Mediator approves/rejects to Buyer

def buyerType : LocalType :=
  .send "Seller" .string (
  .recv "Mediator" .bool (
  .branch "Mediator" [
    ("approve", .send "Seller" .unit .end_),
    ("reject", .end_)
  ]))

def sellerType : LocalType :=
  .recv "Buyer" .string (
  .send "Mediator" .nat (
  .recv "Buyer" .unit .end_))

def mediatorType : LocalType :=
  .recv "Seller" .nat (
  .select "Buyer" [
    ("approve", .end_),
    ("reject", .end_)
  ])
```

---

### Decidability.lean
**Location:** `Effects/Decidability.lean` (101 lines)

**Decidable Predicates:**

```lean
-- Edge equality
instance : DecidableEq Edge :=
  fun e₁ e₂ => ...

-- Endpoint equality
instance : DecidableEq Endpoint :=
  fun ep₁ ep₂ => ...

-- Role equality
instance : DecidableEq Role :=
  String.decEq

-- RoleSet membership
def mem_roles_decidable (r : Role) (rs : RoleSet) : Decidable (r ∈ rs.roles) :=
  List.decidableMem

-- LocalType equality (structural)
def localTypeEq_decidable : DecidableEq LocalType :=
  fun L₁ L₂ => ...
```

**Use Case:** Computational protocol analysis and runtime checking.

---

## Cross-Reference Index

### By Topic

#### **Core Type System**
1. `LocalType` definition → LocalType.lean
2. `HasTypeProcN` judgment → Typing.lean
3. `WTConfigN` well-typed config → Typing.lean
4. Value typing `HasTypeVal` → Coherence.lean

#### **Coherence Chain**
1. `Consume` / `consumeOne` → Coherence.lean
2. `EdgeCoherent` → Coherence.lean
3. `Coherent` → Coherence.lean
4. `trace_empty_when_*` shortcuts → Coherence.lean
5. `Consume_append` / `Consume_cons` → Coherence.lean

#### **Safety Properties**
1. `preservation` → Preservation.lean (uses Coherence)
2. `progress` → DeadlockFreedom.lean
3. `stepBase_det` → Determinism.lean
4. `spatial_independence` → Spatial.lean

#### **Runtime Infrastructure**
1. `MonStep` monitor transitions → Monitor.lean
2. `stepDecide` executable simulation → Simulation.lean
3. `DistStep` distributed execution → Deployment.lean

#### **Environment Management**
1. Lookup/update lemmas → Environments.lean
2. Session renaming → Environments.lean
3. Initialization → Environments.lean

### By Dependency

#### **Foundation Stack**
```
Basic.lean
    ↓
LocalType.lean → Values.lean
    ↓              ↓
Environments.lean
    ↓
Process.lean
```

#### **Type System Stack**
```
Coherence.lean (defines Consume, Coherent)
    ↓
Typing.lean (uses Coherent in WTConfigN)
    ↓
Semantics.lean (operational rules)
    ↓
Preservation.lean (proves type safety)
```

#### **Metatheory Stack**
```
Preservation.lean
    ↓
Determinism.lean + DeadlockFreedom.lean + Spatial.lean
```

#### **Runtime Stack**
```
Typing.lean + Coherence.lean
    ↓
Monitor.lean (validates actions)
    ↓
Deployment.lean (distributed execution)
```

---

## Proof Status & Sorries

### Complete Implementations ✓
- All type definitions and syntax
- Environment lookup/update lemmas
- Process typing judgment
- Operational semantics
- Monitor state transitions
- Simulation infrastructure
- Decidability instances

### Partial Implementations ⚠
- **Coherence.lean**: Core structure complete, some inductive case proofs have sorries
- **Preservation.lean**: Main theorem structure present, some helper lemmas incomplete
- **DeadlockFreedom.lean**: Progress infrastructure defined, some proofs incomplete

### Key Completed Theorems ✓
- `Consume_append`, `Consume_cons` - Consumption composition
- `trace_empty_when_send_receiver` - Send receiver shortcut
- `trace_empty_when_recv_other_sender` - Recv different sender shortcut
- `trace_empty_when_branch_other_sender` - Branch different sender shortcut
- `HasTypeVal_unique` - Value typing uniqueness
- `HasTypeVal_mono` - Value typing monotonicity
- `stepBase_deterministic` - Base step determinism
- All environment lookup/update lemmas

---

## Quick Navigation Guide

**Want to understand...**

- **How async MPST works?** → Start with README.md, then Basic.lean, LocalType.lean
- **The coherence invariant?** → Read Coherence.lean (start with `Consume`, `EdgeCoherent`, `Coherent`)
- **Type system?** → Read Typing.lean (focus on `HasTypeProcN` and `WTConfigN`)
- **Operational semantics?** → Read Semantics.lean (`StepBase` and `Step`)
- **Type safety proof?** → Read Preservation.lean (uses Coherence lemmas)
- **Runtime monitoring?** → Read Monitor.lean (`MonStep` transitions)
- **Testing protocols?** → Read Simulation.lean and Examples.lean
- **Distributed deployment?** → Read Deployment.lean
- **Session isolation?** → Read Spatial.lean

---

## Design Principles

### 1. **Async-First Design**
Unlike synchronous session types, sends complete immediately. Messages sit in explicit FIFO buffers, typed by trace environments.

### 2. **Coherence Over Duality**
Binary session types use endpoint duality (L ↔ L̄). MPST uses coherence: for each edge, consuming the trace from the receiver's perspective succeeds.

### 3. **Linear Capability Tokens**
Tokens are unforgeable capabilities tied to endpoints. Protocol steps consume/produce tokens, enforcing linear resource usage and preventing aliasing.

### 4. **Three-Way Edge Analysis**
For coherence preservation:
1. **Edge being updated** - Type and trace change
2. **Edge involving modified endpoint** - Other endpoint may change
3. **Unrelated edge** - Environments unchanged

### 5. **Consumption as Core Abstraction**
`Consume from_ L ts` models how a receiver's type evolves as messages arrive. The appendix property (`Consume L (ts ++ [T]) = Consume (Consume L ts) [T]`) is critical for preservation.

---

## Contributing

When adding new theorems or lemmas:
1. Update this code map with theorem name, location, and description
2. Add to cross-reference index
3. Document dependencies
4. Note if proof is complete or contains sorries

---

## Version History

- 2026-01-16: Initial code map created

---

## License

Same as Effects library.
