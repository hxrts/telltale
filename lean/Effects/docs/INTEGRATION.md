# Effects/MPST ↔ RumpsteakV2 Integration Roadmap

This document outlines the integration path between the `Effects/MPST` runtime system and the `RumpsteakV2` type-theoretic formalization.

## Architecture Overview

| Aspect | Effects/MPST | RumpsteakV2 |
|--------|--------------|-------------|
| **Focus** | Runtime semantics, process calculus | Type theory, projection, coinductive equality |
| **Local Types** | Simple inductive with `mu` | Dual: `LocalTypeR` + coinductive `LocalTypeC` |
| **Global Types** | None | Full `GlobalType` with well-formedness |
| **Recursion** | `mu`/`var` with `unfold` | Same + coinductive unfolding transparency |
| **Buffers** | `Edge`-keyed (sid, sender, receiver) | `Channel`-keyed (sender, receiver) |
| **Session IDs** | Explicit `SessionId : Nat` | Implicit (single protocol) |
| **Environments** | `GEnv`, `DEnv`, `Store`, `Buffers` | `EnvConfig` with queues + timeouts |
| **Process Language** | Full process calculus | None (type-level focus) |
| **Coherence** | Explicit `EdgeCoherent` predicate | Implicit via projection correctness |
| **Equality** | Structural | Coinductive `EQ2` (unfolding-transparent) |

---

## Integration Tasks

### Legend

- ⬜ **Mechanical**: Straightforward, no novel claims
- 🟨 **Moderate**: Requires thought but uses known techniques
- 🟧 **Challenging**: Net new claims, research-level

---

## Phase 1: Bridging Functions

### 1.1 Type Conversions

| Task | Difficulty | Affordance |
|------|------------|------------|
| `toEffectsLocalType : LocalTypeR → Effects.MPST.LocalType` | ⬜ Mechanical | Use RumpsteakV2 projection output in Effects runtime |
| `fromEffectsLocalType : Effects.MPST.LocalType → LocalTypeR` | ⬜ Mechanical | Verify Effects types against RumpsteakV2 properties |
| Prove roundtrip: `from (to L) = L` | ⬜ Mechanical | Ensure no information loss in conversion |
| Prove roundtrip: `to (from L) = L` | ⬜ Mechanical | Ensure conversions are inverses |

**Affordances:**
- Seamless interop between the two systems
- Use RumpsteakV2's proven projection in Effects runtime
- Validate Effects types using RumpsteakV2's well-formedness predicates

---

## Phase 2: Add GlobalType to Effects

### 2.1 Core Definitions

| Task | Difficulty | Affordance |
|------|------------|------------|
| Copy `GlobalType` definition | ⬜ Mechanical | Choreographic specifications in Effects |
| Copy well-formedness predicates | ⬜ Mechanical | Reject malformed protocols statically |
| Add `wellFormed_substitute` lemmas | ⬜ Mechanical | Safe recursion unfolding |
| Add `wellFormed_mu_unfold` | ⬜ Mechanical | Unfolding preserves validity |

**Affordances:**
- Write protocols as global choreographies
- Automatic well-formedness checking
- Foundation for projection

### 2.2 Projection

| Task | Difficulty | Affordance |
|------|------------|------------|
| Port `trans` (computational projection) | ⬜ Mechanical | Derive local types from global |
| Port `projectb` (boolean checker) | ⬜ Mechanical | Decidable projection verification |
| Thread `SessionId` through projection | ⬜ Mechanical | Multi-session support |
| Prove projection preserves well-formedness | ⬜ Mechanical | Projected types are valid |

**Affordances:**
- Single source of truth: write global, derive local
- Automated local type generation per role
- Multi-session choreographies

---

## Phase 3: Unify Representations

### 3.1 Edge/Channel Unification

| Task | Difficulty | Affordance |
|------|------------|------------|
| Decide canonical representation | ⬜ Mechanical | Consistent API |
| Refactor to unified type | ⬜ Mechanical | Single buffer abstraction |
| Update all lookup/update functions | ⬜ Mechanical | Clean codebase |

**Affordances:**
- Reduced cognitive overhead
- Easier theorem statements
- Shared lemmas

### 3.2 Add SessionId to RumpsteakV2

| Task | Difficulty | Affordance |
|------|------------|------------|
| Parameterize `Channel` by `SessionId` | ⬜ Mechanical | Multi-session in RumpsteakV2 |
| Update `EnvConfig` for multi-session | 🟨 Moderate | Concurrent protocol instances |
| Define session isolation invariant | 🟨 Moderate | Sessions don't interfere |
| Prove session isolation | 🟨 Moderate | Safety across sessions |

**Affordances:**
- Run multiple protocol instances concurrently
- Session-local reasoning
- Compose independent protocols

---

## Phase 4: Coinductive Infrastructure

### 4.1 EQ2 (Unfolding-Transparent Equality)

| Task | Difficulty | Affordance |
|------|------------|------------|
| Port `EQ2` definition | ⬜ Mechanical | Semantic type equality |
| Port `EQ2_refl`, `EQ2_symm`, `EQ2_trans` | ⬜ Mechanical | Equivalence relation |
| Port `EQ2_unfold` theorem | ⬜ Mechanical | `μt.L ≈ L[μt.L/t]` |
| Integrate EQ2 into Effects coherence | 🟨 Moderate | Coherence up to unfolding |

**Affordances:**
- Identify types that differ only in μ-placement
- Quotient types: `QLocalType = LocalType / EQ2`
- More flexible typing (accept semantically equivalent types)

### 4.2 Coinductive LocalTypeC

| Task | Difficulty | Affordance |
|------|------------|------------|
| Port M-type (PFunctor) infrastructure | 🟨 Moderate | Coinductive type foundation |
| Port `LocalTypeC` definition | 🟨 Moderate | Infinite behavior traces |
| Port `ObservableC` | ⬜ Mechanical | Observable events |
| Port smart constructors + injectivity | ⬜ Mechanical | Safe construction |
| Connect to Effects process semantics | 🟧 Challenging | Trace semantics for processes |

**Affordances:**
- Model infinite protocol behaviors
- Bisimulation-based reasoning
- Observable equivalence (ignore internal μ-unfolding)

---

## Phase 5: Core Theorems

### 5.1 Projected-implies-Coherent (Recommended)

The key theorem connecting RumpsteakV2 projection to Effects/MPST coherence:

```
∀ G, wellFormed G → Coherent (projEnv G)
```

This says: if you derive local types via projection from a well-formed global type,
those types are automatically coherent. This is **more useful than full harmony** because:

- It's a one-directional implication (simpler to prove)
- It lets you use RumpsteakV2's projection without re-proving coherence
- The Effects runtime doesn't need to know about global types at runtime

| Task | Difficulty | Affordance |
|------|------------|------------|
| Define `projEnv : GlobalType → GEnv` | ⬜ Mechanical | Project all roles to GEnv |
| State projected-implies-coherent | 🟨 Moderate | Core theorem statement |
| Prove projected-implies-coherent | 🟨 Moderate | Use projection properties |

**Affordances:**
- **Automatic coherence**: Projection produces coherent types by construction
- **Specification convenience**: Write 1 global type instead of n local types
- **No runtime overhead**: Effects runtime works with local types only
- **Leverage RumpsteakV2**: Reuse existing projection proofs

### 5.2 Full Projection Harmony (Optional)

Full bidirectional harmony: "Global step ↔ local steps". Only needed if you want
to reason at the global level about runtime behavior.

| Task | Difficulty | Affordance |
|------|------------|------------|
| State harmony theorem | 🟨 Moderate | "Global step ↔ local steps" |
| Define step simulation relation | 🟨 Moderate | Correspondence structure |
| Prove forward simulation | 🟧 Challenging | Global step implies local steps |
| Prove backward simulation | 🟧 Challenging | Local steps imply global step |

**Affordances:**
- Debugging: trace local errors back to global protocol
- Global reasoning: prove properties at choreography level
- **Skip this unless**: You need to reason about global types at runtime

### 5.3 Coherence ↔ Projection Correspondence (Research)

The converse question: are coherent local types always projections of some global type?

| Task | Difficulty | Affordance |
|------|------------|------------|
| State: "coherent implies projectable" | 🟧 Challenging | Novel theorem |
| Prove or find counterexample | 🟧 Challenging | Deep structure theory |

**Affordances:**
- **Unified theory**: Coherence and projection are equivalent characterizations
- Likely false in general (coherence is weaker), but interesting to characterize gap

---

## Phase 6: Safety Theorems

### 6.1 Type Safety

| Task | Difficulty | Affordance |
|------|------------|------------|
| Progress theorem | 🟨 Moderate | Well-typed configs can step or terminate |
| Preservation theorem | 🟨 Moderate | Steps preserve typing |
| Fill `sorry` proofs in Preservation.lean | 🟨 Moderate | Complete formalization |

**Affordances:**
- **No stuck states**: Well-typed programs always make progress
- **Type preservation**: Runtime never violates type invariants
- Foundation for stronger properties

### 6.2 Communication Safety

| Task | Difficulty | Affordance |
|------|------------|------------|
| Session fidelity | 🟨 Moderate | Processes follow their local types |
| Communication safety | 🟨 Moderate | No type mismatches in messages |
| Deadlock freedom | 🟧 Challenging | Well-typed protocols don't deadlock |

**Affordances:**
- **No runtime type errors**: Sent values match expected types
- **Protocol compliance**: Processes follow prescribed choreography
- **Liveness**: System eventually completes (no circular waits)

---

## Phase 7: Advanced Features

### 7.1 Async Subtyping

| Task | Difficulty | Affordance |
|------|------------|------------|
| Define async subtyping relation | ⬜ Mechanical | `L₁ <: L₂` |
| Port subtyping rules | ⬜ Mechanical | Covariant/contravariant rules |
| Prove subtyping is sound | 🟧 Challenging | Substitutability |
| Integrate with typing | 🟨 Moderate | Use subtyping in HasTypeProcN |

**Affordances:**
- **Flexibility**: Accept more implementations as valid
- **"Less is More"**: Outputs can be dropped, inputs can be ignored
- **Reusability**: Generic code over subtype-related protocols

### 7.2 Roundtrip Theorems

| Task | Difficulty | Affordance |
|------|------------|------------|
| `project (embed L) = L` | 🟨 Moderate | Embedding is section |
| `embed (project G) ≈ G` (up to EQ2) | 🟧 Challenging | Projection is retraction |
| Full isomorphism proof | 🟧 Challenging | Complete correspondence |

**Affordances:**
- **Lossless conversion**: No information lost in projection/embedding
- **Canonical forms**: Unique representatives up to EQ2
- **Optimization**: Work in whichever representation is convenient

---

## Phase 8: Process-Type Correspondence

### 8.1 Typed Processes

| Task | Difficulty | Affordance |
|------|------------|------------|
| Type processes against projected types | ⬜ Mechanical | Use projection in HasTypeProcN |
| Prove typed processes respect projection | 🟧 Challenging | Deep correspondence |

**Affordances:**
- **End-to-end safety**: From choreography to running process
- Single specification drives both types and implementation

### 8.2 Trace Semantics

| Task | Difficulty | Affordance |
|------|------------|------------|
| Define process traces | 🟨 Moderate | Observable execution history |
| Relate to coinductive types | 🟧 Challenging | Traces ⊆ LocalTypeC behaviors |
| Prove trace inclusion | 🟧 Challenging | Processes only do allowed actions |

**Affordances:**
- **Behavioral typing**: Types describe observable behavior
- **Testing**: Generate tests from type traces
- **Verification**: Model check against type specification

---

## Summary by Priority

### High Priority (Unblocks everything)
1. ⬜ Bridging functions (Phase 1)
2. ⬜ Add GlobalType + projection (Phase 2)
3. 🟨 Fill Preservation.lean sorries (Phase 6.1)

### Medium Priority (Core value)
4. 🟨 **Projected-implies-Coherent** (Phase 5.1) — *the key theorem*
5. 🟨 Progress + Preservation completion (Phase 6.1)
6. 🟨 EQ2 integration (Phase 4.1)

### Lower Priority (Advanced)
7. 🟧 Deadlock freedom (Phase 6.2)
8. 🟧 Async subtyping (Phase 7.1)
9. 🟧 Full projection harmony (Phase 5.2) — *only if needed*

### Research Extensions
10. 🟧 Coherence ↔ Projection correspondence (Phase 5.3)
11. 🟧 Coinductive trace semantics (Phase 8.2)
12. 🟧 Full roundtrip theorems (Phase 7.2)

---

## Estimated Effort

| Category | Tasks | Estimated Effort |
|----------|-------|------------------|
| ⬜ Mechanical | ~20 | 1-2 weeks |
| 🟨 Moderate | ~12 | 2-4 weeks |
| 🟧 Challenging | ~10 | 4-8 weeks |

**Total**: 7-14 weeks for complete integration

---

## File Locations

| Component | Effects/MPST | RumpsteakV2 |
|-----------|--------------|-------------|
| Local Types | `LocalType.lean` | `Protocol/LocalTypeR.lean`, `Coinductive/LocalTypeC.lean` |
| Global Types | (to add) | `Protocol/GlobalType.lean` |
| Projection | (to add) | `Protocol/Projection/Trans.lean`, `Projectb.lean` |
| Environments | `Environments.lean` | `Semantics/Environment.lean` |
| Coherence | `Coherence.lean` | (implicit in projection) |
| Process | `Process.lean` | (none) |
| Typing | `Typing.lean` | `Semantics/Typing.lean` |
| Semantics | `Semantics.lean` | `Semantics/EnvStep.lean` |
| Preservation | `Preservation.lean` | `Proofs/Safety/SubjectReduction.lean` |
| EQ2 | (to add) | `Protocol/CoTypes/EQ2.lean`, `Coinductive/EQ2C.lean` |

---

## Next Steps

1. **Immediate**: Create `Effects/MPST/Bridge.lean` with type conversions
2. **Short-term**: Copy `GlobalType` and `trans` to Effects
3. **Medium-term**: Complete Preservation.lean proofs
4. **Key theorem**: Prove `wellFormed G → Coherent (projEnv G)`
5. **Optional**: Full projection harmony (only if global-level reasoning needed)
