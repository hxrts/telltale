# VM Multi-Coroutine Runtime: Work Plan

## Purpose
This plan tracks the implementation of the canonical VM defined in [VM and Runtime Design for Lean 4 Specification](runtime.md). The goal is to align Lean, Rust, and the simulator with the same core semantics. The plan also includes proof work and cross testing.

## Alignment Decisions
These decisions are fixed for this plan.

- Guard, speculation, and ownership opcodes are part of the core instruction set.
- Unknown opcodes are rejected with a deterministic fault.
- Session local logical clocks are the default trace comparand.
- Strict ticked equality is for same engine regression tests.
- Per session projection equality is the formal invariance target.

## Status Summary
Lean implements the core VM state, scheduler, dynamic loading, trace normalization, and per-session trace invariants in `Runtime.Proofs.Concurrency`. Lean implements the LocalTypeR compiler and code image loader. Rust implements the LocalTypeR compiler, dynamic loading, guard/speculation/ownership opcodes, and progress-aware scheduling. Cross-language trace normalization is implemented, with wasm bindings and tests in Rust.

## Phases 1–8 (Complete)

**Phase 1. Trace Equivalence and Shared Fixtures** — Session-local clock normalization in Lean and Rust. Strict ticked equality retained as test mode. Simulator defaults to session-local normalization. Shared JSON trace schema documented.

**Phase 2. Lean Core Completion** — `compileLocalTypeR`, `CodeImage.fromLocalTypes`, per-coroutine programs, `loadChoreography`, N-concurrent scheduling, guard/speculation/ownership opcodes with full operational semantics and monitor integration, JSON trace output with session-local ticks.

**Phase 3. Rust Core Completion** — LocalTypeR compilation, CodeImage loading, `load_choreography`, N-concurrent scheduling, guard/speculation/ownership opcodes, unknown opcode rejection, progress-aware scheduling, trace output with session-local ticks.

**Phase 4. Simulator Alignment** — VM runner is the sole execution engine. Effect handlers and middleware use session-local clock normalization. Fault/network injection uses VM global tick only for time-based effects.

**Phase 5. Cross Testing** — Cross-language test harness comparing Lean and Rust traces via shared JSON schema and session-local normalization. Regression tests with strict ticked equality. Deterministic LocalTypeR test corpus.

**Phase 6. Rust WASM Build** — WASM target compiles without unstable features. API exposes `load_choreography`, `step_round`, and trace retrieval. WASM traces match native under session-local normalization.

**Phase 7. Proof Completion** — `compile_nonempty`, `compile_ends_halt_or_jmp`, `loadChoreography_disjoint`, `per_session_trace_N_invariant`, `per_session_trace_policy_invariant` proved. Cross-session diamond and WP framing axioms discharged.

**Phase 8. Documentation and Maintenance** — Doc references updated. Plan aligned with spec. Style guides followed.

## Phase 9 (Complete)

All preservation, progress, and subject reduction theorems proved in `Protocol/Preservation.lean`. All deadlock freedom lemmas proved in `Protocol/DeadlockFreedom.lean`. All deployment interface lemmas proved in `Protocol/Deployment/Interface.lean`. `disjoint_sessions_independent` and `updateSEnv_append_left` proved. Handler/effect polymorphism theorems proved (`handler_progress`, `effect_polymorphic_safety`, `handler_transport_refines`, `handler_is_session`). Progress token theorems proved (`session_type_mints_tokens_stub`, `recv_consumes_token`, `starvation_free_stub`). Cost credit basics proved (`cost_credit_sound`, `cost_budget_bounds_steps`, `cost_frame_preserving`). Aura basics proved (`facts_monotone`, `aura_typeclass_resolution`). `vm_deadlock_free` proved via Lyapunov progress measure. `transfer_preserves_coherent` proved via conservation argument. `schedule_confluence` proved. `no_phantom_events` proved. `finalization_token_persistent` replaced with real proof. All VM operational placeholders replaced (`SessionDisjoint`, `deterministic_finalization_ok`, `monitorAllows`, `FStarDrain`). All session invariant stubs proved (`open_coherent`, `migrate_preserves_spatial`, `leave_preserves_coherent`, `close_empty`, `close_makes_inaccessible`, `conservation_inv_preserved`).

---

## Phase 10. Protocol Typing and Deployment Linking

Discharge the remaining protocol-level typing axioms, prove monitor preservation, and complete the deployment linking metatheory. The typing axioms unblock the monitor and linking proofs; linking completes compositional deadlock freedom.

> **Gibbs connection.** The deployment linking proofs correspond to compositional coherence — proving that linked protocols preserve well-typedness. Gibbs's `KernelCoherent` and `projection_sound` in `ContinuumField/EffectsIntegration.lean` prove the analogous result for nonlocal operators: coherent local kernels reproduce the global operator. The `nonlocal_exact` proof (by `rfl`) shows that the right abstraction can make composition definitional. The per-edge structure of Coherence in Telltale maps to per-kernel contributions in Gibbs.

### Typing Axioms
- [ ] Prove `ParSplit.unique` in `lean/Protocol/Typing/Core.lean`. (Medium, Unblocked)
- [ ] Prove `SessionsOf_subset_of_HasTypeProcPreOut` in `lean/Protocol/Typing/Framing.lean`. (Medium, Unblocked)
- [ ] Prove `DisjointS_preserved_TypedStep_right` in `lean/Protocol/Typing/Preservation.lean`. (Medium, Unblocked)

### Monitor Preservation
- [ ] Prove `MonStep_preserves_WTMon` in `lean/Protocol/Monitor/Preservation.lean`. (Hard)
- [ ] Prove `newSession_preserves_WTMon` in `lean/Protocol/Monitor/Preservation.lean`. (Medium, Unblocked)

### Deployment Linking
- [ ] Prove `mergeBufs_typed` in `lean/Protocol/Deployment/Linking.lean`. (Hard)
- [ ] Prove `mergeLin_valid` in `lean/Protocol/Deployment/Linking.lean`. (Medium, Unblocked)
- [ ] Prove `mergeLin_unique` in `lean/Protocol/Deployment/Linking.lean`. (Medium, Unblocked)
- [ ] Prove `link_preserves_WTMon_full` in `lean/Protocol/Deployment/Linking.lean`. (Hard)
- [ ] Prove `link_preserves_WTMon` in `lean/Protocol/Deployment/Linking.lean`. (Hard)
- [ ] Prove `link_preserves_WTMon_complete` in `lean/Protocol/Deployment/Linking.lean`. (Hard)
- [ ] Prove `link_preserves_WTMon_complete_full` in `lean/Protocol/Deployment/Linking.lean`. (Hard)
- [ ] Prove `compose_deadlock_free` in `lean/Protocol/Deployment/Linking.lean`. (Hard)

## Phase 11. VM Safety and Commutativity

Prove guard chain properties, the cross-session diamond (per-instruction commutativity for disjoint sessions), and WP effect dispatch. These are the core VM-level safety proofs.

> **Gibbs connection.** `vm_deadlock_free` is proved via the Lyapunov liveness technique ported from Gibbs. The progress measure framework in `Lyapunov.lean` adapts `StrictLyapunovData` and `strict_lyapunov_implies_asymptotic` to a discrete Nat-valued setting. `transfer_preserves_coherent` parallels Gibbs's `drift_conserves` — both prove that a state transfer operation preserves an invariant.

### Guards
- [ ] Prove `guard_chain_compose` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Medium, Unblocked)
- [ ] Prove `guard_abort_restores` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Hard)
- [ ] Prove `guard_hot_swap` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Hard)
- [ ] Prove `wp_doEffect` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Hard)

### Cross-Session Diamond
- [~] Prove `cross_session_diamond` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Hard) — Definition replaced with `execInstr` commutativity for disjoint sessions. Proof body requires per-instruction case analysis (sorry pending). Subtasks:
  - [ ] Case `send` — `stepSend` modifies session buffers; needs disjoint session frame lemma.
  - [ ] Case `recv` — `stepRecv` dequeues from session buffers; needs disjoint session frame lemma.
  - [ ] Case `offer` — `stepOffer` enqueues label; session-local.
  - [ ] Case `choose` — `stepChoose` dispatches on label; coroutine-local.
  - [ ] Case `acquire` — `stepAcquire` acquires guard; coroutine-local.
  - [ ] Case `release` — `stepRelease` releases guard; coroutine-local.
  - [ ] Case `invoke` — `stepInvoke` runs effect handler; coroutine-local.
  - [ ] Case `open` — `stepOpen` creates new session; needs fresh session ID disjointness.
  - [ ] Case `close` — `stepClose` closes session; session-local.
  - [ ] Case `fork` — `stepFork` spawns coroutine; modifies coroutine map.
  - [ ] Case `join` — `stepJoin` joins coroutine; coroutine-local.
  - [ ] Case `abort` — `stepAbort` aborts coroutine; coroutine-local.
  - [ ] Case `transfer` — `stepTransfer` moves endpoint; needs disjoint session frame lemma.
  - [ ] Case `tag` — `stepTag` tags knowledge fact; coroutine-local.
  - [ ] Case `check` — `stepCheck` checks knowledge; coroutine-local.
  - [ ] Case `loadImm` — `stepLoadImm` loads immediate; register-only.
  - [ ] Case `mov` — `stepMov` moves register; register-only.
  - [ ] Case `jmp` — `stepJmp` jumps PC; register-only.
  - [ ] Case `spawn` — `stepSpawn` creates coroutine; modifies coroutine map.
  - [ ] Case `yield` — `stepYield` yields; coroutine-local.
  - [ ] Case `halt` — `haltPack` halts; coroutine-local.
  - [ ] Early returns — done/faulted/missing program/pc out of range; trivially commute (no state change).
- [ ] Prove `wp_frame_concurrent` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Hard)

## Phase 12. Program Logic and Adequacy

Replace ghost state and resource model placeholders with real definitions, complete finalization and pipeline WP rules, prove cost metering WP integration, and close the adequacy theorem. The ghost state infrastructure is prerequisite for all WP-based proofs.

> **Gibbs connection.** Cost metering corresponds to free energy accounting in Gibbs. `send_cost_plus_flow` parallels the channel capacity constraint. Gibbs's `branchEntropy` in `Hamiltonian/ChannelSession.lean` quantifies the information-theoretic component of send cost. `cost_speculation_bounded` connects to the energy gap. `HamiltonianChoreography` and `MeanFieldChoreography` in Gibbs provide concrete choreographic protocol instances that can serve as nontrivial test cases for the adequacy proof. *(Entropy, KL divergence, mutual information, and data processing inequality definitions have been ported from Gibbs into `lean/Protocol/InformationCost.lean`.)*

### Ghost State and Resources
- [ ] Replace `KnowledgeReachable := True` with a real predicate in `lean/Runtime/ProgramLogic/GhostState.lean`. (Medium, Unblocked)
- [ ] Replace `bundle_complete := True` with a real predicate in `lean/Runtime/ProgramLogic/GhostState.lean`. (Medium, Unblocked)
- [ ] Replace `higher_order_transfer_preserves := True` with a real statement in `lean/Runtime/ProgramLogic/GhostState.lean`. (Hard)
- [ ] Replace `guard_layer_owns := iProp.emp` with a real resource assertion in `lean/Runtime/ProgramLogic/GhostState.lean`. (Medium, Unblocked)
- [ ] Replace `effect_ctx_owns := iProp.emp` with a real resource assertion in `lean/Runtime/ProgramLogic/GhostState.lean`. (Medium, Unblocked)
- [ ] Replace `session_progress_supply := iProp.emp` with a real resource assertion in `lean/Runtime/ProgramLogic/GhostState.lean`. (Medium, Unblocked)
- [ ] Replace `ResourceLogicProof := Unit` with a real proof type in `lean/Runtime/Resources/ResourceModel.lean`. (Hard)
- [ ] Replace `DeltaProof := Unit` with a real proof type in `lean/Runtime/Resources/ResourceModel.lean`. (Hard)

### WP Rules
- [ ] Replace `wp_close_final := iProp.emp` with a real WP rule in `lean/Runtime/ProgramLogic/FinalizationWP.lean`. (Hard)
- [ ] Replace `wp_invoke_final := iProp.emp` with a real WP rule in `lean/Runtime/ProgramLogic/FinalizationWP.lean`. (Hard)
- [ ] Replace `wp_send_pipeline` placeholder with a real pipeline composition in `lean/Runtime/ProgramLogic/WPPipeline.lean`. (Hard)

### Cost Metering
- [x] Prove `wp_lift_step_with_cost` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Medium, Unblocked) — Real proposition: chargeCost success + budget conservation + strict decrease; proved via CostModel invariants.
- [x] Prove `send_cost_plus_flow` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Medium, Unblocked) — Real proposition: branch entropy nonneg + Shannon bound; proved via ported `InformationCost` theorems.
- [x] Prove `cost_speculation_bounded` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Medium, Unblocked) — Real proposition: KL divergence nonneg + zero iff equal; proved via ported `InformationCost` theorems.

### Adequacy
- [ ] Replace `compile_refines := True` with a real statement tied to `CodeImage.fromLocalTypes` in `lean/Runtime/Adequacy/Adequacy.lean`. (Hard)
- [ ] Prove `vm_adequacy` in `lean/Runtime/Adequacy/Adequacy.lean`. (Hard)

## Phase 13. Refinement Stack and Scheduling

Prove the three-layer refinement chain (effects → scheduler step → failure → speculative), the domain composition properties, and scheduler fairness. These establish that the abstract execution models correctly simulate one another.

> **Gibbs connection.** Effect composition safety parallels Gibbs's conservation under drift composition (`drift_conserves` and `driftFromRules_conserves`) — composed effects preserve session type invariants just as composed drift terms preserve population invariants. `protocol_federation` maps to Gibbs's sum instances on `EffectModel`. `starvation_free` can be bounded via the spectral gap of the scheduling chain (advance_further_physics.md #3).

### Refinement Chain
- [ ] Prove `effects_refines_schedStep` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Hard)
- [ ] Prove `schedStep_refines_failure` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Hard)
- [ ] Prove `failure_refines_speculative` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Hard)

### Domain Composition
- [ ] Replace `effect_composition_safe := True` with a real statement in `lean/Runtime/VM/DomainComposition.lean`. (Hard)
- [ ] Replace `composed_frame_rule := True` with a real statement in `lean/Runtime/VM/DomainComposition.lean`. (Hard)
- [ ] Replace `composed_persistence_commutation := True` with a real statement in `lean/Runtime/VM/DomainComposition.lean`. (Hard)
- [ ] Replace `protocol_federation := True` with a real statement in `lean/Runtime/VM/DomainComposition.lean`. (Hard)

### Scheduler Fairness
- [x] Prove `cooperative_refines_concurrent` in `lean/Runtime/VM/Scheduler.lean`. (Hard)
- [x] Prove `starvation_free` in `lean/Runtime/VM/Scheduler.lean`. (Medium, Unblocked)

## Phase 14. Aura Instantiation

Prove the domain-specific theorems for the Aura handler: capability tracking, journal idempotency, consensus refinement, and guard hot-swap under the Aura effect model.

- [ ] Prove `charge_before_send` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Medium, Unblocked)
- [ ] Prove `journal_idempotent` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Medium, Unblocked)
- [ ] Prove `caps_monotone` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Medium, Unblocked)
- [ ] Prove `context_isolation` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Medium, Unblocked)
- [ ] Prove `epoch_drain_safe` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Hard)
- [ ] Prove `wp_aura_invoke` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Hard)
- [ ] Prove `wp_aura_send_pipeline` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Medium, Unblocked)
- [ ] Prove `aura_guard_hot_swap` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Hard)
- [ ] Prove `consensus_handler_refines` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Medium, Unblocked)
- [ ] Prove `direct_handler_refines` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Medium, Unblocked)
- [ ] Prove `aura_non_leakage` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Hard)
- [ ] Prove `optimistic_consensus_sound` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Hard)
- [ ] Prove `transfer_with_caps` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Medium, Unblocked)
- [ ] Prove `aura_send_dual_resource` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Medium, Unblocked)
- [ ] Prove `aura_cost_budget_from_caps` in `lean/Runtime/Proofs/TheoremStubs.lean`. (Medium, Unblocked)

## Phase 15. Engineering and CI

Runtime boundary cleanup, remaining Rust work, and CI coverage for release readiness.

- [ ] Finish the runtime boundary cleanup in `work/runtime_proof_separation.md` by splitting `EffectRuntime` and `EffectSpec`, and ensuring Rust mirrors only the spec surface.
- [ ] Resolve the remaining Rust TODO in `rust/choreography/src/compiler/runner.rs` for output struct fields.
- [ ] Re-enable Lean checks in `Justfile` `ci-dry-run` once the axiom removals are complete.
- [ ] Add CI coverage for `just wasm-check` and `just wasm-test` and document browser prerequisites.
- [ ] Add CI coverage for `cargo bench` with a performance regression budget.
- [ ] Publish an API stability and migration policy for trace schema and VM JSON formats.

## Phase 16. Obligation Tracking in Types

Lift liveness conditions from proof-level predicates into first-class type annotations. This completes the vision's most ambitious piece: a decidable liveness logic baked into the session type system.

> **Gibbs connection.** The Lyapunov liveness approach from advance_further_physics.md #1 has been implemented in `lean/Runtime/Proofs/Lyapunov.lean`, proving `vm_deadlock_free` without obligation annotations. The progress measure (`LocalType.progressMeasure`) counts remaining communication actions and decreases under well-typed steps, giving deadlock freedom and quantitative termination bounds. The design tasks below for syntactic obligation tracking are no longer required for liveness but may still be useful for richer static checking or user-facing guarantees.

### Design (Lean)
- [ ] Define obligation annotation syntax on `LocalType` in `lean/Protocol/LocalType.lean`. (Hard)
- [ ] Define `Obligation` predicate capturing "this role must eventually perform this action" in a new `lean/Protocol/Obligations/Core.lean`. (Hard)
- [ ] Define `ObligationDischarge` predicate for checking that a peer's obligations are met at composition boundaries in `lean/Protocol/Obligations/Discharge.lean`. (Hard)
- [ ] Prove decidability of `ObligationDischarge` in `lean/Protocol/Obligations/Decidability.lean`. (Hard)

### Soundness (Lean)
- [ ] Prove that the extended type system preserves `preservation_typed` in `lean/Protocol/Obligations/Preservation.lean`. (Hard)
- [ ] Prove that obligation discharge implies `Guarded` in `lean/Protocol/Obligations/GuardedImplication.lean`. (Medium, Unblocked)
- [ ] Prove that obligation discharge implies `ReachesComm` in `lean/Protocol/Obligations/ReachesCommImplication.lean`. (Medium, Unblocked)
- [ ] Prove compositional obligation closure: discharged obligations at linking boundaries imply `compose_deadlock_free` conditions in `lean/Protocol/Obligations/Composition.lean`. (Hard)

### Rust Implementation
- [ ] Extend `LocalType` in `rust/types/` with obligation annotations matching the Lean definitions. (Medium, Unblocked)
- [ ] Extend the projection algorithm in `rust/choreography/src/compiler/projection.rs` to propagate obligation annotations. (Medium, Unblocked)
- [ ] Add obligation checking to the Lean bridge export in `rust/lean-bridge/`. (Medium, Unblocked)

## Phase 17. Parameterize Delivery Model

Abstract the Coherence invariant and Consume function over a delivery model parameter. This enables the metatheory to cover FIFO, causal, and lossy delivery without redoing proofs.

> **Gibbs connection.** Gibbs's `ContinuumField/Projection.lean` demonstrates exactly this pattern. The kernel coherence framework (`KernelCoherent`, `projection_sound`) generalizes over nonlocal integral operators, and the `nonlocal_exact` proof (by `rfl`) shows that the right typeclass abstraction makes global-local correspondence definitional. The `DeliveryModel` typeclass below should follow this pattern: define the typeclass, prove coherence generically, and instantiate for specific models. Gibbs's `SpatialChannelModel` with distance-dependent capacity provides a concrete example of delivery model parameterization that goes beyond FIFO.

### Abstraction Layer (Lean)
- [ ] Define `DeliveryModel` structure or typeclass in `lean/Protocol/DeliveryModel.lean` capturing buffer semantics (enqueue, dequeue, reorder constraints). (Hard)
- [ ] Refactor `Consume` in `lean/Protocol/Coherence/Consume.lean` to be parametric over `DeliveryModel`. (Hard)
- [ ] Refactor `EdgeCoherent` and `Coherent` to use the parametric `Consume`. (Hard)
- [ ] Refactor Coherence preservation proofs in `lean/Protocol/Coherence/Preservation.lean` and `SelectPreservation.lean` to be generic over `DeliveryModel`. (Hard)
- [ ] Refactor `Coherent_empty` and `initSession_coherent` in `lean/Protocol/Coherence/ValidLabels.lean` to be generic. (Medium, Unblocked)

### FIFO Instantiation (Lean)
- [ ] Define `FIFODelivery` instance of `DeliveryModel` recovering the current buffer semantics. (Medium, Unblocked)
- [ ] Verify that all existing theorems instantiate correctly under `FIFODelivery`. (Medium, Unblocked)

### Additional Delivery Model (Lean)
- [ ] Define `CausalDelivery` instance of `DeliveryModel` with causal ordering constraints. (Hard)
- [ ] Prove Coherence preservation for `CausalDelivery`. (Hard)
- [ ] Or: Define `LossyDelivery` instance with message loss and retry semantics. (Hard)
- [ ] Prove Coherence preservation for `LossyDelivery`. (Hard)

### Rust Alignment
- [ ] Parameterize the simulator network middleware in `rust/simulator/src/network.rs` over a delivery model trait matching the Lean `DeliveryModel`. (Medium, Unblocked)
- [ ] Add causal or lossy delivery model implementations in the simulator. (Medium, Unblocked)

---

### Iris Shim Axioms (Deferred)
- [ ] Retire `GhostName` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `iProp` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `iProp.entails` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `iProp.emp` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `iProp.sep` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `iProp.wand` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `iProp.pure` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `iProp.later` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `iProp.persistently` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `iProp.exist` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `iProp.forall` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `sep_comm` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `sep_assoc` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `sep_mono` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `wand_intro` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `wand_elim` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `pure_intro` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `pure_elim` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `persistently_idemp` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `persistently_sep_dup` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `own` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `bupd` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `bupd_mono` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `bupd_intro` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `bupd_trans` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `bupd_frame_r` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `own_update` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `own_alloc` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `Auth` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `Auth.auth` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `Auth.frag` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `auth_frag_included` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `auth_update` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `GMap` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `GMap.lookup` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `GMap.insert` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `GMap.delete` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `ghost_map_auth` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `ghost_map_elem` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `ghost_map_alloc` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `ghost_map_lookup` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `ghost_map_insert` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `ghost_map_update` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `ghost_map_delete` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `big_sepL` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `big_sepM` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `big_sepL_nil` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `big_sepL_cons` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `big_sepL_app` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `big_sepM_insert` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `big_sepM_lookup` in `lean/Runtime/Shim/ResourceAlgebra.lean`. (Deferred)
- [ ] Retire `Mask` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `Mask.top` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `Mask.empty` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `Mask.diff` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `Mask.union` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `Mask.subseteq` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `Mask.disjoint` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `Mask.singleton` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `Namespace` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `Namespace.root` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `Namespace.append` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `Namespace.append_nat` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `namespace_to_mask` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `namespace_disjoint` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `fupd` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `fupd_intro` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `fupd_mono` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `fupd_trans` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `fupd_frame_r` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `fupd_mask_subseteq` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `inv` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `inv_persistent` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `inv_alloc` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `inv_acc` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `CancelToken` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `cancel_token_own` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `cinv` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `cinv_persistent` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `cinv_alloc` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `cinv_acc` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `cinv_cancel` in `lean/Runtime/Shim/Invariants.lean`. (Deferred)
- [ ] Retire `wp` in `lean/Runtime/Shim/WeakestPre.lean`. (Deferred)
- [ ] Retire `state_interp` in `lean/Runtime/Shim/WeakestPre.lean`. (Deferred)
- [ ] Retire `wp_value` in `lean/Runtime/Shim/WeakestPre.lean`. (Deferred)
- [ ] Retire `wp_strong_mono` in `lean/Runtime/Shim/WeakestPre.lean`. (Deferred)
- [ ] Retire `wp_bind` in `lean/Runtime/Shim/WeakestPre.lean`. (Deferred)
- [ ] Retire `wp_frame_l` in `lean/Runtime/Shim/WeakestPre.lean`. (Deferred)
- [ ] Retire `wp_fupd` in `lean/Runtime/Shim/WeakestPre.lean`. (Deferred)
- [ ] Retire `wp_lift_step` in `lean/Runtime/Shim/WeakestPre.lean`. (Deferred)
- [ ] Retire `MultiStep` in `lean/Runtime/Shim/WeakestPre.lean`. (Deferred)
- [ ] Retire `MultiStep'` in `lean/Runtime/Shim/WeakestPre.lean`. (Deferred)
- [ ] Retire `wp_adequacy` in `lean/Runtime/Shim/WeakestPre.lean`. (Deferred)
- [ ] Retire `wp_invariance` in `lean/Runtime/Shim/WeakestPre.lean`. (Deferred)
- [ ] Retire `saved_prop_own` in `lean/Runtime/Shim/SavedProp.lean`. (Deferred)
- [ ] Retire `saved_prop_alloc` in `lean/Runtime/Shim/SavedProp.lean`. (Deferred)
- [ ] Retire `saved_prop_agree` in `lean/Runtime/Shim/SavedProp.lean`. (Deferred)
- [ ] Retire `saved_prop_persistent` in `lean/Runtime/Shim/SavedProp.lean`. (Deferred)
- [ ] Retire `ghost_var` in `lean/Runtime/Shim/SavedProp.lean`. (Deferred)
- [ ] Retire `ghost_var_alloc` in `lean/Runtime/Shim/SavedProp.lean`. (Deferred)
- [ ] Retire `ghost_var_agree` in `lean/Runtime/Shim/SavedProp.lean`. (Deferred)
- [ ] Retire `ghost_var_update` in `lean/Runtime/Shim/SavedProp.lean`. (Deferred)
- [ ] Retire `HeapLookup` in `lean/Runtime/Shim/GenHeap.lean`. (Deferred)
- [ ] Retire `HeapInsert` in `lean/Runtime/Shim/GenHeap.lean`. (Deferred)
- [ ] Retire `pointsto` in `lean/Runtime/Shim/GenHeap.lean`. (Deferred)
- [ ] Retire `gen_heap_alloc` in `lean/Runtime/Shim/GenHeap.lean`. (Deferred)
- [ ] Retire `gen_heap_valid` in `lean/Runtime/Shim/GenHeap.lean`. (Deferred)
- [ ] Retire `gen_heap_update` in `lean/Runtime/Shim/GenHeap.lean`. (Deferred)
