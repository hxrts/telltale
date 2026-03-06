# Runtime Performance Design And Work Plan

## Goal

Retain the strict normalized determinism model in the runtime while improving:

- execution throughput
- CPU utilization
- memory utilization
- retention / leak behavior
- hotspot visibility and profiling discipline

The constraint is explicit: no change in canonical observable behavior, commit order, or replay/equivalence guarantees.

## Non-Goals

- No weakening of `DeterminismMode::Full`
- No replacement of canonical one-step commit semantics with nondeterministic parallel commits
- No "fast path" that produces different observable traces
- No profiling-only hacks that change runtime semantics

## Design Principles

1. Optimize representation, retention, and read-only precomputation first.
2. Keep commit semantics single-source-of-truth and canonical.
3. Separate production execution from instrumentation overhead with explicit modes.
4. Make memory retention measurable, not anecdotal.
5. Prefer removing repeated allocation and repeated scanning before adding more scheduler complexity.

## Workstreams

### 1. Closed Session Reaping

#### Problem

Closed sessions currently clear only part of their owned state. Session entries can retain local types, roles, authentication structures, and handler metadata after closure. That is a retention bug even if Rust itself is not leaking heap memory.

#### Design

Introduce an explicit reaping lifecycle:

- `close`: transition to `Closed`, record final observability data, stop execution
- `archive`: optional summary extraction for diagnostics/checkpointing
- `reap`: remove closed session state from the live `SessionStore` and associated VM-owned side tables

Reaping must not delete state still required for:

- serialization/checkpoint export
- deterministic replay artifacts
- debug or test assertions when explicitly enabled

So the design should split "live session state" from "archival summary".

#### Tasks

- [x] Audit all state owned directly or indirectly by `SessionState`
- [x] Define `ClosedSessionSummary` or equivalent archival record
- [x] Add `SessionStore::reap_closed` or equivalent targeted reaping API
- [x] Remove retained `local_types`, `roles`, `auth_leaves`, `auth_trees`, `auth_roots`, `edge_handlers`, and related closed-only state from live storage after archival
- [x] Reap VM side tables keyed by `SessionId` such as resource state, monitor/session-kind metadata, and any per-session caches
- [x] Add tests for repeated open/close churn that assert bounded retained live-session state
- [x] Add a benchmark or stress test for short-lived sessions

#### Success Criteria

- Repeated open/close churn does not monotonically increase live retained session count
- Repeated open/close churn does not monotonically increase retained bytes attributed to closed-session runtime state
- Serialization and replay paths still behave deterministically when archival is enabled
- Existing session close semantics and trace behavior remain unchanged for observable events

### 2. Bounded Trace Retention

#### Problem

`obs_trace`, `effect_trace`, and communication replay artifacts grow without bound in long runs. This is useful for debugging, but it is not acceptable as the default production memory behavior.

#### Design

Introduce explicit retention policies:

- full retention
- capped ring-buffer retention
- streamed/exported retention
- disabled retention

Keep trace ordering canonical. Retention policy must affect only storage strategy, not event content or event order.

#### Tasks

- [x] Add configuration for observability retention mode and capacity
- [x] Convert unbounded trace vectors to policy-driven storage
- [x] Add export/drain APIs so harnesses can consume traces incrementally
- [x] Keep existing `EffectTraceCaptureMode` semantics but layer bounded storage underneath
- [x] Add tests for ring-buffer truncation behavior with deterministic ordering
- [x] Add long-running stress test showing bounded trace memory under capped mode

#### Success Criteria

- Long-running workloads under capped mode have bounded trace memory growth
- Full mode preserves current behavior byte-for-byte where expected
- Disabled/topology-only modes materially reduce retained event counts
- Trace ordering and canonicalization remain stable across policies

### 3. Shared Immutable Code Images

#### Problem

Role programs are cloned into VM-owned vectors during coroutine spawn. This duplicates immutable code and wastes memory and cache locality.

#### Design

Move to shared immutable program storage:

- load once into a code arena
- store `Arc<[Instr]>` or equivalent immutable slices
- coroutines keep program references / indices, not owned clones

This is semantically safe because programs are immutable after load.

#### Tasks

- [x] Audit where `Vec<Instr>` is cloned during load/spawn
- [x] Define an immutable program storage abstraction for loaded code images
- [x] Refactor coroutine/program ownership to use indices or shared slices
- [x] Remove redundant `program.clone()` paths in choreography/session loading
- [x] Add regression tests for serialization, stepping, and replay with shared code storage
- [x] Add memory comparison benchmark for large multi-role images

#### Success Criteria

- Memory per coroutine/session decreases for large loaded choreographies
- No change in stepping semantics, fault behavior, or trace output
- No measurable regression in instruction dispatch latency

### 4. Stable Numeric Runtime Interning

#### Problem

Hot runtime paths repeatedly clone `String`s for roles, labels, handlers, and edges. Ordered maps preserve determinism, but strings in the hot path are expensive.

#### Design

Intern stable identifiers at load time:

- role ids
- label ids
- handler ids
- edge ids

Use deterministic assignment order derived from canonical load order. Keep string forms only in external-facing layers, serialization, and observability rendering.

#### Tasks

- [ ] Identify hot string-bearing runtime structures in scheduler/session/dispatch paths
- [ ] Define deterministic intern tables for roles, labels, handlers, and edges
- [ ] Refactor hot runtime state to use interned ids internally
- [ ] Preserve canonical string output at API/trace boundaries
- [x] Add serialization compatibility tests
- [x] Add CPU microbenchmarks for send/recv/choose-heavy traces

#### Success Criteria

- Reduced allocation counts in send/recv/choose-heavy workloads
- Lower CPU time in edge construction / map lookup / trace emission hot paths
- No change in externally visible trace strings or serialization shape unless explicitly versioned

### 5. Scheduler Eligibility Caching

#### Problem

The runtime performs repeated readiness and eligibility scans each round. That creates avoidable CPU overhead under large coroutine counts.

#### Design

Maintain incremental eligibility sets inside the scheduler:

- ready
- ready-and-eligible
- blocked by reason
- paused/crashed/timed-out filtered state

Update membership on state transitions instead of recomputing from global scans each round.

#### Tasks

- [ ] Profile current scheduler round cost under large runnable/blocked coroutine sets
- [ ] Identify repeated scans in kernel step selection
- [ ] Extend scheduler bookkeeping with cached eligibility state
- [ ] Update transition sites for pause/crash/timeout/unblock/reschedule
- [ ] Add scheduler invariant checks in debug builds
- [ ] Add scale benchmark for many mostly-blocked coroutines

#### Success Criteria

- Lower scheduler CPU cost at high coroutine counts
- No change in selected coroutine order under equivalent logical state
- Debug invariant checks pass across all scheduler policies

### 6. Auth / Replay Cost Isolation

#### Problem

Message signing, verification, and Merkle/auth bookkeeping are expensive and can dominate runtime cost even when the performance question is scheduler/runtime overhead rather than authenticated transport.

#### Design

Keep strict semantics, but separate runtime modes clearly:

- scheduler/runtime baseline
- structural validation
- strict schema validation
- replay tracking
- full auth verification and authenticated history

Also improve encoding cost by using canonical binary encoding instead of JSON for hashed leaf material where possible.

#### Tasks

- [ ] Measure current cost share of signing, verification, and auth tree maintenance
- [x] Replace JSON hashing in auth-tree updates with canonical binary encoding where safe
- [x] Separate replay/auth overhead in benchmark harnesses and tuning profiles
- [x] Add targeted microbenchmarks for send/recv with replay off/sequence/nullifier modes
- [x] Add targeted microbenchmarks for payload validation off/structural/strict-schema
- [x] Ensure configuration combinations are explicit and documented

#### Success Criteria

- Clear overhead attribution for replay/auth vs scheduler/runtime
- Lower CPU time in authenticated transport paths after encoding improvements
- No replay/auth semantic regressions in strict modes

### 7. Choreography Interpreter Allocation Reduction

#### Problem

The free-algebra interpreter uses recursive async execution and clones branch/loop bodies. This is clean but alloc-heavy.

#### Design

Convert interpreter execution from recursive cloning to an explicit execution stack:

- stack frames for branch/loop/timeout control
- borrowed or shared program segments where possible
- preserved deterministic effect order

This is an implementation optimization only; the effect model stays unchanged.

#### Tasks

- [ ] Profile recursion/cloning overhead in interpreter-heavy workloads
- [ ] Design explicit interpreter frame stack
- [ ] Remove unnecessary `Program`/branch body clones in loops and branches
- [ ] Preserve timeout and failure propagation semantics exactly
- [ ] Add interpreter equivalence tests comparing old/new outputs on the same programs
- [ ] Add choreography-side allocation benchmark

#### Success Criteria

- Lower allocation counts in branch/loop-heavy interpreted programs
- No change in effect order, error propagation, or timeout semantics
- No regressions in existing choreography integration tests

### 8. Pre-Sizing And Layout Hygiene

#### Problem

Several runtime structures know their eventual size at open/load time but still grow opportunistically. That increases allocator traffic.

#### Design

Pre-size based on known role/session/cardinality metadata and use tighter layouts where practical.

#### Tasks

- [x] Pre-size buffers/maps/vectors during session open based on role count
- [x] Pre-size coroutine/program arrays during choreography load
- [ ] Review large enums/structs in hot state for unnecessary padding or cloning
- [ ] Add allocation-count benchmarks for session open and choreography load

#### Success Criteria

- Reduced allocations in session open/load benchmarks
- No change in runtime semantics

### 9. Explicit Memory Accounting

#### Problem

Without subsystem-level retained-byte accounting, memory regressions are difficult to localize.

#### Design

Add lightweight memory accounting APIs that estimate retained bytes by subsystem:

- sessions
- closed-session archival state
- buffers
- traces
- auth state
- code storage
- coroutine state

This does not need allocator-perfect precision; it needs stable comparative signal.

#### Tasks

- [ ] Define retained-byte accounting structures per subsystem
- [x] Expose memory usage snapshots from VM runtime APIs
- [x] Add churn and long-run tests that assert bounded growth under capped modes
- [x] Add benchmark harness output for memory snapshots before/after workloads

#### Success Criteria

- Memory regressions can be attributed to named subsystems
- Churn tests can assert that closed-session and trace retention stay bounded under configured policies

## Profiling Profiles

These profiles are intended to be added to workspace `Cargo.toml`.

```toml
[profile.perf-cpu]
inherits = "release"
debug = 1
lto = "thin"
codegen-units = 1
incremental = false
strip = "none"

[profile.perf-heap]
inherits = "release"
debug = 1
lto = "off"
codegen-units = 1
incremental = false
strip = "none"

[profile.perf-debug]
inherits = "dev"
opt-level = 1
debug = 2
incremental = false
```

## Runtime Profiling Matrix

Use the existing VM config knobs to define reproducible runtime scenarios.

### Profile A: Strict Minimal

- `determinism_mode = full`
- `threaded_round_semantics = canonical_one_step`
- `effect_trace_capture_mode = disabled`
- `payload_validation_mode = structural`
- `communication_replay_mode = off`

Purpose:

- baseline scheduler and instruction dispatch cost

### Profile B: Strict Observable

- same as Strict Minimal
- full observable/effect tracing enabled

Purpose:

- instrumentation overhead

### Profile C: Strict Verified

- same deterministic settings
- `payload_validation_mode = strict_schema`
- replay enabled
- authenticated transport bookkeeping enabled

Purpose:

- validation/auth/replay overhead

### Profile D: Strict Churn

- many short-lived sessions
- moderate role count
- closure/reaping focused workload

Purpose:

- retention bugs and close-path cost

### Profile E: Strict Buffer Pressure

- tiny initial capacities
- exercise `Block` and `Resize`

Purpose:

- allocator pressure and queue contention behavior

### Profile F: Strict Large-Fanout

- many roles
- high edge count
- many mostly-blocked coroutines

Purpose:

- scheduler scaling and metadata overhead

### Profile G: Interpreter Heavy

- choreography interpreter path
- branch- and loop-heavy programs

Purpose:

- interpreter recursion/cloning/allocation hotspots

## Tooling

### CPU

- macOS: `samply record -- cargo test -p telltale-vm --bench vm_runtime_bench --profile perf-cpu`
- Linux: `cargo flamegraph -p telltale-vm --bench vm_runtime_bench --profile perf-cpu`
- Symbol/size pressure: `cargo llvm-lines -p telltale-vm`, `cargo bloat -p telltale-vm --profile perf-cpu`

### Heap / Retention

- macOS: Instruments Allocations and Leaks
- Linux: `heaptrack`, `valgrind --tool=massif`
- Rust allocation attribution: `dhat-rs` on churn and interpreter-heavy workloads

### Determinism Guarding

- compare canonical traces across optimization branches
- run replay/equivalence tests under all runtime profiles
- keep debug-only scheduler/state invariants enabled in `perf-debug`

## Recommended Execution Order

1. Closed session reaping
2. Bounded trace retention
3. Explicit memory accounting
4. Shared immutable code images
5. Scheduler eligibility caching
6. Stable numeric interning
7. Auth/replay cost isolation
8. Interpreter allocation reduction
9. Pre-sizing/layout cleanup

## Program-Level Success Criteria

- Canonical traces remain unchanged under `DeterminismMode::Full`
- `cargo test --workspace --all-targets --all-features` remains green
- WASM paths remain green under the pinned Nix shell/toolchain
- Long-running stress tests show bounded memory under capped-trace and reaping modes
- Profiling runs identify named hotspots with before/after deltas, not just anecdotal speedups
