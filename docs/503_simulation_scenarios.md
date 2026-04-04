# Simulation Scenarios

This page documents scenario configuration and middleware behavior.
It covers the TOML schema, budgeted adversary declarations, first-class reconfiguration, network modeling, properties, checkpointing, and current limits.

## Scenario Schema

`Scenario` is parsed from TOML and drives `run_with_scenario(...)`.
`seed` defaults to `0`.
`field` is optional and is only required by built-in field-driven surfaces such as `FieldAdapter::from_scenario(...)`, `derive_initial_states(&Scenario)`, and the simulator CLI binaries.
Execution defaults are resolved through `Scenario.execution`.
`backend = "auto"` resolves to the authoritative canonical lane with `scheduler_concurrency = 1` and `worker_threads = 1`.
Theorem-facing interpretation is configured separately through `Scenario.theorem`.

```rust
pub struct Scenario {
    pub name: String,
    pub roles: Vec<String>,
    pub steps: u64,
    pub execution: ExecutionSpec,
    pub seed: u64,
    pub network: Option<NetworkSpec>,
    pub field: Option<FieldSpec>,
    pub reconfigurations: Vec<ReconfigurationSpec>,
    pub adversaries: Vec<AdversarySpec>,
    pub properties: Option<PropertiesSpec>,
    pub checkpoint_interval: Option<u64>,
    pub theorem: TheoremProfileSpec,
    pub extensions: BTreeMap<String, toml::Value>,
}
```

`network`, `field`, `reconfigurations`, `adversaries`, `properties`, `checkpoint_interval`, and `extensions` are optional.

```rust
pub struct ExecutionSpec {
    pub backend: ExecutionBackend,
    pub scheduler_policy: SchedulerPolicySpec,
    pub scheduler_concurrency: Option<u64>,
    pub worker_threads: Option<u64>,
}
```

`scheduler_policy` selects the underlying protocol-machine scheduling discipline.
`scheduler_concurrency` controls how much scheduler work one simulator round may admit.
`worker_threads` controls physical parallelism for the threaded backend only.
Canonical execution requires both values to resolve to `1`.
Threaded execution with `scheduler_concurrency = 1` remains exact with respect to the canonical lane, while `scheduler_concurrency > 1` is only authoritative modulo the declared concurrency envelope.

```rust
pub struct TheoremProfileSpec {
    pub scheduler_profile: TheoremSchedulerProfile,
    pub envelope_profile: TheoremEnvelopeProfile,
    pub assumption_bundle: TheoremAssumptionBundle,
}
```

The theorem block does not change runtime execution.
It declares which theorem-side contract the caller wants the run to be interpreted under.
The simulator resolves that declaration against the actual execution regime and reports eligibility in `ScenarioStats.theorem_profile` and `ScenarioReplayArtifact.theorem_profile`.

For recursion-free scenarios, the simulator also derives theorem-native progress quantities in `ScenarioStats.theorem_progress`.
See [Simulation Runner](502_simulation_runner.md) for definitions of the weighted measure, depth, buffer, and critical-capacity phase.

## Scenario Example

```toml
name = "mean_field_adversary_window"
roles = ["A", "B"]
steps = 200
seed = 42
checkpoint_interval = 25

[execution]
backend = "threaded"
scheduler_policy = "round_robin"
scheduler_concurrency = 2
worker_threads = 4

[field]
layer = "mean_field"

[field.params]
beta = "1.5"
species = ["up", "down"]
initial_state = ["0.6", "0.4"]
step_size = "0.01"

[network]
base_latency_ms = 20
latency_variance = "0.10"
loss_probability = "0.02"

[[reconfigurations]]
trigger = { at_tick = 50 }
action = { type = "link", from = "A", to = "B", enabled = false }

[[adversaries]]
id = "loss_window"
trigger = { at_tick = 75 }
action = { type = "withholding" }
budget = { total = 16, mode = "windowed", window_ticks = 8, max_per_window = 2 }

[properties]
invariants = ["no_faults", "simplex", "buffer_bound(0,16)"]
```

Quoted decimal strings are the safest TOML form for `FixedQ32` values.
The parser also accepts compatible numeric representations.

## Adversary Middleware

`AdversaryInjector` wraps the inner handler.
It manages trigger activation, budget accounting, delayed delivery, corruption, withholding, correlated bursts, and crash state.

Supported actions are `withholding`, `timing_disturbance`, `corruption`, `crash`, and `byzantine_interference`.
Supported triggers are `Immediate`, `AtTick`, `AfterStep`, `Random`, and `OnEvent`.
If a trigger declaration sets no trigger field, it defaults to `Immediate`.

An adversary must not set more than one trigger field at once.
The parser rejects multi-trigger declarations.
`Trigger::AfterStep` is evaluated against logical round count rather than raw tick count.

### Adversary Budgets

Every adversary must declare a budget.

```rust
pub struct AdversarySpec {
    pub id: Option<String>,
    pub trigger: TriggerSpec,
    pub action: AdversaryActionSpec,
    pub budget: AdversaryBudgetSpec,
}
```

`budget.total` is the total disturbance or activation budget.
`budget.mode` can be `activation` (one-shot), `independent` (per-message Bernoulli), `windowed` (per-window correlated quotas), or `correlated` (burst-style windows).
`budget.assumption_failure` optionally states which theorem-side clause should fail if the budget exhausts.

Use adversaries for transport disruption and runtime failure only.
Do not encode topology change, handoff, federation cutover, or mode change as adversaries.

## Environment Extensions

`Scenario.extensions` is a domain-neutral namespace map for downstream environment config.
Core `telltale-simulator` does not interpret those values directly.
Instead a `HostAdapter` may inspect one namespace, build external environment models, and return them through `HostAdapter::environment_models(...)`.

This is the supported path for downstream projects that need geometry, radio, mobility, or device-capability config without adding vertical-specific fields to core `Scenario`.

## Reconfiguration Program

`Scenario.reconfigurations` is the first-class surface for simulator-visible topology and authority change.
Each entry has the same trigger vocabulary as `adversaries`, but it activates a semantic reconfiguration operation instead of a transport disturbance.

```rust
pub struct ReconfigurationSpec {
    pub trigger: TriggerSpec,
    pub action: ReconfigurationAction,
    pub effect: ReconfigurationEffect,
}
```

Supported actions are:

- `link`: update one directed link policy
- `delegation`: record an explicit delegation scope transfer between two roles
- `handoff`: record an explicit handoff identifier plus revoked/activated roles
- `federation`: activate or clear a named communication grouping policy
- `mode_transition`: record a mode change for one or more roles

`effect.kind = "pure"` records a pure reconfiguration and must not consume transition budget.
`effect.kind = "transition_choreography"` records a separate cutover budget and must declare `budget_cost > 0`.

The simulator validates reconfiguration footprints before execution.
Unknown roles, duplicated federation members, same-source/same-target delegation, empty handoff ids, and zero-cost transition choreography are rejected at parse time.

## Network Middleware

`NetworkModel` wraps `AdversaryInjector` when network simulation is enabled.
It applies federation connectivity checks, link overrides, latency sampling, loss sampling, and deferred delivery.

Per-link policies match directed `(from, to)` pairs.
`network.links` now describes the static baseline policy for a run.
Dynamic link updates happen through `reconfigurations`.
Reconfiguration-applied link overrides shadow the baseline policy for the affected directed edge only.

Loss is evaluated before latency scheduling.
Dropped messages never enter the in-flight queue.
Zero effective latency produces immediate delivery.

The three middleware surfaces serve distinct purposes: `network` defines baseline transport parameters, `reconfigurations` handles topology and federation cutovers, and `adversaries` injects budgeted disturbances with theorem-facing assumption diagnostics.

## Property Monitoring

`PropertyMonitor` performs online checks by scanning newly appended observable events and machine state each round.
Built-in checks are:

- `NoFaults`: verifies that no coroutine has entered a faulted state during execution.
- `Simplex`: verifies that all coroutine state vectors remain on the probability simplex (all components non-negative, sum to 1 within tolerance).
- `SendRecvLiveness(sid, bound)`: verifies that every send in session `sid` is matched by a receive within `bound` session-local ticks. Uses per-session event counters rather than raw global ticks.
- `TypeMonotonicity(sid)`: verifies that session-type depth never increases for non-recursive local types in session `sid`. Recursive types are skipped.
- `BufferBound(sid, max)`: verifies that no buffer in session `sid` exceeds `max` pending messages.
- `Liveness(name, precondition, goal, bound)`: a custom liveness check. Once the precondition predicate becomes true, the goal predicate must become true within `bound` steps. Predicates can be `no_faults`, `simplex`, tick comparisons, or `distance_to_equilibrium` comparisons.

Invariant strings are parsed by `parse_property`.
Predicate strings are parsed by `parse_predicate`.

## Checkpointing and Replay

`CheckpointStore` snapshots protocol-machine state through the typed persisted replay contract at configured intervals.
When `checkpoint_interval` is set, `run_with_scenario(...)` writes `PersistedReplayArtifact` checkpoint files under `artifacts/<scenario.name>/`.
Replay loads one of those persisted artifacts and re-executes the same shared middleware loop used by fresh scenario runs.
`resume_with_checkpoint_artifact(...)` is the exact resume path because it restores both protocol-machine state and simulator middleware state from the captured artifact.

Scenario replay artifacts also retain the resolved adversary schedule, budget-consumption history, assumption diagnostics, and the canonical reconfiguration trace.

Checkpoint snapshots currently require the canonical backend.
Threaded scenario runs still emit replay artifacts but checkpoint serialization remains canonical-only, and scenarios that request both threaded execution and checkpoints fail validation instead of degrading later at run time.
Checkpoint persistence is best-effort: serialization or file-write failures do not fail the run.
`CheckpointStore::last_persist_error()` exposes the last recorded persistence error.

## Current Limits

Generated effect-family helpers (e.g. `record_return()`, `with_delay_ms()`, `record_stale_late_result()`) are separate programmatic APIs.
They are not a TOML scenario feature.
They are also not yet wired into `SimulationHarness`.

## Related Docs

- [Simulation Overview](501_simulation_overview.md)
- [Simulation Runner](502_simulation_runner.md)
- [Simulation Fields](504_simulation_fields.md)
