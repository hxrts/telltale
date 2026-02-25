# VM Simulation Runner

This page documents runner behavior in `telltale-simulator`.
It covers trace shapes, runner APIs, harness APIs, and sampling logic.

## Core Data Types

`Trace` is the simulator output container.
Each `StepRecord` stores one role snapshot at one sampled step.

```rust
pub struct StepRecord {
    pub step: u64,
    pub role: String,
    pub state: Vec<FixedQ32>,
}

pub struct Trace {
    pub records: Vec<StepRecord>,
}
```

`step` is a simulator sampling index.
`state` is extracted from VM registers as fixed-point values.

## Runner Entry Points

The runner exposes single choreography, multi choreography, and scenario entry points.

```rust
pub fn run(
    local_types: &BTreeMap<String, LocalTypeR>,
    global_type: &GlobalType,
    initial_states: &BTreeMap<String, Vec<FixedQ32>>,
    steps: usize,
    handler: &dyn EffectHandler,
) -> Result<Trace, String>

pub fn run_concurrent(
    specs: &[ChoreographySpec],
    steps: usize,
    handler: &dyn EffectHandler,
) -> Result<Vec<Trace>, String>

pub fn run_with_scenario(
    local_types: &BTreeMap<String, LocalTypeR>,
    global_type: &GlobalType,
    initial_states: &BTreeMap<String, Vec<FixedQ32>>,
    scenario: &Scenario,
    handler: &dyn EffectHandler,
) -> Result<ScenarioResult, String>
```

`run` returns one trace.
`run_concurrent` returns one trace per input choreography in deterministic input order.
`run_with_scenario` adds middleware, property checks, and replay artifacts.

## Harness API

`SimulationHarness` is the integration path for external projects.

```rust
pub trait HostAdapter {
    fn effect_handler(&self) -> &dyn EffectHandler;
    fn initial_states(&self, scenario: &Scenario)
        -> Result<Option<BTreeMap<String, Vec<FixedQ32>>>, String>;
    fn validate_result(&self, scenario: &Scenario, result: &ScenarioResult)
        -> Result<(), String>;
}
```

`DirectAdapter` wraps a direct `EffectHandler`.
`MaterialAdapter` constructs handlers from scenario material parameters.

## Initial State Derivation

`derive_initial_states(&Scenario)` builds default states by material type.
`mean_field` broadcasts one concentration vector to every role.
`hamiltonian` maps each role index to `[position, momentum]`.
`continuum_field` assigns one scalar field value per role.

## Sampling and Step Mapping

The simulator records samples on invocation boundaries.
It does not record after every VM instruction.

For each round, the runner counts new `ObsEvent::Invoked` events.
When invoke count reaches role count, the runner records one sample for each role.
The runner also inserts a Mu-step sample at active-node boundaries from `active_per_role`.

## Scenario Execution Order

Scenario runs use a fixed per-round order for determinism.

1. Compute `next_tick` from VM clock.
2. Advance fault schedule from newly appended VM events.
3. Deliver due delayed messages into VM buffers.
4. Deliver network middleware queues when network is enabled.
5. Update paused roles from active crash faults.
6. Execute `vm.step_round(handler, scenario.concurrency as usize)`.
7. Update trace samples from new invoke events.
8. Run online property checks.
9. Persist checkpoint when interval policy triggers.

The replay binary mirrors this order when resuming from checkpoints.

## Determinism and Reproducibility

Simulator randomness is scoped to `SimRng` and seeded from scenario seed.
The VM core remains deterministic given effect outcomes and scheduler inputs.
Record ordering is stable within each sampling pass for role snapshots.

## Related Docs

- [VM Simulation](14_vm_simulation_overview.md)
- [VM Simulation Scenarios](14_vm_simulation_scenarios.md)
- [VM Simulation Materials](14_vm_simulation_materials.md)
- [VM Parity](15_vm_parity.md)
