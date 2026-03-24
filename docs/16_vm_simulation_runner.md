# Protocol-Machine Simulation Runner

This page documents runner behavior in `telltale-simulator`.
It covers trace shapes, runner APIs, harness APIs, and sampling logic.

## Core Data Types

`Trace` is the sampled role-state output container.
Each `StepRecord` stores one role snapshot at one sampled step.
Scenario-driven runs also carry replay artifacts and run statistics from the protocol machine.
Effect outcomes, publication, and handoff state can be validated from these artifacts without reconstructing them from raw traces.

```rust
pub struct StepRecord {
    pub step: u64,
    pub role: String,
    pub state: Vec<FixedQ32>,
}

pub struct Trace {
    pub records: Vec<StepRecord>,
}

pub struct ScenarioResult {
    pub trace: Trace,
    pub violations: Vec<PropertyViolation>,
    pub replay: ScenarioReplayArtifact,
    pub stats: ScenarioStats,
}
```

`step` is a simulator sampling index.
`state` is extracted from protocol-machine registers as fixed-point values.
`ScenarioResult` bundles the trace with property violations, replay artifacts, and run statistics.
`ScenarioReplayArtifact` contains canonical semantic objects, semantic audit records, effect traces, and output-condition checks.

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

`run` returns one sampled trace.
`run_concurrent` returns one trace per input choreography in deterministic input order.
`run_with_scenario` adds middleware, property checks, replay artifacts, run statistics, and canonical semantic objects.

## Harness API

`SimulationHarness` is the integration path for external projects.
It can run against a direct external handler, a material-backed handler, or a generated effect-family scenario.

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
Generated effect-family scenarios should use `GeneratedEffectScenario` and `ScenarioEffectResult<T>`.
These types let tests script timeouts, stale late results, blocked outcomes, and degraded execution without falling back to raw trace surgery.

## Initial State Derivation

`derive_initial_states(&Scenario)` builds default states by material type.
`mean_field` broadcasts one concentration vector to every role.
`hamiltonian` maps each role index to `[position, momentum]`.
`continuum_field` assigns one scalar field value per role.

## Sampling and Step Mapping

The simulator records samples on invocation boundaries.
It does not record after every protocol-machine instruction.

For each round, the runner counts new `ObsEvent::Invoked` events.
When invoke count reaches role count, the runner records one sample for each role.
The runner also inserts a Mu-step sample at active-node boundaries from `active_per_role`.

## Scenario Execution Order

Scenario runs use a fixed per-round order for determinism.

1. Compute `next_tick` from protocol-machine clock.
2. Advance fault schedule from newly appended semantic audit events.
3. Deliver due delayed messages into protocol-machine buffers.
4. Deliver network middleware queues when network is enabled.
5. Update paused roles from active crash faults.
6. Execute one protocol-machine round with the selected handler domain.
7. Update trace samples from new invoke events.
8. Run online property checks.
9. Persist checkpoint when interval policy triggers.

The replay binary mirrors this order when resuming from checkpoints.

## Determinism and Reproducibility

Simulator randomness is scoped to `SimRng` and seeded from scenario seed.
The protocol machine remains deterministic given effect outcomes and scheduler inputs.
Record ordering is stable within each sampling pass for role snapshots.

## Related Docs

- [Protocol-Machine Simulation](15_vm_simulation_overview.md)
- [Protocol-Machine Simulation Scenarios](17_vm_simulation_scenarios.md)
- [Protocol-Machine Simulation Materials](18_vm_simulation_materials.md)
- [Rust-Lean Parity](19_rust_lean_parity.md)
