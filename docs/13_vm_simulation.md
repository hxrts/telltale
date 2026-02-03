# VM Simulation

This document covers observable events, trace collection, and the simulator runner.

## Observable Events

The VM emits `ObsEvent` entries into its trace.

```rust
pub enum ObsEvent {
    Sent { tick: u64, session: SessionId, from: String, to: String, label: String },
    Received { tick: u64, session: SessionId, from: String, to: String, label: String },
    Opened { tick: u64, session: SessionId, roles: Vec<String> },
    Closed { tick: u64, session: SessionId },
    Halted { tick: u64, coro_id: usize },
    Invoked { tick: u64, coro_id: usize, role: String },
    Faulted { tick: u64, coro_id: usize, fault: Fault },
}
```

Each event carries the scheduler tick from the simulation clock. The `Sent` and `Received` events track message flow by role name and label. The `Invoked` event records the role and coroutine that reached an effect boundary.

## Simulation Clock

The VM uses a deterministic `SimClock` for reproducible runs.

```rust
pub struct SimClock {
    pub tick: u64,
    pub time: Duration,
    pub tick_duration: Duration,
}

impl SimClock {
    pub fn advance(&mut self) {
        self.tick += 1;
        self.time += self.tick_duration;
    }
}
```

The clock advances once per scheduler round. The `tick` field is a monotonic counter and `time` is a simulated duration.

## Trace Collection

The VM exposes its trace as a slice.

```rust
impl VM {
    pub fn trace(&self) -> &[ObsEvent] {
        &self.trace
    }
}
```

Consumers filter the slice to extract session specific subsequences. Tests often normalize events by projecting only `Sent` and `Received` tuples for comparison across runs.

```rust
let per_session: Vec<(String, String, String, String)> = vm
    .trace()
    .iter()
    .filter_map(|ev| match ev {
        ObsEvent::Sent { session, from, to, label, .. } if *session == sid => {
            Some(("sent".into(), from.clone(), to.clone(), label.clone()))
        }
        ObsEvent::Received { session, from, to, label, .. } if *session == sid => {
            Some(("recv".into(), from.clone(), to.clone(), label.clone()))
        }
        _ => None,
    })
    .collect();
```

This filtering pattern appears in the simulator and VM test suites. It supports N invariance checks by comparing per session traces.

## Simulator Trace Format

The simulator records state snapshots as `Trace` records.

```rust
pub struct StepRecord {
    pub step: usize,
    pub role: String,
    pub state: Vec<f64>,
}

pub struct Trace {
    pub records: Vec<StepRecord>,
}
```

Each `StepRecord` stores the post step register state for one role. The `Trace` type is a collection of those records and is the output of the simulator runners.

## VM Runner Integration

The `telltale-simulator` runner executes bytecode and produces `Trace` output.

```rust
pub struct ChoreographySpec {
    pub local_types: BTreeMap<String, LocalTypeR>,
    pub global_type: GlobalType,
    pub initial_states: HashMap<String, Vec<f64>>,
}

pub fn run(
    local_types: &BTreeMap<String, LocalTypeR>,
    global_type: &GlobalType,
    initial_states: &HashMap<String, Vec<f64>>,
    steps: usize,
    handler: &dyn EffectHandler,
) -> Result<Trace, String>

pub fn run_concurrent(
    specs: &[ChoreographySpec],
    steps: usize,
    handler: &dyn EffectHandler,
) -> Result<Vec<Trace>, String>
```

The `run` function executes a single choreography and returns a `Trace` of role states. The `run_concurrent` function runs multiple choreographies in one VM and returns one trace per input spec.

```rust
pub struct ScenarioResult {
    pub trace: Trace,
    pub violations: Vec<PropertyViolation>,
}

pub fn run_with_scenario(
    local_types: &BTreeMap<String, LocalTypeR>,
    global_type: &GlobalType,
    initial_states: &HashMap<String, Vec<f64>>,
    scenario: &Scenario,
    handler: &dyn EffectHandler,
) -> Result<ScenarioResult, String>
```

The scenario runner applies fault injection, network models, and property monitoring. It returns both the trace and any property violations.

See [Effect Handlers](07_effect_handlers.md) for handler implementation and [VM Scheduling](11_vm_scheduling.md) for concurrency details.
