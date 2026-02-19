# Topology

Topology separates protocol logic from deployment configuration. Choreographies remain location free while topology definitions specify where roles execute.

## Core Types

Locations capture how a role is deployed.

```rust
pub enum Location {
    Local,
    Remote(TopologyEndpoint),
    Colocated(RoleName),
}
```

The `Local` variant means in process execution. The `Remote` variant stores a network endpoint. The `Colocated` variant ties a role to another role location.

Topology state holds role mappings, constraints, and optional mode shortcuts.

```rust
pub struct Topology {
    pub mode: Option<TopologyMode>,
    pub locations: BTreeMap<RoleName, Location>,
    pub channel_capacities: BTreeMap<(RoleName, RoleName), ChannelCapacity>,
    pub constraints: Vec<TopologyConstraint>,
    pub role_constraints: BTreeMap<String, RoleFamilyConstraint>,
}
```

`TopologyMode` provides common presets. `TopologyConstraint` and `RoleFamilyConstraint` add placement and role family rules.

```rust
pub enum TopologyMode {
    Local,
    PerRole,
    Kubernetes(Namespace),
    Consul(Datacenter),
}

pub enum TopologyConstraint {
    Colocated(RoleName, RoleName),
    Separated(RoleName, RoleName),
    Pinned(RoleName, Location),
    Region(RoleName, Region),
}

pub struct RoleFamilyConstraint {
    pub min: u32,
    pub max: Option<u32>,
}
```

`TopologyMode` is parsed from DSL values like `local` and `kubernetes(ns)`. Role family constraints are used to validate wildcard and range roles.

## DSL Syntax

Topologies are defined in `.topology` files or parsed from strings.

```text
topology TwoPhaseCommit_Prod for TwoPhaseCommit {
    mode: per_role

    Coordinator: coordinator.prod.internal:9000
    ParticipantA: participant-a.prod.internal:9000
    ParticipantB: participant-b.prod.internal:9000

    role_constraints {
        Participant: min = 2, max = 5
    }

    channel_capacities {
        Coordinator -> ParticipantA: 4
        Coordinator -> ParticipantB: 4
    }

    constraints {
        separated: Coordinator, ParticipantA
        separated: Coordinator, ParticipantB
        region: Coordinator -> us_east_1
    }
}
```

The `role_constraints` block controls acceptable family sizes. The `channel_capacities` block sets per-edge capacity in bits (used for branching feasibility checks). The `constraints` block encodes separation, pinning, and region requirements.

## Rust API

You can build topologies programmatically and validate them against choreography roles.

```rust
use telltale_choreography::{RoleName, Topology, TopologyEndpoint};

let topology = Topology::builder()
    .local_role(RoleName::from_static("Coordinator"))
    .remote_role(
        RoleName::from_static("ParticipantA"),
        TopologyEndpoint::new("localhost:9001").unwrap(),
    )
    .remote_role(
        RoleName::from_static("ParticipantB"),
        TopologyEndpoint::new("localhost:9002").unwrap(),
    )
    .build();

let roles = [
    RoleName::from_static("Coordinator"),
    RoleName::from_static("ParticipantA"),
    RoleName::from_static("ParticipantB"),
];
let validation = topology.validate(&roles);
assert!(validation.is_valid());
```

`Topology::builder` produces a `TopologyBuilder` with fluent helpers. `Topology::validate` checks that all roles referenced in the topology and constraints exist in the choreography.

Topologies can also be loaded from DSL files.

```rust
let parsed = Topology::load("deploy/prod.topology")?;
let topology = parsed.topology;
```

`Topology::load` returns a `ParsedTopology` that includes both the topology and the target protocol name.

## TopologyHandler

`TopologyHandler` wraps transport selection and routing for a role.

```rust
use telltale_choreography::{RoleName, TopologyHandler};

let handler = TopologyHandler::local(RoleName::from_static("Alice"));
handler.initialize().await?;
```

The local constructor sets `TopologyMode::Local` and creates in process transports. For custom layouts, use `TopologyHandler::new` or the builder with a `Topology`.

Generated protocols include helpers like `Protocol::handler(role)` and `Protocol::with_topology(topology, role)`. These return a `TopologyHandler` for the selected role.

## Transport Selection

Transport selection is based on role locations.

```rust
use telltale_choreography::topology::{TransportFactory, TransportType};

let transport_type = TransportFactory::transport_for_location(
    &RoleName::from_static("Alice"),
    &RoleName::from_static("Bob"),
    &topology,
)?;
assert!(matches!(transport_type, TransportType::Tcp));
```

`TransportFactory::create` currently returns an `InMemoryChannelTransport` for all modes. The `TransportType` value signals intent but remote transports are placeholders.

## Lean Correspondence

The Lean formalization for topology is in `lean/Protocol/Spatial.lean`. Projection correctness does not depend on topology data, so location checks are enforced during deployment instead of compilation.

See [Choreographic DSL](04_choreographic_dsl.md) for role declarations and [Effect Handlers](08_effect_handlers.md) for handler usage patterns.
