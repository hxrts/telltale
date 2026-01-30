# Topology

Topology separates protocol logic from deployment configuration. Choreographies remain location-free while topology definitions specify where roles execute. This enables the same protocol to run in different environments without modification.

## Overview

The topology system provides three capabilities. It maps roles to network locations. It defines constraints on role placement. It selects transports based on location relationships.

## Design Principle

Choreographies describe what happens between roles, not where they are.

```
Alice -> Bob: Ping
Bob -> Alice: Pong
```

This protocol works regardless of whether Alice and Bob are in the same process, on the same machine, or across continents. Location is a deployment concern, not a protocol concern.

The topology layer makes this separation explicit.

```
Choreography        GlobalType          Topology            Execution
─────────────────────────────────────────────────────────────────────
Alice -> Bob: Ping  comm "Alice" "Bob"  Alice ↦ nodeA      send(nodeA, nodeB, Ping)
                    [("Ping", end)]     Bob ↦ nodeB
```

This diagram shows how a choreography and a topology combine at runtime. It highlights that location mapping happens after projection.

## Location Types

Locations specify where a role executes.

```rust
pub enum Location {
    Local,                       // In-process
    Remote(TopologyEndpoint),    // Network endpoint
    Colocated(RoleName),         // Same node as another role
}
```

The `Local` variant indicates in-process execution using memory channels. The `Remote` variant specifies a network endpoint. The `Colocated` variant references another role's location.

## Topology Structure

A topology maps roles to locations with optional constraints.

```rust
pub struct Topology {
    mode: Option<TopologyMode>,
    locations: BTreeMap<RoleName, Location>,
    constraints: Vec<TopologyConstraint>,
}
```

The `mode` field stores an optional deployment mode. The `locations` field maps role names to their locations. The `constraints` field specifies placement requirements.

## Topology Constraints

Constraints express requirements on role placement.

```rust
pub enum TopologyConstraint {
    Colocated(RoleName, RoleName), // Must be same node
    Separated(RoleName, RoleName), // Must be different nodes
    Pinned(RoleName, Location),    // Must be at specific location
    Region(RoleName, Region),      // Must be in specific region
}
```

Constraints are validated when binding a topology to a choreography.

## Role Family Constraints

For protocols with parameterized roles (wildcards and ranges), you can specify instance count constraints.

```rust
pub struct RoleFamilyConstraint {
    min: u32,              // Minimum instances required
    max: Option<u32>,      // Maximum instances allowed (None = unlimited)
}
```

These constraints validate that resolved role families have an acceptable number of instances.

### DSL Syntax

Role constraints are specified in a `role_constraints` block.

```rust
topology ThresholdSig for ThresholdSignature {
    Coordinator: localhost:8000

    role_constraints {
        Witness: min = 3, max = 10
        Worker: min = 1
    }

    constraints {
        region: Coordinator -> us_east_1
    }
}
```

The `min` specifies the minimum number of instances required. The `max` specifies the maximum allowed. If `max` is omitted, there is no upper limit.

### Rust API

Role constraints are available through the `Topology` struct.

```rust
use telltale_choreography::topology::{Topology, RoleFamilyConstraint};

// Access constraint for a family
let constraint = topology.get_family_constraint("Witness");
if let Some(c) = constraint {
    println!("Witness: min={}, max={:?}", c.min, c.max);
}

// Validate a resolved count
let count = adapter.family_size("Witness")?;
topology.validate_family("Witness", count)?;
```

The `validate_family` method returns an error if the count is below minimum or above maximum.

### Integration with TestAdapter

Role constraints integrate with the runtime adapter for validation at startup.

```rust
let topology = Topology::parse(config)?.topology;

// Create adapter with role family
let witnesses: Vec<Role> = (0..5).map(Role::Witness).collect();
let adapter = TestAdapter::new(Role::Coordinator)
    .with_family("Witness", witnesses);

// Validate before running protocol
let count = adapter.family_size("Witness")?;
topology.validate_family("Witness", count)?;
```

This ensures the configured role family meets the deployment requirements before the protocol starts.

## DSL Syntax

Topologies are defined using a DSL extension.

```rust
topology TwoPhaseCommit_Dev for TwoPhaseCommit {
    Coordinator: localhost:9000
    ParticipantA: localhost:9001
    ParticipantB: localhost:9002
}
```

This topology maps three roles to local network endpoints.

Constraints are specified in a nested block.

```rust
topology TwoPhaseCommit_Prod for TwoPhaseCommit {
    Coordinator: coordinator.prod.internal:9000
    ParticipantA: participant-a.prod.internal:9000
    ParticipantB: participant-b.prod.internal:9000

    constraints {
        separated: Coordinator, ParticipantA
        separated: Coordinator, ParticipantB
        region: Coordinator -> us_east_1
        region: ParticipantA -> us_west_2
    }
}
```

The constraints block specifies separation constraints and regions. Use multiple `separated` lines when more than two roles must be distinct.

## Built-in Modes

Topology modes provide common configurations.

```
topology MyProtocol_Test for MyProtocol {
    mode: local
}
```

The `local` mode places all roles in the same process. This is the default for testing.

```
topology MyProtocol_K8s for MyProtocol {
    mode: kubernetes(my_app)
}
```

The `kubernetes` mode discovers services using the Kubernetes API. The namespace is provided in the mode value.

```
topology MyProtocol_Consul for MyProtocol {
    mode: consul(dc1)
}
```

The `consul` mode discovers services using the Consul API. The datacenter is provided in the mode value.

Available modes include `local`, `per_role`, `kubernetes`, and `consul`.

## Rust API

### Zero Configuration

Testing requires no explicit topology.

```rust
let handler = InMemoryHandler::new(Role::Alice);
```

This creates an in-memory handler with implicit local topology.

### Minimal Configuration

Simple deployments specify peer addresses directly.

```rust
use telltale_choreography::{RoleName, TopologyEndpoint};

let topology = Topology::builder()
    .local_role(RoleName::from_static("Alice"))
    .remote_role(
        RoleName::from_static("Bob"),
        TopologyEndpoint::new("localhost:8081").unwrap(),
    )
    .build();

let handler = PingPong::with_topology(topology, Role::Alice)?;
```

This builds a topology in code and binds it to a generated protocol handler.

### Full Configuration

Production deployments use explicit topology objects.

```rust
use telltale_choreography::{Region, RoleName, TopologyEndpoint};

let topology = Topology::builder()
    .remote_role(
        RoleName::from_static("Coordinator"),
        TopologyEndpoint::new("coordinator.internal:9000").unwrap(),
    )
    .remote_role(
        RoleName::from_static("ParticipantA"),
        TopologyEndpoint::new("participant-a.internal:9000").unwrap(),
    )
    .remote_role(
        RoleName::from_static("ParticipantB"),
        TopologyEndpoint::new("participant-b.internal:9000").unwrap(),
    )
    .separated(
        RoleName::from_static("Coordinator"),
        RoleName::from_static("ParticipantA"),
    )
    .separated(
        RoleName::from_static("Coordinator"),
        RoleName::from_static("ParticipantB"),
    )
    .region(
        RoleName::from_static("Coordinator"),
        Region::new("us_east_1").unwrap(),
    )
    .build();

let handler = TwoPhaseCommit::with_topology(topology, Role::Coordinator)?;
```

This example configures explicit endpoints and constraints. It then creates a topology aware handler for a role.

### Loading from Files

Topologies can be loaded from external files.

```rust
let parsed = Topology::load("deploy/prod.topology")?;
let handler = PingPong::with_topology(parsed.topology, Role::Alice)?;
```

This supports separation of code and configuration.

## Topology Integration

Topology definitions are separate from the choreography DSL. Define topologies in standalone `.topology` files or strings and load them at runtime.

```rust
let parsed = Topology::load("deploy/dev.topology")?;
let handler = PingPong::with_topology(parsed.topology, Role::Alice)?;
```

This loads a topology file and binds it to a generated handler.

You can also parse a topology from a string.

```rust
use telltale_choreography::topology::parse_topology;

let parsed = parse_topology(r#"
topology Dev for PingPong {
  Alice: localhost:8080
  Bob: localhost:8081
}
"#)?;

let handler = PingPong::with_topology(parsed.topology, Role::Alice)?;
```

This parses the DSL into a `ParsedTopology`. The `topology` field contains the `Topology` value used at runtime.

## Transport Selection

The topology determines which transport to use for each role pair.

```rust
use telltale_choreography::{RoleName, TopologyError};

fn select_transport(
    topo: &Topology,
    from: &RoleName,
    to: &RoleName,
) -> Result<Transport, TopologyError> {
    let from_loc = topo.get_location(from)?;
    let to_loc = topo.get_location(to)?;
    Ok(match (from_loc, to_loc) {
        (Location::Local, Location::Local) => InMemoryTransport::new(),
        (_, Location::Remote(endpoint)) => TcpTransport::new(endpoint),
        (_, Location::Colocated(peer)) => SharedMemoryTransport::new(peer),
    })
}
```

The handler automatically routes messages through appropriate transports.

## Validation

Topologies are validated against choreography roles.

```rust
use telltale_choreography::RoleName;

let choreo = parse_choreography_str(dsl)?;
let topo = parse_topology(topo_dsl)?;

let roles = [
    RoleName::from_static("Alice"),
    RoleName::from_static("Bob"),
];
let validation = topo.topology.validate(&roles);
if !validation.is_valid() {
    return Err(format!("Topology validation failed: {:?}", validation).into());
}
```

Validation ensures all choreography roles appear in the topology. It also verifies constraints are satisfiable.

## Lean Correspondence

The Lean formalization defines topology types and validation.

```lean
inductive Location where
  | local
  | remote (endpoint : String)
  | colocated (peer : String)

structure Topology where
  locations : RBMap String Location compare
  constraints : List TopologyConstraint

def Topology.valid (topo : Topology) (g : GlobalType) : Bool :=
  g.roles.all (fun r => topo.locations.contains r)
```

Projection correctness is proven independent of topology. The `project` function does not reference location information.

## Default Behavior

The `InMemoryHandler::new()` API remains valid. Choreographies without explicit topologies use implicit local mode.

## Usage Example

```rust
use telltale_choreography::{choreography, RoleName, Topology, TopologyEndpoint};

choreography!(r#"
protocol Auction =
  roles Auctioneer, Bidder1, Bidder2
  Auctioneer -> Bidder1 : Item
  Auctioneer -> Bidder2 : Item
  Bidder1 -> Auctioneer : Bid
  Bidder2 -> Auctioneer : Bid
  Auctioneer -> Bidder1 : Result
  Auctioneer -> Bidder2 : Result
"#);

// Development topology
let dev_topo = Topology::builder()
    .remote_role(
        RoleName::from_static("Auctioneer"),
        TopologyEndpoint::new("localhost:9000").unwrap(),
    )
    .remote_role(
        RoleName::from_static("Bidder1"),
        TopologyEndpoint::new("localhost:9001").unwrap(),
    )
    .remote_role(
        RoleName::from_static("Bidder2"),
        TopologyEndpoint::new("localhost:9002").unwrap(),
    )
    .build();

// Production topology
let prod_topo = Topology::builder()
    .remote_role(
        RoleName::from_static("Auctioneer"),
        TopologyEndpoint::new("auction.prod:9000").unwrap(),
    )
    .remote_role(
        RoleName::from_static("Bidder1"),
        TopologyEndpoint::new("bidder1.prod:9000").unwrap(),
    )
    .remote_role(
        RoleName::from_static("Bidder2"),
        TopologyEndpoint::new("bidder2.prod:9000").unwrap(),
    )
    .separated(
        RoleName::from_static("Auctioneer"),
        RoleName::from_static("Bidder1"),
    )
    .separated(
        RoleName::from_static("Auctioneer"),
        RoleName::from_static("Bidder2"),
    )
    .build();

// Same protocol, different deployments
let dev_handler = Auction::with_topology(dev_topo, Role::Auctioneer)?;
let prod_handler = Auction::with_topology(prod_topo, Role::Auctioneer)?;
```

This example shows the same auction protocol deployed in development and production environments.
