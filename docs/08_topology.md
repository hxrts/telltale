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
    Local,            // In-process
    Remote(String),   // Network endpoint
    Colocated(String), // Same node as another role
}
```

The `Local` variant indicates in-process execution using memory channels. The `Remote` variant specifies a network endpoint. The `Colocated` variant references another role's location.

## Topology Structure

A topology maps roles to locations with optional constraints.

```rust
pub struct Topology {
    mode: Option<TopologyMode>,
    locations: BTreeMap<String, Location>,
    constraints: Vec<TopologyConstraint>,
}
```

The `mode` field stores an optional deployment mode. The `locations` field maps role names to their locations. The `constraints` field specifies placement requirements.

## Topology Constraints

Constraints express requirements on role placement.

```rust
pub enum TopologyConstraint {
    Colocated(String, String),      // Must be same node
    Separated(String, String),      // Must be different nodes
    Pinned(String, Location),       // Must be at specific location
    Region(String, String),         // Must be in specific region
}
```

Constraints are validated when binding a topology to a choreography.

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
let topology = Topology::builder()
    .local_role("Alice")
    .remote_role("Bob", "localhost:8081")
    .build();

let handler = PingPong::with_topology(topology, "Alice")?;
```

This builds a topology in code and binds it to a generated protocol handler.

### Full Configuration

Production deployments use explicit topology objects.

```rust
let topology = Topology::builder()
    .remote_role("Coordinator", "coordinator.internal:9000")
    .remote_role("ParticipantA", "participant-a.internal:9000")
    .remote_role("ParticipantB", "participant-b.internal:9000")
    .separated("Coordinator", "ParticipantA")
    .separated("Coordinator", "ParticipantB")
    .region("Coordinator", "us_east_1")
    .build();

let handler = TwoPhaseCommit::with_topology(topology, "Coordinator")?;
```

This example configures explicit endpoints and constraints. It then creates a topology aware handler for a role.

### Loading from Files

Topologies can be loaded from external files.

```rust
let parsed = Topology::load("deploy/prod.topology")?;
let handler = PingPong::with_topology(parsed.topology, "Alice")?;
```

This supports separation of code and configuration.

## Topology Integration

Topology definitions are separate from the choreography DSL. Define topologies in standalone `.topology` files or strings and load them at runtime.

```rust
let parsed = Topology::load("deploy/dev.topology")?;
let handler = PingPong::with_topology(parsed.topology, "Alice")?;
```

This loads a topology file and binds it to a generated handler.

You can also parse a topology from a string.

```rust
use rumpsteak_aura_choreography::topology::parse_topology;

let parsed = parse_topology(r#"
topology Dev for PingPong {
  Alice: localhost:8080
  Bob: localhost:8081
}
"#)?;

let handler = PingPong::with_topology(parsed.topology, "Alice")?;
```

This parses the DSL into a `ParsedTopology`. The `topology` field contains the `Topology` value used at runtime.

## Transport Selection

The topology determines which transport to use for each role pair.

```rust
fn select_transport(topo: &Topology, from: &str, to: &str) -> Transport {
    match (topo.get_location(from), topo.get_location(to)) {
        (Location::Local, Location::Local) => InMemoryTransport::new(),
        (_, Location::Remote(endpoint)) => TcpTransport::new(endpoint),
        (_, Location::Colocated(peer)) => SharedMemoryTransport::new(peer),
    }
}
```

The handler automatically routes messages through appropriate transports.

## Validation

Topologies are validated against choreography roles.

```rust
let choreo = parse_choreography_str(dsl)?;
let topo = parse_topology(topo_dsl)?;

let roles = ["Alice", "Bob"];
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
use rumpsteak_aura_choreography::{choreography, Topology};

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
    .remote_role("Auctioneer", "localhost:9000")
    .remote_role("Bidder1", "localhost:9001")
    .remote_role("Bidder2", "localhost:9002")
    .build();

// Production topology
let prod_topo = Topology::builder()
    .remote_role("Auctioneer", "auction.prod:9000")
    .remote_role("Bidder1", "bidder1.prod:9000")
    .remote_role("Bidder2", "bidder2.prod:9000")
    .separated("Auctioneer", "Bidder1")
    .separated("Auctioneer", "Bidder2")
    .build();

// Same protocol, different deployments
let dev_handler = Auction::with_topology(dev_topo, "Auctioneer")?;
let prod_handler = Auction::with_topology(prod_topo, "Auctioneer")?;
```

This example shows the same auction protocol deployed in development and production environments.
